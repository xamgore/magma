#!/usr/bin/env python3
"""Bundle project sources in the module order shared by defs and deps."""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import heapq
import json
from pathlib import Path
import subprocess
import sys
from typing import Iterator

ROOT = Path(__file__).resolve().parents[1]
PROJECT_ROOTS = ('Difan', 'Magma')


def name_parts(name: str) -> list[str]:
    """Split a Lean module name, preserving dots inside quoted components."""
    parts: list[str] = []
    current: list[str] = []
    quoted = False
    for char in name:
        if char == '«':
            quoted = True
        elif char == '»':
            quoted = False
        elif char == '.' and not quoted:
            parts.append(''.join(current))
            current = []
        else:
            current.append(char)
    parts.append(''.join(current))
    return parts


def project_module(name: str) -> bool:
    return name_parts(name)[0] in PROJECT_ROOTS


def header_tokens(source: str) -> Iterator[str]:
    """Read header tokens without mistaking nested comments for imports."""
    i = 0
    while i < len(source):
        if source[i].isspace():
            i += 1
        elif source.startswith('--', i):
            end = source.find('\n', i)
            i = len(source) if end < 0 else end + 1
        elif source.startswith('/-', i):
            depth = 1
            i += 2
            while i < len(source) and depth:
                if source.startswith('/-', i):
                    depth += 1
                    i += 2
                elif source.startswith('-/', i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            if depth:
                raise ValueError('Unclosed block comment in module header')
        else:
            start = i
            quoted = False
            while i < len(source):
                char = source[i]
                if char == '«':
                    quoted = True
                elif char == '»':
                    quoted = False
                if not quoted and (char.isspace() or source.startswith(('--', '/-'), i)):
                    break
                i += 1
            yield source[start:i]


def source_imports(source: str) -> tuple[str, ...]:
    tokens = iter(header_tokens(source))
    imports: list[str] = []
    while (token := next(tokens, None)) is not None:
        if token in ('module', 'prelude'):
            continue
        while token in ('public', 'meta'):
            token = next(tokens, None)
        if token != 'import':
            break
        name = next(tokens, None)
        if name == 'all':
            name = next(tokens, None)
        if not name:
            raise ValueError('Missing module name after import')
        if project_module(name):
            imports.append(name)
    return tuple(dict.fromkeys(imports))


@dataclass(frozen=True)
class Module:
    name: str
    path: str
    imports: tuple[str, ...]


def ordered_modules(report: dict, root: Path, include_evidence: bool = True) -> list[Module]:
    """Stable Kahn order; Lean's traversal breaks ties for compiled modules."""
    if report.get('schemaVersion', 0) < 2:
        raise ValueError('Dependency metadata needs schema version 2; rebuild deps')
    modules = {
        item['name']: Module(item['name'], item['path'], tuple(dict.fromkeys(item['imports'])))
        for item in report['modules']
    }
    by_path = {module.path: module.name for module in modules.values()}
    if include_evidence:
        for path in sorted(path for library in PROJECT_ROOTS
                           for path in (root / library).rglob('*.lean')):
            relative = path.relative_to(root).as_posix()
            if relative in by_path:
                continue
            parts = path.relative_to(root).with_suffix('').parts
            name = '.'.join(part if part.isidentifier() else f'«{part}»' for part in parts)
            modules[name] = Module(name, relative, source_imports(path.read_text(encoding='utf-8')))
            by_path[relative] = name

    # Resolve quoted spellings by their actual source path.
    normalized: dict[str, Module] = {}
    for module in modules.values():
        dependencies = []
        for dependency in module.imports:
            path = '/'.join(name_parts(dependency)) + '.lean'
            if path not in by_path:
                raise ValueError(f'{module.name} imports missing project module {dependency}')
            dependencies.append(by_path[path])
        normalized[module.name] = Module(module.name, module.path, tuple(dict.fromkeys(dependencies)))
    modules = normalized
    preferred = report['moduleOrder']
    if len(preferred) != len(set(preferred)) or set(preferred) != {item['name'] for item in report['modules']}:
        raise ValueError('Inconsistent moduleOrder in dependency metadata')
    extra = sorted(set(modules) - set(preferred), key=lambda n: modules[n].path)
    scale = len(extra) + 1
    ranks = {name: index * scale for index, name in enumerate(preferred)}
    previous = -1
    for name in extra:
        # Numbered Evidence iterations follow their library prerequisites and
        # each other, without moving later independent library branches forward.
        previous = max([previous, *(ranks.get(dep, -1) for dep in modules[name].imports)]) + 1
        ranks[name] = previous
    users: dict[str, list[str]] = {name: [] for name in modules}
    remaining = {name: len(module.imports) for name, module in modules.items()}
    for name, module in modules.items():
        for dependency in module.imports:
            users[dependency].append(name)
    ready = [(ranks[name], name) for name, count in remaining.items() if count == 0]
    heapq.heapify(ready)
    result = []
    while ready:
        _, name = heapq.heappop(ready)
        result.append(modules[name])
        for user in users[name]:
            remaining[user] -= 1
            if remaining[user] == 0:
                heapq.heappush(ready, (ranks[user], user))
    if len(result) != len(modules):
        cycle = ', '.join(name for name in modules if remaining[name])
        raise ValueError(f'Project import cycle: {cycle}')
    if [module.name for module in result if module.name in set(preferred)] != preferred:
        raise ValueError('Compiled moduleOrder is not dependency-first; rebuild deps')
    # Aggregate roots reexport libraries. Flatten either root, including nested
    # aggregate imports, while preserving dependencies across both libraries.
    def prerequisites(name: str) -> tuple[str, ...]:
        if name not in PROJECT_ROOTS:
            return (name,)
        return tuple(dependency for imported in modules[name].imports
                     for dependency in prerequisites(imported))

    return [Module(module.name, module.path, tuple(dict.fromkeys(
        dependency
        for imported in module.imports
        for dependency in prerequisites(imported)
    ))) for module in result if module.name not in PROJECT_ROOTS]


def render_bundle(modules: list[Module], root: Path) -> str:
    parts = [
        '-- Project reading bundle: complete original sources in dependency order.\n',
        '-- Module markers record import names and source paths.\n',
        '-- Each marked section is a separate original Lean module.\n\n',
    ]
    for module in modules:
        source = (root / module.path).read_text(encoding='utf-8')
        parts.append(f'-- BEGIN MODULE: {module.name} | {module.path}\n')
        parts.append(source)
        if not source.endswith('\n'):
            parts.append('\n')
        parts.append(f'-- END MODULE: {module.name}\n\n')
    return ''.join(parts)


def render_mermaid(modules: list[Module]) -> str:
    """Transitive reduction keeps the actual import DAG readable."""
    identifiers = {module.name: f'm{index}' for index, module in enumerate(modules)}
    ancestors: dict[str, set[str]] = {}
    lines = ['%% Generated module DAG; arrows point from dependency to importer.', 'flowchart TD']
    for module in modules:
        label = module.name.replace('"', '&quot;')
        lines.append(f'  {identifiers[module.name]}["{label}"]')
        closure = set(module.imports)
        for dependency in module.imports:
            closure.update(ancestors[dependency])
        ancestors[module.name] = closure
    for module in modules:
        for dependency in module.imports:
            if any(dependency in ancestors[other] for other in module.imports if other != dependency):
                continue
            lines.append(f'  {identifiers[dependency]} --> {identifiers[module.name]}')
    return '\n'.join(lines) + '\n'


def load_report() -> dict:
    # Build output must never enter the source bundle on stdout.
    subprocess.run(['lake', 'build', 'deps'], cwd=ROOT, stdout=sys.stderr, check=True)
    executable = ROOT / '.lake/build/bin' / ('deps.exe' if sys.platform == 'win32' else 'deps')
    result = subprocess.run(['lake', 'env', str(executable)], cwd=ROOT, stdout=subprocess.PIPE, text=True, check=True)
    return json.loads(result.stdout)


def write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding='utf-8')


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('-o', '--output', type=Path, help='Write the source bundle here instead of stdout')
    parser.add_argument('--mermaid', type=Path, help='Also write the reduced module DAG as Mermaid')
    parser.add_argument('--library-only', action='store_true',
                        help='Only bundle compiled library modules; default also reads every Evidence source')
    args = parser.parse_args()
    try:
        report = load_report()
        modules = ordered_modules(report, ROOT, not args.library_only)
        bundle = render_bundle(modules, ROOT)
        if args.output:
            write_text(args.output, bundle)
        else:
            sys.stdout.write(bundle)
        if args.mermaid:
            write_text(args.mermaid, render_mermaid(modules))
    except (ValueError, OSError, subprocess.CalledProcessError) as error:
        parser.exit(1, f'export_sources: {error}\n')


if __name__ == '__main__':
    main()
