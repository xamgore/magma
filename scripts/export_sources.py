#!/usr/bin/env python3
"""Bundle project sources in dependency order, without compiling experiments."""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import heapq
from pathlib import Path
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


def ordered_modules(root: Path, *, library_only: bool = False) -> list[Module]:
    """Read project imports and reproduce the Lean libraries' dependency-first order.

    Traverse the two aggregate root modules exactly as Lean does. Other Lean
    sources (notably numbered experiments) are read without elaborating them.
    """
    paths = sorted(
        [root / f'{name}.lean' for name in PROJECT_ROOTS]
        + [p for name in PROJECT_ROOTS for p in (root / name).rglob('*.lean')]
    )
    by_path: dict[str, str] = {}
    modules: dict[str, Module] = {}
    for path in paths:
        relative = path.relative_to(root).as_posix()
        parts = path.relative_to(root).with_suffix('').parts
        name = '.'.join(part if part.isidentifier() else f'«{part}»' for part in parts)
        if name in modules:
            raise ValueError(f'Duplicate project module {name}')
        modules[name] = Module(name, relative, source_imports(path.read_text(encoding='utf-8')))
        by_path[relative] = name

    # Quoted Lean components such as «01_UInt16Search» refer to filenames
    # beginning with digits. Resolve those imports through the source paths.
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

    preferred: list[str] = []
    states: dict[str, int] = {}

    def visit(name: str) -> None:
        status = states.get(name, 0)
        if status == 1:
            raise ValueError(f'Project import cycle through {name}')
        if status == 2:
            return
        states[name] = 1
        for dependency in modules[name].imports:
            visit(dependency)
        states[name] = 2
        preferred.append(name)

    for name in PROJECT_ROOTS:
        visit(name)

    if library_only:
        modules = {name: modules[name] for name in preferred}

    # Keep compiler-imported modules in the same order as the reading index.
    # Place independent experimental sources after their prerequisites, sorted
    # by pathname, without running or compiling any of them.
    extra = sorted(set(modules) - set(preferred), key=lambda n: modules[n].path)
    scale = len(extra) + 1
    ranks = {name: index * scale for index, name in enumerate(preferred)}
    previous = -1
    for name in extra:
        previous = max([previous, *(ranks.get(dep, -1) for dep in modules[name].imports)]) + 1
        ranks[name] = previous
    users: dict[str, list[str]] = {name: [] for name in modules}
    remaining = {name: len(module.imports) for name, module in modules.items()}
    for name, module in modules.items():
        for dependency in module.imports:
            users[dependency].append(name)
    ready = [(ranks[name], name) for name, count in remaining.items() if count == 0]
    heapq.heapify(ready)
    result: list[Module] = []
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
        raise ValueError('Library import order is inconsistent with dependency order')

    # Aggregate roots are re-exporters, not source sections in the bundle.
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


def write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding='utf-8')


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('-o', '--output', type=Path, help='Write the source bundle here instead of stdout')
    parser.add_argument('--library-only', action='store_true',
                        help='Only bundle modules imported by the library roots; default includes experiments')
    args = parser.parse_args()
    try:
        modules = ordered_modules(ROOT, library_only=args.library_only)
        bundle = render_bundle(modules, ROOT)
        if args.output:
            write_text(args.output, bundle)
        else:
            sys.stdout.write(bundle)
    except (ValueError, OSError) as error:
        parser.exit(1, f'export_sources: {error}\n')


if __name__ == '__main__':
    main()
