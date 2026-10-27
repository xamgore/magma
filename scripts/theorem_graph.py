#!/usr/bin/env python3
"""Draw theorem dependencies from elaborated types and proofs exported by deps."""

from __future__ import annotations

import argparse
from collections import Counter, defaultdict
import heapq
from html import escape
import json
from pathlib import Path
import re
import subprocess
import sys

# BMP letters count as one UTF-16 code unit in Pele's source-length check.
ID_DIGITS = ('0123456789abcdefghijklmnopqrstuvwxyz'
             'абвгдеёжзийклмнопрстуфхцчшщъыьэюя'
             + ''.join(chr(code) for code in range(0x4E00, 0xA000)))

if __package__:
    from .export_sources import load_report, name_parts, write_text
else:
    from export_sources import load_report, name_parts, write_text


def theorem_dependencies(report: dict, module: str | None = None) -> dict[str, set[str]]:
    """Project local constant paths onto visible theorem nodes, including private helpers."""
    declarations = {item['name']: item for item in report['declarations']}
    dependencies = {
        name: set(item['typeDependencies']['local']) | set(item['bodyDependencies']['local'])
        for name, item in declarations.items()
    }
    missing = set().union(set(), *dependencies.values()) - declarations.keys()
    if missing:
        raise ValueError(f'Missing local declarations in deps metadata: {", ".join(sorted(missing))}')
    visible = {
        name for name, item in declarations.items()
        if item['kind'] == 'theorem' and
        (module is None or item['module'] == module or (item['module'] or '').startswith(module + '.'))
    }
    graph = {}
    for name in sorted(visible):
        found = set()
        visited = {name}
        pending = list(dependencies[name])
        while pending:
            dependency = pending.pop()
            if dependency in visited:
                continue
            visited.add(dependency)
            if dependency in visible:
                found.add(dependency)
            else:
                pending.extend(dependencies[dependency] - visited)
        graph[name] = found
    return graph


def focused_graph(graph: dict[str, set[str]], names: list[str]) -> dict[str, set[str]]:
    """Keep selected theorems and all their visible prerequisites."""
    missing = set(names) - graph.keys()
    if missing:
        raise ValueError(f'Theorems not found in selection: {", ".join(sorted(missing))}')
    keep = set()
    pending = list(names)
    while pending:
        name = pending.pop()
        if name not in keep:
            keep.add(name)
            pending.extend(graph[name] - keep)
    return {name: graph[name] for name in sorted(keep)}


def reduced_graph(graph: dict[str, set[str]]) -> dict[str, set[str]]:
    """Remove transitive edges in a DAG; retain every edge if cycles are present."""
    users = {name: [] for name in graph}
    remaining = {name: len(dependencies) for name, dependencies in graph.items()}
    for name, dependencies in graph.items():
        for dependency in dependencies:
            users[dependency].append(name)
    ready = [name for name, count in remaining.items() if count == 0]
    heapq.heapify(ready)
    order = []
    while ready:
        name = heapq.heappop(ready)
        order.append(name)
        for user in users[name]:
            remaining[user] -= 1
            if remaining[user] == 0:
                heapq.heappush(ready, user)
    if len(order) != len(graph):
        return {name: set(graph[name]) for name in sorted(graph)}
    ancestors: dict[str, set[str]] = {}
    result = {}
    for name in order:
        indirect = set().union(set(), *(ancestors[dependency] for dependency in graph[name]))
        result[name] = graph[name] - indirect
        ancestors[name] = indirect | graph[name]
    return result


def short_name(name: str) -> str:
    """Strip Lean's private-name mangling and the shared project prefix."""
    if name.startswith('_private.'):
        name = re.sub(r'^_private\..*?\.\d+\.', '', name, count=1)
    return name.removeprefix('Magma.')


def node_id(index: int) -> str:
    result = ''
    while index:
        index, digit = divmod(index, len(ID_DIGITS))
        result = ID_DIGITS[digit] + result
    return 't' + (result or '0')


def theorem_labels(graph: dict[str, set[str]]) -> dict[str, tuple[str, str]]:
    private_counts = Counter(short_name(name) for name in graph if name.startswith('_private.'))
    occurrences: Counter[str] = Counter()
    labels = {}
    for name in graph:
        short = short_name(name)
        parts = name_parts(short)
        namespace = parts[0] if len(parts) > 1 else ''
        label = '.'.join(parts[1:]) if namespace else parts[0]
        if name.startswith('_private.'):
            occurrences[short] += 1
            label += '*' + (str(occurrences[short]) if private_counts[short] > 1 else '')
        labels[name] = namespace, label
    return labels


def label_text(text: str) -> str:
    """Apostrophes are literal inside double-quoted Mermaid labels (Pele does not decode &#x27;)."""
    return escape(text, quote=False).replace('"', '&quot;')


def render_theorems(graph: dict[str, set[str]], identifiers=None, labels=None, boundary=None) -> str:
    identifiers = identifiers if identifiers is not None else {name: node_id(i) for i, name in enumerate(graph)}
    labels = labels if labels is not None else theorem_labels(graph)
    boundary = boundary or {}
    lines = [
        '%% Prerequisite -> user; hidden paths contracted; transitive DAG edges reduced.',
        '%% Namespace groups omit Magma.; * marks private names; numbered * disambiguates duplicates.',
        'flowchart LR',
    ]
    groups: dict[str, list[str]] = defaultdict(list)
    for name in graph:
        namespace, label = labels[name]
        if name in boundary:
            label += f' @{boundary[name]}'
        groups[namespace].append(f'{identifiers[name]}["{label_text(label)}"]')
    for index, (namespace, nodes) in enumerate(groups.items()):
        if namespace:
            lines.append(f'subgraph g{index}["{label_text(namespace)}"]')
        lines.extend(nodes)
        if namespace:
            lines.append('end')
    users: dict[str, list[str]] = defaultdict(list)
    for name, dependencies in graph.items():
        for dependency in sorted(dependencies):
            users[dependency].append(identifiers[name])
    for dependency, targets in users.items():
        lines.append(f'{identifiers[dependency]}-->{" & ".join(targets)}')
    return '\n'.join(lines) + '\n'


def page_graph(graph: dict[str, set[str]], owners: list[str]) -> dict[str, set[str]]:
    """Include every edge into an owned node, with boundary prerequisites as leaf nodes."""
    owned = set(owners)
    present = owned | set().union(set(), *(graph[name] for name in owners))
    return {name: graph[name] if name in owned else set() for name in graph if name in present}


def render_diagrams(graph: dict[str, set[str]], stem: str, max_chars: int) -> dict[str, str]:
    """Split oversized diagrams without dropping any theorem or dependency edge."""
    full = render_theorems(graph)
    if len(full) <= max_chars:
        return {f'{stem}.mmd': full}
    identifiers = {name: node_id(i) for i, name in enumerate(graph)}
    labels = theorem_labels(graph)
    groups: dict[str, list[str]] = defaultdict(list)
    for name in graph:
        groups[labels[name][0]].append(name)

    def fits(owners):
        subset = page_graph(graph, owners)
        # Pessimistic boundary numbers and room for the part header.
        owned = set(owners)
        boundary = {name: len(graph) for name in subset if name not in owned}
        return len(render_theorems(subset, identifiers, labels, boundary)) + 256 <= max_chars

    pages, current = [], []
    for group in groups.values():
        if fits(current + group):
            current += group
            continue
        if current:
            pages.append(current)
            current = []
        if fits(group):
            current = list(group)
            continue
        for name in group:
            if not fits(current + [name]):
                if current:
                    pages.append(current)
                current = []
                if not fits([name]):
                    raise ValueError(f'Theorem and its direct prerequisites exceed the budget: {name}')
            current.append(name)
    if current:
        pages.append(current)
    page_of = {name: i for i, owners in enumerate(pages, 1) for name in owners}
    files = {}
    overview = [
        '%% Parts preserve all theorem nodes and edges; open the numbered .mmd files.',
        '%% Edge labels count dependencies crossing between parts.',
        'flowchart LR',
    ]
    for i, owners in enumerate(pages, 1):
        filename = f'{stem}.{i:02}.mmd'
        subset = page_graph(graph, owners)
        boundary = {name: page_of[name] for name in subset if page_of[name] != i}
        diagram = f'%% Part {i}; @N marks a prerequisite owned by part N. Node IDs are global.\n'
        diagram += render_theorems(subset, identifiers, labels, boundary)
        files[filename] = diagram
        overview.append(f'p{i}["{label_text(filename)}: {len(owners)} theorems"]')
    crossing = Counter((page_of[dep], page_of[name]) for name, deps in graph.items()
                       for dep in deps if page_of[dep] != page_of[name])
    for (dependency, user), count in sorted(crossing.items()):
        overview.append(f'p{dependency}-->|{count}|p{user}')
    files = {f'{stem}.mmd': '\n'.join(overview) + '\n', **files}
    if any(len(diagram) > max_chars for diagram in files.values()):
        raise ValueError('Diagram exceeds the character budget; use --module or --focus')
    return files


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path, help='Reuse deps JSON instead of building and running deps')
    parser.add_argument('-o', '--output', type=Path, help='Write Mermaid here instead of stdout')
    parser.add_argument('--module', help='Show theorems from this module or module subtree')
    parser.add_argument('--focus', action='append', help='Show this theorem and its prerequisites; repeatable')
    parser.add_argument('--max-chars', type=int, default=48000,
                        help='Character budget per diagram (default: 48000, below the 50000 limit)')
    args = parser.parse_args()
    try:
        report = json.loads(args.input.read_text(encoding='utf-8')) if args.input else load_report()
        graph = theorem_dependencies(report, args.module)
        if args.focus:
            graph = focused_graph(graph, args.focus)
        if not graph:
            raise ValueError('No theorems found in selection')
        original_edges = sum(map(len, graph.values()))
        graph = reduced_graph(graph)
        if args.max_chars <= 0:
            raise ValueError('--max-chars must be positive')
        files = render_diagrams(graph, args.output.stem if args.output else 'theorems', args.max_chars)
        if args.output:
            for filename, diagram in files.items():
                write_text(args.output if filename == args.output.stem + '.mmd'
                           else args.output.parent / filename, diagram)
        else:
            if len(files) > 1:
                raise ValueError('Graph needs multiple diagrams; pass -o to write an overview and numbered parts')
            sys.stdout.write(next(iter(files.values())))
        print(f'{len(graph)} theorems, {original_edges} -> {sum(map(len, graph.values()))} edges, '
              f'{len(files)} diagrams, largest {max(map(len, files.values()))} characters', file=sys.stderr)
    except (ValueError, KeyError, OSError, subprocess.CalledProcessError) as error:
        parser.exit(1, f'theorem_graph: {error}\n')


if __name__ == '__main__':
    main()
