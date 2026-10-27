#!/usr/bin/env python3
"""Draw theorem dependencies from elaborated types and proofs exported by deps."""

from __future__ import annotations

import argparse
import heapq
from html import escape
import json
from pathlib import Path
import subprocess
import sys

if __package__:
    from .export_sources import load_report, write_text
else:
    from export_sources import load_report, write_text


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


def render_theorems(graph: dict[str, set[str]]) -> str:
    identifiers = {name: f't{index}' for index, name in enumerate(graph)}
    lines = [
        '%% Theorem dependencies from elaborated types and proof terms.',
        '%% Arrows: prerequisite -> user; paths through hidden declarations are contracted.',
        '%% Redundant transitive edges are omitted for acyclic graphs; cycles are preserved.',
        'flowchart TD',
    ]
    for name in graph:
        lines.append(f'  {identifiers[name]}["{escape(name, quote=True)}"]')
    for name, dependencies in graph.items():
        for dependency in sorted(dependencies):
            lines.append(f'  {identifiers[dependency]} --> {identifiers[name]}')
    return '\n'.join(lines) + '\n'


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path, help='Reuse deps JSON instead of building and running deps')
    parser.add_argument('-o', '--output', type=Path, help='Write Mermaid here instead of stdout')
    parser.add_argument('--module', help='Show theorems from this module or module subtree')
    parser.add_argument('--focus', action='append', help='Show this theorem and its prerequisites; repeatable')
    args = parser.parse_args()
    try:
        report = json.loads(args.input.read_text(encoding='utf-8')) if args.input else load_report()
        graph = theorem_dependencies(report, args.module)
        if args.focus:
            graph = focused_graph(graph, args.focus)
        if not graph:
            raise ValueError('No theorems found in selection')
        graph = reduced_graph(graph)
        diagram = render_theorems(graph)
        if args.output:
            write_text(args.output, diagram)
        else:
            sys.stdout.write(diagram)
        print(f'{len(graph)} theorems, {sum(map(len, graph.values()))} edges', file=sys.stderr)
    except (ValueError, KeyError, OSError, subprocess.CalledProcessError) as error:
        parser.exit(1, f'theorem_graph: {error}\n')


if __name__ == '__main__':
    main()
