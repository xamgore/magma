import unittest
import re

from scripts.theorem_graph import (ID_DIGITS, focused_graph, node_id, reduced_graph, render_diagrams,
                                  render_theorems, short_name, theorem_dependencies)


def declaration(name, kind='theorem', body=(), types=(), module='Magma.A'):
    return dict(name=name, kind=kind, module=module,
                typeDependencies=dict(local=list(types), external=['Mathlib.external']),
                bodyDependencies=dict(local=list(body), external=[]))


class TheoremGraphTests(unittest.TestCase):
    def test_proof_and_type_dependencies_through_helpers(self):
        report = dict(declarations=[
            declaration('base'), declaration('typeLemma'),
            declaration('helper', 'def', body=['base', 'helper2']),
            declaration('helper2', 'def', body=['helper']),
            declaration('result', body=['helper'], types=['typeLemma']),
        ])
        self.assertEqual(theorem_dependencies(report),
                         dict(base=set(), typeLemma=set(), result={'base', 'typeLemma'}))

    def test_module_filter_contracts_hidden_theorems(self):
        report = dict(declarations=[
            declaration('a'), declaration('hidden', body=['a'], module='Magma.B'),
            declaration('b', body=['hidden'], module='Magma.A.Sub'),
            declaration('other', module='Magma.AA'),
        ])
        self.assertEqual(theorem_dependencies(report, 'Magma.A'), dict(a=set(), b={'a'}))

    def test_reduction_and_focus_preserve_reachability(self):
        graph = dict(a=set(), b={'a'}, c={'a', 'b'}, unrelated=set())
        result = reduced_graph(focused_graph(graph, ['c']))
        self.assertEqual(result, dict(a=set(), b={'a'}, c={'b'}))
        diagram = render_theorems(result)
        self.assertIn('t0-->t1', diagram)
        self.assertIn('t1-->t2', diagram)
        self.assertNotIn('t0-->t2', diagram)
        with self.assertRaisesRegex(ValueError, 'not found'):
            focused_graph(graph, ['missing'])

    def test_cycles_are_preserved(self):
        graph = dict(a={'b'}, b={'a'}, c={'a', 'b'})
        self.assertEqual(reduced_graph(graph), graph)

    def test_missing_local_node_is_reported(self):
        with self.assertRaisesRegex(ValueError, 'Missing local'):
            theorem_dependencies(dict(declarations=[declaration('a', body=['missing'])]))

    def test_compact_names_and_edges_preserve_node_identity(self):
        first = '_private.Magma.A.0.Magma.Shared.helper'
        second = '_private.Magma.B.0.Magma.Shared.helper'
        graph = {first: set(), second: set(), 'Magma.Shared.helper': set(),
                 'Magma.Shared.result': {first, second}, 'Magma.Other.result': {first}}
        diagram = render_theorems(graph)
        self.assertNotIn('_private.', diagram)
        self.assertNotIn('Magma.Shared.', diagram)
        self.assertIn('subgraph g0["Shared"]', diagram)
        self.assertIn('t0["helper*1"]', diagram)
        self.assertIn('t1["helper*2"]', diagram)
        self.assertIn('t2["helper"]', diagram)
        self.assertIn('t0-->t3 & t4', diagram)
        self.assertIn('t1-->t3', diagram)
        self.assertEqual(short_name('Magma.«A.B».lemma'), '«A.B».lemma')

    def test_unicode_ids_are_unique_bmp_and_labels_are_escaped(self):
        graph = {f'Magma.Shared.item{i}': set() for i in range(40)}
        graph['Magma.Shared.a<b'] = set()
        diagram = render_theorems(graph)
        self.assertIn('tz["item35"]', diagram)
        self.assertIn('tа["item36"]', diagram)
        self.assertIn('["a&lt;b"]', diagram)
        ids = {node_id(i) for i in range(len(ID_DIGITS) + 1)}
        self.assertEqual(len(ids), len(ID_DIGITS) + 1)
        self.assertEqual(len(node_id(1622).encode('utf-16-le')), 4)
        self.assertEqual(node_id(len(ID_DIGITS)), 't10')
        self.assertTrue(all(ord(char) <= 0xFFFF for char in ID_DIGITS))

    def test_partition_preserves_edges_and_global_ids_under_budget(self):
        graph = {f'Magma.Shared.item{i}': {f'Magma.Shared.item{j}' for j in range(max(0, i - 3), i)}
                 for i in range(100)}
        files = render_diagrams(graph, 'test', 1500)
        self.assertGreater(len(files), 2)
        self.assertTrue(all(len(text) <= 1500 for text in files.values()))
        edges, nodes = set(), set()
        for filename, text in files.items():
            if filename == 'test.mmd':
                continue
            nodes.update(re.findall(r'^(t\w+)\[', text, re.M))
            for source, targets in re.findall(r'^(t\w+)-->(.*)$', text, re.M):
                edges.update((source, target.strip()) for target in targets.split('&'))
        ids = {name: node_id(i) for i, name in enumerate(graph)}
        self.assertEqual(nodes, set(ids.values()))
        self.assertEqual(edges, {(ids[dep], ids[name]) for name, deps in graph.items() for dep in deps})
        self.assertTrue(any('@' in text for name, text in files.items() if name != 'test.mmd'))

    def test_small_graph_is_not_split_and_impossible_budget_is_reported(self):
        graph = {'a': set(), 'b': {'a'}}
        self.assertEqual(render_diagrams(graph, 'small', 50000), {'small.mmd': render_theorems(graph)})
        with self.assertRaisesRegex(ValueError, 'exceed'):
            render_diagrams(graph, 'small', 10)

    def test_apostrophes_stay_literal_in_pele_labels(self):
        diagram = render_theorems({"Magma.N'.π'": set()})
        self.assertIn('["N\'"]', diagram)
        self.assertIn('["π\'"]', diagram)
        self.assertNotIn('&#x27;', diagram)

    def test_transitive_reduction_removes_triangle_and_longer_shortcuts(self):
        graph = {'A': {'B', 'C'}, 'B': {'C'}, 'C': set(), 'D': {'A', 'B', 'C'}}
        self.assertEqual(reduced_graph(graph), {'C': set(), 'B': {'C'}, 'A': {'B'}, 'D': {'A'}})


if __name__ == '__main__':
    unittest.main()
