import unittest

from scripts.theorem_graph import focused_graph, reduced_graph, render_theorems, short_name, theorem_dependencies


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
        self.assertIn('t0-->t3&t4', diagram)
        self.assertIn('t1-->t3', diagram)
        self.assertEqual(short_name('Magma.«A.B».lemma'), '«A.B».lemma')

    def test_base36_ids_are_unique_and_labels_are_escaped(self):
        graph = {f'Magma.Shared.item{i}': set() for i in range(40)}
        graph['Magma.Shared.a<b'] = set()
        diagram = render_theorems(graph)
        self.assertIn('tz["item35"]', diagram)
        self.assertIn('t10["item36"]', diagram)
        self.assertIn('["a&lt;b"]', diagram)


if __name__ == '__main__':
    unittest.main()
