import unittest

from scripts.theorem_graph import focused_graph, reduced_graph, render_theorems, theorem_dependencies


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
        self.assertIn('t0 --> t1', diagram)
        self.assertIn('t1 --> t2', diagram)
        self.assertNotIn('t0 --> t2', diagram)
        with self.assertRaisesRegex(ValueError, 'not found'):
            focused_graph(graph, ['missing'])

    def test_cycles_are_preserved(self):
        graph = dict(a={'b'}, b={'a'}, c={'a', 'b'})
        self.assertEqual(reduced_graph(graph), graph)

    def test_missing_local_node_is_reported(self):
        with self.assertRaisesRegex(ValueError, 'Missing local'):
            theorem_dependencies(dict(declarations=[declaration('a', body=['missing'])]))


if __name__ == '__main__':
    unittest.main()
