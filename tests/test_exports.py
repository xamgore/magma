import tempfile
from pathlib import Path
import unittest

from scripts.export_sources import name_parts, ordered_modules, render_bundle, render_mermaid, source_imports


def metadata(items):
    return {
        'schemaVersion': 2,
        'moduleOrder': [item[0] for item in items],
        'modules': [dict(name=name, path=name.replace('.', '/') + '.lean', imports=imports)
                    for name, imports in items],
    }


class ExportTests(unittest.TestCase):
    def test_header_comments_modifiers_and_quoted_names(self):
        source = '''/- outer /- nested -/ import Magma.Fake -/
module
-- import Magma.Fake
public import Magma.A
public import Diffan.Chain
import DiffanExtra.NotProject
meta import all Magma.Evidence.«08_Test»
import Mathlib.Data.Nat.Basic
/- import Magma.Fake -/
@[expose] public section
def text := "import Magma.Fake"
'''
        self.assertEqual(source_imports(source),
                         ('Magma.A', 'Diffan.Chain', 'Magma.Evidence.«08_Test»'))
        self.assertEqual(name_parts('Magma.«Part.With.Dot».Item'), ['Magma', 'Part.With.Dot', 'Item'])

    def test_malformed_header(self):
        with self.assertRaisesRegex(ValueError, 'Unclosed'):
            source_imports('/- unterminated')
        with self.assertRaisesRegex(ValueError, 'Missing'):
            source_imports('module\nimport all')

    def test_dependency_order_and_transitive_reduction(self):
        report = metadata([('Magma.A', []), ('Magma.B', ['Magma.A']),
                           ('Magma.C', ['Magma.A', 'Magma.B'])])
        with tempfile.TemporaryDirectory() as temporary:
            modules = ordered_modules(report, Path(temporary))
        self.assertEqual([module.name for module in modules], report['moduleOrder'])
        diagram = render_mermaid(modules)
        self.assertIn('m0 --> m1', diagram)
        self.assertIn('m1 --> m2', diagram)
        self.assertNotIn('m0 --> m2', diagram)

    def test_cycle_missing_module_and_bad_order(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            with self.assertRaisesRegex(ValueError, 'cycle'):
                ordered_modules(metadata([('Magma.A', ['Magma.B']), ('Magma.B', ['Magma.A'])]), root)
            with self.assertRaisesRegex(ValueError, 'missing'):
                ordered_modules(metadata([('Magma.A', ['Magma.Missing'])]), root)
            with self.assertRaisesRegex(ValueError, 'dependency-first'):
                ordered_modules(metadata([('Magma.B', ['Magma.A']), ('Magma.A', [])]), root)

    def test_evidence_is_read_verbatim_and_interleaved_without_execution(self):
        report = metadata([('Magma.A', []), ('Magma.B', ['Magma.A']), ('Magma', ['Magma.B'])])
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            for item in report['modules']:
                path = root / item['path']
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text('module\n\n-- original source\n', encoding='utf-8')
            folder = root / 'Magma/Evidence'
            folder.mkdir()
            first = 'module\nimport Magma.A\n\n#eval panic! "must not run"\n'
            second = 'module\nimport Magma.Evidence.«01_First»\n\nexample : True := by\n  trivial\n'
            (folder / '01_First.lean').write_text(first, encoding='utf-8')
            (folder / '02_Second.lean').write_text(second, encoding='utf-8')
            modules = ordered_modules(report, root)
            self.assertEqual([module.name for module in modules],
                             ['Magma.A', 'Magma.Evidence.«01_First»', 'Magma.Evidence.«02_Second»',
                              'Magma.B'])
            bundle = render_bundle(modules, root)
            self.assertIn(first, bundle)
            self.assertIn(second, bundle)
            self.assertIn('Magma.Evidence.«01_First» | Magma/Evidence/01_First.lean', bundle)
            self.assertEqual(len(ordered_modules(report, root, include_evidence=False)), 2)

    def test_aggregate_is_omitted_and_its_imports_are_preserved(self):
        report = metadata([('Magma.A', []), ('Magma.B', ['Magma.A']),
                           ('Magma', ['Magma.A', 'Magma.B'])])
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            folder = root / 'Magma/Evidence'
            folder.mkdir(parents=True)
            (folder / '01_Test.lean').write_text('module\nimport Magma\n', encoding='utf-8')
            modules = ordered_modules(report, root)
        self.assertEqual([module.name for module in modules],
                         ['Magma.A', 'Magma.B', 'Magma.Evidence.«01_Test»'])
        self.assertEqual(modules[-1].imports, ('Magma.A', 'Magma.B'))
        diagram = render_mermaid(modules)
        self.assertNotIn('["Magma"]', diagram)
        self.assertIn('m1 --> m2', diagram)
        self.assertNotIn('m0 --> m2', diagram)

    def test_unimported_source_without_project_dependencies(self):
        report = metadata([('Magma', [])])
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / 'Magma').mkdir()
            (root / 'Magma/Extra.lean').write_text('module\nimport Lean\n', encoding='utf-8')
            modules = ordered_modules(report, root)
            self.assertEqual(set(module.name for module in modules), {'Magma.Extra'})

    def test_both_libraries_and_nested_aggregate_imports(self):
        report = metadata([
            ('Diffan.Core', []), ('Diffan.Unused', ['Diffan.Core']),
            ('Diffan', ['Diffan.Core', 'Diffan.Unused']),
            ('Magma.RFC8891', []), ('Magma.Bridge', ['Magma.RFC8891', 'Diffan']),
            ('Magma', ['Magma.Bridge']),
        ])
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            for item in report['modules']:
                path = root / item['path']
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text('module\n', encoding='utf-8')
            (root / 'Diffan/Extra.lean').write_text('import Diffan.Core\n', encoding='utf-8')
            folder = root / 'Magma/Evidence'
            folder.mkdir()
            (folder / '01_Test.lean').write_text('import Diffan\nimport Magma\n', encoding='utf-8')
            modules = ordered_modules(report, root)
            by_name = {module.name: module for module in modules}
            self.assertNotIn('Magma', by_name)
            self.assertNotIn('Diffan', by_name)
            self.assertIn('Diffan.Extra', by_name)
            self.assertEqual(by_name['Magma.Bridge'].imports,
                             ('Magma.RFC8891', 'Diffan.Core', 'Diffan.Unused'))
            self.assertEqual(by_name['Magma.Evidence.«01_Test»'].imports,
                             ('Diffan.Core', 'Diffan.Unused', 'Magma.Bridge'))
            positions = {module.name: index for index, module in enumerate(modules)}
            for module in modules:
                for dependency in module.imports:
                    self.assertLess(positions[dependency], positions[module.name])
            self.assertIn('-- BEGIN MODULE: Diffan.Extra', render_bundle(modules, root))
            render_mermaid(modules)
            self.assertEqual([module.name for module in ordered_modules(
                report, root, include_evidence=False)],
                ['Diffan.Core', 'Diffan.Unused', 'Magma.RFC8891', 'Magma.Bridge'])


if __name__ == '__main__':
    unittest.main()
