"""Research modules and their reproducible experiments remain connected."""

import re
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]


class ResearchStructureTests(unittest.TestCase):
    def test_proofs_and_experiments_share_research_branches(self):
        pairs = (
            ('FiveRounds/FiveRoundMiddleFiberMass.lean',
             'FiveRounds/Experiments/JOINT_MIDDLE_TRANSFER.md'),
            ('SevenRounds/SevenTopNibbleImpossible.lean',
             'SevenRounds/Experiments/NIBBLE_VALUATION_FAMILIES.md'),
            ('NinePlus/Model.lean', 'NinePlus/Experiments/README.md'),
            ('FullCipher/Full32SlicedJoin.lean',
             'FullCipher/Experiments/HALF_ZERO_32_COMPOSITION.md'),
            ('Windows/IndependentRoundSupport.lean',
             'Windows/Experiments/Sparse/SPARSE_WINDOWS.md'),
        )
        for theory, experiment in pairs:
            self.assertTrue((ROOT / 'Magma/Differential' / theory).is_file(), theory)
            self.assertTrue((ROOT / 'Magma/Differential' / experiment).is_file(), experiment)
        self.assertFalse((ROOT / 'research').exists())
        self.assertFalse((ROOT / 'Magma/Experiments').exists())

    def test_project_lean_imports_resolve_to_moved_sources(self):
        modules = {
            '.'.join(p.relative_to(ROOT).with_suffix('').parts)
            for folder in ('Diffan', 'Magma')
            for p in (ROOT / folder).rglob('*.lean')
        }
        missing = []
        for folder in ('Diffan', 'Magma'):
            for source in (ROOT / folder).rglob('*.lean'):
                for imported in re.findall(
                    r'(?m)^\s*(?:(?:public|meta)\s+)?import\s+(?:all\s+)?'
                    r'((?:Diffan|Magma)\.[^\s]+)', source.read_text()
                ):
                    if imported.replace('«', '').replace('»', '') not in modules:
                        missing.append(f'{source.relative_to(ROOT)}: {imported}')
        self.assertEqual(missing, [])

    def test_markdown_navigation_reaches_existing_files(self):
        documents = [ROOT / 'README.md', ROOT / 'Diffan/README.md']
        documents.extend((ROOT / 'Magma').rglob('*.md'))
        problems = []
        for doc in documents:
            for link in re.findall(r'\]\(([^\s\)]+)', doc.read_text()):
                if link.startswith(('https:', 'http:', '#', 'mailto:', 'data:', '(')):
                    continue
                if not (doc.parent / link.split('#', 1)[0]).exists():
                    problems.append(f'{doc.relative_to(ROOT)}: {link}')
        self.assertEqual(problems, [])


if __name__ == '__main__':
    unittest.main()
