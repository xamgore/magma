from pathlib import Path
p = Path('Magma/FastSearch.lean')
s = p.read_text()
s = s.replace('printed type; errors still fail the build. Replace `#check` with `#eval` to run\none recipe. Historical outputs below belong to earlier evaluations.', '''printed type; errors still fail the build. To run a recipe and see its output,
replace `#check` with `#eval` and remove its guard. Historical outputs below
belong to earlier evaluations.''')
s = s.replace('''/-
  Typechecked profiling recipes (no execution). No historical transcript was recorded for these
  particular calls; timings and outcomes must be read from a completed run.
  Stable recorded checks live in Magma.Evidence.SearchChecks.

  -- Display a per-stage profile; false avoids unnecessary slow validation.
-/''','''/-
  Typechecked profiling recipes (no execution). No historical transcript was
  recorded for these calls; timings and outcomes require a completed run.
  Stable recorded checks live in Magma.Evidence.SearchChecks.
-/

-- Display a per-stage profile; false avoids unnecessary slow validation.''')
s = s.replace('''/-

  -- Force the OLD verifier to measure its actual cost on the same input.
-/''','''
-- Force the original verifier to measure its cost on the same input.''')
s = s.replace('''/-

  -- Fast total run, with rejection BEFORE invoking the expensive verifier.
-/''','''
-- Reject before invoking the expensive verifier.''')
s = s.replace('''/-
-/

''', '\n')
s = s.replace('''  Boolean outputs are rechecked in Magma.Evidence.SearchChecks.

  -- Recorded initialization cost: about 38 sec -> 66 ms.
-/''','''  Boolean outputs are rechecked in Magma.Evidence.SearchChecks.
-/

-- Recorded initialization cost: about 38 sec -> 66 ms.''')
s = s.replace('''/-

  -- One-time equality check for the example; THIS runs the slow path too.
-/''','''
-- Evaluation compares both implementations, including the slow path.''')
s = s.replace('''/-
  -- Recorded output: true; elapsed time: 72 sec.
  -- This checks one input; it is not a universal equivalence proof.

  -- Return false rapidly if the fast search sees no empty domain.
-/''','''-- Recorded output: true; elapsed time: 72 sec.
-- This checks one input; it is not a universal equivalence proof.

-- Return false rapidly if the fast search sees no empty domain.''')
s = s.replace('''/-
  -- Recorded output: false; elapsed time: 35 sec.
  -- No certificate was found by this pruning strategy on this input.
-/''','''-- Recorded output: false; elapsed time: 35 sec.
-- No certificate was found by this pruning strategy on this input.''')
s = s.replace('''  as observations from the original run and vary with the environment.

-/''','''  as observations from the original run and vary with the environment.
-/''')
s = s.replace('''/-
  -- Recorded output: true; elapsed time: about 45 sec.

-/''','''-- Recorded output: true; elapsed time: about 45 sec.
''')
s = s.replace('''/-

  /-
  [carry]''','''/-
  [carry]''')
s = s.replace('''  --/

  `empty=true`''','''
  `empty=true`''')
s = s.replace('\n    (0#32) (0#32) (1#32) (1#32) (0#32)', '\n  (0#32) (0#32) (1#32) (1#32) (0#32)')
p.write_text(s)
p = Path('Magma/Evidence/ThreeRoundImpossible.lean')
s = p.read_text().replace('''  The following recipes are typechecked without execution; replace `#check`
  with `#eval` to run them. Only type information is suppressed by the guard.''','''  The following recipes are typechecked without execution. To run one and see
  its output, replace `#check` with `#eval` and remove the surrounding guard.''')
s = s.replace('''  the original run and depend on the environment.

-/''','''  the original run and depend on the environment.
-/''')
s = s.replace('''/-

  -- [carry-cert]''','''/-
  [carry-cert]''')
s = s.replace('  -- [carry-cert]', '  [carry-cert]')
s = s.replace('  -- result: true', '  Recorded output: true')
s = s.replace('  -- [carry-cert] initialCheck=568194ms\n\n-/', '  [carry-cert] initialCheck=568194ms\n-/')
s = s.replace('initialCheck=568194ms\n\n-/', 'initialCheck=568194ms\n-/')
p.write_text(s)
p = Path('test.lean')
s = p.read_text().replace('''  scratch file. Replace `#check` with `#eval` to run one; the guards suppress
  only type information, not errors.''','''  scratch file. To run a recipe and see its output, replace `#check` with
  `#eval` and remove its guard. Type errors still fail elaboration.''')
p.write_text(s)
p = Path('README.md')
s = p.read_text().replace('''suppresses the printed type while preserving errors. Replace `#check` with `#eval` to run
an individual recipe.''','''suppresses the printed type while preserving errors. To run an individual recipe and see
its output, replace `#check` with `#eval` and remove the surrounding guard.''')
p.write_text(s)
