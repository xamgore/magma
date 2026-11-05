from pathlib import Path
scratch = Path('test.lean')
s = scratch.read_text()
Path('.lake/research-checks/test.before-integration.lean').write_text(s)
core_start = s.index('/-! ## 1. Enumerate')
core_end = s.index('/-- Same concrete proposal')
core = s[core_start:core_end]
p = Path('Magma/Certificates.lean')
c = p.read_text()
c = c.replace('Search algorithms belong to `Magma.FastSearch`.', '''`FastInitialCheck` verifies initial-mask coverage directly from `sboxCarryStep`
transitions. Its soundness theorem implies acceptance by the original Finset
checker without executing that checker or assuming equivalence of search code.
Search algorithms belong to `Magma.FastSearch`.''')
c += '''
namespace Magma.Certificates.FastInitialCheck

open Magma.Certificates.BackwardMask

/-!
## Transition-based verification of initial UInt16 masks

Enumerate the original `sboxCarryStep` transitions and check that the proposed
masks cover them. Acceptance implies the original `verifyInitialMaskCover`
condition for all inputs. This does not assert universal equality between
`fastInitialBitDomains` and the original finite-set domains. Carry and grouped
certificate formats, their checkers, and their soundness theorem are reused.
-/

''' + core + 'end Magma.Certificates.FastInitialCheck\n'
p.write_text(c)

p = Path('Magma/Evidence/ThreeRoundImpossible.lean')
e = p.read_text()
e = e.replace('can find a candidate whose impossibility is independently proved.', '''can find a candidate whose impossibility is independently proved.
The current proof uses transition-based initial-mask verification; the original
Finset diagnostic and its historical transcript remain available for comparison.''')
e = e.replace('open Magma.Certificates.Encoding Magma.Certificates.BackwardMask Magma.FastSearch', '''open Magma.Certificates.Encoding Magma.Certificates.BackwardMask Magma.FastSearch
open Magma.Certificates.FastInitialCheck''')
concrete = s[core_end:s.index('/-\n  These recipes are typechecked')]
# The finite loops contain 8 * 4 * 16 + 8 * 16 * 4 * 16 = 8704 checks.
concrete = concrete.replace('is checked by ~8704 explicit local transitions instead of Finset-DP.', 'is checked by 8704 explicit local transition cases instead of Finset-DP.')
e = e.replace('/-- Print checks separately', concrete + '''/-
  These calls are typechecked without execution. Replace `#check` with `#eval`
  and remove its guard to run the recipe and see its output.
-/
#guard_msgs (drop info) in
#check (profileFastInitialCoverBySteps : IO Unit)
/-
  Historical initial-coverage profile:
  [initial-fast] accepted=true; time=7829ms
  Elapsed times depend on the environment.
-/

#guard_msgs (drop info) in
#check (testCarryGroupedCertificateFastInit : Bool)
-- Acceptance is established by concreteFastInitialCarryGroupedCheck below.

/-- Print checks separately''')
a = e.index('/-\n  The historical diagnostic evaluation of testCarryGroupedCertificate')
b = e.index('/--\ninfo:',a)
e = e[:a] + '''/-- The transition-based checker supplies initial coverage to the existing
    carry/grouped soundness theorem for the same concrete proposal. -/
theorem concreteThreeRoundImpossible_of_fastChecked
    (k₂ bR : V 32)
    (hchecked : testCarryGroupedCertificateFastInit = true) :
    xorDDT_rounds 3
      (threeRoundKeys (0#32) (0#32) k₂)
      ((1#32), (1#32)) ((0#32), bR) = 0 := by
  let D := fastInitialBitDomains (0#32) (0#32) (1#32) (0#32)
  let cert := proposeCarryReduction (0#32) (0#32) (1#32) (0#32) D
  let next := fastGroupedUInt16 (1#32) cert.next
  have hparts :
      verifyInitialCoverBySteps (0#32) (0#32) (1#32) (0#32) D = true ∧
      verifyOneCarryThenGrouped
        (0#32) (0#32) (1#32) (1#32) (0#32) D cert next = true :=
    Bool.and_eq_true_iff.mp hchecked
  exact xorDDT_rounds_three_zero_of_checkedCarryGrouped_fastInit
    (0#32) (0#32) k₂ (1#32) (1#32) (0#32) bR
    D cert next hparts.1 hparts.2

/-- Kernel-checked acceptance using transition-based initial coverage.
    The expensive Finset initialization checker is not evaluated. -/
set_option maxHeartbeats 0 in
theorem concreteFastInitialCarryGroupedCheck : testCarryGroupedCertificateFastInit = true := by
  decide +kernel

/-- Preserve the original acceptance statement via the proved implication,
    without evaluating its expensive initial-coverage condition. -/
theorem concreteCarryGroupedCheck : testCarryGroupedCertificate = true := by
  have hparts := Bool.and_eq_true_iff.mp concreteFastInitialCarryGroupedCheck
  exact Bool.and_eq_true_iff.mpr
    ⟨verifyInitialMaskCover_of_steps _ _ _ _ _ hparts.1, hparts.2⟩

theorem concreteThreeRoundImpossible (k₂ bR : V 32) :
    xorDDT_rounds 3 (threeRoundKeys (0#32) (0#32) k₂)
      ((1#32), (1#32)) ((0#32), bR) = 0 := by
  exact concreteThreeRoundImpossible_of_fastChecked
    k₂ bR concreteFastInitialCarryGroupedCheck

''' + e[b:]
p.write_text(e)

p = Path('Magma/Evidence/SearchChecks.lean')
c = p.read_text().replace('''`Magma.Evidence.ThreeRoundImpossible.concreteCarryGroupedCheck` in the normal
build. Its statement is `testCarryGroupedCertificate = true`; the final
impossibility theorem uses that proof.''','''`Magma.Evidence.ThreeRoundImpossible.concreteFastInitialCarryGroupedCheck` in
the normal build. It proves `testCarryGroupedCertificateFastInit = true` using
transition-based initial coverage; the final impossibility theorem uses that
proof. `concreteCarryGroupedCheck` recovers the original checker's acceptance
through the soundness implication without evaluating its Finset condition.''')
p.write_text(c)

p = Path('README.md')
r = p.read_text().replace('''| `Magma.Certificates` | Certificate formats, independent checkers, and soundness proofs |''', '''| `Magma.Certificates` | Certificate formats, independent checkers, soundness, and transition-based initial coverage |''')
r = r.replace('''machine encodings use `Magma.Certificates.Encoding`.''','''machine encodings use `Magma.Certificates.Encoding`. The transition-based initial-mask
checker and its soundness theorems live in `Magma.Certificates.FastInitialCheck`.
Acceptance implies the original Finset coverage condition for every input; this does not
assert universal equality of `fastInitialBitDomains` with the original domains. The concrete
three-round proof uses this implication and reuses the existing carry/grouped checkers.''')
r = r.replace('''as well. The complete concrete certificate acceptance is already proved with `decide +kernel`
in the normal build; its proof is distinct from diagnostic output.''','''as well. The complete concrete certificate acceptance is already proved with `decide +kernel`
in the normal build using the transition-based initial checker. The original acceptance
statement follows from soundness without evaluating the old Finset checker.''')
r = r.replace('''run explicitly say so. `test.lean` is a standalone research scratch file; its profiler is also
opt-in. Its concrete certificate acceptance example is an active kernel-checked proof.''','''run explicitly say so. To evaluate the integrated fast initial checker interactively in
`Main.lean`, use:

```lean
#eval Magma.Evidence.ThreeRoundImpossible.profileFastInitialCoverBySteps
#eval Magma.Evidence.ThreeRoundImpossible.testCarryGroupedCertificateFastInit
```

The first command prints a profile; the second returns `true`. Its acceptance is also
established by the kernel-checked `concreteFastInitialCarryGroupedCheck` theorem.''')
p.write_text(r)
# All mathematics, research calls and the historical profile have moved to their modules.
scratch.unlink()
