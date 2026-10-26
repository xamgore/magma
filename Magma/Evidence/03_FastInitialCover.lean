module

public import Magma.FastSearch
meta import Magma.FastSearch
-- Kernel checks unfold the legacy range loops used by the search code.
import all Init.Data.Range.Basic

@[expose] public section

/-!
# 03: fast initial coverage for the concrete impossible differential

Research stages: independently checked carry/grouped certificates, the first
concrete impossibility proof, and a faster initial-mask verifier. The candidate
was discovered by the experiments in `02_CarryGroupedPropagation.lean`.

The original certificate was accepted with the Finset-based checker, and its
closed impossibility theorem was checked with only `propext`, `Classical.choice`,
and `Quot.sound`. Profiling then identified initial coverage as the bottleneck:
568194 ms versus 16917 ms for the remaining checks. The historical transcript
is retained below; the reported transition-based replacement took about
8 seconds and the full certificate check returned `true`.

This file reruns the transition-based checker and proves the same concrete
result using its soundness theorem in `Magma.Certificates.FastInitialCheck`:
`(1, 1) -> (0, bR)` is impossible for zero first two round keys, every third
key, and every right output difference. Carry/grouped checkers are reused.

Sound transition-based coverage already avoids the old check for this
certificate. Universal correctness of `fastInitialBitDomains` remains a
separate open task; no universal equality with the old domains is assumed.
The next experimental direction is reusable bases and batch candidate search.

Historical record:
https://chatgpt.com/c/6ade1478-dfa8-83ed-83bc-dc3b84cc42cf
Build explicitly with `lake build Magma/Evidence/03_FastInitialCover.lean`.
Earlier experiments are not imported or executed.
-/

open Magma.Internal Magma.CarryAutomaton Magma.MultiRoundDDT Magma.Pruning Magma.Certificates
open Magma.Certificates.Encoding Magma.Certificates.BackwardMask Magma.FastSearch
open Magma.Certificates.FastInitialCheck

namespace Magma.Evidence.FastInitialCover

/-- Concrete carry/grouped certificate with initial coverage checked by
    8704 source transition cases, using the sound checker in FastInitialCheck. -/
def testCarryGroupedCertificateFastInit : Bool :=
  let k₀ := (0#32)
  let k₁ := (0#32)
  let aL := (1#32)
  let aR := (1#32)
  let bL := (0#32)
  let D := fastInitialBitDomains k₀ k₁ aR bL
  let cert := proposeCarryReduction k₀ k₁ aR bL D
  let next := fastGroupedUInt16 aL cert.next
  verifyInitialCoverBySteps k₀ k₁ aR bL D &&
    verifyOneCarryThenGrouped k₀ k₁ aL aR bL D cert next

/-- Optional timings; only checks the initial mask cover, not the old
    568-second Finset verifier. -/
def profileFastInitialCoverBySteps : IO Unit := do
  let k₀ := (0#32)
  let k₁ := (0#32)
  let aR := (1#32)
  let bL := (0#32)
  let D := fastInitialBitDomains k₀ k₁ aR bL
  let t₀ ← IO.monoMsNow
  let result := verifyInitialCoverBySteps k₀ k₁ aR bL D
  let t₁ ← IO.monoMsNow
  IO.println s!"[initial-fast] accepted={result}; time={t₁ - t₀}ms"

/-- Print checks separately to locate an invalid proposal without
    expanding the proof of the entire trace. -/
def profileCheckedCarryReduction : IO Unit := do
  let k₀ := (0#32)
  let k₁ := (0#32)
  let aL := (1#32)
  let aR := (1#32)
  let bL := (0#32)
  let t₀ ← IO.monoMsNow
  let D := fastInitialBitDomains k₀ k₁ aR bL
  let cert := proposeCarryReduction k₀ k₁ aR bL D
  let after := fastGroupedUInt16 aL cert.next
  let t₁ ← IO.monoMsNow
  IO.println s!"[carry-cert] proposal={t₁-t₀}ms; carryEmpty={emptyUInt16BitDomain cert.next}; groupedEmpty={emptyUInt16BitDomain after}"
  IO.println s!"[carry-cert] edges0={verifyFirstCarryEdges k₀ aR D cert.edges₀} edges1={verifySecondCarryEdges k₁ aR bL D cert.edges₁}"
  IO.println s!"[carry-cert] forwards={verifyForwardCarryFrontiers cert.edges₀ cert.forward₀},{verifyForwardCarryFrontiers cert.edges₁ cert.forward₁}"
  IO.println s!"[carry-cert] backwards={verifyBackwardCarryFrontiers cert.edges₀ cert.backward₀},{verifyBackwardCarryFrontiers cert.edges₁ cert.backward₁}"
  IO.println s!"[carry-cert] maskCover={verifyFirstCarryMaskCover k₀ aR D cert.next cert.forward₀ cert.backward₀},{verifySecondCarryMaskCover k₁ aR bL D cert.next cert.forward₁ cert.backward₁}"
  IO.println s!"[carry-cert] groupedCover={verifyGroupedMaskCover aL cert.next after}; empty={verifyEmptyMaskedDomain after}"
  let t₂ ← IO.monoMsNow
  IO.println s!"[carry-cert] checks={t₂-t₁}ms"
  IO.println s!"[carry-cert] initialCover={verifyInitialCoverBySteps k₀ k₁ aR bL D}"
  let t₃ ← IO.monoMsNow
  IO.println s!"[carry-cert] initialCheck={t₃-t₂}ms"

/-
  Historical profile of the former Finset initialization checker:
  [carry-cert] proposal=80ms; carryEmpty=false; groupedEmpty=true
  [carry-cert] edges0=true edges1=true
  [carry-cert] forwards=true,true
  [carry-cert] backwards=true,true
  [carry-cert] maskCover=true,true
  [carry-cert] groupedCover=true; empty=true
  [carry-cert] checks=16917ms
  [carry-cert] initialCover=true
  [carry-cert] initialCheck=568194ms

  The current profiler uses verifyInitialCoverBySteps instead of that old
  initial checker. A previous run of the transition-based initial check gave:
  [initial-fast] accepted=true; time=7829ms
  The full transition-based certificate check also returned true.
  These elapsed times are historical observations, not current guarantees.
  The profiles below execute this iteration with the transition-based checker.
-/

-- This small module separates the *mathematical theorem* from the
-- computational proof obligation.  `#eval ... = true` does not by itself
-- construct a Lean proof.

/-- The transition-based checker supplies initial coverage to the existing
    carry/grouped soundness theorem for the same concrete proposal. -/
theorem concreteThreeRoundImpossible_of_checked
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

set_option maxHeartbeats 0 in
/-- Kernel-checked acceptance using transition-based initial coverage.
    The expensive Finset initialization checker is not evaluated. -/
theorem concreteFastInitialCarryGroupedCheck : testCarryGroupedCertificateFastInit = true := by
  decide +kernel

/-- Acceptance of the concrete certificate with the transition-based checker. -/
theorem concreteCarryGroupedCheck : testCarryGroupedCertificateFastInit = true :=
  concreteFastInitialCarryGroupedCheck

theorem concreteThreeRoundImpossible (k₂ bR : V 32) :
    xorDDT_rounds 3 (threeRoundKeys (0#32) (0#32) k₂) ((1#32), (1#32)) ((0#32), bR) = 0 := by
  exact concreteThreeRoundImpossible_of_checked k₂ bR concreteFastInitialCarryGroupedCheck

-- Measurements remain evaluations; fixed acceptance is proved above.
#eval profileFastInitialCoverBySteps

#eval profileCheckedCarryReduction

end Magma.Evidence.FastInitialCover
