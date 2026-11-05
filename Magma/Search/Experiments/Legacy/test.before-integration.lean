import Magma.Search.FastSearch

namespace Magma
namespace Certificates
namespace FastInitialCheck

/-
  Fast, independently VERIFIED initialization-mask checker.

  Experimental checker built on the imported mask encoding, fast domain
  initialization and the general carry/grouped certificate soundness theorem.

  The old initial-mask checker repeatedly decides an existential over carry
  states and nibble inputs.  Here we enumerate actual sboxCarryStep transitions
  once, and prove the result IMPLIES the old initial-mask checker.

  Important: this proves checker soundness; it does NOT claim that
  fastInitialBitDomains is definitionally equal to the old Finset domains.
  The new checker still tests the proposed masks at runtime.

  No new axiom / sorry / native_decide.
-/

open Magma.CarryAutomaton
open Magma.MultiRoundDDT
open Magma.Pruning Magma.Certificates.Encoding Magma.FastSearch
open Magma.Certificates
open Magma.Certificates.BackwardMask

/-! ## 1. Enumerate source transitions, not nested `Decidable` witnesses -/

/-- Every genuine first-machine local transition has its output value
    in the corresponding proposed UInt16 mask. -/
def verifyFirstInitialCoverBySteps
    (k₀ aR : V 32) (D : UInt16BitDomains) : Bool :=
  (List.finRange 8).all fun i =>
    (List.finRange 2).all fun c₀ =>
      (List.finRange 2).all fun c₁ =>
        (List.finRange 16).all fun x =>
          uint16DomainHas (D.1.getD i.val 0)
            (sboxCarryStep i (wordDigits k₀ i) (wordDigits aR i)
              x (c₀, c₁)).1

/-- For the second machine, only transitions producing the prescribed
    target difference impose a membership obligation on the input difference. -/
def verifySecondInitialCoverBySteps
    (k₁ aR bL : V 32) (D : UInt16BitDomains) : Bool :=
  let target := (xor bL aR).rotateRight 11
  (List.finRange 8).all fun i =>
    (List.finRange 16).all fun d =>
      (List.finRange 2).all fun c₀ =>
        (List.finRange 2).all fun c₁ =>
          (List.finRange 16).all fun x =>
            let step := sboxCarryStep i (wordDigits k₁ i) d x (c₀, c₁)
            (!(decide (step.1 = wordDigits target i))) ||
              uint16DomainHas (D.2.getD i.val 0) d

/-- A cheap source-semantics check for the two initial mask arrays. -/
def verifyInitialCoverBySteps
    (k₀ k₁ aR bL : V 32) (D : UInt16BitDomains) : Bool :=
  verifyFirstInitialCoverBySteps k₀ aR D &&
    verifySecondInitialCoverBySteps k₁ aR bL D

/-! ## 2. Boolean reflection without unfolding large Decidable instances -/

private theorem firstStep_mem
    (k₀ aR : V 32) (D : UInt16BitDomains)
    (h : verifyFirstInitialCoverBySteps k₀ aR D = true)
    (i : Fin 8) (s : CarryState) (x : Fin 16) :
    uint16DomainHas (D.1.getD i.val 0)
      (sboxCarryStep i (wordDigits k₀ i) (wordDigits aR i) x s).1 = true := by
  unfold verifyFirstInitialCoverBySteps at h
  have hi := (List.all_eq_true.mp h) i (by simp)
  have h₀ := (List.all_eq_true.mp hi) s.1 (by simp)
  have h₁ := (List.all_eq_true.mp h₀) s.2 (by simp)
  exact (List.all_eq_true.mp h₁) x (by simp)

private theorem secondStep_mem
    (k₁ aR bL : V 32) (D : UInt16BitDomains)
    (h : verifySecondInitialCoverBySteps k₁ aR bL D = true)
    (i : Fin 8) (s : CarryState) (d x : Fin 16)
    (htarget :
      (sboxCarryStep i (wordDigits k₁ i) d x s).1 =
        wordDigits ((xor bL aR).rotateRight 11) i) :
    uint16DomainHas (D.2.getD i.val 0) d = true := by
  unfold verifySecondInitialCoverBySteps at h
  dsimp only at h
  have hi := (List.all_eq_true.mp h) i (by simp)
  have hd := (List.all_eq_true.mp hi) d (by simp)
  have h₀ := (List.all_eq_true.mp hd) s.1 (by simp)
  have h₁ := (List.all_eq_true.mp h₀) s.2 (by simp)
  have hx := (List.all_eq_true.mp h₁) x (by simp)
  simp only [Bool.or_eq_true_iff] at hx
  rcases hx with hbad | hgood
  · simp [htarget] at hbad
  · exact hgood

/-! ## 3. Universal coverage of the *original* Finset local domains -/

private theorem firstCover_sound
    (k₀ aR : V 32) (D : UInt16BitDomains)
    (h : verifyFirstInitialCoverBySteps k₀ aR D = true)
    (i : Fin 8) (v : Fin 16)
    (hv : v ∈ outputDigitDomain i (wordDigits k₀ i) (wordDigits aR i)) :
    uint16DomainHas (D.1.getD i.val 0) v = true := by
  have hp := (Finset.mem_filter.mp hv).2
  obtain ⟨s, t, x, hstep⟩ := (decide_eq_true_eq).mp hp
  have hfound := firstStep_mem k₀ aR D h i s x
  have hout :
      (sboxCarryStep i (wordDigits k₀ i) (wordDigits aR i) x s).1 = v :=
    congrArg Prod.fst hstep
  simpa only [hout] using hfound

private theorem secondCover_sound
    (k₁ aR bL : V 32) (D : UInt16BitDomains)
    (h : verifySecondInitialCoverBySteps k₁ aR bL D = true)
    (i : Fin 8) (d : Fin 16)
    (hd : d ∈ inputDiffDigitDomain i (wordDigits k₁ i)
      (wordDigits ((xor bL aR).rotateRight 11) i)) :
    uint16DomainHas (D.2.getD i.val 0) d = true := by
  have hp := (Finset.mem_filter.mp hd).2
  obtain ⟨s, t, x, hstep⟩ := (decide_eq_true_eq).mp hp
  have htarget :
      (sboxCarryStep i (wordDigits k₁ i) d x s).1 =
        wordDigits ((xor bL aR).rotateRight 11) i :=
    congrArg Prod.fst hstep
  exact secondStep_mem k₁ aR bL D h i s d x htarget

/-- Universal semantic soundness: the fast checker covers EVERY member
    of both original Finset-domain families, for ALL 32-bit inputs. -/
theorem verifyInitialCoverBySteps_sound
    (k₀ k₁ aR bL : V 32) (D : UInt16BitDomains)
    (h : verifyInitialCoverBySteps k₀ k₁ aR bL D = true) :
    ∀ i : Fin 8,
      (∀ v ∈ outputDigitDomain i (wordDigits k₀ i) (wordDigits aR i),
        uint16DomainHas (D.1.getD i.val 0) v = true) ∧
      (∀ v ∈ inputDiffDigitDomain i (wordDigits k₁ i)
        (wordDigits ((xor bL aR).rotateRight 11) i),
        uint16DomainHas (D.2.getD i.val 0) v = true) := by
  obtain ⟨hfirst, hsecond⟩ := Bool.and_eq_true_iff.mp h
  intro i
  exact ⟨fun v hv => firstCover_sound k₀ aR D hfirst i v hv,
    fun d hd => secondCover_sound k₁ aR bL D hsecond i d hd⟩

/-- IMPORTANT: an accepted fast transition checker logically implies
    acceptance by the PREVIOUS, expensive initial Finset checker.
    This theorem does NOT execute the old checker. -/
theorem verifyInitialMaskCover_of_steps
    (k₀ k₁ aR bL : V 32) (D : UInt16BitDomains)
    (h : verifyInitialCoverBySteps k₀ k₁ aR bL D = true) :
    verifyInitialMaskCover k₀ k₁ aR bL D = true := by
  have hc := verifyInitialCoverBySteps_sound k₀ k₁ aR bL D h
  unfold verifyInitialMaskCover
  apply List.all_eq_true.mpr
  intro i _
  apply List.all_eq_true.mpr
  intro v _
  apply Bool.and_eq_true_iff.mpr
  constructor
  · by_cases hp : v ∈ outputDigitDomain i (wordDigits k₀ i) (wordDigits aR i)
    · have hm := (hc i).1 v hp
      simpa only [hp, decide_true, Bool.not_true, Bool.false_or] using hm
    · simp [hp]
  · by_cases hp : v ∈ inputDiffDigitDomain i (wordDigits k₁ i)
        (wordDigits ((xor bL aR).rotateRight 11) i)
    · have hm := (hc i).2 v hp
      simpa only [hp, decide_true, Bool.not_true, Bool.false_or] using hm
    · simp [hp]

/-! ## 4. Reuse the existing trusted carry + grouped theorem unchanged -/

/-- Final zero-DDT result with a fast initial-mask checker.
    The previous carry and grouped certificate checking stays unchanged. -/
theorem xorDDT_rounds_three_zero_of_checkedCarryGrouped_fastInit
    (k₀ k₁ k₂ aL aR bL bR : V 32)
    (D : UInt16BitDomains)
    (cert : CarryReductionCertificate)
    (next : UInt16BitDomains)
    (hinit : verifyInitialCoverBySteps k₀ k₁ aR bL D = true)
    (hchecked : verifyOneCarryThenGrouped
      k₀ k₁ aL aR bL D cert next = true) :
    xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
      (aL, aR) (bL, bR) = 0 := by
  exact xorDDT_rounds_three_zero_of_checkedCarryGrouped
    k₀ k₁ k₂ aL aR bL bR D cert next
    (verifyInitialMaskCover_of_steps k₀ k₁ aR bL D hinit) hchecked

/-- Same concrete proposal as before, but its initial-mask coverage
    is checked by ~8704 explicit local transitions instead of Finset-DP. -/
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

/-
  These recipes are typechecked without execution on each elaboration of this
  scratch file. To run a recipe and see its output, replace `#check` with
  `#eval` and remove its guard. Type errors still fail elaboration.
-/
#guard_msgs (drop info) in
#check (Magma.Certificates.FastInitialCheck.profileFastInitialCoverBySteps : IO Unit)
/-
  Recorded output from the previous project check:
  [initial-fast] accepted=true; time=7829ms
  The elapsed time is historical and environment-dependent.
-/

#guard_msgs (drop info) in
#check (Magma.Certificates.FastInitialCheck.testCarryGroupedCertificateFastInit : Bool)

-- Establish acceptance with a kernel-checked equality, independently of diagnostic output.
set_option maxHeartbeats 0 in
example : Magma.Certificates.FastInitialCheck.testCarryGroupedCertificateFastInit = true := by
  decide +kernel

end FastInitialCheck
end Certificates
end Magma
