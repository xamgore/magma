module

public import Magma.OneHotKeyClasses
import all Init.Data.Range.Basic

@[expose] public section

/-!
# Independently certified representatives of the 32 local key classes

The representative of a local class has the specified key nibble and common
incoming-carry flag. A key and its representative therefore have the same
local prediction. The aggregate checker independently verifies both DDT
support inclusions for each of the 32 representative keys.

`OneHotClassInvariant` states the semantic condition that replacing an
arbitrary key by its representative preserves full-word one-bit DDT support.
The conditional classification theorem in this module takes this invariant
and acceptance of the representative certificates as explicit hypotheses.
-/

open Magma.Internal Magma.CarryAutomaton Magma.MultiRoundDDT
open Magma.OneHotKeyClasses Magma.OneHotCompleteSupport

namespace Magma.OneHotClassCertificates

/-! ## 1. Closed arithmetic on the 32 class representatives -/

/-- The representative for a class really has that key nibble and carry flag. -/
theorem representativeKey_has_class (q : Fin 16) (c : Bool) :
    keyNibble5 (representativeKey q c) = q ∧
    canCarryIntoNibble5 (representativeKey q c) = c := by
  fin_cases q <;> cases c <;> decide

/-- The *local prediction* is identical for a key and its representative.
    This does NOT yet prove equality of true DDT supports. -/
theorem predictedOneHotPositions_eq_representative (k : V 32) :
    predictedOneHotPositions k =
      predictedOneHotPositions
        (representativeKey (keyNibble5 k) (canCarryIntoNibble5 k)) := by
  have hclass := representativeKey_has_class
    (keyNibble5 k) (canCarryIntoNibble5 k)
  unfold predictedOneHotPositions
  rw [hclass.1, hclass.2]

/-! ## 2. One checker, 32 independent original-arithmetic certificates -/

/-- Run the ORIGINAL two-sided checker on all 16 × 2 representatives.
    Unlike `profileKeyClasses`, this checks actual original `g` witnesses
    and original carry-frontier no-path certificates. -/
def verifyAllRepresentativeClasses : Bool :=
  (List.finRange 16).all fun q =>
    ([false, true] : List Bool).all fun c =>
      checkPredictedOneHotSupport (representativeKey q c)

/-- The finite combined certificate establishes the EXACT one-hot support
    for every one of the 32 representative keys. -/
theorem verifyAllRepresentativeClasses_sound
    (h : verifyAllRepresentativeClasses = true)
    (q : Fin 16) (c : Bool) (j : Fin 32) :
    0 < xorDDT_g (representativeKey q c)
        (BitVec.ofNat 32 (2 ^ j.val)) (1#32) ↔
      j ∈ predictedOneHotPositions (representativeKey q c) := by
  simp only [verifyAllRepresentativeClasses] at h
  have hq := (List.all_eq_true.mp h) q (by simp)
  have hc : c ∈ ([false, true] : List Bool) := by
    cases c <;> simp
  have hv := (List.all_eq_true.mp hq) c hc
  exact checkedPredictedOneHotSupport_iff (representativeKey q c) hv j

/-- One representative certificate also certifies entire zero-left
    three-round columns for arbitrary first and third keys. -/
theorem verifiedRepresentativeThreeRoundColumns
    (h : verifyAllRepresentativeClasses = true)
    (q : Fin 16) (c : Bool) (j : Fin 32)
    (k₀ k₂ : V 32) :
    (∀ aL : V 32,
       xorDDT_rounds 3
         (threeRoundKeys k₀ (representativeKey q c) k₂)
         (aL, 1#32)
         (0#32, BitVec.ofNat 32 (2 ^ j.val)) = 0) ↔
      j ∉ predictedOneHotPositions (representativeKey q c) := by
  simp only [verifyAllRepresentativeClasses] at h
  have hq := (List.all_eq_true.mp h) q (by simp)
  have hc : c ∈ ([false, true] : List Bool) := by
    cases c <;> simp
  have hv := (List.all_eq_true.mp hq) c hc
  exact checkedPredictedThreeRoundColumns_iff
    k₀ (representativeKey q c) k₂ hv j

/-! ## 3. The full-word key-class invariance proposition -/

/-- A statement purely about the FULL 32-bit round-function DDT:
    replacing a key by the representative of its two local invariants
    preserves the support of the one-bit-input, output-1 slice.

    This is a proposition about every key, independently of Boolean
    checks on the 32 representatives. -/
def OneHotClassInvariant : Prop :=
  ∀ (k : V 32) (j : Fin 32),
    (0 < xorDDT_g k (BitVec.ofNat 32 (2 ^ j.val)) (1#32)) ↔
    (0 < xorDDT_g
      (representativeKey (keyNibble5 k) (canCarryIntoNibble5 k))
      (BitVec.ofNat 32 (2 ^ j.val)) (1#32))

/-- Once the representative certificates and the structural key-class
    invariance are both established, ALL 2^32 keys are classified. -/
theorem allKeys_support_of_classInvariant
    (hcert : verifyAllRepresentativeClasses = true)
    (hinv : OneHotClassInvariant)
    (k : V 32) (j : Fin 32) :
    0 < xorDDT_g k (BitVec.ofNat 32 (2 ^ j.val)) (1#32) ↔
      j ∈ predictedOneHotPositions k := by
  let q := keyNibble5 k
  let c := canCarryIntoNibble5 k
  calc
    0 < xorDDT_g k (BitVec.ofNat 32 (2 ^ j.val)) (1#32) ↔
        0 < xorDDT_g (representativeKey q c)
            (BitVec.ofNat 32 (2 ^ j.val)) (1#32) :=
      hinv k j
    _ ↔ j ∈ predictedOneHotPositions (representativeKey q c) :=
      verifyAllRepresentativeClasses_sound hcert q c j
    _ ↔ j ∈ predictedOneHotPositions k := by
      rw [predictedOneHotPositions_eq_representative k]

end Magma.OneHotClassCertificates
