module

public import Magma.OneHot.DiagonalExactWeights
import Mathlib.Tactic.Ring
import all Init.Data.Range.Basic

@[expose] public section

/-!
Quantitative one-hot DDT: exact cardinality of the *factorized* input
fiber, at an arbitrary active nibble i=0..7.

This module proves the
multiplicative prefix / active digit / suffix count with no enumeration of
32-bit inputs, and provides a single named quantitative bridge as the next
proof obligation.

Unlike the already proved support equivalence, no statement below infers
equality of positive numbers merely from matching supports. In particular,
`real_DDT_eq_diagonalWeight_of_fiberCount` is CONDITIONAL on the precise
full-input fiber count. The unconditional theorem in this module is
`factorizedInputFiber_card`.

-/

namespace Magma.OneHotDiagonalQuantitativeFibers

open Magma
open Magma.CarryAutomaton
open Magma.OneHotDiagonalExactWeights

private abbrev Word :=
  V 32

/-! ### 1. The three independent coordinates of the proposed fiber. -/

/-- Lower input prefixes that generate the *actual arithmetic* incoming
    carry `c` into the active nibble. Its elements are plain naturals
    below 16^i, not 32-bit words. -/
def lowerCarryFiber (k : Word) (i : Fin 8) (c : Fin 2) : Finset Nat :=
  (Finset.range (lowBase i)).filter (fun x =>
    (x + keyPrefix k i) / lowBase i = c.val)

/-- Accepted active input digits for this exact incoming carry, as
    specified by the same S-box and two-carry transition as the real DP.
    At i=7 the final carries are intentionally discarded. -/
def activeDigitFiber (k : Word) (i : Fin 8)
    (r s : Fin 4) (c : Fin 2) : Finset (Fin 16) :=
  (Finset.univ : Finset (Fin 16)).filter (fun x =>
    let step := sboxCarryStep i (wordDigits k i)
      (Fin.ofNat 16 (2 ^ r.val)) x (c, c)
    step.1 = Fin.ofNat 16 (2 ^ s.val) ∧
      (i.val = 7 ∨ step.2.1 = step.2.2))

/-- All 16^(7-i) higher digit assignments are free once the two
    carry chains have rejoined at the active nibble. -/
private abbrev Upper (i : Fin 8) := Fin (suffixFactor i)

/-- Input coordinates: (lower prefix, (active digit, upper suffix)).
    The two branches distinguish the incoming carry values 0 and 1. -/
def factorizedInputFiber (k : Word) (i : Fin 8)
    (r s : Fin 4) : Finset (Nat × (Fin 16 × Upper i)) :=
  (lowerCarryFiber k i 0 ×ˢ
    (activeDigitFiber k i r s 0 ×ˢ (Finset.univ : Finset (Upper i)))) ∪
  (lowerCarryFiber k i 1 ×ˢ
    (activeDigitFiber k i r s 1 ×ˢ (Finset.univ : Finset (Upper i))))

/-- Membership is entirely determined by the low prefix and the
    active digit: the upper suffix is unrestricted. This is the precise
    predicate needed to connect the real trace to the coordinate fiber. -/
theorem factorizedInputFiber_mem_iff
    (k : Word) (i : Fin 8) (r s : Fin 4)
    (x : Nat) (a : Fin 16) (upper : Upper i) :
    (x, (a, upper)) ∈ factorizedInputFiber k i r s ↔
      (x ∈ lowerCarryFiber k i 0 ∧ a ∈ activeDigitFiber k i r s 0) ∨
      (x ∈ lowerCarryFiber k i 1 ∧ a ∈ activeDigitFiber k i r s 1) := by
  simp only [factorizedInputFiber, Finset.mem_union,
    Finset.mem_product, Finset.mem_univ, and_true]

/-! ### 2. Exactly one fiber for each incoming carry. -/

private theorem lowerCarryFiber_zero_card (k : Word) (i : Fin 8) :
    (lowerCarryFiber k i 0).card = lowBase i - keyPrefix k i := by exact count_zero_prefixes k i

private theorem lowerCarryFiber_one_card (k : Word) (i : Fin 8) :
    (lowerCarryFiber k i 1).card = keyPrefix k i := by exact count_one_prefixes k i

private theorem activeDigitFiber_card (k : Word) (i : Fin 8) (r s : Fin 4) (c : Fin 2) :
    (activeDigitFiber k i r s c).card = localMultiplicity i (wordDigits k i) c r s := by rfl

/-- The two branches cannot share an input prefix because the actual
    incoming carry cannot be both 0 and 1. -/
private theorem twoBranches_disjoint (k : Word) (i : Fin 8)
    (r s : Fin 4) :
    Disjoint
      (lowerCarryFiber k i 0 ×ˢ
        (activeDigitFiber k i r s 0 ×ˢ (Finset.univ : Finset (Upper i))))
      (lowerCarryFiber k i 1 ×ˢ
        (activeDigitFiber k i r s 1 ×ˢ (Finset.univ : Finset (Upper i)))) := by
  apply Finset.disjoint_left.mpr
  intro p hp₀ hp₁
  have h₀ := (Finset.mem_product.mp hp₀).1
  have h₁ := (Finset.mem_product.mp hp₁).1
  change p.1 ∈ lowerCarryFiber k i 0 at h₀
  change p.1 ∈ lowerCarryFiber k i 1 at h₁
  simp only [lowerCarryFiber, Finset.mem_filter,
    Finset.mem_range] at h₀ h₁
  omega

/-! ### 3. The quantitative product count — unconditional. -/

/-- The factorized fiber has EXACTLY the proposed closed DDT weight.
    This is a general eight-nibble cardinality theorem. It consumes no
    key-space enumeration and has no semantic DDT assumption. -/
theorem factorizedInputFiber_card
    (k : Word) (i : Fin 8) (r s : Fin 4) :
    (factorizedInputFiber k i r s).card = diagonalWeight k i r s := by
  unfold factorizedInputFiber
  rw [Finset.card_union_of_disjoint (twoBranches_disjoint k i r s)]
  simp only [Finset.card_product, Finset.card_univ,
    Fintype.card_fin]
  rw [lowerCarryFiber_zero_card, lowerCarryFiber_one_card,
    activeDigitFiber_card, activeDigitFiber_card]
  change
    (lowBase i - keyPrefix k i) *
        (localMultiplicity i (wordDigits k i) 0 r s * suffixFactor i) +
      keyPrefix k i *
        (localMultiplicity i (wordDigits k i) 1 r s * suffixFactor i) =
      suffixFactor i *
        ((lowBase i - keyPrefix k i) *
            localMultiplicity i (wordDigits k i) 0 r s +
          keyPrefix k i * localMultiplicity i (wordDigits k i) 1 r s)
  ring

/-- An unconditional consistency result: the explicitly counted
    coordinate fiber is nonempty exactly when the ACTUAL DDT coefficient
    is positive. The two counts need not be equal to prove this lemma. -/
theorem factorizedInputFiber_nonempty_iff_real_positive
    (k : Word) (i : Fin 8) (r s : Fin 4) :
    (factorizedInputFiber k i r s).Nonempty ↔
      0 < xorDDT_g k
        (BitVec.ofNat 32 (2 ^ (4 * i.val + r.val)))
        (rot11 (BitVec.ofNat 32 (2 ^ (4 * i.val + s.val)))) := by
  rw [← Finset.card_pos, factorizedInputFiber_card]
  exact diagonalWeight_pos_iff_real k i r s

/-! ### 4. The remaining precise semantic task. -/

/-- The full input fiber is the DDT count before the final rotation.
    The remaining proof should use the explicit bijection (for B=16^i)
      x ↦ (x.toNat % B,
            wordDigits x i,
            ⟨x.toNat / (16*B), proof_of_lt_16_pow_(7-i)⟩)
    between full input words and (lower, active, upper) coordinates.
    Its inverse is `BitVec.ofNat 32 (low + B*(active+16*upper))`.
    Crucially, its membership equivalence needs the *actual* carryTrace:
    incoming carry is determined by the lower coordinate, the active
    transition must match `activeDigitFiber`, and the upper digits are
    unconstrained when the outgoing carries synchronize. The last nibble
    is treated separately because overflow is ignored.

    This is a named, genuinely missing quantitative obligation — NOT
    an axiom and NOT proved by matching support alone. -/
def quantitativeFiberBridge : Prop :=
  ∀ (k : Word) (i : Fin 8) (r s : Fin 4),
    carryWordCount k
      (BitVec.ofNat 32 (2 ^ (4 * i.val + r.val)))
      (BitVec.ofNat 32 (2 ^ (4 * i.val + s.val))) =
        (factorizedInputFiber k i r s).card

/-- With the precise semantic fiber equivalence established, the
    exact formula for the ORIGINAL Magma DDT follows in three rewrites.
    The hypothesis is explicit; this is not yet an unconditional result. -/
theorem real_DDT_eq_diagonalWeight_of_fiberCount
    (h : quantitativeFiberBridge)
    (k : Word) (i : Fin 8) (r s : Fin 4) :
    xorDDT_g k
      (BitVec.ofNat 32 (2 ^ (4 * i.val + r.val)))
      (rot11 (BitVec.ofNat 32 (2 ^ (4 * i.val + s.val)))) =
        diagonalWeight k i r s := by
  rw [xorDDT_g_eq_carryMatrixCount]
  rw [← carryWordCount_eq_carryMatrixCount]
  exact (h k i r s).trans (factorizedInputFiber_card k i r s)

end Magma.OneHotDiagonalQuantitativeFibers
