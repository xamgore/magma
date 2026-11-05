module

import all Init.Data.Range.Basic
public import Magma.Differential.Windows.DiagonalSupportScheduledWindows
public import Magma.DDT.OneHot.KeyClasses.FullKeyClassInvariant
public import Magma.DDT.ZeroLeft.ParityCompleteSlice

@[expose] public section

/-!
# Master-key classes for the three-round diagonal

Two already proved one-round classifications now lift to any of the 30
ordinary three-round windows of the REAL 256-bit Magma key schedule:

* aR = 1: **exact coefficients** depend only on the parities of the
  first and third round keys in the chosen three-round window;
* aR = oneHot j and aL = bR = 1: **exact support** is specified by two
  local nibble-5/carry classes. Outside nibble 5, the whole diagonal
  differential is impossible for all master keys.

These are predicates on ONE master word, not independent round keys.
-/

namespace Magma.DifanDiagonalMasterKeyClasses

open Magma
open Magma.MultiRoundDDT
open Magma.CarryAutomaton
open Magma.DifanDiagonalSupportScheduledWindows
open Magma.DifanThreeRoundMiddleDiagonal
open Magma.OneHotKeyClasses
open Magma.OneHotFullKeyClassInvariant
open Magma.ZeroLeftParityCompleteSlice

private abbrev Word :=
  V 32

/-- Recover three explicit round keys from a scheduled three-round window.
    This is a definitional bridge, not a duplicate cipher model. -/
private theorem scheduledThreeKeys_as_threeRoundKeys
    (master : V 256) (start : Fin 30) :
    scheduledThreeKeys master start =
      threeRoundKeys
        (roundKey master ⟨start.val, by omega⟩)
        (roundKey master ⟨start.val + 1, by omega⟩)
        (roundKey master ⟨start.val + 2, by omega⟩) := by
  funext i
  fin_cases i <;> rfl

/-- **Exact coefficient**, not just support, for the whole diagonal
    with unit input-right/output-left difference. Both local DDTs are
    classified for every key by the verified even/odd reference rows. -/
theorem scheduledThree_unit_diagonal_exact
    (master : V 256) (start : Fin 30) (aL bR : Word) :
    xorDDT_rounds 3 (scheduledThreeKeys master start)
      (aL, 1#32) (1#32, bR) =
    parityRowCount (roundKey master ⟨start.val, by omega⟩) aL *
      parityRowCount (roundKey master ⟨start.val + 2, by omega⟩) bR := by
  rw [scheduledThreeKeys_as_threeRoundKeys,
    threeRound_middleDiagonal_factorization]
  simp only [one_round_unit_exact]

/-- A single one-round entry with input 1 is positive exactly when its
    output lies in the certified parity-selected support set. -/
private theorem unit_ddt_pos_iff_parity_support (k d : Word) :
    0 < xorDDT_g k (1#32) d ↔ d ∈ parityRowSupport k := by
  rw [← one_round_unit_support_exact k]
  change 0 < xorDDT_g k (1#32) d ↔
    d ∈ (Finset.univ : Finset Word).filter
      (fun b => 0 < xorDDT_g k (1#32) b)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- **Exact master-key predicate** for the unit diagonal: it is the
    intersection of two even/odd row-support conditions, with genuine
    scheduled subkeys of the SAME master. -/
theorem scheduledThree_unit_diagonal_support_iff
    (master : V 256) (start : Fin 30) (aL bR : Word) :
    0 < xorDDT_rounds 3 (scheduledThreeKeys master start)
      (aL, 1#32) (1#32, bR) ↔
      aL ∈ parityRowSupport
        (roundKey master ⟨start.val, by omega⟩) ∧
      bR ∈ parityRowSupport
        (roundKey master ⟨start.val + 2, by omega⟩) := by
  rw [scheduledThree_diagonal_support_iff]
  change
    (0 < xorDDT_g (roundKey master ⟨start.val, by omega⟩)
      (1#32) aL ∧
     0 < xorDDT_g (roundKey master ⟨start.val + 2, by omega⟩)
      (1#32) bR) ↔ _
  rw [unit_ddt_pos_iff_parity_support,
    unit_ddt_pos_iff_parity_support]

/-- The exact coefficient is constant on each class of master keys
    with equal parities in both relevant round-key positions. -/
theorem scheduledThree_unit_diagonal_same_parities
    (master other : V 256) (start : Fin 30) (aL bR : Word)
    (h₀ : (roundKey master ⟨start.val, by omega⟩).toNat % 2 =
      (roundKey other ⟨start.val, by omega⟩).toNat % 2)
    (h₂ : (roundKey master ⟨start.val + 2, by omega⟩).toNat % 2 =
      (roundKey other ⟨start.val + 2, by omega⟩).toNat % 2) :
    xorDDT_rounds 3 (scheduledThreeKeys master start)
      (aL, 1#32) (1#32, bR) =
    xorDDT_rounds 3 (scheduledThreeKeys other start)
      (aL, 1#32) (1#32, bR) := by
  rw [scheduledThree_unit_diagonal_exact,
    scheduledThree_unit_diagonal_exact]
  simp only [parityRowCount, h₀, h₂]

/-- The complete 32-class input-one-hot support condition at a local
    key (one nibble and a reachable carry-in regime). -/
def oneHotLocalClass (k : Word) (j : Fin 32) : Prop :=
  ∃ r : Fin 4,
    j.val = 20 + r.val ∧
      r ∈ localOneHotSupportedBits
        (keyNibble5 k) (canCarryIntoNibble5 k)

private theorem local_class_iff_ddt (k : Word) (j : Fin 32) :
    oneHotLocalClass k j ↔ 0 < xorDDT_g k (BitVec.ofNat 32 (2 ^ j.val)) (1#32) := by
  exact (oneHot_all_pos_iff_localTable k j).symm

/-- One-hot input-right and unit input-left/output-right differences:
    the 3-round transition is possible exactly when both OUTER
    round keys belong to the appropriate certified local classes. -/
theorem scheduledThree_oneHot_unit_support_iff
    (master : V 256) (start : Fin 30) (j : Fin 32) :
    0 < xorDDT_rounds 3 (scheduledThreeKeys master start)
      (1#32, BitVec.ofNat 32 (2 ^ j.val))
      (BitVec.ofNat 32 (2 ^ j.val), 1#32) ↔
    oneHotLocalClass (roundKey master ⟨start.val, by omega⟩) j ∧
      oneHotLocalClass (roundKey master ⟨start.val + 2, by omega⟩) j := by
  rw [scheduledThree_diagonal_support_iff]
  change
    (0 < xorDDT_g (roundKey master ⟨start.val, by omega⟩)
       (BitVec.ofNat 32 (2 ^ j.val)) (1#32) ∧
     0 < xorDDT_g (roundKey master ⟨start.val + 2, by omega⟩)
       (BitVec.ofNat 32 (2 ^ j.val)) (1#32)) ↔ _
  simp only [← local_class_iff_ddt]

/-- All 28 positions outside nibble 5 are impossible on the chosen
    three-round diagonal, uniformly over the complete master-key space. -/
theorem scheduledThree_oneHot_outside_nibble5_zero
    (master : V 256) (start : Fin 30) (j : Fin 32)
    (hout : j.val < 20 ∨ 24 ≤ j.val) :
    xorDDT_rounds 3 (scheduledThreeKeys master start)
      (1#32, BitVec.ofNat 32 (2 ^ j.val))
      (BitVec.ofNat 32 (2 ^ j.val), 1#32) = 0 := by
  apply Nat.eq_zero_of_not_pos
  intro hp
  obtain ⟨⟨r, hr, _⟩, _⟩ :=
    (scheduledThree_oneHot_unit_support_iff master start j).mp hp
  omega

/-- For this one-hot diagonal, two master keys with matching nibble-5
    and carry-class invariants at both scheduled positions have identical
    support. This is a classification, not an independence assumption. -/
theorem scheduledThree_oneHot_same_local_classes
    (master other : V 256) (start : Fin 30) (j : Fin 32)
    (h₀ : keyNibble5 (roundKey master ⟨start.val, by omega⟩) =
      keyNibble5 (roundKey other ⟨start.val, by omega⟩))
    (hc₀ : canCarryIntoNibble5
        (roundKey master ⟨start.val, by omega⟩) =
      canCarryIntoNibble5 (roundKey other ⟨start.val, by omega⟩))
    (h₂ : keyNibble5 (roundKey master ⟨start.val + 2, by omega⟩) =
      keyNibble5 (roundKey other ⟨start.val + 2, by omega⟩))
    (hc₂ : canCarryIntoNibble5
        (roundKey master ⟨start.val + 2, by omega⟩) =
      canCarryIntoNibble5 (roundKey other ⟨start.val + 2, by omega⟩)) :
    (0 < xorDDT_rounds 3 (scheduledThreeKeys master start)
      (1#32, BitVec.ofNat 32 (2 ^ j.val))
      (BitVec.ofNat 32 (2 ^ j.val), 1#32)) ↔
    (0 < xorDDT_rounds 3 (scheduledThreeKeys other start)
      (1#32, BitVec.ofNat 32 (2 ^ j.val))
      (BitVec.ofNat 32 (2 ^ j.val), 1#32)) := by
  rw [scheduledThree_oneHot_unit_support_iff,
    scheduledThree_oneHot_unit_support_iff]
  simp only [oneHotLocalClass, h₀, hc₀, h₂, hc₂]

end Magma.DifanDiagonalMasterKeyClasses
