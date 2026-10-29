module

public import Magma.DDT.OneHot.Extrema.CandidateSharpWitnesses
import all Init.Data.Range.Basic

@[expose] public section

/-!
# Exact one-hot DDT support for a fixed key

`fastOneHotDDT` computes the genuine DDT by carry DP, skipping the 948
universally impossible cells. Its correctness holds for every key.
The key `0x06120010` has exactly 72 positive one-hot entries, whereas
the union of support over all keys has 76 entries.

A separate local-potential model has a symbolic ceiling of 72 when
prefix carries are consistent. The bridge bounding the actual support
of every key by this model is not established here. Reproducible
computations are in Evidence iteration 18.
-/

namespace Magma.OneHotFixedKeySupportAudit

open Magma
open Magma.CarryAutomaton
open Magma.OneHotDiagonalCarryMasks

private abbrev Word :=
  V 32

private theorem rotate_single_bit_back (ell : Fin 32) :
    rot11 (BitVec.ofNat 32 (2 ^ ((ell.val + 21) % 32))) = BitVec.ofNat 32 (2 ^ ell.val) := by
  fin_cases ell <;> decide

/-- Exact, computationally tractable one-hot DDT entry.
    The zero branch is justified by the already proved mask theorem. -/
def fastOneHotDDT (k : Word) (j ell : Fin 32) : Nat :=
  if decide (candidateCell j ell) then
    carryDPCount
      (wordDigits k)
      (wordDigits (BitVec.ofNat 32 (2 ^ j.val)))
      (wordDigits (BitVec.ofNat 32 (2 ^ ((ell.val + 21) % 32))))
  else 0

/-- `fastOneHotDDT` counts the genuine RFC round-function transitions
    for EVERY key and pair of positions, not just for witness keys. -/
theorem fastOneHotDDT_correct (k : Word) (j ell : Fin 32) :
    fastOneHotDDT k j ell =
      xorDDT_g k (BitVec.ofNat 32 (2 ^ j.val))
        (BitVec.ofNat 32 (2 ^ ell.val)) := by
  by_cases hc : candidateCell j ell
  · unfold fastOneHotDDT
    have htrue : decide (candidateCell j ell) = true := by simp [hc]
    simp only [htrue, ite_true]
    rw [← rotate_single_bit_back ell]
    exact (carryDPCount_eq_carryMatrixCount _ _ _).trans
      (xorDDT_g_eq_carryMatrixCount k
        (BitVec.ofNat 32 (2 ^ j.val))
        (BitVec.ofNat 32 (2 ^ ((ell.val + 21) % 32)))).symm
  · simp [fastOneHotDDT, hc,
      oneHot_DDT_zero_of_not_candidate k j ell hc]

/-- Support of the 32×32 one-hot matrix for one particular round key. -/
def fastPositiveCells (k : Word) : Finset (Fin 32 × Fin 32) :=
  (Finset.univ : Finset (Fin 32 × Fin 32)).filter
    (fun p : Fin 32 × Fin 32 => 0 < fastOneHotDDT k p.1 p.2)

/-- Bridge to the mathematical (Finset-based) DDT support. -/
theorem fastPositiveCells_eq_real (k : Word) :
    fastPositiveCells k =
      (Finset.univ : Finset (Fin 32 × Fin 32)).filter
        (fun p : Fin 32 × Fin 32 => 0 < xorDDT_g k
          (BitVec.ofNat 32 (2 ^ p.1.val))
          (BitVec.ofNat 32 (2 ^ p.2.val))) := by
  ext p
  simp only [fastPositiveCells, Finset.mem_filter,
    Finset.mem_univ, true_and]
  rw [fastOneHotDDT_correct k p.1 p.2]

/-- Count all four-by-four cells in input nibble i, by exact carry-DP. -/
def positiveCellsInNibble (k : Word) (i : Fin 8) : Nat :=
  ((Finset.univ : Finset (Fin 4 × Fin 4)).filter (fun rs : Fin 4 × Fin 4 =>
      0 < fastOneHotDDT k
        (⟨4 * i.val + rs.1.val, by omega⟩ : Fin 32)
        (⟨(4 * i.val + rs.2.val + 11) % 32, by omega⟩ : Fin 32))).card

/-- Candidate used to probe the difference between global union support
    and support for a single fixed key. -/
def candidate72Key : Word := 0x06120010#32

/-- Stronger optional kernel-checkable result about ONE PARTICULAR key.
    It does not assert the universal 72 upper bound over all keys. -/
theorem candidate72Key_has_72_cells :
    (fastPositiveCells candidate72Key).card = 72 := by
  decide +kernel

/-- The actual RFC DDT has exactly 72 positive one-hot entries at this key. -/
theorem real_candidate72Key_has_72_cells :
    ((Finset.univ : Finset (Fin 32 × Fin 32)).filter
      (fun p : Fin 32 × Fin 32 => 0 < xorDDT_g candidate72Key
        (BitVec.ofNat 32 (2 ^ p.1.val))
        (BitVec.ofNat 32 (2 ^ p.2.val)))).card = 72 := by
  rw [← fastPositiveCells_eq_real candidate72Key]
  exact candidate72Key_has_72_cells

/-! A small *symbolic* ceiling calculation. It is deliberately separate
from `fastOneHotDDT_correct`: the remaining bridge must prove that every
real positive cell is counted by the appropriate local-potential mask. -/

/-- A necessary local witness at one fixed key digit. If the lower-key
    prefix is zero, incoming carry 1 is impossible. -/
def localPotential (i : Fin 8) (q : Fin 16) (allowCarryOne : Bool)
    (r s : Fin 4) : Bool :=
  (List.finRange 16).any (fun x =>
    (List.finRange 2).any (fun c =>
      if c = (0 : Fin 2) ∨ (allowCarryOne = true ∧ c = 1) then
        let step := sboxCarryStep i q (Fin.ofNat 16 (2 ^ r.val)) x (c, c)
        decide (step.1 = Fin.ofNat 16 (2 ^ s.val) ∧
          (i.val = 7 ∨ step.2.1 = step.2.2))
      else false))

/-- Number of locally possible bit pairs for a given key digit and
    incoming-carry regime (only 16 cell checks). -/
def localPotentialCount (i : Fin 8) (q : Fin 16)
    (allowCarryOne : Bool) : Nat :=
  ((Finset.univ : Finset (Fin 4 × Fin 4)).filter
    (fun rs : Fin 4 × Fin 4 => localPotential i q allowCarryOne rs.1 rs.2 = true)).card

private def nibbleCap (i : Fin 8) : Nat :=
  match i.val with
  | 0 => 11
  | 1 => 8
  | 2 => 9
  | 3 => 9
  | 4 => 10
  | 5 => 11
  | 6 => 7
  | _ => 9

/-- The independent local upper bounds with *both* carries allowed.
    The sum over i=1..7 is 63; the first nibble is handled separately. -/
theorem localPotentialCount_le_cap (i : Fin 8) (q : Fin 16) :
    localPotentialCount i q true ≤ nibbleCap i := by
  revert i q
  decide +kernel

/-- The first nibble has incoming carry zero. A nonzero key nibble loses
    at least one of the ten achievable local one-hot cells. -/
theorem firstNibble_local_bound (q : Fin 16) :
    localPotentialCount 0 q false ≤ 10 ∧
    (q ≠ 0 → localPotentialCount 0 q false ≤ 9) := by
  revert q
  decide +kernel

/-- With lower key digit zero, a NONzero second key digit can have
    at most seven locally possible cells (rather than eight). -/
theorem secondNibble_noCarry_nonzero_bound (q : Fin 16) (hq : q ≠ 0) :
    localPotentialCount 1 q false ≤ 7 := by
  revert q
  decide +kernel

/-- With no lower carry, the next two nibble maxima are 8 and 8. -/
theorem secondThird_noCarry_bounds (q₁ q₂ : Fin 16) :
    localPotentialCount 1 q₁ false ≤ 8 ∧
    localPotentialCount 2 q₂ false ≤ 8 := by
  revert q₁ q₂
  decide +kernel

/-- Numeric key-prefix consistency: at the first three nibbles, the
    sum of locally available bit pairs is at most 26, not 27.
    Only nibble 0 can have a 10-cell score, and this determines whether
    carries into nibble 1 and 2 can exist. -/
theorem firstThree_local_ceiling (q₀ q₁ q₂ : Fin 16) :
    localPotentialCount 0 q₀ false +
    localPotentialCount 1 q₁ (decide (q₀ ≠ 0)) +
    localPotentialCount 2 q₂ (decide (q₀ ≠ 0 ∨ q₁ ≠ 0)) ≤ 26 := by
  have hfirst := firstNibble_local_bound q₀
  have hsecondAny := localPotentialCount_le_cap (1 : Fin 8) q₁
  have hthirdAny := localPotentialCount_le_cap (2 : Fin 8) q₂
  have hzero := secondThird_noCarry_bounds q₁ q₂
  have hfirst' : localPotentialCount 0 q₀ false ≤ 10 := hfirst.1
  have hsecondAny' : localPotentialCount 1 q₁ true ≤ 8 := by
    simpa [nibbleCap] using hsecondAny
  have hthirdAny' : localPotentialCount 2 q₂ true ≤ 9 := by
    simpa [nibbleCap] using hthirdAny
  by_cases h₀ : q₀ = 0
  · by_cases h₁ : q₁ = 0
    · have hf₁ : decide (q₀ ≠ 0) = false := by simp [h₀]
      have hf₂ : decide (q₀ ≠ 0 ∨ q₁ ≠ 0) = false := by simp [h₀, h₁]
      rw [hf₁, hf₂]
      omega
    · have hsecond' := secondNibble_noCarry_nonzero_bound q₁ h₁
      have hf₁ : decide (q₀ ≠ 0) = false := by simp [h₀]
      have hf₂ : decide (q₀ ≠ 0 ∨ q₁ ≠ 0) = true := by simp [h₀, h₁]
      rw [hf₁, hf₂]
      omega
  · have hfirst_nonzero := hfirst.2 h₀
    have hf₁ : decide (q₀ ≠ 0) = true := by simp [h₀]
    have hf₂ : decide (q₀ ≠ 0 ∨ q₁ ≠ 0) = true := by simp [h₀]
    rw [hf₁, hf₂]
    omega

/-- The remaining five nibble maxima sum to 46. Consequently the
    exact local-potential model, with prefix-carry consistency, has an
    absolute ceiling of 72 possible bit-pair cells. -/
theorem consistent_local_ceiling_72
    (q₀ q₁ q₂ q₃ q₄ q₅ q₆ q₇ : Fin 16) :
    localPotentialCount 0 q₀ false +
    localPotentialCount 1 q₁ (decide (q₀ ≠ 0)) +
    localPotentialCount 2 q₂ (decide (q₀ ≠ 0 ∨ q₁ ≠ 0)) +
    localPotentialCount 3 q₃ true +
    localPotentialCount 4 q₄ true +
    localPotentialCount 5 q₅ true +
    localPotentialCount 6 q₆ true +
    localPotentialCount 7 q₇ true ≤ 72 := by
  have h012 := firstThree_local_ceiling q₀ q₁ q₂
  have h3 := localPotentialCount_le_cap (3 : Fin 8) q₃
  have h4 := localPotentialCount_le_cap (4 : Fin 8) q₄
  have h5 := localPotentialCount_le_cap (5 : Fin 8) q₅
  have h6 := localPotentialCount_le_cap (6 : Fin 8) q₆
  have h7 := localPotentialCount_le_cap (7 : Fin 8) q₇
  norm_num [nibbleCap] at h3 h4 h5 h6 h7
  omega

end Magma.OneHotFixedKeySupportAudit
