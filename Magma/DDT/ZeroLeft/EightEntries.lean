module

public import Magma.DDT.ZeroLeft.ColumnTransport
public import Magma.DDT.OneHot.Coefficients.ExactCoefficientMasks
import all Init.Data.Range.Basic

@[expose] public section

/-!
# Eight exact entries in zero-left columns with arbitrary second key

For first round key zero and right input difference one, the first-round
DDT row has exactly eight positive entries, each equal to `2^29`.
Recover this row from the complete 64-pair zero-key slice using a fixed
anchor column and cancellation of its nonzero second-round factor.

For arbitrary second and third keys, every nonempty zero-left column
is an XOR translation of these eight offsets. All eight entries have
value `2^29 * DDT_g[k₁](bR, 1)`. At one-bit right output differences in
positions 20 through 23, the common value has an exact affine key formula.
-/

namespace Magma.ZeroLeftEightEntries

open Magma.Internal Magma.CarryAutomaton Magma.MultiRoundDDT
open Magma.ZeroLeftSupport
open Magma.ZeroLeft64Completeness
open Magma.ZeroLeftColumnTransport
open Magma.OneHotExactCoefficientMasks
open Magma.OneHotKeyClasses

/-- A convenient value of the right output difference: bit 23. -/
private def anchorBR : (V 32) := 0x00800000#32

/-- The eight genuine possible output differences of g[0] for input XOR
    difference 1. The literals are precisely u * 2^11 for
    u in {2,3,4,6,8,10,14,15}. -/
def eightOffsets : Finset (V 32) :=
  {0x00001000#32, 0x00001800#32,
   0x00002000#32, 0x00003000#32,
   0x00004000#32, 0x00005000#32,
   0x00007000#32, 0x00007800#32}

/-- Construct the same eight offsets from the previously verified complete
    64-pair three-round support, restricted to the anchor column. -/
def offsetsFrom64 : Finset (V 32) :=
  ((predictedPairs.toFinset).filter (fun p => p.2 = anchorBR)).image
    (fun p => xor anchorBR p.1)

private theorem xor_anchor_twice (d : (V 32)) : xor anchorBR (xor anchorBR d) = d := by
  change anchorBR ^^^ (anchorBR ^^^ d) = d
  rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

/-- A purely structural change of indices: filtering a 64-pair list at a
    fixed right component and XOR-translating the left component. -/
theorem mem_offsetsFrom64_iff (d : (V 32)) :
    d ∈ offsetsFrom64 ↔
      (xor anchorBR d, anchorBR) ∈ predictedPairs := by
  classical
  constructor
  · intro hd
    obtain ⟨p, hp, hpd⟩ := Finset.mem_image.mp hd
    obtain ⟨hpList, hpRight⟩ := Finset.mem_filter.mp hp
    have hpLeft : p.1 = xor anchorBR d := by
      calc
        p.1 = xor anchorBR (xor anchorBR p.1) :=
          (xor_anchor_twice p.1).symm
        _ = xor anchorBR d := by rw [hpd]
    have hpPair : p = (xor anchorBR d, anchorBR) := by
      cases p with
      | mk a b => exact Prod.ext hpLeft hpRight
    rw [hpPair] at hpList
    exact List.mem_toFinset.mp hpList
  · intro hd
    apply Finset.mem_image.mpr
    refine ⟨(xor anchorBR d, anchorBR), ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      exact ⟨List.mem_toFinset.mpr hd, rfl⟩
    · exact xor_anchor_twice d

/-- Small closed computation over eight-by-eight known pairs, not words. -/
theorem offsetsFrom64_eq_eight : offsetsFrom64 = eightOffsets := by
  decide +kernel

/-- There are exactly eight offsets; all concrete words are distinct. -/
theorem eightOffsets_card : eightOffsets.card = 8 := by
  decide

/-- The anchor second-round g-DDT count, proved from the general affine
    key formula (not evaluated from a 2^32-input Finset). -/
theorem anchor_second_factor :
    xorDDT_g (0#32) anchorBR (1#32) = 2 ^ 29 := by
  have hb : anchorBR =
      BitVec.ofNat 32 (2 ^ (20 + (3 : Fin 4).val)) := by decide
  rw [hb, oneHot_g_DDT_exact_mask]
  decide

/-- Reconstruct an entire 32-bit DDT row using the previously complete
    64-pair theorem, the Feistel product, and the known nonzero factor.
    No fresh S-box-locality argument or huge enumeration is necessary. -/
theorem zeroKey_first_row_exact (d : (V 32)) :
    xorDDT_g (0#32) (1#32) d =
      if d ∈ eightOffsets then 2 ^ 29 else 0 := by
  have h := zeroLeftSlice_exact_iff_listed
    (0#32) (xor anchorBR d) anchorBR
  rw [xorDDT_rounds_three_zero_left_factorization,
      xor_anchor_twice, anchor_second_factor] at h
  by_cases hd : d ∈ eightOffsets
  · have hp : (xor anchorBR d, anchorBR) ∈ predictedPairs := by
      apply (mem_offsetsFrom64_iff d).mp
      rw [offsetsFrom64_eq_eight]
      exact hd
    simp only [hp, ite_true] at h
    simp only [hd, ite_true]
    norm_num at h
    omega
  · have hp : (xor anchorBR d, anchorBR) ∉ predictedPairs := by
      intro hp
      apply hd
      rw [← offsetsFrom64_eq_eight]
      exact (mem_offsetsFrom64_iff d).mpr hp
    simp only [hp, ite_false] at h
    simp only [hd, ite_false]
    norm_num at h
    omega

/-- The exact first-round positive support is the same explicit set E. -/
theorem firstRoundSupport_zero_one :
    firstRoundSupport (0#32) (1#32) = eightOffsets := by
  classical
  ext d
  simp only [firstRoundSupport, Finset.mem_filter,
    Finset.mem_univ, true_and]
  rw [zeroKey_first_row_exact]
  by_cases hd : d ∈ eightOffsets <;> simp [hd]

/-- Main theorem: ALL individual coefficients of an arbitrary-key
    three-round column are either zero or the same scalar. -/
theorem zeroLeft_column_exact_eight
    (k₁ k₂ bR aL : (V 32)) :
    xorDDT_rounds 3 (threeRoundKeys (0#32) k₁ k₂)
        (aL, 1#32) (0#32, bR) =
      if xor bR aL ∈ eightOffsets then
        2 ^ 29 * xorDDT_g k₁ bR (1#32)
      else 0 := by
  rw [xorDDT_rounds_three_zero_left_factorization,
      zeroKey_first_row_exact]
  split_ifs <;> simp

/-- Individual coefficient is positive exactly when the first-round
    XOR offset is allowed AND the second-round DDT factor is positive. -/
theorem zeroLeft_column_positive_iff
    (k₁ k₂ bR aL : (V 32)) :
    0 < xorDDT_rounds 3 (threeRoundKeys (0#32) k₁ k₂)
        (aL, 1#32) (0#32, bR) ↔
      xor bR aL ∈ eightOffsets ∧
        0 < xorDDT_g k₁ bR (1#32) := by
  rw [zeroLeft_column_exact_eight]
  by_cases hd : xor bR aL ∈ eightOffsets
  · simp only [hd, ite_true, true_and]
    constructor
    · intro hp
      exact Nat.pos_of_mul_pos_left hp
    · intro hp
      exact Nat.mul_pos (by norm_num) hp
  · simp [hd]

/-- Every nonempty column is exactly an XOR-translate of E. -/
theorem zeroLeft_column_support_exact
    (k₁ k₂ bR : (V 32))
    (hC : 0 < xorDDT_g k₁ bR (1#32)) :
    leftColumnSupport (0#32) k₁ k₂ (1#32) bR =
      eightOffsets.image (fun d => xor bR d) := by
  rw [leftColumnSupport_eq_image_of_pos
    (0#32) k₁ k₂ (1#32) bR hC,
    firstRoundSupport_zero_one]

/-- The NUMBER of nonzero coefficients in such a column is exactly 8,
    for every k1,k2,bR with a nonzero second-round factor. -/
theorem zeroLeft_column_eight_nonzero
    (k₁ k₂ bR : (V 32))
    (hC : 0 < xorDDT_g k₁ bR (1#32)) :
    (leftColumnSupport (0#32) k₁ k₂ (1#32) bR).card = 8 := by
  rw [leftColumnSupport_card_of_pos
    (0#32) k₁ k₂ (1#32) bR hC,
    firstRoundSupport_zero_one]
  exact eightOffsets_card

/-- With a zero second factor the full column vanishes (not merely the
    sum or its support). -/
theorem zeroLeft_column_all_zero
    (k₁ k₂ bR : (V 32))
    (hC : xorDDT_g k₁ bR (1#32) = 0) :
    ∀ aL : (V 32),
      xorDDT_rounds 3 (threeRoundKeys (0#32) k₁ k₂)
        (aL, 1#32) (0#32, bR) = 0 := by
  intro aL
  rw [zeroLeft_column_exact_eight, hC]
  split_ifs <;> simp

/-- For one-hot right output bR = 2^(20+r), we additionally have the
    CLOSED affine value of every nonzero three-round coefficient.
    Only the second key matters: K = its low 20 bits, q = its nibble 5. -/
theorem zeroLeft_oneHot_exact_affine
    (k₁ k₂ aL : (V 32)) (r : Fin 4) :
    xorDDT_rounds 3 (threeRoundKeys (0#32) k₁ k₂)
      (aL, 1#32)
      (0#32, BitVec.ofNat 32 (2 ^ (20 + r.val))) =
    if xor (BitVec.ofNat 32 (2 ^ (20 + r.val))) aL ∈ eightOffsets then
      2 ^ 38 *
        ((2 ^ 20 - k₁.toNat % (2 ^ 20)) *
            coefficientBit (keyNibble5 k₁) r +
          (k₁.toNat % (2 ^ 20)) *
            coefficientBit (nextNibble (keyNibble5 k₁)) r)
    else 0 := by
  rw [zeroLeft_column_exact_eight, oneHot_g_DDT_exact_mask]
  split_ifs <;> norm_num [← Nat.mul_assoc]

/-- Every positive entry in the same column has identical value. -/
theorem zeroLeft_equal_positive_entries
    (k₁ k₂ bR aL aL' : (V 32))
    (h : 0 < xorDDT_rounds 3 (threeRoundKeys (0#32) k₁ k₂)
      (aL, 1#32) (0#32, bR))
    (h' : 0 < xorDDT_rounds 3 (threeRoundKeys (0#32) k₁ k₂)
      (aL', 1#32) (0#32, bR)) :
    xorDDT_rounds 3 (threeRoundKeys (0#32) k₁ k₂)
      (aL, 1#32) (0#32, bR) =
    xorDDT_rounds 3 (threeRoundKeys (0#32) k₁ k₂)
      (aL', 1#32) (0#32, bR) := by
  have he := (zeroLeft_column_positive_iff k₁ k₂ bR aL).mp h
  have he' := (zeroLeft_column_positive_iff k₁ k₂ bR aL').mp h'
  rw [zeroLeft_column_exact_eight, zeroLeft_column_exact_eight]
  simp [he.1, he'.1]

end Magma.ZeroLeftEightEntries
