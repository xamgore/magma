module

public import Magma.OneHotExactColumnMass
import all Init.Data.Range.Basic

@[expose] public section

/-!
# Linear prefix multiplicities for one-bit differences

Among the `2^20` low input prefixes, exactly `2^20 - K` produce carry zero
and exactly `K` produce carry one when the low key prefix is `K`.
These fiber counts are proved symbolically using finite intervals.

The active S-box multiplicity counts original nibble transitions with
output difference two and equal outgoing carries. Weighting it by the
prefix counts and the two free high nibbles gives a closed affine formula
for the explicitly factorized counting model.

`OneHotCountFactorization` states the quantitative connection to the original
carry DP. That equality is not proved here: the single-round DDT and
three-round column formulae retain it as an explicit hypothesis.
-/

open scoped BigOperators

namespace Magma.OneHotLinearPrefixMass

open Magma.CarryAutomaton Magma.MultiRoundDDT
open Magma.OneHotKeyClasses
open Magma.OneHotSilentNibbleStructure

private abbrev B : Nat :=
  2 ^ 20

/-! ### I. Both prefix-carry fibers are contiguous Nat intervals. -/

def prefixCarry (K x : Nat) : Nat :=
  (x + K) / B

/-- There is no carry precisely below the threshold `B-K`. -/
theorem prefixCarry_zero_iff (K x : Nat)
    (_hK : K < B) (_hx : x < B) :
    prefixCarry K x = 0 ↔ x < B - K := by
  change (x + K) / 1048576 = 0 ↔ x < 1048576 - K
  omega

/-- Carry one occurs at or above the complementary threshold. -/
theorem prefixCarry_one_iff (K x : Nat)
    (hK : K < B) (hx : x < B) :
    prefixCarry K x = 1 ↔ B - K ≤ x := by
  change K < 1048576 at hK
  change x < 1048576 at hx
  change (x + K) / 1048576 = 1 ↔ 1048576 - K ≤ x
  omega

/-- Exactly `B-K` low prefixes yield carry zero. -/
theorem prefixCarry_zero_count (K : Nat) (hK : K < B) :
    ((Finset.range B).filter (fun x => prefixCarry K x = 0)).card =
      B - K := by
  have heq :
      (Finset.range B).filter (fun x => prefixCarry K x = 0) =
        Finset.range (B - K) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hx, hc⟩
      exact (prefixCarry_zero_iff K x hK hx).mp hc
    · intro hx
      have hxB : x < B := by omega
      exact ⟨hxB, (prefixCarry_zero_iff K x hK hxB).mpr hx⟩
  rw [heq]
  simp

/-- Exactly `K` low prefixes yield carry one. -/
theorem prefixCarry_one_count (K : Nat) (hK : K < B) :
    ((Finset.range B).filter (fun x => prefixCarry K x = 1)).card = K := by
  have heq :
      (Finset.range B).filter (fun x => prefixCarry K x = 1) =
        Finset.Ico (B - K) B := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    constructor
    · rintro ⟨hx, hc⟩
      exact ⟨(prefixCarry_one_iff K x hK hx).mp hc, hx⟩
    · rintro ⟨hlo, hx⟩
      exact ⟨hx, (prefixCarry_one_iff K x hK hx).mpr hlo⟩
  rw [heq]
  simp only [Nat.card_Ico]
  omega

private theorem prefixCarry_ne_zero_iff_one (K x : Nat) (hK : K < B) (hx : x < B) :
    prefixCarry K x ≠ 0 ↔ prefixCarry K x = 1 := by
  change K < 1048576 at hK
  change x < 1048576 at hx
  have hbound : prefixCarry K x < 2 := by
    change (x + K) / 1048576 < 2
    omega
  omega

/-- The two carry fibers are exhaustive over all 20-bit prefixes. -/
theorem prefixCarry_not_zero_count (K : Nat) (hK : K < B) :
    ((Finset.range B).filter (fun x => prefixCarry K x ≠ 0)).card = K := by
  have heq :
      (Finset.range B).filter (fun x => prefixCarry K x ≠ 0) =
        (Finset.range B).filter (fun x => prefixCarry K x = 1) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hx, hn⟩
      exact ⟨hx, (prefixCarry_ne_zero_iff_one K x hK hx).mp hn⟩
    · rintro ⟨hx, h1⟩
      exact ⟨hx, (prefixCarry_ne_zero_iff_one K x hK hx).mpr h1⟩
  rw [heq, prefixCarry_one_count K hK]

/-! ### II. Exact *numeric* count of successful active digit choices. -/

/-- Number (0..16) of genuine input digits in pi_5 that generate target
    difference 2 and leave the two outgoing carries synchronized. -/
def activeMultiplicity (q : Fin 16) (c : Fin 2) (r : Fin 4) : Nat :=
  ((Finset.univ : Finset (Fin 16)).filter fun x =>
    let step := sboxCarryStep 5 q (Fin.ofNat 16 (2 ^ r.val)) x (c, c)
    step.1 = 2 ∧ step.2.1 = step.2.2).card

/-- The quantitative count is positive exactly when the earlier
    independently certified local Boolean test succeeds. -/
theorem activeMultiplicity_pos_iff (q : Fin 16) (c : Fin 2) (r : Fin 4) :
    0 < activeMultiplicity q c r ↔
      localOneHotStepPossible q c r = true := by
  rw [activeMultiplicity, Finset.card_pos, Finset.filter_nonempty_iff]
  simp only [Finset.mem_univ, true_and]
  rw [localOneHotStepPossible_iff_original_step]
  constructor
  · rintro ⟨x, hout, heq⟩
    let st := sboxCarryStep 5 q (Fin.ofNat 16 (2 ^ r.val)) x (c, c)
    refine ⟨x, st.2.1, ?_⟩
    apply Prod.ext
    · exact hout
    · apply Prod.ext
      · rfl
      · exact heq.symm
  · rintro ⟨x, t, hstep⟩
    refine ⟨x, ?_, ?_⟩
    · exact congrArg Prod.fst hstep
    · rw [hstep]

/-! ### III. Exact affine law for the factorized model. -/

/-- Sum of the local active count over every possible twenty-bit prefix.
    The first five digits influence it only through their common carry. -/
def prefixWeightedActiveCount (K : Nat) (q : Fin 16) (r : Fin 4) : Nat :=
  ∑ x ∈ Finset.range B,
    if prefixCarry K x = 0 then activeMultiplicity q 0 r
    else activeMultiplicity q 1 r

/-- A symbolic evaluation of a million-element sum. No term with a
    million constructors is generated or kernel-reduced. -/
theorem prefixWeightedActiveCount_closed (K : Nat) (hK : K < B)
    (q : Fin 16) (r : Fin 4) :
    prefixWeightedActiveCount K q r =
      (B - K) * activeMultiplicity q 0 r +
        K * activeMultiplicity q 1 r := by
  unfold prefixWeightedActiveCount
  rw [Finset.sum_ite]
  simp only [Finset.sum_const, smul_eq_mul]
  rw [prefixCarry_zero_count K hK,
      prefixCarry_not_zero_count K hK]

/-- Exact factorized model including the two free high nibbles (16²). -/
def factorizedOneHotCount (k : V 32) (r : Fin 4) : Nat :=
  2 ^ 8 * prefixWeightedActiveCount (k.toNat % B) (keyNibble5 k) r

/-- The main exact affine identity, for EVERY 32-bit key and r < 4. -/
theorem factorizedOneHotCount_closed (k : V 32) (r : Fin 4) :
    factorizedOneHotCount k r =
      2 ^ 8 *
        ((B - k.toNat % B) * activeMultiplicity (keyNibble5 k) 0 r +
         (k.toNat % B) * activeMultiplicity (keyNibble5 k) 1 r) := by
  unfold factorizedOneHotCount
  have hk : k.toNat % B < B := Nat.mod_lt _ (by norm_num [B])
  rw [prefixWeightedActiveCount_closed _ hk]

/-! ### IV. Small exact examples (never a 32-bit enumeration). -/

/-- The transition 2^20 -> 1 is impossible with incoming carry zero at q=0. -/
theorem local_q0_r0_c0 :
    activeMultiplicity 0 0 0 = 0 := by decide

/-- Incoming carry one admits precisely two active input nibbles. -/
theorem local_q0_r0_c1 :
    activeMultiplicity 0 1 0 = 2 := by decide

/-- Applying the affine formula to the first two nonzero low keys. -/
theorem factorized_key1_bit20 :
    factorizedOneHotCount (1#32) 0 = 512 := by
  rw [factorizedOneHotCount_closed]
  have hq : keyNibble5 (1#32) = (0 : Fin 16) := by decide
  simp only [hq, local_q0_r0_c0, local_q0_r0_c1]
  norm_num [B]

theorem factorized_key2_bit20 : factorizedOneHotCount (2#32) 0 = 1024 := by
  rw [factorizedOneHotCount_closed]
  have hq : keyNibble5 (2#32) = (0 : Fin 16) := by decide
  simp only [hq, local_q0_r0_c0, local_q0_r0_c1]
  norm_num [B]

/-! ### V. Conditional consequences of quantitative factorization

The full-word support theorem establishes positivity, whereas equality of
multiplicities requires a quantitative factorization. The proposition below
states that identity; both DDT consequences take a proof of it as a hypothesis.
-/

open Magma.OneHotExactColumnMass
open Magma.OneHotThreeRoundColumns

/-- Quantitative equality between the original carry DP and the factorized
    prefix/active/suffix count. This proposition is not proved in this module. -/
def OneHotCountFactorization : Prop :=
  ∀ (k : V 32) (r : Fin 4),
    oneHotDPCount k (⟨20 + r.val, by omega⟩ : Fin 32) =
      factorizedOneHotCount k r

/-- The target exact single-round DDT formula, conditional ONLY on the
    explicitly named quantitative bridge. No extra cryptographic premise. -/
theorem oneHot_g_DDT_affine_of_factorization
    (h : OneHotCountFactorization) (k : V 32) (r : Fin 4) :
    xorDDT_g k (BitVec.ofNat 32 (2 ^ (20 + r.val))) (1#32) =
      2 ^ 8 *
        ((B - k.toNat % B) * activeMultiplicity (keyNibble5 k) 0 r +
         (k.toNat % B) * activeMultiplicity (keyNibble5 k) 1 r) := by
  let j : Fin 32 := ⟨20 + r.val, by omega⟩
  change xorDDT_g k (bitOutput j) (1#32) = _
  rw [oneHotDDT_eq_dp, h k r, factorizedOneHotCount_closed]

/-- The corresponding formula for the entire three-round column.
    The outer two keys disappear exactly as in `zeroLeft_row_mass`. -/
theorem oneHot_three_round_column_mass_affine_of_factorization
    (h : OneHotCountFactorization) (k₀ k₁ k₂ : V 32) (r : Fin 4) :
    (∑ aL : V 32,
      xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
        (aL, 1#32) (0#32,
          bitOutput (⟨20 + r.val, by omega⟩ : Fin 32))) =
      2 ^ 32 * (2 ^ 8 *
        ((B - k₁.toNat % B) * activeMultiplicity (keyNibble5 k₁) 0 r +
         (k₁.toNat % B) * activeMultiplicity (keyNibble5 k₁) 1 r)) := by
  rw [oneHot_column_mass_dp, h k₁ r, factorizedOneHotCount_closed]

end Magma.OneHotLinearPrefixMass
