module
import all Init.Data.Range.Basic
public import Magma.NinePlus.Model
public import Magma.Composition.ZeroLeft.ParityCompleteSlice

@[expose] public section

/-!
# A concrete collision between two required uses of ONE Magma key

For input difference 1 the exact g-DDT row depends on key parity.
Output 0x1800 is admitted only for even keys, whereas output 0x2800
is admitted only for odd keys. Both outputs occur for SOME key.
Thus independent one-round keys can satisfy the two requests, but
one repeated subkey cannot. This is a local obstruction ONLY:
it does not claim a 9-round impossible differential.
-/

namespace Magma.NinePlus

open Magma
open Magma.CarryAutomaton
open Magma.MultiRoundDDT
open Magma.ZeroLeftParityCompleteSlice
open Magma.ZeroLeftEightEntries
open Magma.OddUnitInput77

private abbrev Word := V 32

private theorem positive_of_supportAt
    (k d out : Word) (h : SupportAt k d out) :
    0 < xorDDT_g k d out := by
  classical
  obtain ⟨x, hx⟩ := h
  unfold xorDDT_g
  apply Finset.card_pos.mpr
  refine ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
  exact hx

private theorem support_mem_parityRow (k out : Word)
    (h : SupportAt k (1#32) out) :
    out ∈ parityRowSupport k := by
  have hp := positive_of_supportAt k (1#32) out h
  rw [← one_round_unit_support_exact k]
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩

theorem support_1800_only_even (k : Word)
    (h : SupportAt k (1#32) (0x00001800#32)) :
    k.toNat % 2 = 0 := by
  have hm := support_mem_parityRow k (0x00001800#32) h
  by_contra hk
  simp [parityRowSupport, hk] at hm
  have hnot : (0x00001800#32) ∉ oddOutputSupport := by decide +kernel
  exact hnot hm

theorem support_2800_only_odd (k : Word)
    (h : SupportAt k (1#32) (0x00002800#32)) :
    k.toNat % 2 = 1 := by
  have hm := support_mem_parityRow k (0x00002800#32) h
  have hnot : (0x00002800#32) ∉ eightOffsets := by decide +kernel
  have hk : k.toNat % 2 ≠ 0 := by
    intro heven
    simp only [parityRowSupport, heven, ite_true] at hm
    exact hnot hm
  omega

private theorem support_of_positive
    (k d out : Word) (h : 0 < xorDDT_g k d out) :
    SupportAt k d out := by
  classical
  unfold xorDDT_g at h
  obtain ⟨x, hx⟩ := Finset.card_pos.mp h
  exact ⟨x, (Finset.mem_filter.mp hx).2⟩

/-- Both one-round requests really are realizable, with separate
    (even and odd) keys. This is not merely a vacuous UNSAT. -/
theorem independent_keys_can_realize :
    (∃ k : Word, SupportAt k (1#32) (0x00001800#32)) ∧
    (∃ k : Word, SupportAt k (1#32) (0x00002800#32)) := by
  constructor
  · refine ⟨0#32, support_of_positive _ _ _ ?_⟩
    rw [one_round_unit_exact]
    decide +kernel
  · refine ⟨1#32, support_of_positive _ _ _ ?_⟩
    rw [one_round_unit_exact]
    decide +kernel

/-- Two independent keys can realize the requests, but no
    single repeated 32-bit subkey can satisfy both. -/
theorem no_shared_key_for_parity_clash :
    ¬ ∃ k : Word,
      SupportAt k (1#32) (0x00001800#32) ∧
      SupportAt k (1#32) (0x00002800#32) := by
  rintro ⟨k, h1, h2⟩
  have heven := support_1800_only_even k h1
  have hodd := support_2800_only_odd k h2
  omega


/-- A compact shared-subkey parity predicate for TWO genuine Magma
    one-round derivatives with input XOR difference 1.

    The exact possible outputs for even and odd round keys are the
    kernel-certified finite sets eightOffsets and oddOutputSupport.
    This predicate is suitable for cheap necessary-condition checks
    on reused RFC key words in a carry/difference transducer. -/
def PairParityFeasible (e f : Word) : Prop :=
  (e ∈ eightOffsets ∧ f ∈ eightOffsets) ∨
  (e ∈ oddOutputSupport ∧ f ∈ oddOutputSupport)

/-- Every two genuine derivatives using the same key and input
    difference 1 must admit ONE common key parity. This holds for
    arbitrary output differences, not just 0x1800/0x2800. -/
theorem same_key_pair_parity_necessary (k e f : Word)
    (he : SupportAt k (1#32) e)
    (hf : SupportAt k (1#32) f) :
    PairParityFeasible e f := by
  have hme := support_mem_parityRow k e he
  have hmf := support_mem_parityRow k f hf
  unfold PairParityFeasible
  by_cases hk : k.toNat % 2 = 0
  · left
    constructor
    · simpa [parityRowSupport, hk] using hme
    · simpa [parityRowSupport, hk] using hmf
  · right
    constructor
    · simpa [parityRowSupport, hk] using hme
    · simpa [parityRowSupport, hk] using hmf

/-- A forbidden four-word tile in a recurrence around two consecutive
    occurrences of the SAME key. In a difference stream
      d_i = 0x1801, d_(i+1) = 1,
      d_(i+2) = 1, d_(i+3) = 0x2801,
    the two g differences would be 1->0x1800 and 1->0x2800.
    This is an internal-path prohibition, NOT by itself an ID
    at observable 9-round input/output differences. -/
theorem no_adjacent_reused_key_tile (k : Word)
    (hleft : SupportAt k (1#32)
      (Magma.xor (0x00001801#32) (1#32)))
    (hright : SupportAt k (1#32)
      (Magma.xor (1#32) (0x00002801#32))) : False := by
  have heq : Magma.xor (0x00001801#32) (1#32) =
      0x00001800#32 := by decide
  have hfq : Magma.xor (1#32) (0x00002801#32) =
      0x00002800#32 := by decide
  exact no_shared_key_for_parity_clash
    ⟨k, heq ▸ hleft, hfq ▸ hright⟩


/-- Precisely three g-output XOR differences are possible for
    unit input difference 1 under BOTH even and odd round keys.
    This closed 8-by-77 computation uses the exact reference
    supports already proved in the imported Magma library. -/
theorem unit_input_even_odd_overlap_three :
    (eightOffsets.filter (fun x => x ∈ oddOutputSupport)).card = 3 := by
  decide +kernel

/-- The quantitative gain in ordered pairs of locally supported
    output MASKS when two input-1 g derivatives must share one key.
    This counts masks, not DDT probability mass. -/
theorem parity_pair_extra_forbidden_masks :
    (82 * 82 : Nat) - (8 * 8 + 77 * 77 - 3 * 3) = 740 := by
  decide

end Magma.NinePlus
