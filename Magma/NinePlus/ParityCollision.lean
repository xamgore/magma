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

end Magma.NinePlus
