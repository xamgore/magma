module
public import Magma.Diffan.FullScheduleConjugacy
import all Init.Data.Range.Basic

@[expose] public section

/-!
# An ACTUAL 16-round unknown-key palindrome oracle distinguisher

For ALL eight arbitrary genuine RFC 8891 32-bit subkeys,
the 16 ordinary Feistel rounds [0..7,7..0] satisfy

    #{ x : 64-bit | E16(x) = J(x) } = 2^32.

An ideal uniformly random 64-bit permutation instead
has expectation exactly ONE such matching input.

This does NOT apply to the complete native 32-round
encryption, whose early H^2 hides the chosen input
of the reflected suffix. The 32-round macro C=Q16 H^2
does NOT imply 2^32 observable fixed/crossing points.
-/

namespace Magma.DiffanPalindromicOracle

open Magma Magma.Internal Magma.MultiRoundDDT Magma.DiffanFullScheduleConjugacy
private abbrev W := V 32
private abbrev S := FeistelState

/-- A public/input-output condition on the 16-round
palindrome, without observing any intermediate state. -/
theorem E16_matches_swap_iff_H_diagonal
    (keys : Fin 8 → W) (p : S) :
    E16 keys p = J p ↔ (H keys p).1 = (H keys p).2 := by
  have hq : E16 keys p = J p ↔ Q16 keys p = p := by
    constructor
    · intro h
      change J (E16 keys p) = p
      rw [h]
      exact Prod.swap_swap p
    · intro h
      change J (E16 keys p) = p at h
      have hh := congrArg J h
      simpa only [J, Prod.swap_swap] using hh
  rw [hq]
  constructor
  · intro h
    have hh := H_Q16 keys p
    rw [h] at hh
    exact congrArg Prod.fst hh
  · intro h
    apply (HE keys).injective
    rw [HE_apply, H_Q16, HE_apply]
    cases hp : H keys p with
    | mk l r =>
      simp only [hp] at h
      change (r,l) = (l,r)
      subst r
      rfl

/-- Explicit parametrization of ALL observable
crossing matches by a single 32-bit diagonal word.
The inverse map is H^-1(t,t), which is key dependent:
this is NOT an efficient way to generate them
without knowing the key. -/
def E16SwapMatchEquiv (keys : Fin 8 → W) :
    {p : S // E16 keys p = J p} ≃ W where
  toFun := fun p => ((HE keys) p.1).1
  invFun := fun t =>
    ⟨(HE keys).symm (t,t), by
      apply (E16_matches_swap_iff_H_diagonal keys _).mpr
      rw [← HE_apply]
      simp⟩
  left_inv := by
    intro p
    apply Subtype.ext
    let E := HE keys
    have hh : (E p.1).1 = (E p.1).2 := by
      exact (E16_matches_swap_iff_H_diagonal keys _).mp p.2
    have he : ((E p.1).1,(E p.1).1) = E p.1 := by
      cases hp : E p.1 with
      | mk l r =>
        change (l,l) = (l,r)
        have hr : l = r := by simpa only [hp] using hh
        exact Prod.ext rfl hr
    exact (congrArg E.symm he).trans (E.symm_apply_apply p.1)
  right_inv := by
    intro t
    let E := HE keys
    exact congrArg Prod.fst (E.apply_symm_apply (t,t))

/-- The exact, KEY-UNIVERSAL 16-round distinguisher density:
2^32 matching states among the 2^64 possible inputs. -/
theorem E16_has_exactly_two_pow_32_swap_matches
    (keys : Fin 8 → W) :
    Fintype.card {p : S // E16 keys p = J p} = 2 ^ 32 := by
  calc
    Fintype.card {p : S // E16 keys p = J p} =
        Fintype.card W := Fintype.card_congr (E16SwapMatchEquiv keys)
    _ = 2 ^ 32 := by
      change Fintype.card (BitVec 32) = 2 ^ 32
      rw [← FinEnum.card_eq_fintypeCard]
      exact FinEnum.card_bitVec 32

/-- Exact cardinality of the full input block. -/
theorem all_64bit_states_count :
    Fintype.card S = 2 ^ 64 := by
  change Fintype.card (BitVec 32 × BitVec 32) = 2^64
  rw [Fintype.card_prod]
  have hw : Fintype.card (BitVec 32) = 2 ^ 32 := by
    rw [← FinEnum.card_eq_fintypeCard]
    exact FinEnum.card_bitVec 32
  rw [hw]
  norm_num [← pow_add]

end Magma.DiffanPalindromicOracle
