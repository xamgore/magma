module
public import Magma.Diffan.FullScheduleConjugacy
public import Magma.Diffan.FullScheduleXorSymmetries
import all Init.Data.Range.Basic

set_option maxRecDepth 2048
set_option maxHeartbeats 1000000

@[expose] public section

/-!
# Exact signed correlation structure of native 16+16 RFC Magma

Q16_k = H_k^{-1} o J o H_k is a genuine involution
on real 64-bit Feistel states with eight real 32-bit keys.
The normalized full-state Walsh transfer matrix T(Q16)
is similar to the half-swap mask permutation P:
   T(Q16) = T(H) P T(H)^T.
Its diagonal trace is exactly the number of fixed
points of Q16, which is exactly 2^32 for *every* key.

This file proves the fixed-point count on actual 32-bit words;
the standard character orthogonality identity converts this
to the Walsh transfer trace. This is an aggregate over all
2^64 diagonal masks, not an efficiently evaluated individual
full-32-round Walsh coefficient or a key-recovery method.
-/

namespace Magma.DiffanSignedReflection

open Magma Magma.DiffanFullScheduleConjugacy

private abbrev W := V 32
private abbrev S := W × W

/-- The exact full-state fixed-point set of the reflected
sixteen-round involution is in bijection with a SINGLE
32-bit word, uniformly over all actual subkeys. -/
def fixedQ16EquivWord (keys : Fin 8 → W) :
    {p : S // Q16 keys p = p} ≃ W where
  toFun p := (H keys p.1).1
  invFun w := ⟨(HE keys).symm (w,w), by
    apply (HE keys).injective
    change H keys (Q16 keys ((HE keys).symm (w,w))) =
      H keys ((HE keys).symm (w,w))
    rw [H_Q16]
    simp only [← HE_apply, (HE keys).apply_symm_apply]
    rfl⟩
  left_inv := by
    intro p
    apply Subtype.ext
    apply (HE keys).injective
    change H keys ((HE keys).symm
      ((H keys p.1).1,(H keys p.1).1)) = H keys p.1
    rw [← HE_apply, (HE keys).apply_symm_apply]
    have hp := H_Q16 keys p.1
    rw [p.2] at hp
    rcases h : H keys p.1 with ⟨l,r⟩
    simp only [h] at hp ⊢
    change (l,l)=(l,r)
    have hr : l=r := congrArg Prod.fst hp
    rw [hr]
  right_inv := by
    intro w
    change (H keys ((HE keys).symm (w,w))).1 = w
    rw [← HE_apply, (HE keys).apply_symm_apply]

theorem fixedQ16_card (keys : Fin 8 → W) :
    Fintype.card {p : S // Q16 keys p = p} = 2^32 := by
  calc
    Fintype.card {p : S // Q16 keys p = p} =
        Fintype.card W :=
      Fintype.card_congr (fixedQ16EquivWord keys)
    _ = 2^32 := by
      change Fintype.card (BitVec 32) = 2 ^ 32
      rw [← FinEnum.card_eq_fintypeCard]
      exact FinEnum.card_bitVec 32

end Magma.DiffanSignedReflection
