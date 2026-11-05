module
public import Magma.RFC8891
import all Init.Data.Range.Basic

@[expose] public section

/-!
# Genuine Magma g: modular-input XOR-output DDT is key invariant

This file CHANGES the difference function, not the SMT solver's
Sbox encoding. Domain differences are modular ZMod(2^32);
codomain differences remain native 32-bit XOR.

For any fixed secret round-key word k, the actual RFC g is
  g_k(x)=F(x+k mod 2^32), F=ROL11 o RFC-8-Sbox.

Therefore for every modular input difference d,
  g_k(x+d) XOR g_k(x)
  = F((x+k)+d) XOR F(x+k).
Translation x -> x+k is bijective, so all rows of the
modular-input XOR-output DDT of g are independent of k.

The theorem is about *complete marginal* g DDT counts,
not pointwise base-conditioned fibers (which still depend
on k), and NOT the 32-round native Magma DDT.
-/

namespace Magma.DifanMixedDifferenceKeyInvariance

open Magma

private abbrev Z := Z2 32
private abbrev W := V 32

/-- The genuine RFC nonlinear and rotation layers,
without the preceding modular key addition. -/
def core (z : Z) : W := rot11 (t (Vec_s 32 z))

/-- Genuine RFC g viewed in modular word coordinates. -/
def atKey (key x : Z) : W := core (x + key)

theorem native_g_is_atKey (key x : Z) :
    g (Vec_s 32 key) (Vec_s 32 x) = atKey key x := by
  simp only [g, atKey, core, add₃₂, Magma.Internal.Int_s_Vec_s]

/-- True MODULAR input difference, true XOR output
difference, for one genuine 32-bit keyed round function. -/
def modularInputXorOutputDerivative
    (key d x : Z) : W :=
  xor (atKey key (x + d)) (atKey key x)

/-- Exact pointwise translation of the entire modular
differential fiber. No Sbox properties needed:
the secret key simply shifts its base coordinate. -/
theorem modular_derivative_key_is_base_translation
    (key d x : Z) :
    modularInputXorOutputDerivative key d x =
      modularInputXorOutputDerivative 0 d (x + key) := by
  unfold modularInputXorOutputDerivative atKey
  congr 1
  · congr 1
    · exact add_assoc x d key |>.trans
        (by ac_rfl)
  · simp only [add_zero]

/-- Actual native g formula for same modular input
difference: the base is translated by the key. -/
theorem native_g_modular_derivative_translation
    (key d x : Z) :
    xor (g (Vec_s 32 key) (Vec_s 32 (x+d)))
        (g (Vec_s 32 key) (Vec_s 32 x)) =
    modularInputXorOutputDerivative 0 d (x+key) := by
  rw [native_g_is_atKey,native_g_is_atKey]
  exact modular_derivative_key_is_base_translation key d x

/-- NAT count of all 2^32 actual modular-input
differential witnesses. It is NOT the XOR-input DDT. -/
noncomputable def modXorDDT (key d : Z) (out : W) : Nat :=
  Fintype.card {x : Z //
    modularInputXorOutputDerivative key d x = out}

/-- All mod-input / XOR-output DDT coefficients of the
NATIVE real 32-bit Magma g are EXACTLY KEY-INVARIANT.

This is a rigorous negative result for key filtering
by complete marginal DDT counts with this difference.
Base-conditioned fibers can still reveal key information. -/
theorem modXorDDT_all_keys_same
    (key d : Z) (out : W) :
    modXorDDT key d out = modXorDDT 0 d out := by
  unfold modXorDDT
  apply Fintype.card_congr
  exact {
    toFun := fun p =>
      ⟨p.1 + key, by
        rw [← modular_derivative_key_is_base_translation key d p.1]
        exact p.2⟩
    invFun := fun p =>
      ⟨p.1 - key, by
        rw [modular_derivative_key_is_base_translation]
        simpa only [sub_add_cancel] using p.2⟩
    left_inv := by
      intro p
      apply Subtype.ext
      simp only [add_sub_cancel_right]
    right_inv := by
      intro p
      apply Subtype.ext
      exact sub_add_cancel p.1 key
  }

/-- At a FIXED base word x, XOR and modular differences
are bijective coordinate labels of exactly the SAME
pair of inputs. No pairwise key information is
created or destroyed by this relabelling. -/
def modularDifferenceOfXor (x a : W) : W :=
  (x ^^^ a) - x

def xorDifferenceOfModular (x d : W) : W :=
  x ^^^ (x + d)

theorem modularDifferenceOfXor_left_inverse
    (x a : W) :
    xorDifferenceOfModular x (modularDifferenceOfXor x a) = a := by
  unfold xorDifferenceOfModular modularDifferenceOfXor
  have h : x + ((x ^^^ a) - x) = x ^^^ a := by
    calc
      x + ((x ^^^ a) - x) = ((x ^^^ a) - x) + x :=
        BitVec.add_comm _ _
      _ = x ^^^ a := sub_add_cancel _ _
  rw [h]
  simp only [← BitVec.xor_assoc,BitVec.xor_self,BitVec.zero_xor]

theorem xorDifferenceOfModular_left_inverse
    (x d : W) :
    modularDifferenceOfXor x (xorDifferenceOfModular x d) = d := by
  unfold xorDifferenceOfModular modularDifferenceOfXor
  have h : x ^^^ (x ^^^ (x+d)) = x+d := by
    simp only [← BitVec.xor_assoc,BitVec.xor_self,BitVec.zero_xor]
  rw [h]
  exact add_sub_cancel_left x d

/-- Also if the OUTPUT difference is modular, the
full marginal DDT of g remains key-invariant when
the INPUT difference is modular. This stronger
result does not rely on XOR on the output. -/
def modularInputModularOutputDerivative
    (key d x : Z) : Z :=
  Int_s 32 (atKey key (x+d)) - Int_s 32 (atKey key x)

theorem modular_modular_derivative_translation
    (key d x : Z) :
    modularInputModularOutputDerivative key d x =
      modularInputModularOutputDerivative 0 d (x+key) := by
  unfold modularInputModularOutputDerivative atKey
  simp only [add_zero]
  congr 1
  · congr 1
    ac_rfl

noncomputable def modModDDT (key d out : Z) : Nat :=
  Fintype.card {x : Z //
    modularInputModularOutputDerivative key d x = out}

theorem modModDDT_all_keys_same
    (key d out : Z) :
    modModDDT key d out = modModDDT 0 d out := by
  unfold modModDDT
  apply Fintype.card_congr
  exact {
    toFun := fun p =>
      ⟨p.1 + key, by
        rw [← modular_modular_derivative_translation key d p.1]
        exact p.2⟩
    invFun := fun p =>
      ⟨p.1 - key, by
        rw [modular_modular_derivative_translation]
        simpa only [sub_add_cancel] using p.2⟩
    left_inv := by
      intro p
      apply Subtype.ext
      simp only [add_sub_cancel_right]
    right_inv := by
      intro p
      apply Subtype.ext
      exact sub_add_cancel p.1 key
  }

end Magma.DifanMixedDifferenceKeyInvariance
