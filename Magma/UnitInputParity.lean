module

public import Magma.CarryAutomaton
import Mathlib.Data.Nat.Bitwise
import all Init.Data.Range.Basic

@[expose] public section

/-!
# Key-parity reduction for the unit-input DDT row

Even modular translations preserve the pairs `{x, x XOR 1}`. The bijection
`x ↦ x + e` therefore proves invariance of the entire row `DDT_g[k](1, d)`
under an even key increment. Every even key has the zero-key row and every
odd key has the unit-key row, for every 32-bit output difference.

This argument uses the RFC modular-addition semantics and symbolic finite
cardinalities. It does not require a classification of either reference row.
-/

namespace Magma.UnitInputParityReduction

open Magma.Internal Magma.GProperties Magma.CarryAutomaton

/-! ### I. Translate the original RFC modular addition into BitVec addition. -/

/-- The project's RFC `modShift` and the standard BitVec addition agree.
    We use the *previously proved* `modShift_toNat_bridge` rather than
    unfolding the ZMod implementation repeatedly. -/
private theorem modShift_eq_word_add (k x : (V 32)) :
    modShift k x = x + k := by
  apply BitVec.eq_of_toNat_eq
  rw [modShift_toNat_bridge, BitVec.toNat_add]
  congr 1

/-- Shifting the key by `e` is the same as shifting the INPUT by `e`.
    This identity holds for every input and any key increment. -/
private theorem g_key_shift (k e x : (V 32)) :
    g (k + e) x = g k (x + e) := by
  simp only [g_as_modShift, modShift_eq_word_add]
  congr 2
  ac_rfl

/-! ### II. Addition of an even offset preserves the XOR-1 pairing. -/

/-- Elementary, universal identity on 32-bit words: even translation
    commutes with flipping the least significant bit.

    The proof uses Nat.xor_one_of_even/odd and linear modular arithmetic;
    no bit-blaster or native proof oracle is required. -/
private theorem xor_one_add_even (x e : (V 32))
    (he : e.toNat % 2 = 0) :
    (x ^^^ 1#32) + e = (x + e) ^^^ 1#32 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_xor]
  change ((x.toNat ^^^ 1) + e.toNat) % (2 ^ 32) =
      ((x.toNat + e.toNat) % (2 ^ 32)) ^^^ 1
  let X : Nat := x.toNat
  let E : Nat := e.toNat
  let N : Nat := 2 ^ 32
  let Y : Nat := (X + E) % N
  have hX : X < N := x.toFin.isLt
  have hE : E < N := e.toFin.isLt
  have hN : N = 4294967296 := by decide
  have hY : Y < N := Nat.mod_lt _ (by omega)
  have hYP : Y % 2 = X % 2 := by
    dsimp [Y, X, E, N]
    omega
  change ((X ^^^ 1) + E) % N = Y ^^^ 1
  by_cases hx : X % 2 = 0
  · have hxe : Even X := Nat.even_iff.mpr hx
    have hye : Even Y := Nat.even_iff.mpr (by omega)
    rw [Nat.xor_one_of_even hxe, Nat.xor_one_of_even hye]
    dsimp [Y, X, E, N] at *
    omega
  · have hxo : Odd X := Nat.odd_iff.mpr (by omega)
    have hyo : Odd Y := Nat.odd_iff.mpr (by omega)
    rw [Nat.xor_one_of_odd hxo, Nat.xor_one_of_odd hyo]
    dsimp [Y, X, E, N] at *
    omega

/-- Pointwise identity relating the entire output-difference functions,
    valid for *arbitrary* nonlinear `g` (we never unfold its S-boxes). -/
private theorem g_difference_even_shift (k e x : (V 32))
    (he : e.toNat % 2 = 0) :
    xor (g (k + e) (xor x (1#32))) (g (k + e) x) =
      xor (g k (xor (x + e) (1#32))) (g k (x + e)) := by
  rw [g_key_shift k e (xor x (1#32)), g_key_shift k e x]
  change xor (g k ((x ^^^ 1#32) + e)) (g k (x + e)) =
    xor (g k ((x + e) ^^^ 1#32)) (g k (x + e))
  rw [xor_one_add_even x e he]

/-! ### III. The exact DDT row is invariant under even key increments. -/

/-- The fundamental key-shift invariance, proved by the bijection
      x |-> x+e
    of the FULL input space. This is a *symbolic cardinal equality*,
    not an actual enumeration over the 2^32 elements. -/
theorem unitInput_DDT_add_even_key
    (k e d : (V 32)) (he : e.toNat % 2 = 0) :
    xorDDT_g (k + e) (1#32) d = xorDDT_g k (1#32) d := by
  classical
  unfold xorDDT_g
  apply Finset.card_bij (fun x _ => x + e)
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rw [← g_difference_even_shift k e x he]
    exact hx
  · intro x _ y _ h
    have hh := congrArg (fun z : (V 32) => z - e) h
    simpa only [BitVec.add_sub_cancel] using hh
  · intro y hy
    refine ⟨y - e, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      have hs : (y - e) + e = y := BitVec.sub_add_cancel y e
      rw [g_difference_even_shift k e (y - e) he, hs]
      exact hy
    · exact BitVec.sub_add_cancel y e

/-- All 2^31 EVEN keys have precisely the same complete DDT row
    at input difference 1 as the zero key. -/
theorem unitInput_DDT_even_key (k d : (V 32))
    (hk : k.toNat % 2 = 0) :
    xorDDT_g k (1#32) d = xorDDT_g (0#32) (1#32) d := by
  simpa only [BitVec.zero_add] using
    (unitInput_DDT_add_even_key (0#32) k d hk)

/-- Subtracting one from any ODD 32-bit key gives an even word.
    Since the key is odd, this subtraction cannot underflow. -/
private theorem odd_key_minus_one_even (k : (V 32))
    (hk : k.toNat % 2 = 1) :
    (k - 1#32).toNat % 2 = 0 := by
  rw [BitVec.toNat_sub]
  have hkn : k.toNat < 2 ^ 32 := k.toFin.isLt
  have h1 : (1#32).toNat = 1 := by decide
  rw [h1]
  omega

/-- All 2^31 ODD keys have precisely the same complete DDT row
    at input difference 1 as the one key. -/
theorem unitInput_DDT_odd_key (k d : (V 32))
    (hk : k.toNat % 2 = 1) :
    xorDDT_g k (1#32) d = xorDDT_g (1#32) (1#32) d := by
  let e : (V 32) := k - 1#32
  have he : e.toNat % 2 = 0 := odd_key_minus_one_even k hk
  have hsum : (1#32) + e = k := by
    change (1#32) + (k - 1#32) = k
    rw [BitVec.add_comm]
    exact BitVec.sub_add_cancel k (1#32)
  simpa only [hsum] using
    (unitInput_DDT_add_even_key (1#32) e d he)

/-- The ENTIRE 2^32-entry output-difference row of `g[k]` is determined
    by just one bit of k. This says far more than the earlier 32-class
    support classification for a *different* DDT orientation. -/
theorem unitInput_DDT_by_key_parity (k d : (V 32)) :
    xorDDT_g k (1#32) d =
      if k.toNat % 2 = 0 then
        xorDDT_g (0#32) (1#32) d
      else
        xorDDT_g (1#32) (1#32) d := by
  by_cases hk : k.toNat % 2 = 0
  · simp only [hk, ite_true]
    exact unitInput_DDT_even_key k d hk
  · have hodd : k.toNat % 2 = 1 := by omega
    simp only [hk, ite_false]
    exact unitInput_DDT_odd_key k d hodd

end Magma.UnitInputParityReduction
