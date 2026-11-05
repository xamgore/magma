module

import all Init.Data.Range.Basic
public import Magma.Differential.Windows.FeistelCorrectionObstructions
import Std.Tactic.BVDecide

@[expose] public section

/-!
# No constant XOR correction in direction 0x00006000, at any round key

The previously certified zero-key counterexample is actually uniform in the
32-bit round key. The obstruction is local to Pi_3, the nibble substitution
occupying bits 12..15 *before* the RFC 8891 rotation.

For every k compare the derivatives at 0 and 0x1000 in direction 0x6000.
Their Pi_3 output differences depend only on q = nibble_3(k):

  Pi_3(q + 6) XOR Pi_3(q),
  Pi_3(q + 7) XOR Pi_3(q + 1),

where the additions are modulo 16. These differ for all 16 values of q.

This is an obstruction to *pointwise* uniform transport of state differences,
not an obstruction to the previously proved *marginal DDT* symmetries.
-/

namespace Magma.DifanAllKeyFeistelCorrection

open Magma Magma.Internal Magma.GProperties
open Magma.DifanFeistelDeltaPropagation

private abbrev Word :=
  V 32

private abbrev RoundState :=
  Word × Word

private abbrev Point :=
  Difan.StateDifference RoundState RoundState

private def obs (b : Word) : V 4 :=
  nibble (b.rotateRight 11) (3 : Fin 8)

/-- A four-bit observation of the unrotated output respects XOR. -/
private theorem obs_xor (a b : Word) :
    obs (a ^^^ b) = obs a ^^^ obs b := by
  unfold obs
  change
    BitVec.extractLsb' 12 4 ((a ^^^ b).rotateRight 11) =
      BitVec.extractLsb' 12 4 (a.rotateRight 11) ^^^
        BitVec.extractLsb' 12 4 (b.rotateRight 11)
  bv_decide

/-- The modular key translation agrees with 32-bit addition. -/
private theorem modShift_eq_add (k x : Word) :
    modShift k x = x + k := by
  apply BitVec.eq_of_toNat_eq
  rw [Magma.CarryAutomaton.modShift_toNat_bridge, BitVec.toNat_add]
  simp only [show (16 : Nat) ^ 8 = 2 ^ 32 from by decide]

private theorem rotate_cancel (z : Word) : (rot11 z).rotateRight 11 = z := by
  change (z.rotateLeft 11).rotateRight 11 = z
  bv_decide

/-- The chosen observation of g is precisely the third S-box output
    of the modularly translated 32-bit input. -/
private theorem obs_g (k x : Word) :
    obs (g k x) = π (3 : Fin 8) (nibble (x + k) (3 : Fin 8)) := by
  rw [g_as_modShift, modShift_eq_add]
  change nibble ((rot11 (t (x + k))).rotateRight 11) (3 : Fin 8) = _
  rw [rotate_cancel]
  exact t_substitutes_components (x + k) (3 : Fin 8)

/-! Bits 0..11 of the four constants are zero, so adding them to a key
    creates no carry into nibble 3 from the lower bits. -/

private theorem nibble3_add0 (k : Word) :
    nibble ((0#32) + k) (3 : Fin 8) = nibble k (3 : Fin 8) + (0#4) := by
  change BitVec.extractLsb' 12 4 ((0#32) + k) = BitVec.extractLsb' 12 4 k + (0#4)
  bv_decide

private theorem nibble3_add1 (k : Word) :
    nibble ((0x00001000#32) + k) (3 : Fin 8) = nibble k (3 : Fin 8) + (1#4) := by
  change BitVec.extractLsb' 12 4 ((0x00001000#32) + k) = BitVec.extractLsb' 12 4 k + (1#4)
  bv_decide

private theorem nibble3_add6 (k : Word) :
    nibble ((0x00006000#32) + k) (3 : Fin 8) = nibble k (3 : Fin 8) + (6#4) := by
  change BitVec.extractLsb' 12 4 ((0x00006000#32) + k) = BitVec.extractLsb' 12 4 k + (6#4)
  bv_decide

private theorem nibble3_add7 (k : Word) :
    nibble ((0x00007000#32) + k) (3 : Fin 8) = nibble k (3 : Fin 8) + (7#4) := by
  change BitVec.extractLsb' 12 4 ((0x00007000#32) + k) = BitVec.extractLsb' 12 4 k + (7#4)
  bv_decide

/-- The sole cryptographic finite certificate: 16 values of Pi_3.
    Neither the high key bits nor carries to higher nibbles matter. -/
private theorem pi3_separates :
    ∀ q : V 4,
      (π (3 : Fin 8) (q + (6#4)) ^^^ π (3 : Fin 8) q) ≠
        (π (3 : Fin 8) (q + (7#4)) ^^^
          π (3 : Fin 8) (q + (1#4))) := by
  decide +kernel

/-- Two explicit, key-independent base points yield distinct
    XOR derivatives in direction 0x6000 for every 32-bit key. -/
theorem shift6000_two_witnesses (k : Word) :
    (g k (0x00006000#32) ^^^ g k (0#32)) ≠
      (g k (0x00007000#32) ^^^ g k (0x00001000#32)) := by
  intro h
  have ho := congrArg obs h
  simp only [obs_xor, obs_g, nibble3_add6, nibble3_add0,
    nibble3_add7, nibble3_add1, BitVec.add_zero] at ho
  exact pi3_separates (nibble k (3 : Fin 8)) ho

private def mid0 : Point :=
  ⟨(0#32, 0#32), (0#32, 0#32)⟩

private def mid1000 : Point :=
  ⟨(0#32, 0x00001000#32), (0#32, 0#32)⟩

/-- The same two witnesses are genuine choices of the full midpoint
    state/difference, not merely abstract differences. -/
theorem second_correction_witnesses_distinct (k : Word) :
    secondCorrection k (0x00006000#32) mid0 ≠
      secondCorrection k (0x00006000#32) mid1000 := by
  have hx : (0x00001000#32 : Word) ^^^ (0x00006000#32) =
      (0x00007000#32 : Word) := by decide
  simpa only [secondCorrection, mid0, mid1000,
    BitVec.zero_xor, BitVec.xor_zero, hx] using shift6000_two_witnesses k

/-- Every round key fails the constant-correction criterion. -/
theorem shift6000_correction_not_uniform (k u : Word) :
    ¬ (∀ mid : Point, secondCorrection k (0x00006000#32) mid = u) := by
  intro h
  exact second_correction_witnesses_distinct k
    ((h mid0).trans (h mid1000).symm)

/-- Equivalently, no g[k] has a constant XOR derivative in this direction,
    regardless of the high bits or parity of the key. -/
theorem shift6000_derivative_nonconstant (k u : Word) :
    ¬ (∀ x : Word,
      g k (x ^^^ (0x00006000#32)) ^^^ g k x = u) := by
  intro h
  exact shift6000_correction_not_uniform k u
    ((correction_uniform_iff_g_constant_derivative
      k (0x00006000#32) u).mpr h)

/-- The two explicit midpoint choices witness nonuniformity directly. -/
theorem shift6000_correction_has_distinct_values (k : Word) :
    ∃ p q : Point,
      secondCorrection k (0x00006000#32) p ≠
        secondCorrection k (0x00006000#32) q :=
  ⟨mid0, mid1000, second_correction_witnesses_distinct k⟩

end Magma.DifanAllKeyFeistelCorrection
