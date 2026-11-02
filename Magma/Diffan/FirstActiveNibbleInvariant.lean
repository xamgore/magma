module

public import Magma.Diffan.FiveRoundFirstNibbleObstruction
import all Init.Data.Range.Basic

set_option maxRecDepth 2048

@[expose] public section

/-!
# First active nibble, invariant and a uniform five-round obstruction

All theorems quantify over arbitrary Magma round-key words.
No search over 32-bit states or SAT assumptions are used.
-/

namespace Magma.DiffanFirstActiveNibbleInvariant

open Magma
open Magma.CarryAutomaton
open Magma.MultiRoundDDT
open Magma.DiffanFiveRoundCoreDefect
open Magma.DiffanFiveRoundFirstNibbleObstruction
open Magma.OneHotActiveNibbleNecessary
open Magma.OneHotUniversalLowerNibbleZeros

abbrev Word :=
  V 32

/-- The least index of a changed 4-bit digit, expressed as a proposition. -/
def FirstActiveNibbleAt (d : Word) (i : Fin 8) : Prop :=
  (∀ u : Fin 8, u.val < i.val → wordDigits d u = 0) ∧
  wordDigits d i ≠ 0

private theorem prefix_zero_of_lower_digits (d : Word) (i : Fin 8)
    (h : ∀ u : Fin 8, u.val < i.val → wordDigits d u = 0) : d.toNat % 16 ^ i.val = 0 := by
  rw [← digitPrefixValue_wordDigitStream]
  have aux : ∀ n : Nat, n ≤ i.val → digitPrefixValue (wordDigitStream d) n = 0 := by
    intro n
    induction n with
    | zero =>
      intro _; rfl
    | succ n ih =>
      intro hn
      have h8 : n < 8 := by omega
      have hd : wordDigitStream d n = 0 := by
        rw [wordDigitStream_at d (⟨n, h8⟩ : Fin 8)]
        exact h (⟨n, h8⟩ : Fin 8) (by simpa only [Fin.val_mk] using (show n < i.val by omega))
      change digitPrefixValue (wordDigitStream d) n + (wordDigitStream d n).val * 16 ^ n = 0
      rw [ih (by omega), hd]
      simp
  exact aux i.val (le_refl _)

private theorem mod_prefix_of_mod_prefix (d : Word) (i j : Nat) (hij : i ≤ j)
    (h : d.toNat % 16 ^ j = 0) : d.toNat % 16 ^ i = 0 := by
  calc
    d.toNat % 16 ^ i = (d.toNat % 16 ^ j) % 16 ^ i :=
      (Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 16 hij)).symm
    _ = 0 := by
      rw [h]; simp

private theorem nonzero_ddt_of_derivative (k d x b : Word) (h : gDifference k x d = b) :
    xorDDT_g k d b ≠ 0 := by
  classical
  intro hz
  have hempty : ((Finset.univ : Finset Word).filter (fun y => gDifference k y d = b)) = ∅ := by
    apply Finset.card_eq_zero.mp
    exact hz
  have hx : x ∈ ((Finset.univ : Finset Word).filter (fun y => gDifference k y d = b)) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
  rw [hempty] at hx
  simp at hx

/-- THE FIRST TARGET: the exact first active nibble of the output of
    g, after undoing the 11-bit rotation, equals the first active
    nibble of the nonzero input XOR difference. -/
theorem firstActiveNibble_preserved
    (k d x : Word) (i : Fin 8) (h : FirstActiveNibbleAt d i) :
    FirstActiveNibbleAt ((gDifference k x d).rotateRight 11) i := by
  let b : Word := (gDifference k x d).rotateRight 11
  have hn : xorDDT_g k d (gDifference k x d) ≠ 0 :=
    nonzero_ddt_of_derivative k d x _ rfl
  have hp : d.toNat % 16 ^ i.val = 0 :=
    prefix_zero_of_lower_digits d i h.1
  have hlow : ∀ u : Fin 8, u.val < i.val → wordDigits b u = 0 := by
    intro u hu
    by_contra hb
    have hdprefix : d.toNat % 16 ^ (u.val + 1) = 0 :=
      mod_prefix_of_mod_prefix d (u.val + 1) i.val (by omega) hp
    have hz := xorDDT_zero_of_lower_nibble k d b u hdprefix hb
    rw [Magma.Internal.rot11_rotateRight11] at hz
    exact hn hz
  have hactive : wordDigits b i ≠ 0 := by
    intro hb
    have hz := xorDDT_zero_if_first_active_nibble_is_silent
      k d b i h.1 h.2 hb
    rw [Magma.Internal.rot11_rotateRight11] at hz
    exact hn hz
  exact ⟨hlow, hactive⟩

/-- THE SECOND TARGET: an impossible five-round outer differential when
    the input and output have different first active nibble indices.
    This holds for any five independent (ordinary) round keys. -/
theorem fiveRound_zero_of_distinct_firstActiveNibble
    (k₀ k₁ k₂ k₃ k₄ a s : Word) (i j : Fin 8)
    (ha : FirstActiveNibbleAt a i)
    (hs : FirstActiveNibbleAt s j)
    (hij : i ≠ j) :
    xorDDT_rounds 5 (fiveRoundKeys k₀ k₁ k₂ k₃ k₄)
      (a, 0#32) (0#32, s) = 0 := by
  have hsi : s.toNat % 16 ^ j.val = 0 :=
    prefix_zero_of_lower_digits s j hs.1
  have hai : a.toNat % 16 ^ i.val = 0 :=
    prefix_zero_of_lower_digits a i ha.1
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · apply fiveRound_zero_of_input_earlier_nibble
      k₀ k₁ k₂ k₃ k₄ a s i ha.1 ha.2
    exact mod_prefix_of_mod_prefix s (i.val + 1) j.val (by omega) hsi
  · apply fiveRound_zero_of_output_earlier_nibble
      k₀ k₁ k₂ k₃ k₄ a s j hs.1 hs.2
    exact mod_prefix_of_mod_prefix a (j.val + 1) i.val (by omega) hai

end Magma.DiffanFirstActiveNibbleInvariant
