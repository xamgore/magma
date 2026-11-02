module

public import Magma.Diffan.FiveRoundCoreDefect
public import Magma.DDT.OneHot.Support.ActiveNibbleNecessary
public import Magma.DDT.OneHot.Mechanics.UniversalLowerNibbleZeros
import all Init.Data.Range.Basic

set_option maxRecDepth 2048
set_option linter.constructorNameAsVariable false

@[expose] public section

/-!
# A structural five-round obstruction from the first active nibble

No assumptions on the actual S-box tables beyond the existing bijectivity
lemmas. The lemma applies to any five fixed ordinary Feistel round keys.
-/

namespace Magma.DiffanFiveRoundFirstNibbleObstruction

open Magma
open Magma.CarryAutomaton
open Magma.MultiRoundDDT
open Magma.DiffanFiveRoundCoreDefect
open Magma.OneHotActiveNibbleNecessary
open Magma.OneHotUniversalLowerNibbleZeros

abbrev Word :=
  V 32

private theorem ddt_nonzero_of_derivative (k d x b : Word) (h : gDifference k x d = b) :
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

/-- If d has its first active nibble at i but e has the entire prefix
    through i inactive, the two derivatives cannot share one output.
    Everything is uniform over the two keys and the two base points. -/
theorem no_common_difference_of_earlier_nibble
    (k l d e x y : Word) (i : Fin 8)
    (hdlow : ∀ u : Fin 8, u.val < i.val → wordDigits d u = 0)
    (hdactive : wordDigits d i ≠ 0)
    (heprefix : e.toNat % 16 ^ (i.val + 1) = 0) :
    gDifference k x d ≠ gDifference l y e := by
  intro h
  let b : Word := gDifference k x d
  have hk : xorDDT_g k d b ≠ 0 :=
    ddt_nonzero_of_derivative k d x b rfl
  have hl : xorDDT_g l e b ≠ 0 :=
    ddt_nonzero_of_derivative l e y b h.symm
  by_cases hb : wordDigits (b.rotateRight 11) i = 0
  · have hz := xorDDT_zero_if_first_active_nibble_is_silent
      k d (b.rotateRight 11) i hdlow hdactive hb
    rw [Magma.Internal.rot11_rotateRight11] at hz
    exact hk hz
  · have hz := xorDDT_zero_of_lower_nibble
      l e (b.rotateRight 11) i heprefix hb
    rw [Magma.Internal.rot11_rotateRight11] at hz
    exact hl hz

/-- A three-round core has no witnesses when the first and last
    derivatives cannot agree on any shared intermediate output. -/
private theorem threeRound_zero_of_disjoint_outer_derivatives
    (k₁ k₂ k₃ a s : Word)
    (h : ∀ R Z : Word,
      gDifference k₃ (xor (g k₂ Z) R) s ≠ gDifference k₁ R a) :
    threeRoundCoupledCount k₁ k₂ k₃ (0#32) a s (0#32) = 0 := by
  classical
  unfold threeRoundCoupledCount
  have hn : ∀ p : FeistelState,
      ¬ threeRoundCoupled k₁ k₂ k₃ (0#32) a s (0#32) p.1 p.2 := by
    rintro ⟨R, Z⟩ hc
    have hh := hc.2
    change gDifference k₃ (xor (g k₂ Z) R) s =
      xor (0#32) (xor (gDifference k₁ R a) (0#32)) at hh
    change gDifference k₃ (xor (g k₂ Z) R) s =
      (0#32) ^^^ ((gDifference k₁ R a) ^^^ (0#32)) at hh
    simp only [BitVec.zero_xor, BitVec.xor_zero] at hh
    exact h R Z hh
  simp [hn]

/-- Five ordinary rounds: if a has its first active nibble at i,
    whereas s has no active nibble through i, the sparse outer transition
    (a,0) -> (0,s) has zero fixed-key DDT. -/
theorem fiveRound_zero_of_input_earlier_nibble
    (k₀ k₁ k₂ k₃ k₄ a s : Word) (i : Fin 8)
    (halow : ∀ u : Fin 8, u.val < i.val → wordDigits a u = 0)
    (haactive : wordDigits a i ≠ 0)
    (hsprefix : s.toNat % 16 ^ (i.val + 1) = 0) :
    xorDDT_rounds 5 (fiveRoundKeys k₀ k₁ k₂ k₃ k₄)
      (a, 0#32) (0#32, s) = 0 := by
  rw [fiveRound_eq_threeCore, xorDDT_rounds_three]
  apply threeRound_zero_of_disjoint_outer_derivatives
  intro R Z
  exact (no_common_difference_of_earlier_nibble
    k₁ k₃ a s R (xor (g k₂ Z) R) i halow haactive hsprefix).symm

/-- Same exclusion when the output has the earlier active nibble. -/
theorem fiveRound_zero_of_output_earlier_nibble
    (k₀ k₁ k₂ k₃ k₄ a s : Word) (i : Fin 8)
    (hslow : ∀ u : Fin 8, u.val < i.val → wordDigits s u = 0)
    (hsactive : wordDigits s i ≠ 0)
    (haprefix : a.toNat % 16 ^ (i.val + 1) = 0) :
    xorDDT_rounds 5 (fiveRoundKeys k₀ k₁ k₂ k₃ k₄)
      (a, 0#32) (0#32, s) = 0 := by
  rw [fiveRound_eq_threeCore, xorDDT_rounds_three]
  apply threeRound_zero_of_disjoint_outer_derivatives
  intro R Z
  exact no_common_difference_of_earlier_nibble
    k₃ k₁ s a (xor (g k₂ Z) R) R i hslow hsactive haprefix

end Magma.DiffanFiveRoundFirstNibbleObstruction
