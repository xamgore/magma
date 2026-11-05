module

import all Init.Data.Range.Basic
public import Magma.Differential.FiveRounds.FiveRoundCoreDefect

@[expose] public section

/-!
# Universal local support obstruction for five Magma rounds

The three inner round functions may choose their keys and base points
independently. If even this enlarged family of local differential
constraints has no common middle difference, the true coupled
five-round Feistel differential is impossible.
-/

namespace Magma.DiffanFiveRoundUniversalSupport

open Magma
open Magma.MultiRoundDDT
open Magma.DiffanFiveRoundCoreDefect

private abbrev Word :=
  V 32

/-- One ordinary Magma round-function differential is feasible for some
    32-bit key and some base word. Different uses of this predicate may
    choose different keys and bases. -/
def anyKeyGSupport (d out : Word) : Prop :=
  ∃ k x : Word, gDifference k x d = out

/-- Even allowing all three inner keys and base words to be chosen
    separately, a true five-round path needs a common middle word. -/
theorem fiveRound_zero_of_no_anyKey_joint_support
    (k₀ k₁ k₂ k₃ k₄ a s : Word)
    (hno : ∀ c : Word,
      ¬ (anyKeyGSupport a c ∧
         anyKeyGSupport c (xor s a) ∧
         anyKeyGSupport s c)) :
    xorDDT_rounds 5 (fiveRoundKeys k₀ k₁ k₂ k₃ k₄)
      (a, 0#32) (0#32, s) = 0 := by
  rw [fiveRound_eq_threeCore, xorDDT_rounds_three]
  classical
  unfold threeRoundCoupledCount
  have hn : ∀ p : FeistelState,
      ¬ threeRoundCoupled k₁ k₂ k₃
        (0#32) a s (0#32) p.1 p.2 := by
    rintro ⟨R, Z⟩ hc
    let c : Word := gDifference k₁ R a
    have hfirst : anyKeyGSupport a c := ⟨k₁, R, rfl⟩
    have hm : gDifference k₂ Z c = xor s a := by
      have h := hc.1
      change (gDifference k₂ Z (c ^^^ (0#32))) ^^^ a = s at h
      simp only [BitVec.xor_zero] at h
      have hh := congrArg (fun v : Word => v ^^^ a) h
      change (gDifference k₂ Z c ^^^ a) ^^^ a = s ^^^ a at hh
      change gDifference k₂ Z c = s ^^^ a
      simpa only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero] using hh
    have hmiddle : anyKeyGSupport c (xor s a) := ⟨k₂, Z, hm⟩
    have hlast : gDifference k₃ (xor (g k₂ Z) R) s = c := by
      have h := hc.2
      change gDifference k₃ (xor (g k₂ Z) R) s =
        (0#32) ^^^ (c ^^^ (0#32)) at h
      simpa only [BitVec.zero_xor, BitVec.xor_zero] using h
    have hthird : anyKeyGSupport s c :=
      ⟨k₃, xor (g k₂ Z) R, hlast⟩
    exact hno c ⟨hfirst, hmiddle, hthird⟩
  simp [hn]

/-- The chosen active bit, with indices counted from the least significant bit. -/
def oneHotDifference (i : Fin 32) : Word :=
  BitVec.ofNat 32 (2 ^ i.val)

/-- A finite family of key-independent local-support obligations.
    Unlike the final theorem, this predicate mentions no five-round
    master key, and the three one-round keys may be chosen separately. -/
def AllOneHotJointSupportEmpty : Prop :=
  ∀ i j : Fin 32, ∀ c : Word,
    ¬ (anyKeyGSupport (oneHotDifference i) c ∧
       anyKeyGSupport c (xor (oneHotDifference j) (oneHotDifference i)) ∧
       anyKeyGSupport (oneHotDifference j) c)

/-- A certificate for all key-free one-hot support obligations suffices
    for the complete key-uniform one-hot five-round impossibility claim. -/
theorem universal_oneHot_fiveRound_zero_of_jointSupportEmpty
    (hcert : AllOneHotJointSupportEmpty)
    (k₀ k₁ k₂ k₃ k₄ : Word) (i j : Fin 32) :
    xorDDT_rounds 5 (fiveRoundKeys k₀ k₁ k₂ k₃ k₄)
      (oneHotDifference i, 0#32)
      (0#32, oneHotDifference j) = 0 := by
  exact fiveRound_zero_of_no_anyKey_joint_support
    k₀ k₁ k₂ k₃ k₄ (oneHotDifference i) (oneHotDifference j)
    (hcert i j)

end Magma.DiffanFiveRoundUniversalSupport
