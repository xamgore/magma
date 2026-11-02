module

import all Init.Data.Range.Basic
public import Magma.Diffan.FiveRoundCoreDefect

@[expose] public section

/-!
# Reversing the five ordinary Magma Feistel rounds

The half-swap conjugates an ordinary round to its inverse.
This gives a base-state correspondence for five-round differences
without assuming anything about S-boxes or independent round keys.
-/

namespace Magma.DiffanFiveRoundDDTReverse

open Magma
open Magma.MultiRoundDDT
open Magma.DiffanFiveRoundCoreDefect

private abbrev Word :=
  V 32

private abbrev State :=
  FeistelState

private def forward (k₀ k₁ k₂ k₃ k₄ : Word) (p : State) : State :=
  G k₄ (G k₃ (G k₂ (G k₁ (G k₀ p))))

private def backward (k₀ k₁ k₂ k₃ k₄ : Word) (p : State) : State :=
  G k₀ (G k₁ (G k₂ (G k₃ (G k₄ p))))

private theorem G_swap_G (k : Word) (p : State) : G k (Prod.swap (G k p)) = Prod.swap p := by
  rcases p with ⟨l, r⟩
  change (r, (g k r ^^^ (g k r ^^^ l))) = (r, l)
  rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

theorem backward_swap_forward (k₀ k₁ k₂ k₃ k₄ : Word) (p : State) :
    backward k₀ k₁ k₂ k₃ k₄ (Prod.swap (forward k₀ k₁ k₂ k₃ k₄ p)) = Prod.swap p := by
  unfold backward forward
  rw [G_swap_G k₄, G_swap_G k₃, G_swap_G k₂, G_swap_G k₁, G_swap_G k₀]

theorem forward_swap_backward (k₀ k₁ k₂ k₃ k₄ : Word) (p : State) :
    forward k₀ k₁ k₂ k₃ k₄ (Prod.swap (backward k₀ k₁ k₂ k₃ k₄ p)) = Prod.swap p := by
  unfold backward forward
  rw [G_swap_G k₀, G_swap_G k₁, G_swap_G k₂, G_swap_G k₃, G_swap_G k₄]

private theorem forward_eq_iterate (k₀ k₁ k₂ k₃ k₄ : Word) (p : State) :
    forward k₀ k₁ k₂ k₃ k₄ p = iterateG 5 (fiveRoundKeys k₀ k₁ k₂ k₃ k₄) p := by rfl

private theorem backward_eq_iterate (k₀ k₁ k₂ k₃ k₄ : Word) (p : State) :
    backward k₀ k₁ k₂ k₃ k₄ p = iterateG 5 (fiveRoundKeys k₄ k₃ k₂ k₁ k₀) p := by rfl

private theorem stateXor_cancel (x y : State) : stateXor y (stateXor x y) = x := by
  rcases x with ⟨xl, xr⟩
  rcases y with ⟨yl, yr⟩
  apply Prod.ext
  · change yl ^^^ (xl ^^^ yl) = xl
    bv_decide
  · change yr ^^^ (xr ^^^ yr) = xr
    bv_decide

private theorem stateXor_reconstruct (x y d : State) (h : stateXor x y = d) : x = stateXor y d :=
  (stateXor_cancel x y).symm.trans (congrArg (stateXor y) h)

/-- Transport an actual forward differential witness through the
    half-swap of its output. No assumption on the round functions is used. -/
theorem reverse_witness
    (k₀ k₁ k₂ k₃ k₄ : Word) (p a b : State)
    (h : stateXor
      (forward k₀ k₁ k₂ k₃ k₄ (stateXor p a))
      (forward k₀ k₁ k₂ k₃ k₄ p) = b) :
    stateXor
      (backward k₀ k₁ k₂ k₃ k₄
        (stateXor (Prod.swap (forward k₀ k₁ k₂ k₃ k₄ p))
          (Prod.swap b)))
      (backward k₀ k₁ k₂ k₃ k₄
        (Prod.swap (forward k₀ k₁ k₂ k₃ k₄ p))) =
      Prod.swap a := by
  have hp := stateXor_reconstruct
    (forward k₀ k₁ k₂ k₃ k₄ (stateXor p a))
    (forward k₀ k₁ k₂ k₃ k₄ p) b h
  have hs :
      stateXor (Prod.swap (forward k₀ k₁ k₂ k₃ k₄ p)) (Prod.swap b) =
        Prod.swap (forward k₀ k₁ k₂ k₃ k₄ (stateXor p a)) := by
    rw [hp]
    rfl
  rw [hs, backward_swap_forward, backward_swap_forward]
  rcases p with ⟨pl, pr⟩
  rcases a with ⟨al, ar⟩
  apply Prod.ext
  · change (pr ^^^ ar) ^^^ pr = ar
    bv_decide
  · change (pl ^^^ al) ^^^ pl = al
    bv_decide

/-- A bijection between concrete forward DDT witnesses and the
    reverse-key, half-swapped DDT witnesses. -/
def fiveRoundFiberEquiv
    (k₀ k₁ k₂ k₃ k₄ : Word) (a b : State) :
    {p : State // stateXor
      (forward k₀ k₁ k₂ k₃ k₄ (stateXor p a))
      (forward k₀ k₁ k₂ k₃ k₄ p) = b} ≃
    {q : State // stateXor
      (backward k₀ k₁ k₂ k₃ k₄ (stateXor q (Prod.swap b)))
      (backward k₀ k₁ k₂ k₃ k₄ q) = Prod.swap a} where
  toFun p :=
    ⟨Prod.swap (forward k₀ k₁ k₂ k₃ k₄ p.1),
     reverse_witness k₀ k₁ k₂ k₃ k₄ p.1 a b p.2⟩
  invFun q :=
    ⟨Prod.swap (backward k₀ k₁ k₂ k₃ k₄ q.1), by
      have hh := reverse_witness
        k₄ k₃ k₂ k₁ k₀ q.1 (Prod.swap b) (Prod.swap a) q.2
      simpa only [forward, backward, Prod.swap_swap] using hh⟩
  left_inv := by
    intro p
    apply Subtype.ext
    change Prod.swap
      (backward k₀ k₁ k₂ k₃ k₄
        (Prod.swap (forward k₀ k₁ k₂ k₃ k₄ p.1))) = p.1
    rw [backward_swap_forward]
    exact Prod.swap_swap _
  right_inv := by
    intro q
    apply Subtype.ext
    change Prod.swap
      (forward k₀ k₁ k₂ k₃ k₄
        (Prod.swap (backward k₀ k₁ k₂ k₃ k₄ q.1))) = q.1
    rw [forward_swap_backward]
    exact Prod.swap_swap _

/-- Exact numerical DDT symmetry for five ordinary Magma rounds.
    The reverse key order is essential; this is not a fixed-key
    symmetry unless the key sequence itself is palindromic. -/
theorem fiveRound_ddt_reverse
    (k₀ k₁ k₂ k₃ k₄ : Word) (a b : State) :
    xorDDT_rounds 5 (fiveRoundKeys k₀ k₁ k₂ k₃ k₄) a b =
    xorDDT_rounds 5 (fiveRoundKeys k₄ k₃ k₂ k₁ k₀)
      (Prod.swap b) (Prod.swap a) := by
  classical
  calc
    xorDDT_rounds 5 (fiveRoundKeys k₀ k₁ k₂ k₃ k₄) a b =
        Fintype.card {p : State // stateXor
          (forward k₀ k₁ k₂ k₃ k₄ (stateXor p a))
          (forward k₀ k₁ k₂ k₃ k₄ p) = b} := by
            simp [xorDDT_rounds, multiRoundDelta,
              Fintype.card_subtype, forward_eq_iterate]
            rfl
    _ = Fintype.card {q : State // stateXor
          (backward k₀ k₁ k₂ k₃ k₄ (stateXor q (Prod.swap b)))
          (backward k₀ k₁ k₂ k₃ k₄ q) = Prod.swap a} :=
      Fintype.card_congr (fiveRoundFiberEquiv k₀ k₁ k₂ k₃ k₄ a b)
    _ = xorDDT_rounds 5 (fiveRoundKeys k₄ k₃ k₂ k₁ k₀)
          (Prod.swap b) (Prod.swap a) := by
            simp [xorDDT_rounds, multiRoundDelta,
              Fintype.card_subtype, backward_eq_iterate]
            rfl

/-- The outer sparse family is invariant under reversing the
    five subkeys and exchanging the two nonzero half-differences. -/
theorem outer_ddt_reverse
    (k₀ k₁ k₂ k₃ k₄ α σ : Word) :
    xorDDT_rounds 5 (fiveRoundKeys k₀ k₁ k₂ k₃ k₄)
        (α, 0#32) (0#32, σ) =
    xorDDT_rounds 5 (fiveRoundKeys k₄ k₃ k₂ k₁ k₀)
        (σ, 0#32) (0#32, α) :=
  fiveRound_ddt_reverse k₀ k₁ k₂ k₃ k₄ (α, 0#32) (0#32, σ)

end Magma.DiffanFiveRoundDDTReverse
