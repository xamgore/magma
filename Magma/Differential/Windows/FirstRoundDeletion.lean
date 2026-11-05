module

import all Init.Data.Range.Basic
public import Magma.Differential.FourRounds.FourRoundZeroLeftFactorization

@[expose] public section

/-!
# Removing the first Feistel round from an exact DDT

The input difference `(aL, 0)` propagates through the first ordinary
Feistel round as `(0, aL)`, independently of its key and base state.

Crucially, the first round is a bijection on *concrete* states. Thus its
output is a valid change of variables in the DDT fiber; this proves an
exact count equality rather than merely a statement about possible
output differences.

Combining this first-round deletion with the already proved last-round
zero-left deletion removes *both* boundary rounds of any chain of length
at least two.
-/

namespace Magma.DiffanFirstRoundDeletion

open Magma
open Magma.MultiRoundDDT

private abbrev Word :=
  V 32

private abbrev State :=
  FeistelState

/-- Split an ordered Feistel chain *after its first round*. The original
    `Fin.foldl` convention applies the key at index 0 first. -/
theorem iterateG_succ_first (n : Nat) (keys : Fin (n + 1) → Word)
    (start : State) :
    iterateG (n + 1) keys start =
      iterateG n (fun i : Fin n => keys i.succ) (G (keys 0) start) := by
  unfold iterateG
  rw [Fin.foldl_succ]

/-- At right input difference zero, the first round maps *each concrete
    related pair* to a pair with difference `(0,aL)`. -/
theorem G_stateXor_zero_right (k aL : Word) (start : State) :
    G k (stateXor start (aL, 0#32)) =
      stateXor (G k start) (0#32, aL) := by
  rcases start with ⟨L, R⟩
  apply Prod.ext
  · change R ^^^ (0#32) = R ^^^ (0#32)
    rfl
  · change (g k (R ^^^ (0#32))) ^^^ (L ^^^ aL) =
      ((g k R) ^^^ L) ^^^ aL
    simp only [BitVec.xor_zero, BitVec.xor_assoc]

/-- Strong pointwise form of first-round deletion. The new concrete
    starting state is `G (keys 0) start`, not the original `start`.
    This distinction is essential to preserve correct correlations. -/
theorem multiRoundDelta_succ_first (n : Nat)
    (keys : Fin (n + 1) → Word) (start : State) (aL : Word) :
    multiRoundDelta (n + 1) keys start (aL, 0#32) =
      multiRoundDelta n (fun i : Fin n => keys i.succ)
        (G (keys 0) start) (0#32, aL) := by
  unfold multiRoundDelta
  rw [iterateG_succ_first, iterateG_succ_first]
  rw [G_stateXor_zero_right]

/-- Exact bijection of the two DDT fibers: to delete the first round,
    transport the base state through the Feistel permutation itself.
    In particular this does *not* assume independence of DDT entries. -/
def zeroRight_fiberEquiv (n : Nat)
    (keys : Fin (n + 1) → Word) (aL : Word) (out : State) :
    {start : State //
      multiRoundDelta (n + 1) keys start (aL, 0#32) = out} ≃
    {middle : State //
      multiRoundDelta n (fun i : Fin n => keys i.succ)
        middle (0#32, aL) = out} where
  toFun := fun start =>
    ⟨G (keys 0) start.1, by
      rw [← multiRoundDelta_succ_first n keys start.1 aL]
      exact start.2⟩
  invFun := fun middle =>
    ⟨(GEquiv (keys 0)).symm middle.1, by
      rw [multiRoundDelta_succ_first]
      have hG : G (keys 0) ((GEquiv (keys 0)).symm middle.1) = middle.1 :=
        (GEquiv (keys 0)).apply_symm_apply middle.1
      rw [hG]
      exact middle.2⟩
  left_inv := by
    intro start
    apply Subtype.ext
    exact (GEquiv (keys 0)).symm_apply_apply start.1
  right_inv := by
    intro middle
    apply Subtype.ext
    exact (GEquiv (keys 0)).apply_symm_apply middle.1

/-- General first-round deletion theorem, at arbitrary depth and fixed
    keys. Counts are transferred by the explicit equivalence of fibers. -/
theorem zeroRight_succ_ddt_eq_suffix (n : Nat)
    (keys : Fin (n + 1) → Word) (aL : Word) (out : State) :
    xorDDT_rounds (n + 1) keys (aL, 0#32) out =
      xorDDT_rounds n (fun i : Fin n => keys i.succ)
        (0#32, aL) out := by
  classical
  unfold xorDDT_rounds
  calc
    ((Finset.univ : Finset State).filter (fun start =>
      multiRoundDelta (n + 1) keys start (aL, 0#32) = out)).card =
        Fintype.card {start : State //
          multiRoundDelta (n + 1) keys start (aL, 0#32) = out} :=
      (Fintype.card_subtype
        (fun start : State =>
          multiRoundDelta (n + 1) keys start (aL, 0#32) = out)).symm
    _ = Fintype.card {middle : State //
          multiRoundDelta n (fun i : Fin n => keys i.succ)
            middle (0#32, aL) = out} :=
      Fintype.card_congr (zeroRight_fiberEquiv n keys aL out)
    _ = ((Finset.univ : Finset State).filter (fun middle =>
          multiRoundDelta n (fun i : Fin n => keys i.succ)
            middle (0#32, aL) = out)).card :=
      Fintype.card_subtype
        (fun middle : State =>
          multiRoundDelta n (fun i : Fin n => keys i.succ)
            middle (0#32, aL) = out)

/-- The first key has no influence on this exact DDT slice if the
    remainder of the key sequence is held fixed. -/
theorem zeroRight_firstKey_independent (n : Nat)
    (k k' : Word) (tail : Fin n → Word) (aL : Word) (out : State) :
    xorDDT_rounds (n + 1)
      (Fin.cons k tail) (aL, 0#32) out =
    xorDDT_rounds (n + 1)
      (Fin.cons k' tail) (aL, 0#32) out := by
  calc
    xorDDT_rounds (n + 1) (Fin.cons k tail) (aL, 0#32) out =
        xorDDT_rounds n tail (0#32, aL) out := by
      simpa only [Fin.cons_succ] using
        (zeroRight_succ_ddt_eq_suffix n (Fin.cons k tail) aL out)
    _ = xorDDT_rounds (n + 1) (Fin.cons k' tail)
          (aL, 0#32) out := by
      simpa only [Fin.cons_succ] using
        (zeroRight_succ_ddt_eq_suffix n (Fin.cons k' tail) aL out).symm

/-- Two-sided boundary reduction. For an `n+2`-round chain,
    a zero right input difference eliminates the first round, and a
    zero left output difference eliminates the last. The middle `n`
    rounds retain the original order and the same fixed keys. -/
theorem twoSided_boundary_ddt_eq_inner (n : Nat)
    (keys : Fin (n + 2) → Word) (aL bR : Word) :
    xorDDT_rounds (n + 2) keys (aL, 0#32) (0#32, bR) =
      xorDDT_rounds n
        (fun i : Fin n => keys i.castSucc.succ)
        (0#32, aL) (bR, 0#32) := by
  calc
    xorDDT_rounds (n + 2) keys (aL, 0#32) (0#32, bR) =
        xorDDT_rounds (n + 1)
          (fun j : Fin (n + 1) => keys j.succ)
          (0#32, aL) (0#32, bR) :=
      zeroRight_succ_ddt_eq_suffix (n + 1) keys aL (0#32, bR)
    _ = xorDDT_rounds n
          (fun i : Fin n => keys i.castSucc.succ)
          (0#32, aL) (bR, 0#32) :=
      Magma.DiffanFourRoundZeroLeftFactorization.zeroLeft_succ_ddt_eq_prefix
        n (fun j : Fin (n + 1) => keys j.succ) (0#32, aL) bR

/-- The previously proved four-round slice is literally a two-round
    differential of the two inner round functions.  This exhibits the
    two-step reduction without appealing to the product formula. -/
theorem fourRound_eq_twoRound_inner
    (k₀ k₁ k₂ k₃ aL bR : Word) :
    xorDDT_rounds 4
      (Magma.DiffanFourRoundZeroLeftFactorization.fourRoundKeys
        k₀ k₁ k₂ k₃)
      (aL, 0#32) (0#32, bR) =
    xorDDT_rounds 2 (twoRoundKeys k₁ k₂)
      (0#32, aL) (bR, 0#32) := by
  have h := twoSided_boundary_ddt_eq_inner 2
    (Magma.DiffanFourRoundZeroLeftFactorization.fourRoundKeys
      k₀ k₁ k₂ k₃) aL bR
  have hkeys :
      (fun i : Fin 2 =>
        Magma.DiffanFourRoundZeroLeftFactorization.fourRoundKeys
          k₀ k₁ k₂ k₃ i.castSucc.succ) =
        twoRoundKeys k₁ k₂ := by
    funext i
    fin_cases i <;> rfl
  rw [hkeys] at h
  exact h

end Magma.DiffanFirstRoundDeletion
