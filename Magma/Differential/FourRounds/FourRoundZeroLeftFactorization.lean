module

import all Init.Data.Range.Basic
public import Magma.Differential.ThreeRounds.ThreeRoundZeroRightInputFactorization

@[expose] public section

/-!
# Exact four-round factorization from two zero-boundary differences

For ordinary Feistel rounds (not the final packed GStar), a zero LEFT
output difference cancels the last round function exactly. This is true
at arbitrary depth and for arbitrary fixed round keys.

Combining this general reduction with the three-round factorization
for three rounds with zero RIGHT input gives a new exact four-round result:

  D4 ((aL, 0), (0, bR)) = D_g[k1](aL, bR) * D_g[k2](bR, aL).

Both outer keys k0 and k3 disappear. This is an identity of exact
fixed-key counts, not a product-of-probabilities approximation.
-/

namespace Magma.DifanFourRoundZeroLeftFactorization

open Magma
open Magma.MultiRoundDDT
open Magma.CarryAutomaton
open Magma.FeistelDDT

private abbrev Word :=
  V 32

private abbrev State :=
  FeistelState

/-- Four ordinary Feistel keys, in their application order. -/
def fourRoundKeys (k₀ k₁ k₂ k₃ : Word) : Fin 4 → Word :=
  ![k₀, k₁, k₂, k₃]

private theorem fourRoundKeys_prefix (k₀ k₁ k₂ k₃ : Word) :
    (fun i : Fin 3 => (fourRoundKeys k₀ k₁ k₂ k₃) i.castSucc) = threeRoundKeys k₀ k₁ k₂ := by
  funext i
  fin_cases i <;> rfl

private theorem fourRoundKeys_last (k₀ k₁ k₂ k₃ : Word) :
    fourRoundKeys k₀ k₁ k₂ k₃ (Fin.last 3) = k₃ := by rfl

/-- The last Feistel round can produce `(0,bR)` precisely when the
    incoming difference was `(bR,0)`; the key is irrelevant. -/
private theorem feistel_zero_left_iff
    (k dL dR L R bR : Word) :
    feistelXorDiff k dL dR L R = (0#32, bR) ↔
      (dL, dR) = (bR, 0#32) := by
  rw [feistelXorDiff_eq]
  constructor
  · intro h
    have hr : dR = (0#32) := congrArg Prod.fst h
    have hl : xor (xor (g k (xor R dR)) (g k R)) dL = bR :=
      congrArg Prod.snd h
    rw [hr] at hl
    change ((g k (R ^^^ (0#32))) ^^^ (g k R)) ^^^ dL = bR at hl
    simp only [BitVec.xor_zero, BitVec.xor_self, BitVec.zero_xor] at hl
    exact Prod.ext hl hr
  · intro h
    have hl : dL = bR := congrArg Prod.fst h
    have hr : dR = (0#32) := congrArg Prod.snd h
    rw [hl, hr]
    change (0#32, ((g k (R ^^^ (0#32))) ^^^ (g k R)) ^^^ bR) =
      (0#32, bR)
    simp only [BitVec.xor_zero, BitVec.xor_self, BitVec.zero_xor]

/-- The reduction is pointwise in the concrete base state and works
    at *every* depth, not just at depth four. -/
theorem zeroLeft_succ_iff_prefix (n : Nat)
    (keys : Fin (n + 1) → Word)
    (start inputDiff : State) (bR : Word) :
    multiRoundDelta (n + 1) keys start inputDiff = (0#32, bR) ↔
      multiRoundDelta n (fun i => keys i.castSucc) start inputDiff =
        (bR, 0#32) := by
  rw [multiRoundDelta_succ]
  exact feistel_zero_left_iff _ _ _ _ _ bR

/-- Exact DDT counts reduce at every depth when the output-left difference is zero. -/
theorem zeroLeft_succ_ddt_eq_prefix (n : Nat)
    (keys : Fin (n + 1) → Word)
    (inputDiff : State) (bR : Word) :
    xorDDT_rounds (n + 1) keys inputDiff (0#32, bR) =
      xorDDT_rounds n (fun i => keys i.castSucc) inputDiff
        (bR, 0#32) := by
  classical
  have hsets :
      ((Finset.univ : Finset State).filter (fun start =>
        multiRoundDelta (n + 1) keys start inputDiff = (0#32, bR))) =
      ((Finset.univ : Finset State).filter (fun start =>
        multiRoundDelta n (fun i => keys i.castSucc) start inputDiff =
          (bR, 0#32))) := by
    ext start
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact zeroLeft_succ_iff_prefix n keys start inputDiff bR
  unfold xorDDT_rounds
  exact congrArg Finset.card hsets

/-- Four rounds with zero LEFT output reduce exactly to three rounds.
    In particular, the result does not depend on the fourth key. -/
theorem fourRound_zeroLeft_eq_three
    (k₀ k₁ k₂ k₃ aL aR bR : Word) :
    xorDDT_rounds 4 (fourRoundKeys k₀ k₁ k₂ k₃)
        (aL, aR) (0#32, bR) =
      xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
        (aL, aR) (bR, 0#32) := by
  have h := zeroLeft_succ_ddt_eq_prefix 3
    (fourRoundKeys k₀ k₁ k₂ k₃) (aL, aR) bR
  rw [fourRoundKeys_prefix] at h
  exact h

/-- Exact four-round product formula.

    An input difference `(aL,0)` and output difference `(0,bR)`
    make both outer keys disappear. The two inner fixed-key
    differential counts separate as a genuine Cartesian product. -/
theorem fourRound_zeroRightInput_zeroLeftOutput_factorization
    (k₀ k₁ k₂ k₃ aL bR : Word) :
    xorDDT_rounds 4 (fourRoundKeys k₀ k₁ k₂ k₃)
      (aL, 0#32) (0#32, bR) =
      xorDDT_g k₁ aL bR * xorDDT_g k₂ bR aL := by
  have hzero : xor (0#32) aL = aL := by
    change (0#32) ^^^ aL = aL
    exact BitVec.zero_xor
  rw [fourRound_zeroLeft_eq_three,
    Magma.DifanThreeRoundZeroRightInputFactorization.threeRound_zeroRightInput_factorization, hzero]

/-- Both outer round keys can be changed independently without changing
    this specific coefficient. -/
theorem fourRound_independent_outer_keys
    (k₀ k₀' k₁ k₂ k₃ k₃' aL bR : Word) :
    xorDDT_rounds 4 (fourRoundKeys k₀ k₁ k₂ k₃)
      (aL, 0#32) (0#32, bR) =
    xorDDT_rounds 4 (fourRoundKeys k₀' k₁ k₂ k₃')
      (aL, 0#32) (0#32, bR) := by
  rw [fourRound_zeroRightInput_zeroLeftOutput_factorization,
    fourRound_zeroRightInput_zeroLeftOutput_factorization]

/-- A forbidden local transition in the first inner round eliminates
    the complete four-round differential. -/
theorem fourRound_zero_of_inner_first_zero
    (k₀ k₁ k₂ k₃ aL bR : Word)
    (h : xorDDT_g k₁ aL bR = 0) :
    xorDDT_rounds 4 (fourRoundKeys k₀ k₁ k₂ k₃)
      (aL, 0#32) (0#32, bR) = 0 := by
  rw [fourRound_zeroRightInput_zeroLeftOutput_factorization, h, zero_mul]

/-- A forbidden local transition in the second inner round likewise
    eliminates the complete four-round differential. -/
theorem fourRound_zero_of_inner_second_zero
    (k₀ k₁ k₂ k₃ aL bR : Word)
    (h : xorDDT_g k₂ bR aL = 0) :
    xorDDT_rounds 4 (fourRoundKeys k₀ k₁ k₂ k₃)
      (aL, 0#32) (0#32, bR) = 0 := by
  rw [fourRound_zeroRightInput_zeroLeftOutput_factorization, h, mul_zero]

end Magma.DifanFourRoundZeroLeftFactorization
