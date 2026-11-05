module
public import Magma.Differential.FullCipher.FullScheduleConjugacy
import all Init.Data.Range.Basic

@[expose] public section

/-!
# Actual ordinary XOR-DDT symmetries of the RFC 16-round palindrome

This is a genuinely BASE-FREE invariant, unlike the transported
H-dependent DDT reduction. It does not yield arbitrary 32-round
XOR-DDTs from 16-round scalar DDT products and does not assert
any impossible differential.
-/

namespace Magma.DiffanFullScheduleXorSymmetries
open Magma Magma.MultiRoundDDT Magma.DiffanFullScheduleConjugacy

private abbrev W := V 32
private abbrev S := FeistelState

/-- Involutive equivalence corresponding to a genuine RFC
16-round palindrome with one final Feistel half-swap. -/
def Q16Equiv (k : Fin 8 → W) : S ≃ S where
  toFun := Q16 k
  invFun := Q16 k
  left_inv := Q16_involutive k
  right_inv := Q16_involutive k

/-- Ordinary 64-bit XOR-DDT of the reflected 16-round permutation
is EXACTLY symmetric in input and output differences for all keys.
This property survives the return to standard XOR coordinates. -/
theorem Q16_xorDDT_symmetric (k : Fin 8 → W) (a b : S) :
    Diffan.ddt pairXor pairXor (Q16 k) a b =
      Diffan.ddt pairXor pairXor (Q16 k) b a := by
  calc
    Diffan.ddt pairXor pairXor (Q16 k) a b =
        Diffan.ddt pairXor pairXor
          (Q16Equiv k : S → S) a b := rfl
    _ = Diffan.ddt pairXor pairXor
          ((Q16Equiv k).symm : S → S) b a :=
      Diffan.ddt_equiv_symm pairXor pairXor (Q16Equiv k) a b
    _ = Diffan.ddt pairXor pairXor (Q16 k) b a := rfl

private theorem derivative_J_E16 (k : Fin 8 → W)
    (a p : S) :
    Diffan.derivative pairXor pairXor (Q16 k) a p =
      J (Diffan.derivative pairXor pairXor (E16 k) a p) := by
  rfl

/-- The exact ordinary XOR-DDT of Q16 is the exact ordinary
XOR-DDT of its unswapped E16 output with output difference
halves swapped. Nothing about the base state is discarded
before the final DDT contraction. -/
theorem E16_xorDDT_eq_Q16 (k : Fin 8 → W) (a b : S) :
    Diffan.ddt pairXor pairXor (E16 k) a b =
      Diffan.ddt pairXor pairXor (Q16 k) a (J b) := by
  unfold Diffan.ddt
  apply congrArg Finset.card
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [derivative_J_E16]
  constructor
  · intro h
    rw [h]
  · intro h
    have hh := congrArg J h
    simpa only [J, Prod.swap_swap] using hh

/-- A nontrivial FULL ordinary XOR symmetry of the 16-round
palindrome WITHOUT adapted geometry or any 2^64 base table:

  D_E16(a,b) = D_E16(J(b),J(a)).

Thus its zero/support and all integer coefficients occur in
reflected pairs, for arbitrary actual 32-bit RFC key words.
No scalar DDT product is assumed. -/
theorem E16_xorDDT_reflected_duality
    (k : Fin 8 → W) (a b : S) :
    Diffan.ddt pairXor pairXor (E16 k) a b =
      Diffan.ddt pairXor pairXor (E16 k) (J b) (J a) := by
  calc
    Diffan.ddt pairXor pairXor (E16 k) a b =
        Diffan.ddt pairXor pairXor (Q16 k) a (J b) :=
      E16_xorDDT_eq_Q16 k a b
    _ = Diffan.ddt pairXor pairXor (Q16 k) (J b) a :=
      Q16_xorDDT_symmetric k a (J b)
    _ = Diffan.ddt pairXor pairXor (E16 k) (J b) (J a) := by
      rw [E16_xorDDT_eq_Q16]
      simp only [J, Prod.swap_swap]

/-- EXACT untransformed two-observable correlation duality
for arbitrary Int-valued observables phi,psi on 64-bit states.
This includes ordinary Walsh/LAT correlations by choosing
the functions to be ±1 XOR characters, and works for
ALL genuine 32-bit-word keys without a base-state table.

  Sum_x phi(x) psi(E16(x))
    = Sum_x psi(Jx) phi(J(E16(x))).

It is stronger than just a claim about a spectral trace:
the SAME observables get explicitly half-swapped. -/
theorem E16_observable_correlation_reflected_duality
    (k : Fin 8 → W) (phi psi : S → Int) :
    (∑ x : S, phi x * psi (E16 k x)) =
      ∑ x : S, psi (J x) * phi (J (E16 k x)) := by
  classical
  calc
    (∑ x : S, phi x * psi (E16 k x)) =
        ∑ x : S, phi (Q16 k x) * psi (E16 k (Q16 k x)) := by
      exact (Equiv.sum_comp (Q16Equiv k)
        (fun x : S => phi x * psi (E16 k x))).symm
    _ = ∑ x : S, psi (J x) * phi (J (E16 k x)) := by
      apply Finset.sum_congr rfl
      intro x _
      have hs : E16 k (Q16 k x) = J x := by
        have hh := congrArg J (Q16_involutive k x)
        simpa only [Q16, J, Prod.swap_swap] using hh
      rw [hs]
      change phi (J (E16 k x)) * psi (J x) =
        psi (J x) * phi (J (E16 k x))
      exact mul_comm _ _

end Magma.DiffanFullScheduleXorSymmetries
