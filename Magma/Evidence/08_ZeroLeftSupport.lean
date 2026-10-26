module

public import Magma.MultiRoundDDT
import all Init.Data.Range.Basic

@[expose] public section

/-!
# 08: predicting zero-left-output support from two S-box tables

Following the three constructive witnesses in `07_ThreeExceptionalWitnesses.lean`,
ask whether the zero-left factorization explains the one-bit and two-bit search
results structurally. For zero first two keys and right input difference one,
two exact four-bit RFC tables predict 64 pairs `(aL, bR)`.

The proved support test and its soundness/completeness theorems live in
`Magma.MultiRoundDDT`. The table proofs and enumeration below establish the
predicted list's size and its one-bit/two-bit input masks. They do not establish
that this list equals the full three-round support. Iteration 09 supplies the
universal sixteen-factor DDT formula; identifying its positive entries with
this explicit list remains to be proved.

The fixed results are kernel-checked statements, with no profiling commands:
64 predicted pairs, no one-bit positions, and two-bit pairs
`[(12, 23), (13, 23), (14, 23)]`.

Build explicitly with `lake build Magma/Evidence/08_ZeroLeftSupport.lean`.
Earlier iterations are not imported or executed.
-/

open Magma.Internal Magma.MultiRoundDDT

namespace Magma.Evidence.ZeroLeftSupport

/-- XOR on 4-bit S-box inputs, represented by `Fin 16`. -/
private def xor4 (x d : Fin 16) : Fin 16 :=
  ((BitVec.ofNat 4 x.val) ^^^ (BitVec.ofNat 4 d.val)).toFin

/-- The ordinary 4-bit XOR-DDT of RFC S-box number `i`. -/
def nibbleDDT (i : Fin 8) (d out : Fin 16) : Nat :=
  ((Finset.univ : Finset (Fin 16)).filter fun x =>
    Nat.xor (π'arrays i (xor4 x d)).val (π'arrays i x).val = out.val).card

/-- For S-box 0, input difference 1 gives exactly eight outputs,
    each with DDT count 2 (all other entries zero). -/
theorem pi0_one_exact (out : Fin 16) :
    nibbleDDT 0 1 out =
      if out.val ∈ ([2, 3, 4, 6, 8, 10, 14, 15] : List Nat)
      then 2 else 0 := by
  fin_cases out <;> decide

/-- For S-box 5, output difference 2 is possible for exactly eight
    input differences, each with DDT count 2. -/
theorem pi5_two_exact (d : Fin 16) :
    nibbleDDT 5 d 2 =
      if d.val ∈ ([3, 6, 8, 9, 10, 12, 13, 15] : List Nat)
      then 2 else 0 := by
  fin_cases d <;> decide

/-- Output differences before rotation of the S-box 0 transition. -/
def U : List Nat := [2, 3, 4, 6, 8, 10, 14, 15]

/-- Input differences of S-box 5 producing output difference 2. -/
def W : List Nat := [3, 6, 8, 9, 10, 12, 13, 15]

/-- Predicted `(aL, bR)` pairs from the two independent 4-bit tables.
    They have the form `(w*2^20 XOR u*2^11, w*2^20)`. Since the bit
    ranges are disjoint, `+` equals XOR in this particular expression. -/
def predictedPairs : List (V 32 × V 32) :=
  W.flatMap fun w =>
    U.map fun u =>
      (BitVec.ofNat 32 (w * 2^20 + u * 2^11),
       BitVec.ofNat 32 (w * 2^20))

theorem predictedPairs_length : predictedPairs.length = 64 := by
  decide

/-- Which single-bit input differences belong to the predicted support? -/
def predictedOneBitPositions : List Nat :=
  (List.range 32).filter fun i =>
    predictedPairs.any fun p => p.1 == BitVec.ofNat 32 (2^i)

/-- Which two-bit input differences belong to the predicted support? -/
def predictedTwoBitPairs : List (Nat × Nat) := Id.run do
  let mut result := []
  for i in [:32] do
    for j in [i+1:32] do
      let aL := BitVec.ofNat 32 (2^i + 2^j)
      if predictedPairs.any (fun p => p.1 == aL) then
        result := (i, j) :: result
  return result.reverse

/-- No one-bit input difference occurs in the predicted list. -/
theorem predictedOneBitPositions_eq_nil : predictedOneBitPositions = [] := by
  decide +kernel

/-- The predicted two-bit masks are exactly the three earlier search exceptions. -/
theorem predictedTwoBitPairs_eq :
    predictedTwoBitPairs = [(12, 23), (13, 23), (14, 23)] := by
  decide +kernel

end Magma.Evidence.ZeroLeftSupport
