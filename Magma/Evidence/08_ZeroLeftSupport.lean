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
`Magma.MultiRoundDDT`. The table proofs and enumeration in `Magma.MultiRoundDDT` establish the
predicted list's size and its one-bit/two-bit input masks. They do not establish
that this list equals the full three-round support.

The fixed results are kernel-checked statements, with no profiling commands:
64 predicted pairs, no one-bit positions, and two-bit pairs
`[(12, 23), (13, 23), (14, 23)]`.

Build explicitly with `lake build Magma/Evidence/08_ZeroLeftSupport.lean`.
Earlier iterations are not imported or executed.
-/

open Magma.Internal Magma.MultiRoundDDT

namespace Magma.Evidence.ZeroLeftSupport

export Magma.ZeroLeftSupport (nibbleDDT pi0_one_exact pi5_two_exact U W predictedPairs
  predictedPairs_length predictedOneBitPositions predictedTwoBitPairs
  predictedOneBitPositions_eq_nil predictedTwoBitPairs_eq)

example : Magma.ZeroLeftSupport.predictedPairs.length = 64 :=
  Magma.ZeroLeftSupport.predictedPairs_length

example : Magma.ZeroLeftSupport.predictedOneBitPositions = [] :=
  Magma.ZeroLeftSupport.predictedOneBitPositions_eq_nil

example : Magma.ZeroLeftSupport.predictedTwoBitPairs = [(12, 23), (13, 23), (14, 23)] :=
  Magma.ZeroLeftSupport.predictedTwoBitPairs_eq

end Magma.Evidence.ZeroLeftSupport
