module

public import Magma.Composition.MultiRoundDDT
meta import Magma.Composition.MultiRoundDDT
import all Init.Data.Range.Basic

@[expose] public section

/-!
# 07: constructive witnesses for the three exceptional differentials

Research stage: resolve the three masks left open by the search in
`06_TwoBitFamilyAndExceptions.lean`. Explicit starting states are checked
against the original `multiRoundDelta`, independently of BatchSearch and
the carry/grouped implementations.

The witness statements assert positive DDT support for keys `(0, 0, 0)` and
output difference `(0, 2^23)`. They do not assert feasibility for that same
output difference under arbitrary third keys. They rule out impossibility
uniformly over all third keys and right output differences for these masks.

The starting words were obtained independently using the eight RFC 8891
S-boxes and `G[k](L, R) = (R, g[k](R) XOR L)`. Each positive-DDT proof supplies
an explicit state instead of enumerating the 64-bit input space.

Expected executable result: `checkThreeResidualWitnesses = true`. The example
below fixes this expectation as a kernel-checked proof obligation. This
iteration has not been compiled or evaluated during integration.

Build and print the witness check explicitly:
`lake build Magma/Evidence/07_ThreeExceptionalWitnesses.lean`
Earlier research iterations are not imported or executed.
-/

open Magma.Internal Magma.MultiRoundDDT

namespace Magma.Evidence.ThreeExceptionalWitnesses

private def zeroThreeKeys : Fin 3 → V 32 :=
  threeRoundKeys (0#32) (0#32) (0#32)

private def inputDifference (n : Nat) : FeistelState :=
  (BitVec.ofNat 32 n, 1#32)

/-- Same output difference for all three explicit examples. -/
private def residualOutput : FeistelState :=
  (0#32, BitVec.ofNat 32 8388608)

/-- Explicit starting states (L, R), in Feistel convention. -/
private def start12 : FeistelState :=
  (BitVec.ofNat 32 3191560386, BitVec.ofNat 32 6)

private def start13 : FeistelState :=
  (BitVec.ofNat 32 3191550146, BitVec.ofNat 32 2)

private def start14 : FeistelState :=
  (BitVec.ofNat 32 3191562434, BitVec.ofNat 32 0)

/-- Check the three explicit witnesses using the original round composition. -/
def checkThreeResidualWitnesses : Bool :=
  decide (multiRoundDelta 3 zeroThreeKeys start12
      (inputDifference 8392704) = residualOutput) &&
  decide (multiRoundDelta 3 zeroThreeKeys start13
      (inputDifference 8396800) = residualOutput) &&
  decide (multiRoundDelta 3 zeroThreeKeys start14
      (inputDifference 8404992) = residualOutput)

set_option maxHeartbeats 0 in
example : checkThreeResidualWitnesses = true := by decide +kernel

/-- A witness gives positive cardinality without enumerating the type. -/
private theorem filter_univ_card_pos_of_witness
    {α : Type*} [Fintype α]
    (pred : α → Prop) [DecidablePred pred]
    (w : α) (hw : pred w) :
    0 < ((Finset.univ : Finset α).filter pred).card := by
  apply Finset.Nonempty.card_pos
  exact ⟨w, (Finset.mem_filter_univ w).2 hw⟩

/-- Extract positive DDT support from an explicit starting state. -/
private theorem DDT_pos_of_explicit_start
    (a b p : FeistelState)
    (h : multiRoundDelta 3 zeroThreeKeys p a = b) :
    0 < xorDDT_rounds 3 zeroThreeKeys a b := by
  change 0 <
    ((Finset.univ : Finset FeistelState).filter
      (fun start =>
        multiRoundDelta 3 zeroThreeKeys start a = b)).card
  exact filter_univ_card_pos_of_witness
    (fun start : FeistelState =>
      multiRoundDelta 3 zeroThreeKeys start a = b)
    p h

/-- Bits (12, 23): feasible for k₀ = k₁ = k₂ = 0 and bR = 2^23. -/
theorem exceptional_12_23_nonzero :
    0 < xorDDT_rounds 3 zeroThreeKeys
      (inputDifference 8392704) residualOutput := by
  exact DDT_pos_of_explicit_start
    (inputDifference 8392704) residualOutput start12 (by decide)

/-- Bits (13, 23): another explicit feasible difference for the same keys and output. -/
theorem exceptional_13_23_nonzero :
    0 < xorDDT_rounds 3 zeroThreeKeys
      (inputDifference 8396800) residualOutput := by
  exact DDT_pos_of_explicit_start
    (inputDifference 8396800) residualOutput start13 (by decide)

/-- Bits (14, 23): another explicit feasible difference for the same keys and output. -/
theorem exceptional_14_23_nonzero :
    0 < xorDDT_rounds 3 zeroThreeKeys
      (inputDifference 8404992) residualOutput := by
  exact DDT_pos_of_explicit_start
    (inputDifference 8404992) residualOutput start14 (by decide)

#eval checkThreeResidualWitnesses

-- Inside this namespace the theorem names can be written without their full prefix.
#print axioms exceptional_12_23_nonzero

#print axioms exceptional_13_23_nonzero

#print axioms exceptional_14_23_nonzero

end Magma.Evidence.ThreeExceptionalWitnesses
