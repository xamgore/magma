module

import all Init.Data.Range.Basic
public import Magma.Differential.FiveRounds.FiveRoundFixedInputGraphJoin
public import Magma.Differential.RoundFunction.AutomaticOutputMasks
import Std.Tactic.BVDecide

@[expose] public section

/-!
# Masked observations of the reconstructed five-round join point

A fixed input difference makes the first common difference a graph over
its base. This module proves a compatible *partial* observation of that
graph for any direction accepted by the structural Magma mask extractor.

For all round keys k, all base words x, input differences a, and shifts s,
    gDifference k (x XOR s) a
agrees with gDifference k x a on guaranteedMask s.

This is a theorem about observable bits of the reconstructed difference.
It does NOT state that the base alone can be aggregated into a coarse
weighted join, nor that observed equalities imply full-point equality.
-/

namespace Magma.DifanFixedInputMaskedObservation

open Magma
open Magma.MultiRoundDDT
open Magma.DifanAutomaticOutputMasks
open Magma.DifanFiveRoundFixedInputGraphJoin

private abbrev Word :=
  V 32

private abbrev Master :=
  V 256

private abbrev RoundState :=
  Word × Word

private abbrev Point :=
  Difan.StateDifference RoundState RoundState

/-- Agreement on a mask is preserved by bitwise XOR of two pairs. -/
private theorem masked_xor_congr (a b c d mask : Word)
    (hab : (a &&& mask) = (b &&& mask))
    (hcd : (c &&& mask) = (d &&& mask)) :
    ((a ^^^ c) &&& mask) = ((b ^^^ d) &&& mask) := by
  bv_decide

/-- The automatically extracted guaranteed mask is also sound for the
XOR derivative, with arbitrary input difference `a` and arbitrary key. -/
theorem derivative_guaranteedMask_invariant (k x a s : Word) :
    (gDifference k (x ^^^ s) a &&& guaranteedMask s) =
      (gDifference k x a &&& guaranteedMask s) := by
  have hcomm : (x ^^^ s) ^^^ a = (x ^^^ a) ^^^ s := by
    bv_decide
  have hleft :
      (g k ((x ^^^ s) ^^^ a) &&& guaranteedMask s) =
        (g k (x ^^^ a) &&& guaranteedMask s) := by
    rw [hcomm]
    exact guaranteedMask_sound k (x ^^^ a) s
  have hright := guaranteedMask_sound k x s
  change
    ((g k ((x ^^^ s) ^^^ a) ^^^ g k (x ^^^ s)) &&& guaranteedMask s) =
      ((g k (x ^^^ a) ^^^ g k x) &&& guaranteedMask s)
  exact masked_xor_congr _ _ _ _ _ hleft hright

/-- The second component of the reconstructed middle difference retains
its guaranteed output mask under a change of the *first* base word. -/
theorem predictedDelta_shift_mask (master : Master)
    (a b : RoundState) (s : Word) :
    ((predictedDelta master a (b.1 ^^^ s, b.2)).2 &&& guaranteedMask s) =
      ((predictedDelta master a b).2 &&& guaranteedMask s) := by
  have h := derivative_guaranteedMask_invariant
    (roundKey master (0 : Fin 32)) b.1 a.2 s
  change
    ((gDifference (roundKey master (0 : Fin 32)) (b.1 ^^^ s) a.2 ^^^ a.1) &&&
        guaranteedMask s) =
      ((gDifference (roundKey master (0 : Fin 32)) b.1 a.2 ^^^ a.1) &&&
        guaranteedMask s)
  exact masked_xor_congr _ _ _ _ _ h rfl

/-- Keep the first component of a difference and only those bits of the
second component guaranteed by the structural mask. -/
def observedDifference (s : Word) (m : Point) : RoundState :=
  (m.delta.1, m.delta.2 &&& guaranteedMask s)

/-- Both base states have exactly the same observed *reconstructed*
difference when the first base coordinate is translated by `s`. -/
theorem reconstructed_observation_shift (master : Master)
    (a b : RoundState) (s : Word) :
    observedDifference s (reconstructed master a (b.1 ^^^ s, b.2)) =
      observedDifference s (reconstructed master a b) := by
  apply Prod.ext
  · rfl
  · exact predictedDelta_shift_mask master a b s

/-- The reconstructed middle difference does not depend on the second
base coordinate at all (regardless of the input difference). -/
theorem reconstructed_delta_independent_second_base (master : Master)
    (a : RoundState) (u v v' : Word) :
    (reconstructed master a (u, v)).delta =
      (reconstructed master a (u, v')).delta := by
  rfl

/-- Concrete proven direction `0x6000`: the 12 observed bits in the
second difference word are invariant for every actual master key. -/
theorem predictedDelta_shift6000_mask (master : Master)
    (a b : RoundState) :
    ((predictedDelta master a (b.1 ^^^ (0x00006000#32), b.2)).2 &&&
        (0x007FF800#32)) =
      ((predictedDelta master a b).2 &&& (0x007FF800#32)) := by
  simpa only [mask_6000_exact] using
    predictedDelta_shift_mask master a b (0x00006000#32)

end Magma.DifanFixedInputMaskedObservation
