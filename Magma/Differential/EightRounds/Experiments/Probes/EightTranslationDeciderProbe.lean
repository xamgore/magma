module

import all Init.Data.Range.Basic
public import Difan.Symmetry.FiniteTranslationOrbits
public import Magma.Differential.EightRounds.ZeroKeyEightOrbitReduction

@[expose] public section

/-!
# Certified finite translation tiling of the 76 positive-defect pairs

A Boolean label selects the neutral shift or the proved XOR shift.
`OrbitTiling` certifies that the 38 representatives and these two
translations parametrize the exact 76-pair support bijectively.

The weighted formulas instantiate the generic finite-translation theorem
with the reduced defect, which is constant on each two-element orbit.
-/

namespace Magma.DifanZeroKeyEightTranslationTiling

open Magma
open Magma.DifanZeroKeyEightDefectClassification
open Magma.DifanZeroKeyEightDefectWeights
open Magma.DifanZeroKeyEightDefectSpectrum
open Magma.DifanZeroKeyEightOrbitReduction
open Difan.FiniteTranslationOrbits

private abbrev Word := V 32

/-- Boolean identity/shift action, with no extra bit-vector assumptions. -/
def shiftByBool (p : Word × Word) (b : Bool) : Word × Word :=
  if b then shiftPair p else p

/-- The translation labels form a two-element finite set. -/
def shifts : Finset Bool := Finset.univ


#synth Decidable (OrbitTiling positiveDefectPairs orbitRepresentatives shifts shiftByBool)

end Magma.DifanZeroKeyEightTranslationTiling
