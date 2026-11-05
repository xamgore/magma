module

import all Init.Data.Range.Basic
public import Diffan.Symmetry.FiniteSupportSymmetry
public import Magma.Differential.EightRounds.ZeroKeyEightColumnSymmetry
import Std.Tactic.BVDecide

@[expose] public section

/-!
# The eight-column as a consumer of generic finite-support symmetries

The eight-element column and its two algebraic XOR identities instantiate
`Diffan.FiniteSupportSymmetry`. The resulting laws describe the complete
stabilizer set and the transport of weighted defects and survivor sets.
-/

namespace Magma.DiffanZeroKeyEightGenericSymmetry

open Magma
open Magma.DiffanZeroKeyEightColumn
open Magma.DiffanZeroKeyEightColumnSymmetry
open Diffan.FiniteSupportSymmetry

private abbrev Word :=
  V 32

/-- Generic candidate search is complete for the concrete Magma column. -/
theorem stabilizer_iff_generic_candidates (t : Word) :
    zeroColumnSupport.image (fun c => xor c t) = zeroColumnSupport ↔
      t ∈ stabilizers zeroColumnSupport xor := by
  apply stabilizer_iff_mem zeroColumnSupport xor
  · intro x y
    unfold xor
    bv_decide
  · exact ⟨0x00300000#32, by decide +kernel⟩

/-- Thus the *generic* search returns precisely the two certified shifts. -/
theorem generic_stabilizers_exact :
    stabilizers zeroColumnSupport xor =
      ({0#32, 0x00500000#32} : Finset Word) := by
  ext t
  rw [← stabilizer_iff_generic_candidates t, column_stabilizer_iff t]
  simp only [Finset.mem_insert, Finset.mem_singleton]

/-- Generic finite-support mass specializes to the eight-column row mass. -/
theorem generic_mass_eq_prior (row : Word → Nat) (aL : Word) :
    mass zeroColumnSupport xor row aL = rowMass row aL :=
  rfl

/-- The generic excluded-term sum specializes to the eight-column row defect. -/
theorem generic_defect_eq_prior (row : Word → Nat) (aL bR : Word) :
    defect zeroColumnSupport xor row aL bR = rowDefect row aL bR :=
  rfl

/-- Recover the full symbolic defect symmetry as a generic theorem
    specialized to a finite support, without a 76-pair case split. -/
theorem defect_invariant_from_generic (row : Word → Nat) (aL bR : Word) :
    rowDefect row (translate aL) (translate bR) = rowDefect row aL bR := by
  change defect zeroColumnSupport xor row (translate aL) (translate bR) =
    defect zeroColumnSupport xor row aL bR
  exact defect_invariant zeroColumnSupport xor row translate
    translate_involutive column_stable xor_translate_right
    xor_translate_both aL bR

/-- The generic law also transports the entire set of survivors. -/
theorem survivors_invariant_from_generic (row : Word → Nat) (aL : Word) :
    rowSurvivors row (translate aL) =
      (rowSurvivors row aL).image translate := by
  change survivors zeroColumnSupport xor row (translate aL) =
    (survivors zeroColumnSupport xor row aL).image translate
  exact survivors_invariant zeroColumnSupport xor row translate
    translate_involutive column_stable xor_translate_right
    xor_translate_both aL

end Magma.DiffanZeroKeyEightGenericSymmetry
