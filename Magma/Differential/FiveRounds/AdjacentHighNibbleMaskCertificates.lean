module

import all Init.Data.Range.Basic
public import Magma.Differential.RoundFunction.HighNibbleOutputMaskCertificates
import Std.Tactic.BVDecide

@[expose] public section

/-!
# Two adjacent active nibbles: exact output-mask certificates

A focused experiment following HighNibbleOutputMaskCertificates.
Directions 0x11000000 and 0xA3000000 both change input nibbles
6 and 7 (zero-based, least significant nibble first).

The existing `guaranteedMask_sound` establishes universal invariance;
small concrete witness sets establish maximality for these two directions.
-/

namespace Magma.DifanAdjacentHighNibbleMaskCertificates

open Magma Magma.Internal Magma.GProperties
open Magma.DifanAutomaticOutputMasks
open Magma.DifanHighNibbleOutputMaskCertificates

private abbrev Word :=
  V 32

/-- Two activated neighbouring nibbles: 0x1 in nibble 7 and 0x1 in nibble 6. -/
def firstDirection : Word := 0x11000000#32

/-- A different direction activating precisely the same two nibbles. -/
def secondDirection : Word := 0xA3000000#32

/-- Guaranteed to preserve the 24 output bits outside the rotated
    images of the two most significant input nibbles. -/
theorem first_guaranteed_mask :
    guaranteedMask firstDirection = 0xFFFFF807#32 := by
  decide

theorem second_guaranteed_mask : guaranteedMask secondDirection = 0xFFFFF807#32 := by decide

/-- Only two concrete inputs with the zero round key suffice for the
    first direction. Their output XOR differences cover all omitted bits. -/
def firstWitnesses : List (Word × Word) :=
  [(0x00000000#32, 0x00000000#32),
   (0x00000000#32, 0x64000000#32)]

private theorem firstWitness0 :
    outputDifference firstDirection (0x00000000#32, 0x00000000#32) = 0x00000330#32 := by decide

private theorem firstWitness1 :
    outputDifference firstDirection (0x00000000#32, 0x64000000#32) = 0x000005F8#32 := by decide

/-- Coverage is the complement of the guaranteed output mask. -/
theorem first_coverage :
    witnessCoverage firstDirection firstWitnesses = 0x000007F8#32 := by
  change
    (outputDifference firstDirection (0x00000000#32, 0x00000000#32) |||
       (outputDifference firstDirection (0x00000000#32, 0x64000000#32) |||
         (0#32))) = 0x000007F8#32
  rw [firstWitness0, firstWitness1]
  decide

/-- The second direction needs just one concrete witness. -/
def secondWitnesses : List (Word × Word) :=
  [(0x00000000#32, 0x78000000#32)]

private theorem secondWitness0 :
    outputDifference secondDirection (0x00000000#32, 0x78000000#32) = 0x000007F8#32 := by decide

theorem second_coverage : witnessCoverage secondDirection secondWitnesses = 0x000007F8#32 := by
  change
    (outputDifference secondDirection (0x00000000#32, 0x78000000#32) ||| (0#32)) = 0x000007F8#32
  rw [secondWitness0]
  decide

/-- All universally invariant output masks in direction 0x11000000
    are exactly the submasks of 0xFFFFF807. -/
theorem first_universal_mask_iff (m : Word) :
    (∀ k x : Word,
      (g k (x ^^^ firstDirection) &&& m) =
        (g k x &&& m)) ↔
      (m &&& (0x000007F8#32)) = 0#32 := by
  have hc : witnessCoverage firstDirection firstWitnesses =
      ~~~ (guaranteedMask firstDirection) := by
    rw [first_coverage, first_guaranteed_mask]
    decide
  have h := universalMask_iff_of_coverage firstDirection m firstWitnesses hc
  rw [first_guaranteed_mask] at h
  have heq : (~~~ (0xFFFFF807#32)) = (0x000007F8#32) := by decide
  rw [heq] at h
  exact h

/-- The very same maximal mask is obtained for a substantially different
    pair of active-nibble values, using a separate finite certificate. -/
theorem second_universal_mask_iff (m : Word) :
    (∀ k x : Word,
      (g k (x ^^^ secondDirection) &&& m) =
        (g k x &&& m)) ↔
      (m &&& (0x000007F8#32)) = 0#32 := by
  have hc : witnessCoverage secondDirection secondWitnesses =
      ~~~ (guaranteedMask secondDirection) := by
    rw [second_coverage, second_guaranteed_mask]
    decide
  have h := universalMask_iff_of_coverage secondDirection m secondWitnesses hc
  rw [second_guaranteed_mask] at h
  have heq : (~~~ (0xFFFFF807#32)) = (0x000007F8#32) := by decide
  rw [heq] at h
  exact h

/-- Both selected two-nibble directions admit exactly the same
    universal output masks. This makes no claim about all 255 shifts
    supported in the two highest nibbles. -/
theorem selected_directions_universal_mask_iff (s m : Word)
    (hs : s = firstDirection ∨ s = secondDirection) :
    (∀ k x : Word, (g k (x ^^^ s) &&& m) = (g k x &&& m)) ↔
      (m &&& (0x000007F8#32)) = 0#32 := by
  rcases hs with hs | hs
  · rw [hs]
    exact first_universal_mask_iff m
  · rw [hs]
    exact second_universal_mask_iff m

end Magma.DifanAdjacentHighNibbleMaskCertificates
