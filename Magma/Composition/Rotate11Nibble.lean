module

import all Init.Data.Range.Basic
public import Magma.Composition.TaggedCarryWord
import Std.Tactic.BVDecide

@[expose] public section

/-!
# Exact RFC rotate-left-11 nibble wiring

An output nibble of 32-bit rotate-left-11 depends on just TWO
pre-rotation nibbles, with cyclic indices (i-3) and (i-2).

Reduce a general BitVec assertion to eight concrete nibble positions;
each is kernel-proved using bv_decide. No independence assumptions.
-/

namespace Magma.Composition.Rotate11Nibble

open Magma
open Magma.Internal
open Magma.CarryAutomaton
open Magma.Composition.TaggedCarryWord

/-- Exact four-bit output nibble after the RFC rotate-left-11, via
    one three-bit slice of nibble i-3 and one bit of nibble i-2. -/
def rotateNibble11 (w : V 32) (i : Fin 8) : V 4 :=
  (nibble w ⟨(i.val + 5) % 8, by omega⟩ >>> 1) |||
  (nibble w ⟨(i.val + 6) % 8, by omega⟩ <<< 3)

/-- The rotated-word nibble is exactly the two-source local wiring
    for arbitrary symbolic 32-bit words and all eight positions. -/
theorem rotateNibble11_correct (w : V 32) (i : Fin 8) :
    rotateNibble11 w i = nibble (rot11 w) i := by
  fin_cases i <;>
    dsimp [rotateNibble11, nibble, substring, rot11] <;>
    bv_decide

/-- Apply the verified wiring to the true tagged BASE word. -/
theorem tagged_base_rotated_nibble (k d x : V 32) (i : Fin 8) :
    rotateNibble11
      (packDigits (fun j => (actualTaggedDigits k d x j).1)) i =
    nibble (g k x) i := by
  rw [rotateNibble11_correct]
  exact congrArg (fun w : V 32 => nibble w i)
    (rot11_pack_actualTagged_base k d x)

/-- Likewise for the true XOR derivative, with shared carries. -/
theorem tagged_difference_rotated_nibble (k d x : V 32) (i : Fin 8) :
    rotateNibble11
      (packDigits (fun j => (actualTaggedDigits k d x j).2)) i =
    nibble (xor (g k (xor x d)) (g k x)) i := by
  rw [rotateNibble11_correct]
  exact congrArg (fun w : V 32 => nibble w i)
    (rot11_pack_actualTagged_difference k d x)

/-! ## Exact local post-rotation digit formula on the eight S-box tags -/

def rotatedTagDigit (tag : Fin 8 → Fin 16) (i : Fin 8) : Fin 16 :=
  let a : V 4 := BitVec.ofNat 4 (tag ⟨(i.val+5)%8, by omega⟩).val
  let b : V 4 := BitVec.ofNat 4 (tag ⟨(i.val+6)%8, by omega⟩).val
  ((a >>> 1) ||| (b <<< 3)).toFin

theorem nibble_pack_tags (tag : Fin 8 → Fin 16) (i : Fin 8) :
    nibble (packDigits tag) i = BitVec.ofNat 4 (tag i).val := by
  apply BitVec.toFin_injective
  have h := congrFun (wordDigitsEquiv.right_inv tag) i
  change (nibble (packDigits tag) i).toFin = tag i at h
  simpa only [BitVec.ofNat_finVal] using h

theorem rotatedTagDigit_correct (tag : Fin 8 → Fin 16) (i : Fin 8) :
    rotatedTagDigit tag i = wordDigits (rot11 (packDigits tag)) i := by
  have h := rotateNibble11_correct (packDigits tag) i
  change rotatedTagDigit tag i = (nibble (rot11 (packDigits tag)) i).toFin
  rw [← h]
  simp only [rotatedTagDigit, rotateNibble11, nibble_pack_tags]

/-- The SEQUENTIAL eight-step tagged BASE trace can be read
    through the two-source local rotate-left-11 tag operator,
    yielding the true i-th Magma g output digit. -/
theorem rotated_recorded_base_exact (k d x : V 32) (i : Fin 8) :
    rotatedTagDigit
      (fun j => (((taggedPrefix k d x 8).2 j).getD (0, 0)).1) i =
    wordDigits (g k x) i := by
  rw [rotatedTagDigit_correct]
  exact congrArg (fun w : V 32 => wordDigits w i)
    (taggedPrefix_eight_g k d x).1

/-- Likewise, the local rotated derivative tag reconstructs
    the true derivative digit with no independently chosen carries. -/
theorem rotated_recorded_derivative_exact (k d x : V 32) (i : Fin 8) :
    rotatedTagDigit
      (fun j => (((taggedPrefix k d x 8).2 j).getD (0, 0)).2) i =
    wordDigits (xor (g k (xor x d)) (g k x)) i := by
  rw [rotatedTagDigit_correct]
  exact congrArg (fun w : V 32 => wordDigits w i)
    (taggedPrefix_eight_g k d x).2

end Magma.Composition.Rotate11Nibble
