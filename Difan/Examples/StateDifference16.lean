module

public import Difan.Core.DifferentialMap
public import Difan.Paths.Chain
import all Init.Data.Range.Basic

@[expose] public section

/-!
# Tracking modular differences on 4-bit words

The base state 14 and difference 3 describe the ordered pair (14, 1)
modulo 16. Adding the same key to both states changes the base while
preserving their relative displacement.
-/

namespace Difan.Examples

/-- Difference of modular integers: `a = y - x`, applied by `x + a`. -/
def mod16 : DifferenceSpace (ZMod 16) (ZMod 16) where
  shift := fun x a => x + a
  diff := fun x y => y - x
  shift_diff := by
    intro x y
    abel
  diff_shift := by
    intro x a
    abel

/-- Addition by a fixed round parameter is a state map. -/
def addMod16 (key : ZMod 16) : DifferentialMap mod16 mod16 :=
  ⟨fun x => x + key⟩

/-- We know both concrete states: base=14, other=1 (mod 16). -/
example :
    (StateDifference.mk (14 : ZMod 16) 3).toPair mod16 =
      ((14 : ZMod 16), (1 : ZMod 16)) := by
  decide

/-- Modular translation preserves the difference at every base state.
The base may wrap around the modulus while relative displacement stays fixed. -/
theorem addMod16_derivative (key a x : ZMod 16) :
    (addMod16 key).derivative a x = a := by
  change ((x + a) + key) - (x + key) = a
  abel

/-- The transport keeps the new base and the same difference. -/
theorem addMod16_transport (key a x : ZMod 16) :
    (addMod16 key).transport ⟨x, a⟩ = ⟨x + key, a⟩ := by
  change StateDifference.mk (x + key) ((addMod16 key).derivative a x) =
    StateDifference.mk (x + key) a
  rw [addMod16_derivative]

end Difan.Examples
