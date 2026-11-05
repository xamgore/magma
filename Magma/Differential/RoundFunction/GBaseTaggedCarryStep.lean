module

import all Init.Data.Range.Basic
public import Magma.Carry.Automaton

@[expose] public section

/-!
# A Magma nibble step that records BOTH the base substituted output and XOR derivative

The existing `sboxCarryStep` records the derivative output and carries.
To eliminate the 32-bit middle base Z using its actual g-output, we must
also record the base S-box output, BEFORE rot11. Each local output is
computed using the SAME incoming carry as the corresponding derivative.

This module is deliberately local. The remaining semantic work is to
prove that the eight recorded base outputs concatenate to t(Z+k),
then propagate rot11 into the input of the third carry chain.
-/

namespace Magma.DiffanGBaseTaggedCarryStep

open Magma
open Magma.Internal
open Magma.CarryAutomaton

/-- The actual pre-rotation S-box output of the BASE addition at nibble i.
The first carry is the one for the unshifted x+k (the second carry is
reserved for (x XOR diff)+k). -/
def baseSboxDigit (i : Fin 8) (k x : Fin 16)
    (incoming : CarryState) : Fin 16 :=
  (π i (BitVec.ofNat 4 (outputDigit x k incoming.1).val)).toFin

/-- A deterministic tagged transition: (base S-box digit, XOR output digit),
followed by the same outgoing pair of carry bits as `sboxCarryStep`. -/
def taggedCarryStep (i : Fin 8) (k diff x : Fin 16)
    (incoming : CarryState) : (Fin 16 × Fin 16) × CarryState :=
  let old := sboxCarryStep i k diff x incoming
  ((baseSboxDigit i k x incoming, old.1), old.2)

/-- The new tag does not change the original exact differential transition. -/
theorem taggedStep_preserves_existing_step
    (i : Fin 8) (k diff x : Fin 16) (incoming : CarryState) :
    ((taggedCarryStep i k diff x incoming).1.2,
      (taggedCarryStep i k diff x incoming).2) =
      sboxCarryStep i k diff x incoming := by
  rfl

/-- The tag is the BASE S-box output, not the XOR-difference output. -/
theorem taggedStep_base_digit
    (i : Fin 8) (k diff x : Fin 16) (incoming : CarryState) :
    (taggedCarryStep i k diff x incoming).1.1 =
      baseSboxDigit i k x incoming := by
  rfl

end Magma.DiffanGBaseTaggedCarryStep
