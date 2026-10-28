module

public import Magma.OneHot.DiagonalExactWeights
import all Init.Data.Range.Basic

@[expose] public section

/-!
# 19: diagonal weights against the independently verified carry DP

The proposed affine weights agree with the carry DP on all 128 diagonal
cells at the zero key and at `candidate72Key`. These finite certificates
do not establish quantitative equality for arbitrary keys.
-/

namespace Magma.OneHotDiagonalExactWeights

open Magma
open Magma.CarryAutomaton
open Magma.OneHotFixedKeySupportAudit

def compareDiagonalAtKey (k : V 32) : Bool :=
  (List.finRange 8).all
    (fun i =>
      (List.finRange 4).all
        (fun r =>
          (List.finRange 4).all
            (fun s =>
              decide
                (diagonalWeight k i r s =
                  fastOneHotDDT k (⟨4 * i.val + r.val, by omega⟩ : Fin 32)
                    (⟨(4 * i.val + s.val + 11) % 32, by omega⟩ : Fin 32)))))

example : compareDiagonalAtKey (0#32) = true := by decide +kernel

example : compareDiagonalAtKey candidate72Key = true := by decide +kernel

end Magma.OneHotDiagonalExactWeights
