module

public import Magma.DDT.OneHot.KeyClasses.ClassCertificates
meta import Magma.DDT.OneHot.KeyClasses.ClassCertificates
import all Init.Data.Range.Basic

@[expose] public section

/-!
# 16: original-arithmetic certificates for all 32 class representatives

Iteration 15 compared local key-class predictions with the exploratory UInt8
scan. Here the independently verified two-sided checker certifies the actual
full-word DDT support for the representatives, using original carry edges
for exclusions and the original RFC function `g` for positive witnesses.

The key `0x00800000` is checked first. Its empty predicted support yields
zero DDT for every one-bit input difference with output difference one.
The aggregate evaluation then checks all 16 key nibbles in both carry regimes.

Even a successful aggregate certificate classifies only the representatives.
The arbitrary-key theorem retains the explicit `OneHotClassInvariant`
hypothesis; proving that semantic invariant is a separate mathematical step.
-/

open Magma.Internal Magma.CarryAutomaton Magma.MultiRoundDDT
open Magma.OneHotKeyClasses Magma.OneHotClassCertificates

namespace Magma.Evidence.OneHotClassCertificates

/-- This key lies in the class (q=8,c=false): its predicted support is empty. -/
theorem key_00800000_predicted_empty :
    predictedOneHotPositions (0x00800000#32) = [] := by
  decide

/-- Verified exclusion of ALL 32 one-hot inputs for this single key.
    The premise can be closed by an actual Boolean certificate. -/
theorem key_00800000_no_oneHot_of_checked
    (h : checkPredictedOneHotSupport (0x00800000#32) = true)
    (j : Fin 32) :
    xorDDT_g (0x00800000#32)
      (BitVec.ofNat 32 (2 ^ j.val)) (1#32) = 0 := by
  by_contra hn
  have hp : 0 < xorDDT_g (0x00800000#32)
      (BitVec.ofNat 32 (2 ^ j.val)) (1#32) := Nat.pos_of_ne_zero hn
  have hj := (checkedPredictedOneHotSupport_iff
    (0x00800000#32) h j).mp hp
  rw [key_00800000_predicted_empty] at hj
  exact List.not_mem_nil hj

/-- Original arithmetic certifies the empty support of key `0x00800000`. -/
theorem emptySupportKey_checked :
    checkPredictedOneHotSupport (0x00800000#32) = true := by
  decide +kernel

/-- All 32 one-bit input differences have zero DDT for this key and output one. -/
theorem key_00800000_no_oneHot (j : Fin 32) :
    xorDDT_g (0x00800000#32)
      (BitVec.ofNat 32 (2 ^ j.val)) (1#32) = 0 :=
  key_00800000_no_oneHot_of_checked emptySupportKey_checked j

-- Recorded output: true. Acceptance is also proved by the kernel above.
#eval checkPredictedOneHotSupport (0x00800000#32)

-- Recorded output: true for the independently checked 32-class aggregate.
#eval verifyAllRepresentativeClasses

end Magma.Evidence.OneHotClassCertificates
