module

public import Magma.OneHotCompleteSupport
import all Init.Data.Range.Basic

@[expose] public section

/-!
# Local key classes for one-bit differentials with output difference one

The original RFC S-box at nibble five gives an unconditional finite table
for all 16 key digits and both equal incoming-carry regimes. A full key
selects a local class using bits 20 through 23 and whether its lower 20 bits
are nonzero. The resulting list predicts one-bit input support.

The exact full-word DDT and three-round column theorems retain an explicit
acceptance hypothesis from the independently verified upper and lower bound
checkers. Local tables and representative-key comparisons alone do not
establish the prediction for every 32-bit key.
-/

open Magma.Internal Magma.CarryAutomaton Magma.MultiRoundDDT Magma.OneHotCompleteSupport

namespace Magma.OneHotKeyClasses

/-! ### 1. The local 4-bit calculation in S-box π₅

  A 1-bit input difference at j = 20 + r changes one bit of nibble 5.
  Before the first changed nibble both parallel additions have equal
  incoming carries c ∈ {0,1}. A target output difference of 1 after
  rotate-left-11 means a PRE-rotation difference of 2 at nibble 5.

  To prevent extra nonzero output nibbles, the two outgoing carries
  from nibble 5 must be equal.

  Thus for a key nibble q and an incoming carry c we seek x ∈ Fin 16
  such that

    π₅((x + q + c) mod 16)
      XOR π₅(((x XOR 2^r) + q + c) mod 16) = 2,

  and the two sums have the SAME carry-out (quotient by 16).
-/

private def sbox5Value (n : Nat) : Nat :=
  (Magma.π'arrays 5 (Fin.ofNat 16 n)).val

/-- Exact single-nibble test using the RFC 8891 S-box, not the fast tables. -/
def localOneHotStepPossible (q : Fin 16) (c : Fin 2) (r : Fin 4) : Bool :=
  (List.finRange 16).any fun x =>
    let a := x.val + q.val + c.val
    let b := Nat.xor x.val (2 ^ r.val) + q.val + c.val
    decide (a / 16 = b / 16 ∧
      Nat.xor (sbox5Value (a % 16)) (sbox5Value (b % 16)) = 2)

/-- If the lower 20 key bits are zero, only carry-in 0 is reachable.
    Otherwise both carry-in 0 and carry-in 1 are achievable by a
    suitable common choice of the lower 20 input bits. -/
def localOneHotSupportedBits (q : Fin 16) (allowCarry1 : Bool) : List (Fin 4) :=
  (List.finRange 4).filter fun r =>
    localOneHotStepPossible q 0 r ||
      (allowCarry1 && localOneHotStepPossible q 1 r)

/-! ### 2. A closed finite classification for all 16 possible key nibbles

  Lists contain positions WITHIN nibble 5, i.e. 0..3, not 20..23.
  These two tables are checked against the original π₅ by `decide`.
-/

/-- Local predicted support when the incoming carry is forced to zero. -/
def forcedZeroCarryTable (q : Fin 16) : List (Fin 4) :=
  match q.val with
  | 0 => [3]
  | 1 => [0, 2, 3]
  | 2 => [1, 2, 3]
  | 3 => [0, 1, 2, 3]
  | 4 => [2, 3]
  | 5 => [0, 3]
  | 6 => [1, 3]
  | 7 => [0, 1]
  | 8 => []
  | 9 => [0, 2]
  | 10 => [1, 2]
  | 11 => [0, 1, 2]
  | 12 => [2]
  | 13 => [0]
  | 14 => [1]
  | _ => [0, 1, 3]

/-- Local predicted support when both equal incoming carries 0/1 can occur. -/
def optionalOneCarryTable (q : Fin 16) : List (Fin 4) :=
  match q.val with
  | 0 => [0, 2, 3]
  | 1 => [0, 1, 2, 3]
  | 2 => [0, 1, 2, 3]
  | 3 => [0, 1, 2, 3]
  | 4 => [0, 2, 3]
  | 5 => [0, 1, 3]
  | 6 => [0, 1, 3]
  | 7 => [0, 1]
  | 8 => [0, 2]
  | 9 => [0, 1, 2]
  | 10 => [0, 1, 2]
  | 11 => [0, 1, 2]
  | 12 => [0, 2]
  | 13 => [0, 1]
  | 14 => [0, 1, 3]
  | _ => [0, 1, 3]

/-- Verified finite table for ALL 32 (key nibble, carry regime) classes. -/
theorem localOneHotSupportedBits_eq_tables
    (q : Fin 16) (allowCarry1 : Bool) :
    localOneHotSupportedBits q allowCarry1 =
      if allowCarry1 then optionalOneCarryTable q
      else forcedZeroCarryTable q := by
  fin_cases q <;> cases allowCarry1 <;> decide

/-! ### 3. Map a full 32-bit key into the two local invariants -/

/-- The key digit used by S-box π₅. -/
def keyNibble5 (k : V 32) : Fin 16 :=
  Fin.ofNat 16 (k.toNat / (2 ^ 20))

/-- Whether adding this key can produce carry into bit 20. -/
def canCarryIntoNibble5 (k : V 32) : Bool :=
  k.toNat % (2 ^ 20) != 0

/-- The locally predicted one-hot input support for requested output 1.
    Global equivalence requires an additional proof. -/
def predictedOneHotPositions (k : V 32) : List (Fin 32) :=
  (localOneHotSupportedBits
    (keyNibble5 k) (canCarryIntoNibble5 k)).map
      (fun r => Fin.ofNat 32 (20 + r.val))

/-! ### 4. Trust boundary: independently certify an actual 32-bit key

  Local prediction is inexpensive but, until its universal carry-path
  theorem is proved, we submit the predicted support to the independently
  verified upper and lower bound checkers.
-/

def checkPredictedOneHotSupport (k : V 32) : Bool :=
  verifyOneHotUpperBound k (1#32) (predictedOneHotPositions k) &&
  verifyOneHotLowerBound k (1#32) (predictedOneHotPositions k)

/-- A certified full-g support classification for any chosen 32-bit key.
    The Boolean hypothesis independently verifies both directions. -/
theorem checkedPredictedOneHotSupport_iff
    (k : V 32) (h : checkPredictedOneHotSupport k = true)
    (j : Fin 32) :
    0 < xorDDT_g k (BitVec.ofNat 32 (2 ^ j.val)) (1#32) ↔
      j ∈ predictedOneHotPositions k := by
  obtain ⟨hu, hl⟩ := Bool.and_eq_true_iff.mp h
  exact oneHot_g_support_iff k (1#32)
    (predictedOneHotPositions k) hu hl j

/-- The same checked support classifies entire zero-left columns of
    the three-round DDT; k₀ and k₂ are completely arbitrary. -/
theorem checkedPredictedThreeRoundColumns_iff
    (k₀ k₁ k₂ : V 32)
    (h : checkPredictedOneHotSupport k₁ = true)
    (j : Fin 32) :
    (∀ aL : V 32,
      xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
        (aL, 1#32) (0#32, BitVec.ofNat 32 (2 ^ j.val)) = 0) ↔
      j ∉ predictedOneHotPositions k₁ := by
  obtain ⟨hu, hl⟩ := Bool.and_eq_true_iff.mp h
  exact oneHot_threeRound_column_zero_iff
    k₀ k₁ k₂ (1#32) (predictedOneHotPositions k₁) hu hl j

/-- One representative from each of 16 × 2 key classes. -/
def representativeKey (q : Fin 16) (allowCarry1 : Bool) : V 32 :=
  BitVec.ofNat 32
    (q.val * (2 ^ 20) + (if allowCarry1 then 1 else 0))

end Magma.OneHotKeyClasses
