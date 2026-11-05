/-!
Magma / exact DDT counts for ALL 496 strictly ordered two-hot inputs,
with output XOR difference one. The only potentially positive pairs are
(20,21), (20,22), (20,23), (21,22), (21,23), (22,23), (23,24).

The unconditional theorem `ordered_twoHot_DDT_exact` gives a *complete*
small-four-state-DP formula for every key and every increasing pair.
No Finset of 2^32 words is evaluated. We also construct a substantially
smaller, explicit weighted two-nibble formula (`weightedSevenCount`).

IMPORTANT PROOF STATUS:
  * `ordered_twoHot_DDT_exact`: unconditional, based on the previously
    proven full-DP semantic bridge and seven-pair classification.
  * `weightedSevenCount`: precisely specified and independently tested
    against the full DP, but the quantitative fiber equivalence has
    NOT yet been established in this file. The final theorem deliberately
    takes that separate obligation as a hypothesis.

At the top of the module no existing `private` declarations are changed.
No sorry, native_decide or new axioms.
-/

import Magma.DDT.TwoHot.OutputOne.Support.OutputOneSevenSoundness

namespace Magma.TwoHotOutputOneSevenExactCounts

open Magma
open Magma.CarryAutomaton
open Magma.TwoHotOutputOneFirstActive
open Magma.TwoHotOutputOneSevenLocal
open Magma.TwoHotOutputOneSevenSoundness

private abbrev Word := V 32
private abbrev PairBits := Fin 32 × Fin 32
private abbrev Digit := Fin 16
private abbrev Carry := Fin 2

private def preRotationTarget : Word := 0x00200000#32

private theorem target_rotated : rot11 preRotationTarget = (1#32) := by
  decide +kernel

/-! ## 1. Exact numeric DP for all increasing bit-pairs -/

/-- At most seven four-state DP calculations are ever needed for a
    given key. The other 489 pairs are returned as certified zeroes. -/
def orderedTwoHotCount (k : Word) (p : PairBits) : Nat :=
  if p ∈ sevenPairs then
    carryDPCount (wordDigits k)
      (wordDigits (twoHot p.1 p.2))
      (wordDigits preRotationTarget)
  else 0

/-- COMPLETE unconditional numeric correctness for arbitrary 32-bit
    keys, restricted to the 496 canonical pairs i<j. -/
theorem ordered_twoHot_DDT_exact (k : Word) (p : PairBits)
    (hij : p.1.val < p.2.val) :
    xorDDT_g k (twoHot p.1 p.2) (1#32) =
      orderedTwoHotCount k p := by
  by_cases hp : p ∈ sevenPairs
  · have h := xorDDT_g_eq_carryMatrixCount k
      (twoHot p.1 p.2) preRotationTarget
    rw [target_rotated] at h
    rw [← carryDPCount_eq_carryMatrixCount] at h
    simpa only [orderedTwoHotCount, ite_eq_left hp] using h
  · have hz :
        xorDDT_g k (twoHot p.1 p.2) (1#32) = 0 := by
      by_contra hn
      have hpos :
          0 < xorDDT_g k (twoHot p.1 p.2) (1#32) := by omega
      exact hp (ordered_positive_implies_seven k p hij hpos)
    simpa only [orderedTwoHotCount, ite_eq_right hp] using hz

/-- The table gives the exact positive support at *each* key;
    the global seven-pair union is generally larger. -/
theorem ordered_twoHot_positive_iff_small_count
    (k : Word) (p : PairBits) (hij : p.1.val < p.2.val) :
    0 < xorDDT_g k (twoHot p.1 p.2) (1#32) ↔
      p ∈ sevenPairs ∧ 0 < orderedTwoHotCount k p := by
  rw [ordered_twoHot_DDT_exact k p hij]
  by_cases hp : p ∈ sevenPairs
  · simp only [hp, true_and]
  · simp [orderedTwoHotCount, hp]

/-! ## 2. Two closed-weight candidates: 6 same-nibble, 1 cross-nibble -/

/-- Low five key digits, treated as one 20-bit prefix.
    The carry-in to nibble 5 is 1 for precisely K of 16^5 input prefixes. -/
def prefixK (k : Word) : Nat := k.toNat % (16 ^ 5)

/-- Six pairs wholly in nibble 5: count local digits satisfying
    output difference 2 and *equal outgoing* carries. -/
def localFiveCount (q delta : Digit) (c : Carry) : Nat :=
  ((Finset.univ : Finset Digit).filter (fun x =>
    let step := sboxCarryStep (5 : Fin 8) q delta x (c,c)
    step.1 = 2 ∧ step.2.1 = step.2.2)).card

/-- The seventh pair (23,24) passes through two active nibbles.
    Nibble 5 has difference 8 and target 2. Nibble 6 has input
    difference 1 and target 0; its outgoing carries must rejoin for
    the unchanged nibble 7 to produce output zero.

    Exactly 16^2 pairs (x5,x6) are inspected for each starting carry.
    The full prefix and the free last digit are counted separately. -/
def localFiveSixCount (q5 q6 : Digit) (c : Carry) : Nat :=
  ∑ x5 : Digit, ∑ x6 : Digit,
    let st5 := sboxCarryStep (5 : Fin 8) q5 8 x5 (c,c)
    let st6 := sboxCarryStep (6 : Fin 8) q6 1 x6 st5.2
    if st5.1 = 2 ∧ st6.1 = 0 ∧ st6.2.1 = st6.2.2
    then (1 : Nat) else 0

/-- Exact proposed closed count for all seven pairs. The q5/q6 local
    digits, the 20-bit key prefix, and the free upper digits are the
    *only* inputs. It is independent of key nibble 7.

    For j<24:  16^2 * ((16^5-K)*L0 + K*L1).
    For (23,24): 16 * ((16^5-K)*C0 + K*C1). -/
def weightedSevenCount (k : Word) (p : PairBits) : Nat :=
  let K := prefixK k
  let q5 := wordDigits k (5 : Fin 8)
  if p = ((23 : Fin 32), (24 : Fin 32)) then
    let q6 := wordDigits k (6 : Fin 8)
    16 * ((16^5-K) * localFiveSixCount q5 q6 0 +
                 K * localFiveSixCount q5 q6 1)
  else
    let delta := wordDigits (twoHot p.1 p.2) (5 : Fin 8)
    256 * ((16^5-K) * localFiveCount q5 delta 0 +
                   K * localFiveCount q5 delta 1)

/-- The exact-weight function for the whole 496-entry family. -/
def proposedTwoHotClosedCount (k : Word) (p : PairBits) : Nat :=
  if p ∈ sevenPairs then weightedSevenCount k p else 0

/-- A precise statement of the SINGLE remaining semantic obligation.
    It is a quantitative fiber count, not a positivity condition.

    The next module should prove it using the already established
    20-bit prefix carry cardinalities, the local digit fibers, and
    the fact that suffixes are arbitrary once carries coincide. -/
def sevenWeightFiberBridge : Prop :=
  ∀ (k : Word) (p : PairBits), p ∈ sevenPairs →
    carryDPCount (wordDigits k)
      (wordDigits (twoHot p.1 p.2))
      (wordDigits preRotationTarget) = weightedSevenCount k p

/-- If the numeric fiber reduction is established, the closed-weight
    formula becomes the full 496-entry DDT theorem in one rewrite.
    The hypothesis remains explicit: this theorem is not yet unconditional. -/
theorem ordered_twoHot_closed_of_fiber_bridge
    (h : sevenWeightFiberBridge)
    (k : Word) (p : PairBits) (hij : p.1.val < p.2.val) :
    xorDDT_g k (twoHot p.1 p.2) (1#32) =
      proposedTwoHotClosedCount k p := by
  rw [ordered_twoHot_DDT_exact k p hij]
  by_cases hp : p ∈ sevenPairs
  · simp only [orderedTwoHotCount, proposedTwoHotClosedCount, ite_eq_left hp]
    exact h k p hp
  · simp only [orderedTwoHotCount, proposedTwoHotClosedCount,
      ite_eq_right hp]

end Magma.TwoHotOutputOneSevenExactCounts
