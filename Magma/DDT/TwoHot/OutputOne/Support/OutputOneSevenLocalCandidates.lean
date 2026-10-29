module

public import Magma.DDT.TwoHot.OutputOne.Support.OutputOneFirstActiveNibble
import all Init.Data.Range.Basic
import Magma.Carry.Automaton

@[expose] public section

/-!
Magma / two-hot input, one-hot output = 1: local reduction of 38
first-active-nibble candidates, and 7 independently certified real witnesses.

No changes to an existing `private` declaration are required.

MATHEMATICAL STATUS
-------------------
The previous module proves that 458 / 496 two-hot input differences
have zero DDT at output difference 1 for every round key. This module
investigates the 38 remaining pairs (first active nibble = 5).

The *small* local model asks for an S-box-5 transition producing nibble
output difference 2 with equal incoming carries. If there is no later
active nibble, outgoing carries must be equal. If the second active
bit is bit 24, the outgoing carries must be unequal, so that they can
cancel this bit at nibble 6. Higher second-bit positions are locally
excluded. This local test leaves exactly SEVEN pairs.

We prove all seven pairs have actual round-function witnesses, via 7
closed concrete equalities and the DDT's exact Finset membership.

IMPORTANT: `localCandidate` is a necessary-condition *model*; the bridge
that EVERY actual positive DDT entry satisfies this local model is NOT
proved in this file. No unconditional exclusion of the other 31 pairs
is claimed. The last theorem makes that premise explicit so it cannot
be mistaken for a proved cryptographic claim.

Computational checks concern only 32×32 bit-index pairs and 2×16×16
local step choices, or 7 explicit complete-word witnesses. No 2^32
DDT computation is performed.
-/

namespace Magma.TwoHotOutputOneSevenLocal

open Magma
open Magma.CarryAutomaton
open Magma.TwoHotOutputOneFirstActive

private abbrev Word :=
  V 32

private abbrev PairBits :=
  Fin 32 × Fin 32

private abbrev Witness :=
  PairBits × (Word × Word)

/-- The exact 4-bit transition in the first active input nibble (index 5).
    Lower input difference digits are zero, so its two incoming carries
    must be equal. -/
def firstActiveStep (p : PairBits) (c : Fin 2) (q x : Fin 16) :=
  sboxCarryStep (5 : Fin 8) q (wordDigits (twoHot p.1 p.2) 5)
    x (c, c)

/-- A deliberately small, locally necessary candidate test.

    The outgoing carry-pair distinction is important:
      * j<24: the rest of the input difference is zero;
      * j=24: the next input bit can compensate unequal carries;
      * j>24: a single higher bit cannot satisfy this local model.

    The next research lemma must prove soundness of the j>24 exclusion
    from actual carries; this definition alone does not assert it. -/
def localCandidate (p : PairBits) : Bool :=
  decide (relevantPair p ∧
    ∃ (c : Fin 2) (q x : Fin 16),
      (firstActiveStep p c q x).1 = 2 ∧
        (if p.2.val < 24 then
           (firstActiveStep p c q x).2.1 =
             (firstActiveStep p c q x).2.2
         else if p.2.val = 24 then
           (firstActiveStep p c q x).2.1 ≠
             (firstActiveStep p c q x).2.2
         else False))

/-- The seven locally admitted two-bit input differences. -/
def sevenPairs : Finset PairBits :=
  { (20, 21), (20, 22), (20, 23),
    (21, 22), (21, 23), (22, 23), (23, 24) }

/-- Exact finite classification of the local test, not yet a theorem
    about the full 32-bit DDT. -/
theorem localCandidate_iff_seven (p : PairBits) :
    localCandidate p = true ↔ p ∈ sevenPairs := by
  rcases p with ⟨i, j⟩
  revert i j
  decide +kernel

/-- Exactly seven of the 496 index pairs pass the small local test. -/
theorem local_candidates_card :
    ((Finset.univ : Finset PairBits).filter
      (fun p => localCandidate p = true)).card = 7 := by
  have heq : ((Finset.univ : Finset PairBits).filter
      (fun p => localCandidate p = true)) = sevenPairs := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact localCandidate_iff_seven p
  rw [heq]
  decide +kernel

/-- The other 31 of the old 38 candidates fail the small local test.
    This is deliberately a statement about the local model, NOT yet an
    unconditional universal DDT-zero theorem. -/
def otherThirtyOne : Finset PairBits :=
  ((Finset.univ : Finset PairBits).filter relevantPair) \
    sevenPairs

theorem otherThirtyOne_card : otherThirtyOne.card = 31 := by decide +kernel

/-- The finite local candidate reduction partitions the 38 pairs. -/
theorem local_seven_and_other_thirty_one :
    (sevenPairs ∪ otherThirtyOne).card = 38 := by
  decide +kernel

/-- Each row is ((i,j), (roundKey, inputWord)).
    Both key and input have at most two nonzero digits. -/
def sevenWitnesses : List Witness := [
  ((20, 21), (0x00000000#32, 0x00100000#32)),
  ((20, 22), (0x00400000#32, 0x00300000#32)),
  ((20, 23), (0x00000000#32, 0x00000000#32)),
  ((21, 22), (0x00000000#32, 0x00B00000#32)),
  ((21, 23), (0x00000000#32, 0x00500000#32)),
  ((22, 23), (0x00000000#32, 0x00400000#32)),
  ((23, 24), (0x00700000#32, 0x01700000#32))
]

/-- This checks the actual full g[k], including modular addition,
    all eight S-boxes and the output rotation, for just 7 words. -/
theorem sevenWitnesses_correct :
    sevenWitnesses.all (fun w =>
      decide (xor (g w.2.1 (xor w.2.2 (twoHot w.1.1 w.1.2)))
                  (g w.2.1 w.2.2) = (1#32))) = true := by
  decide +kernel

/-- The witness list covers every locally admitted index pair. -/
theorem sevenWitnesses_pairs :
    (sevenWitnesses.map Prod.fst).toFinset = sevenPairs := by
  decide +kernel

/-- A listed concrete solution proves positivity of the *actual* DDT. -/
theorem listed_witness_positive (w : Witness)
    (hw : w ∈ sevenWitnesses) :
    0 < xorDDT_g w.2.1 (twoHot w.1.1 w.1.2) (1#32) := by
  have hs := (List.all_eq_true.mp sevenWitnesses_correct) w hw
  have hsolution :
      xor (g w.2.1 (xor w.2.2 (twoHot w.1.1 w.1.2)))
          (g w.2.1 w.2.2) = (1#32) := by
    simpa only [decide_eq_true_eq] using hs
  unfold xorDDT_g
  apply Finset.card_pos.mpr
  refine ⟨w.2.2, ?_⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsolution⟩

/-- All seven locally admitted pairs are REALLY realizable for some
    full 32-bit round key, without any carry-model assumptions. -/
theorem seven_pairs_really_reachable (p : PairBits)
    (hp : p ∈ sevenPairs) :
    ∃ k : Word, 0 < xorDDT_g k (twoHot p.1 p.2) (1#32) := by
  have hm : p ∈ (sevenWitnesses.map Prod.fst).toFinset := by
    rw [sevenWitnesses_pairs]
    exact hp
  have hml : p ∈ sevenWitnesses.map Prod.fst :=
    List.mem_toFinset.mp hm
  obtain ⟨w, hw, hwp⟩ := List.mem_map.mp hml
  refine ⟨w.2.1, ?_⟩
  have hpos := listed_witness_positive w hw
  cases w with
  | mk wp data =>
    dsimp only at hwp
    subst wp
    exact hpos

open scoped Classical

/-- The full 496-pair union of possible transitions already contains
    at least these seven concrete pairs. -/
theorem seven_pairs_subset_realizable :
    sevenPairs ⊆
      ((Finset.univ : Finset PairBits).filter (fun p =>
        p.1.val < p.2.val ∧ ∃ k : Word, 0 < xorDDT_g k (twoHot p.1 p.2) (1#32))) := by
  intro p hp
  have hpair : p.1.val < p.2.val := by
    have hc := (localCandidate_iff_seven p).mpr hp
    exact (of_decide_eq_true hc).1.1
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, hpair, seven_pairs_really_reachable p hp⟩

/-- This states the ONE missing direction transparently.
    Once local soundness for full 8-nibble carry paths is established,
    `sevenPairs` becomes the complete universal support.
    There is no hidden `sorry` or assumption in the preceding theorems. -/
theorem complete_universal_support_of_local_soundness
    (hsound : ∀ (k : Word) (p : PairBits),
      p.1.val < p.2.val → 0 < xorDDT_g k (twoHot p.1 p.2) (1#32) →
        localCandidate p = true) :
    ((Finset.univ : Finset PairBits).filter (fun p =>
      p.1.val < p.2.val ∧ ∃ k : Word, 0 < xorDDT_g k (twoHot p.1 p.2) (1#32))) =
      sevenPairs := by
  ext p
  constructor
  · intro hp
    obtain ⟨hpair, k, hk⟩ := (Finset.mem_filter.mp hp).2
    exact (localCandidate_iff_seven p).mp (hsound k p hpair hk)
  · intro hp
    exact seven_pairs_subset_realizable hp

end Magma.TwoHotOutputOneSevenLocal
