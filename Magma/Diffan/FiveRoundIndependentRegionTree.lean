module

import all Init.Data.Range.Basic
public import Magma.Diffan.FiveRoundTwoRegionJoin
public import Diffan.PriorityRegionTree

@[expose] public section

/-!
# A second, disjoint 64-base certified region and a prioritized Magma tree

For the previously fixed nonzero input/output differential, the
original 16-base cube has first base coordinate zero. This file finds
another base-only region with first coordinate ONE, consisting of a
6-dimensional 64-base bit cube in the second base coordinate.

On this new cube all reconstructed right first-difference words differ
from the fixed left first-difference word on the 3-bit mask 0x380.
This finite certificate is not deduced from the old 16-base certificate;
its 64 cases are verified independently. In particular the regions
are disjoint and the new mask needs three rather than one bit.

The candidate tree tests the known true base with zero observed bits,
then the other 15 vertices of the old cube using 0x80, then the
new independent 64-base cube using 0x380, finally full equality.
The tree is semantically exact over ALL bases, on arbitrary internal
window restrictions, for every master sharing the first five subkeys.
-/

namespace Magma.DiffanFiveRoundIndependentRegionTree

open Magma
open Magma.DiffanFiveRoundOverlappingWindows
open Magma.DiffanFiveRoundMiddleFiberMass
open Magma.DiffanFiveRoundLabelJoinDefect
open Magma.DiffanFiveRoundZeroBoundaryBaseLabel
open Magma.DiffanFiveRoundBaseDeltaLabelAudit
open Magma.DiffanFiveRoundFixedInputGraphJoin
open Magma.DiffanFiveRoundDualBoundaryGraphJoin
open Magma.DiffanFiveRoundGraphSyndrome
open Magma.DiffanFiveRoundNonemptyMaskGain
open Magma.DiffanFiveRoundPrefixKeyFamily
open Magma.DiffanFiveRoundBitCubeExactMask
open Magma.DiffanFiveRoundTwoRegionJoin

private abbrev Master :=
  V 256

private abbrev Word :=
  V 32

private abbrev RoundState :=
  Word × Word

private abbrev Point :=
  Diffan.StateDifference RoundState RoundState

/-- A six-bit index embeds in positions {0,1,2,3,6,7}, a geometric
bit-cube predicate independent of the differential syndrome. -/
def wideOffset (i : Fin 64) : Word :=
  BitVec.ofNat 32 (i.val % 16 + 64 * (i.val / 16))

/-- A second cube not overlapping the original 16-base cube. -/
def wideBase (i : Fin 64) : RoundState := ((1#32), wideOffset i)

def wideRegion (b : RoundState) : Prop :=
  ∃ i : Fin 64, b = wideBase i

/-- Observe exactly three bits, 7,8,9, of the FIRST middle difference. -/
def wideMask : RoundState := ((0x380#32), (0#32))

/-- The original cube has first base coordinate zero; the new cube
has first coordinate one. This is stronger than mere non-inclusion. -/
theorem wide_disjoint_old (i : Fin 64) (j : Fin 16) :
    wideBase i ≠ cubeBase j := by
  intro h
  have hf := congrArg Prod.fst h
  have hn : (1#32) ≠ (0#32) := by decide
  exact hn hf

/-- Even on the original true base, this new independent region is
inapplicable: the first coordinate of the true base is zero. -/
theorem wide_not_true (i : Fin 64) :
    wideBase i ≠ trueMiddle.base := by
  rw [← cube_base_zero]
  exact wide_disjoint_old i 0

/-- The first component of the reconstructed LEFT difference is 1
for every common base, a structural round-0 fact independent of S-box. -/
theorem left_first_constant (b : RoundState) :
    (reconstructed chosenMaster chosenInput b).delta.1 = (1#32) := by
  rfl

/-- A small CLOSED certificate covering 64 structured bases.
At every vertex, the reconstructed right first difference has at least
one bit from 0x380 set, while the left predicted first difference has
none. -/
theorem wide_bit_certificate (i : Fin 64) :
    ((rightReconstructed chosenMaster chosenOutput (wideBase i)).delta.1 &&&
      (0x380#32)) ≠ (0#32) := by
  revert i
  decide +kernel

/-- The independently certified 64-base region always rejects a
false join by observing only three bits of the middle difference. -/
theorem wide_region_separates (i : Fin 64) :
    maskedDifference wideMask
        (reconstructed chosenMaster chosenInput (wideBase i)) ≠
      maskedDifference wideMask
        (rightReconstructed chosenMaster chosenOutput (wideBase i)) := by
  intro h
  have hf := congrArg Prod.fst h
  change
      (reconstructed chosenMaster chosenInput (wideBase i)).delta.1 &&&
          (0x380#32) =
      (rightReconstructed chosenMaster chosenOutput (wideBase i)).delta.1 &&&
          (0x380#32) at hf
  rw [left_first_constant] at hf
  have hz : ((1#32) &&& (0x380#32)) = (0#32) := by decide
  rw [hz] at hf
  exact wide_bit_certificate i hf.symm

/-- Independent local certificate for every key in the scheduled family. -/
theorem wide_region_certificate (K : Master) (h : sameFirstFive K)
    (b : RoundState) (hb : wideRegion b)
    (hobs : maskedDifference wideMask (reconstructed K chosenInput b) =
      maskedDifference wideMask (rightReconstructed K chosenOutput b)) :
    reconstructed K chosenInput b =
      rightReconstructed K chosenOutput b := by
  obtain ⟨i, rfl⟩ := hb
  rw [reconstructed_eq K h chosenInput (wideBase i),
    rightReconstructed_eq K h chosenOutput (wideBase i)] at hobs ⊢
  exact False.elim (wide_region_separates i hobs)

/-- A genuine left four-round window whose first common base is the
first vertex of the new cube. Feistel invertibility constructs its start. -/
def wideStart : Point :=
  ⟨(GEquiv (roundKey chosenMaster (0 : Fin 32))).symm (wideBase 0),
    chosenInput⟩

theorem wide_left_base : (leftFrom chosenMaster wideStart).p₁.base = wideBase 0 := by
  change
    G (roundKey chosenMaster (0 : Fin 32))
        ((GEquiv (roundKey chosenMaster (0 : Fin 32))).symm (wideBase 0)) =
      wideBase 0
  exact (GEquiv _).apply_symm_apply (wideBase 0)

open scoped Classical in
theorem wide_left_weight_pos :
    0 <
      leftWeight chosenMaster (inputDifference chosenInput) unrestricted
        (leftFrom chosenMaster wideStart).p₁ := by
  classical
  change
    0 <
      Fintype.card
        (LeftAt chosenMaster (inputDifference chosenInput) unrestricted
          (leftFrom chosenMaster wideStart).p₁)
  apply Fintype.card_pos_iff.mpr
  exact ⟨⟨⟨leftFrom chosenMaster wideStart, ⟨rfl, trivial⟩⟩, rfl⟩⟩

/-- Real left window identifies the graph prediction at the new base. -/
theorem wide_left_graph :
    reconstructed chosenMaster chosenInput (wideBase 0) =
      (leftFrom chosenMaster wideStart).p₁ := by
  have h := (left_active_graph chosenMaster chosenInput unrestricted
    (leftFrom chosenMaster wideStart).p₁ wide_left_weight_pos).symm
  change reconstructed chosenMaster chosenInput
    (leftFrom chosenMaster wideStart).p₁.base =
    (leftFrom chosenMaster wideStart).p₁ at h
  rw [wide_left_base] at h
  exact h

/-- The right window at the new base is a real path reaching the same
fixed output difference. Only four concrete rounds are evaluated. -/
theorem wide_right_output :
    (rightFrom chosenMaster
      (rightReconstructed chosenMaster chosenOutput (wideBase 0))).p₄.delta =
      chosenOutput := by
  decide +kernel

open scoped Classical in
theorem wide_right_weight_pos :
    0 <
      rightWeight chosenMaster (outputDifference chosenOutput)
        (rightReconstructed chosenMaster chosenOutput (wideBase 0)) := by
  classical
  change
    0 <
      Fintype.card
        (RightAt chosenMaster (outputDifference chosenOutput)
          (rightReconstructed chosenMaster chosenOutput (wideBase 0)))
  apply Fintype.card_pos_iff.mpr
  exact
    ⟨⟨⟨rightFrom chosenMaster (rightReconstructed chosenMaster chosenOutput (wideBase 0)),
          wide_right_output⟩,
        rfl⟩⟩

open scoped Classical in
/-- Positive genuine left and right *conditional* weights at the new
independent base, not a fabricated positive summand. -/
theorem wide_base_weight_pos :
    0 < baseWeight chosenMaster chosenInput chosenOutput unrestricted
      (wideBase 0) := by
  classical
  change 0 < leftWeight chosenMaster (inputDifference chosenInput)
    unrestricted (reconstructed chosenMaster chosenInput (wideBase 0)) *
    rightWeight chosenMaster (outputDifference chosenOutput)
      (rightReconstructed chosenMaster chosenOutput (wideBase 0))
  rw [wide_left_graph]
  exact Nat.mul_pos wide_left_weight_pos wide_right_weight_pos

/-- Three priority branches with the SAME observation result type.
Branch 1 observes zero bits; branch 2 one bit on the old cube;
branch 3 three bits on the independent 64-base cube. -/
def stages : List (Diffan.PriorityRegionTree.Branch RoundState Point RoundState) :=
  [ ⟨provenBase, maskedDifference emptyMask⟩,
    ⟨otherCube, maskedDifference separatingMask⟩,
    ⟨wideRegion, maskedDifference wideMask⟩ ]

/-- Every local branch is semantically certified; no disjointness is
needed for correctness because branches run in priority order. -/
theorem stages_certified (K : Master) (h : sameFirstFive K) :
    Diffan.PriorityRegionTree.Certified stages
      (reconstructed K chosenInput) (rightReconstructed K chosenOutput) := by
  intro s hs b hb hobs
  have hs' :
      s = (⟨provenBase, maskedDifference emptyMask⟩ :
          Diffan.PriorityRegionTree.Branch RoundState Point RoundState) ∨
      s = (⟨otherCube, maskedDifference separatingMask⟩ :
          Diffan.PriorityRegionTree.Branch RoundState Point RoundState) ∨
      s = (⟨wideRegion, maskedDifference wideMask⟩ :
          Diffan.PriorityRegionTree.Branch RoundState Point RoundState) := by
    simpa only [stages, List.mem_cons, List.not_mem_nil, or_false] using hs
  rcases hs' with hs' | hs' | hs'
  · subst s
    change b = trueMiddle.base at hb
    subst b
    exact true_base_graphs_agree K h
  · subst s
    exact one_bit_certificate K h b hb hobs
  · subst s
    exact wide_region_certificate K h b hb hobs

/-- Priority gates of the three branches and the exact fallback.
Each next gate excludes every earlier region, even when proposed
regions overlap. -/
def firstGate : RoundState → Prop := fun _ => True

def secondGate : RoundState → Prop := fun b => firstGate b ∧ ¬provenBase b

def thirdGate : RoundState → Prop := fun b => secondGate b ∧ ¬otherCube b

def finalGate : RoundState → Prop := fun b => thirdGate b ∧ ¬wideRegion b

/-- The tree's actual weighted candidate count for arbitrary interior
restrictions R, with the full-equality fallback at unmatched bases. -/
noncomputable def treeCount (K : Master) (R : Point → Prop) : Nat := by
  classical
  exact Diffan.PriorityRegionTree.mass stages
    (reconstructed K chosenInput) (rightReconstructed K chosenOutput)
    (baseWeight K chosenInput chosenOutput R)

open scoped Classical in
/-- The entire prioritized tree exactly counts
five-round paths over the full 64-bit base space, with one master key. -/
theorem tree_exact (K : Master) (h : sameFirstFive K)
    (R : Point → Prop) :
    treeCount K R =
      Fintype.card (FiveRestricted K (inputDifference chosenInput)
        (outputDifference chosenOutput) R) := by
  classical
  unfold treeCount
  rw [Diffan.PriorityRegionTree.mass_eq_exact_of_certified
    stages (reconstructed K chosenInput) (rightReconstructed K chosenOutput)
    (baseWeight K chosenInput chosenOutput R) (stages_certified K h)]
  exact (five_exact_as_graph_mass K chosenInput chosenOutput R).symm

/-- Four disjoint rejection budgets: three fast branches and the exact
fallback. In particular, the same base is never charged to two branches. -/
noncomputable def rejectionBudgets (K : Master) (R : Point → Prop) : List Nat := by
  classical
  exact Diffan.PriorityRegionTree.rejections stages (fun _ => True)
    (reconstructed K chosenInput) (rightReconstructed K chosenOutput)
    (baseWeight K chosenInput chosenOutput R)

open scoped Classical in
/-- The rejection list has exactly three prioritized branches and one
full fallback, with no duplicate ownership of any common base. -/
theorem rejection_budgets_four (K : Master) (R : Point → Prop) :
    rejectionBudgets K R =
    [ Diffan.PriorityRegionTree.branchRejected firstGate
        (⟨provenBase, maskedDifference emptyMask⟩ :
          Diffan.PriorityRegionTree.Branch RoundState Point RoundState)
        (reconstructed K chosenInput) (rightReconstructed K chosenOutput)
        (baseWeight K chosenInput chosenOutput R),
      Diffan.PriorityRegionTree.branchRejected secondGate
        (⟨otherCube, maskedDifference separatingMask⟩ :
          Diffan.PriorityRegionTree.Branch RoundState Point RoundState)
        (reconstructed K chosenInput) (rightReconstructed K chosenOutput)
        (baseWeight K chosenInput chosenOutput R),
      Diffan.PriorityRegionTree.branchRejected thirdGate
        (⟨wideRegion, maskedDifference wideMask⟩ :
          Diffan.PriorityRegionTree.Branch RoundState Point RoundState)
        (reconstructed K chosenInput) (rightReconstructed K chosenOutput)
        (baseWeight K chosenInput chosenOutput R),
      Diffan.PriorityRegionTree.fallbackRejected finalGate
        (reconstructed K chosenInput) (rightReconstructed K chosenOutput)
        (baseWeight K chosenInput chosenOutput R) ] := by
  rfl

open scoped Classical in
/-- Exact coarse-to-true mass decomposition for the real Magma fibers. -/
theorem tree_accounting (K : Master) (h : sameFirstFive K)
    (R : Point → Prop) :
    (∑ b : RoundState, baseWeight K chosenInput chosenOutput R b) =
      Fintype.card (FiveRestricted K (inputDifference chosenInput)
        (outputDifference chosenOutput) R) +
        (rejectionBudgets K R).sum := by
  classical
  have hh := Diffan.PriorityRegionTree.coarse_eq_exact_add_rejections
    stages (reconstructed K chosenInput) (rightReconstructed K chosenOutput)
    (baseWeight K chosenInput chosenOutput R) (stages_certified K h)
  change (∑ b : RoundState, baseWeight K chosenInput chosenOutput R b) =
      Diffan.ObservedGraphJoin.exactMass (reconstructed K chosenInput)
        (rightReconstructed K chosenOutput)
        (baseWeight K chosenInput chosenOutput R) +
      (rejectionBudgets K R).sum at hh
  rw [← five_exact_as_graph_mass K chosenInput chosenOutput R] at hh
  exact hh

private theorem expand_four_rejections (total accepted a b c d : Nat)
    (h : total = accepted + [a, b, c, d].sum) : total = accepted + a + b + c + d := by
  simpa only [List.sum_cons, List.sum_nil, Nat.add_zero, Nat.add_assoc] using h

open scoped Classical in
/-- The fully expanded four-way accounting identity, matching the
mathematical leaf-by-leaf budget rather than an opaque list sum. -/
theorem tree_accounting_four (K : Master) (h : sameFirstFive K)
    (R : Point → Prop) :
    (∑ b : RoundState, baseWeight K chosenInput chosenOutput R b) =
      Fintype.card (FiveRestricted K (inputDifference chosenInput)
        (outputDifference chosenOutput) R) +
      Diffan.PriorityRegionTree.branchRejected firstGate
        (⟨provenBase, maskedDifference emptyMask⟩ :
          Diffan.PriorityRegionTree.Branch RoundState Point RoundState)
        (reconstructed K chosenInput) (rightReconstructed K chosenOutput)
        (baseWeight K chosenInput chosenOutput R) +
      Diffan.PriorityRegionTree.branchRejected secondGate
        (⟨otherCube, maskedDifference separatingMask⟩ :
          Diffan.PriorityRegionTree.Branch RoundState Point RoundState)
        (reconstructed K chosenInput) (rightReconstructed K chosenOutput)
        (baseWeight K chosenInput chosenOutput R) +
      Diffan.PriorityRegionTree.branchRejected thirdGate
        (⟨wideRegion, maskedDifference wideMask⟩ :
          Diffan.PriorityRegionTree.Branch RoundState Point RoundState)
        (reconstructed K chosenInput) (rightReconstructed K chosenOutput)
        (baseWeight K chosenInput chosenOutput R) +
      Diffan.PriorityRegionTree.fallbackRejected finalGate
        (reconstructed K chosenInput) (rightReconstructed K chosenOutput)
        (baseWeight K chosenInput chosenOutput R) := by
  classical
  have hc := tree_accounting K h R
  rw [rejection_budgets_four K R] at hc
  exact expand_four_rejections _ _ _ _ _ _ hc

open scoped Classical in
/-- A positively weighted candidate is REJECTED by the third (new)
region, and is not owned by either of the two preceding regions. -/
theorem third_branch_gain_positive (K : Master) (h : sameFirstFive K) :
    0 < Diffan.PriorityRegionTree.branchRejected
      thirdGate
      (⟨wideRegion, maskedDifference wideMask⟩ :
        Diffan.PriorityRegionTree.Branch RoundState Point RoundState)
      (reconstructed K chosenInput) (rightReconstructed K chosenOutput)
      (baseWeight K chosenInput chosenOutput unrestricted) := by
  classical
  apply Diffan.PriorityRegionTree.branch_rejected_pos_of_witness
    thirdGate
    (⟨wideRegion, maskedDifference wideMask⟩ :
      Diffan.PriorityRegionTree.Branch RoundState Point RoundState)
    (reconstructed K chosenInput) (rightReconstructed K chosenOutput)
    (baseWeight K chosenInput chosenOutput unrestricted) (wideBase 0)
  · rw [baseWeight_eq K h chosenInput chosenOutput unrestricted (wideBase 0)]
    exact wide_base_weight_pos
  · change (True ∧ ¬provenBase (wideBase 0)) ∧
      ¬otherCube (wideBase 0)
    constructor
    · constructor
      · trivial
      · intro hb
        exact wide_not_true 0 hb
    · intro hb
      obtain ⟨⟨i, hi⟩, _⟩ := hb
      exact wide_disjoint_old 0 i hi
  · exact ⟨0, rfl⟩
  · rw [reconstructed_eq K h chosenInput (wideBase 0),
      rightReconstructed_eq K h chosenOutput (wideBase 0)]
    exact wide_region_separates 0

open scoped Classical in
/-- Both the old one-bit region and the new three-bit region perform
real positive-weight rejection while a true five-round path survives. -/
theorem three_stage_nonempty_gain (K : Master) (h : sameFirstFive K) :
    0 < treeCount K unrestricted ∧
    0 < Diffan.TwoRegionCertifiedJoin.secondRejected provenBase otherCube
      (maskedDifference separatingMask)
      (reconstructed K chosenInput) (rightReconstructed K chosenOutput)
      (baseWeight K chosenInput chosenOutput unrestricted) ∧
    0 < Diffan.PriorityRegionTree.branchRejected
      thirdGate
      (⟨wideRegion, maskedDifference wideMask⟩ :
        Diffan.PriorityRegionTree.Branch RoundState Point RoundState)
      (reconstructed K chosenInput) (rightReconstructed K chosenOutput)
      (baseWeight K chosenInput chosenOutput unrestricted) := by
  constructor
  · rw [tree_exact K h unrestricted,
        fiveCount_eq K h (inputDifference chosenInput)
          (outputDifference chosenOutput) unrestricted]
    exact actual_five_round_count_positive
  constructor
  · exact second_stage_rejection_positive K h
  · exact third_branch_gain_positive K h

end Magma.DiffanFiveRoundIndependentRegionTree
