module

public import Magma.Composition.MultiRoundDDT
import all Init.Data.Range.Basic

@[expose] public section

/-!
# Sound domain pruning

Local domains, bit and grouped rotation-wiring consistency, preservation of
solutions, fixed-point bounds and empty-domain impossibility criteria.
-/

open Magma.Internal Magma.GProperties Magma.CarryAutomaton Magma.MultiRoundDDT

namespace Magma.Pruning

-- This is SOUND, deliberately INCOMPLETE domain filtering:
-- every globally feasible two-carry path has locally feasible nibble
-- transitions, but local feasibility does not imply a global path.

/-- A single S-box/nibble differential can be realized with SOME pair
    of incoming carries, SOME pair of outgoing carries, and SOME input digit.
    This is an inexpensive necessary condition for a complete carry path. -/
def nibbleTransitionPossible
    (i : Fin 8) (key diff target : Fin 16) : Bool :=
  decide (∃ s t : CarryState, ∃ x : Fin 16,
    sboxCarryStep i key diff x s = (target, t))

/-- Soundness of local nibble feasibility for a globally accepted
    Boolean carry path.  The proof uses the previously verified
    equality between the path count and the carry matrix count,
    and extracts ONE concrete accepted input. -/
theorem carryHasPathBoolean_implies_local
    (k d out : V 32)
    (h : carryHasPathBoolean (wordDigits k) (wordDigits d)
      (wordDigits out) = true)
    (i : Fin 8) :
    nibbleTransitionPossible i (wordDigits k i)
      (wordDigits d i) (wordDigits out i) = true := by
  have hp : 0 < carryWordCount k d out := by
    rw [carryWordCount_eq_carryMatrixCount]
    exact (carryHasPath_iff_count_pos _ _ _).mp
      ((carryHasPathBoolean_iff _ _ _).mp h)
  unfold carryWordCount at hp
  obtain ⟨x, hx⟩ := (Finset.card_pos.mp hp)
  have haccept :
      (carryTrace (wordDigits k) (wordDigits d)
        (wordDigits out) (wordDigits x)).2 = true :=
    (Finset.mem_filter.mp hx).2
  have hdiff :
      localSBoxDifference k d x i = wordDigits out i :=
    (localSBoxDifference_eq_iff k d out x i).mpr
      ((carryTrace_iff_nibbleDifferences k d out x).mp haccept i)
  have hstep := sboxCarryStep_word_correct k d x i
  have hlocal :
      ∃ s t : CarryState, ∃ z : Fin 16,
        sboxCarryStep i (wordDigits k i) (wordDigits d i) z s =
          (wordDigits out i, t) := by
    refine ⟨wordCarryPair k d x i.val,
      wordCarryPair k d x (i.val + 1), wordDigits x i, ?_⟩
    calc
      sboxCarryStep i (wordDigits k i) (wordDigits d i)
          (wordDigits x i) (wordCarryPair k d x i.val) =
        (localSBoxDifference k d x i,
          wordCarryPair k d x (i.val + 1)) := hstep
      _ = (wordDigits out i, wordCarryPair k d x (i.val + 1)) := by
        rw [hdiff]
  exact (decide_eq_true_eq).mpr hlocal

/-- Possible pre-rotation output digits for a fixed input difference.
    Computed using only 16 candidates and the four carry states. -/
def outputDigitDomain (i : Fin 8) (key diff : Fin 16) : Finset (Fin 16) :=
  (Finset.univ : Finset (Fin 16)).filter
    (fun target => nibbleTransitionPossible i key diff target = true)

/-- Possible input-difference digits for a fixed required output digit. -/
def inputDiffDigitDomain (i : Fin 8) (key target : Fin 16) : Finset (Fin 16) :=
  (Finset.univ : Finset (Fin 16)).filter
    (fun diff => nibbleTransitionPossible i key diff target = true)

/-- A relaxed, nibble-local approximation of the coupled two-automaton
    problem.  It keeps the EXACT 11-bit rotation/XOR wiring, but replaces
    each global carry path by necessary per-nibble feasibility conditions.

    Every solution of `jointCarryConstraint` satisfies this predicate;
    the reverse implication is NOT asserted. -/
def locallyPrunedJointConstraint
    (k₀ k₁ aL aR bL : V 32)
    (c y : Fin 8 → Fin 16) : Prop :=
  jointRotationWiring aL c y ∧
  (∀ i : Fin 8,
    y i ∈ outputDigitDomain i (wordDigits k₀ i) (wordDigits aR i)) ∧
  (∀ i : Fin 8,
    c i ∈ inputDiffDigitDomain i (wordDigits k₁ i)
      (wordDigits ((xor bL aR).rotateRight 11) i))

/-- Both complete carry automata imply their corresponding local
    nibble-domain constraints.  This is the soundness theorem for
    the first stage of constraint propagation. -/
theorem jointCarryConstraint_implies_localDomains
    (k₀ k₁ aL aR bL : V 32)
    (c y : Fin 8 → Fin 16)
    (h : jointCarryConstraint k₀ k₁ aL aR bL c y) :
    locallyPrunedJointConstraint k₀ k₁ aL aR bL c y := by
  rcases h with ⟨hw, hf, hs⟩
  refine ⟨hw, ?_, ?_⟩
  · intro i
    have hf' :
        carryHasPathBoolean (wordDigits k₀) (wordDigits aR)
          (wordDigits (packDigits y)) = true := by
      exact (congrArg
        (fun ds : Fin 8 → Fin 16 =>
          carryHasPathBoolean (wordDigits k₀) (wordDigits aR) ds)
        (wordDigitsEquiv.right_inv y)).trans hf
    have hloc := carryHasPathBoolean_implies_local
      k₀ aR (packDigits y) hf' i
    have hy : wordDigits (packDigits y) i = y i :=
      congrArg (fun ds : Fin 8 → Fin 16 => ds i)
        (wordDigitsEquiv.right_inv y)
    rw [hy] at hloc
    change y i ∈ (Finset.univ : Finset (Fin 16)).filter
      (fun target => nibbleTransitionPossible i
        (wordDigits k₀ i) (wordDigits aR i) target = true)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hloc⟩
  · intro i
    have hs' :
        carryHasPathBoolean (wordDigits k₁)
          (wordDigits (packDigits c))
          (wordDigits ((xor bL aR).rotateRight 11)) = true := by
      exact (congrArg
        (fun ds : Fin 8 → Fin 16 =>
          carryHasPathBoolean (wordDigits k₁) ds
            (wordDigits ((xor bL aR).rotateRight 11)))
        (wordDigitsEquiv.right_inv c)).trans hs
    have hloc := carryHasPathBoolean_implies_local
      k₁ (packDigits c) ((xor bL aR).rotateRight 11) hs' i
    have hc : wordDigits (packDigits c) i = c i :=
      congrArg (fun ds : Fin 8 → Fin 16 => ds i)
        (wordDigitsEquiv.right_inv c)
    rw [hc] at hloc
    change c i ∈ (Finset.univ : Finset (Fin 16)).filter
      (fun diff => nibbleTransitionPossible i
        (wordDigits k₁ i) diff
        (wordDigits ((xor bL aR).rotateRight 11) i) = true)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hloc⟩

/-- A certificate that the RELAXED local-domain/wiring CSP has no
    solution is sufficient to rule out the exact three-round difference.
    It is not necessary: the relaxed CSP can admit spurious paths. -/
theorem xorDDT_rounds_three_zero_of_no_localDomains
    (k₀ k₁ k₂ aL aR bL bR : V 32)
    (hno : ¬ ∃ c y : Fin 8 → Fin 16,
      locallyPrunedJointConstraint k₀ k₁ aL aR bL c y) :
    xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
      (aL, aR) (bL, bR) = 0 := by
  apply xorDDT_rounds_three_zero_of_no_joint_constraint
    k₀ k₁ k₂ aL aR bL bR
  rintro ⟨c, y, hjoint⟩
  exact hno ⟨c, y,
    jointCarryConstraint_implies_localDomains
      k₀ k₁ aL aR bL c y hjoint⟩

/-- A certificate purely about the 4-bit domains and fixed rotation
    wiring suffices for an impossible three-round XOR differential.

    The premise is intended to be discharged by a symbolic CSP/SAT solver:
    it contains no carry-path folds or 32-bit DDT computations. -/
theorem xorDDT_rounds_three_zero_of_domain_wiring_conflict
    (k₀ k₁ k₂ aL aR bL bR : V 32)
    (hconflict : ∀ c y : Fin 8 → Fin 16,
      (∀ i : Fin 8,
        y i ∈ outputDigitDomain i (wordDigits k₀ i) (wordDigits aR i)) →
      (∀ i : Fin 8,
        c i ∈ inputDiffDigitDomain i (wordDigits k₁ i)
          (wordDigits ((xor bL aR).rotateRight 11) i)) →
      ¬ jointRotationWiring aL c y) :
    xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
      (aL, aR) (bL, bR) = 0 := by
  apply xorDDT_rounds_three_zero_of_no_localDomains
    k₀ k₁ k₂ aL aR bL bR
  rintro ⟨c, y, hw, hfirst, hsecond⟩
  exact (hconflict c y hfirst hsecond) hw

/-- Absolute bit position corresponding to digit `i` and its local bit `r`. -/
def bitPos (i : Fin 8) (r : Fin 4) : Fin 32 :=
  ⟨4 * i.val + r.val, by omega⟩

/-- Digit containing the given absolute bit. -/
def digitAt (j : Fin 32) : Fin 8 :=
  ⟨j.val / 4, by omega⟩

/-- Offset of an absolute bit within its four-bit digit. -/
def offsetAt (j : Fin 32) : Fin 4 :=
  ⟨j.val % 4, by omega⟩

private theorem digitAt_bitPos (i : Fin 8) (r : Fin 4) : digitAt (bitPos i r) = i := by
  apply Fin.ext
  change (4 * i.val + r.val) / 4 = i.val
  omega

private theorem offsetAt_bitPos (i : Fin 8) (r : Fin 4) : offsetAt (bitPos i r) = r := by
  apply Fin.ext
  change (4 * i.val + r.val) % 4 = r.val
  omega

private theorem bitPos_digitAt_offsetAt (j : Fin 32) : bitPos (digitAt j) (offsetAt j) = j := by
  apply Fin.ext
  change 4 * (j.val / 4) + j.val % 4 = j.val
  omega

/-- A bit of a packed word is precisely the matching bit of its digit.
    This lemma is proved through the existing digit equivalence rather
    than computing the eight-way concatenation. -/
private theorem component_packDigits (ds : Fin 8 → Fin 16) (j : Fin 32) :
    component (packDigits ds) j =
      component (BitVec.ofFin (ds (digitAt j))) (offsetAt j) := by
  let i := digitAt j
  let r := offsetAt j
  have hrec : wordDigits (packDigits ds) = ds :=
    wordDigitsEquiv.right_inv ds
  have hval : (nibble (packDigits ds) i).toFin = ds i :=
    congrArg (fun f : Fin 8 → Fin 16 => f i) hrec
  have hword : nibble (packDigits ds) i = BitVec.ofFin (ds i) := by
    apply BitVec.eq_of_toFin_eq
    simpa only [BitVec.toFin_ofFin] using hval
  have hsub : component (nibble (packDigits ds) i) r =
      component (packDigits ds) (bitPos i r) := by
    exact substring_components_are_string_components
      (packDigits ds) (4 * i.val) 4 (by omega) r
  have hj : bitPos i r = j := by
    simpa only [i, r] using bitPos_digitAt_offsetAt j
  calc
    component (packDigits ds) j =
        component (nibble (packDigits ds) i) r := by
      rw [← hj]
      exact hsub.symm
    _ = component (BitVec.ofFin (ds i)) r :=
      congrArg (fun z : V 4 => component z r) hword

/-- A single source/output bit and destination/intermediate bit satisfy
    the fixed rotation and XOR wiring. Only two local 4-bit values occur. -/
abbrev compatibleBit (aL : V 32)
    (src dst : Fin 32) (yd cd : Fin 16) : Prop :=
  component (BitVec.ofFin yd) (offsetAt src) =
    Bool.xor (component (BitVec.ofFin cd) (offsetAt dst))
      (component aL dst)

/-- Remove each output nibble value lacking support for at least one
    of its four bits in the corresponding intermediate-difference domain.
    The destination nibble depends on the rotated bit position. -/
def pruneOutputBits (aL : V 32)
    (Y C : Fin 8 → Finset (Fin 16)) (i : Fin 8) : Finset (Fin 16) :=
  (Y i).filter (fun yd =>
    ∀ r : Fin 4,
      ∃ cd ∈ C (digitAt (bitPos i r + 11)),
        compatibleBit aL (bitPos i r) (bitPos i r + 11) yd cd)

/-- Symmetric pruning for the intermediate-difference nibble values.
    Every output bit must be supported by a nibble in the other domain. -/
def pruneIntermediateBits (aL : V 32)
    (Y C : Fin 8 → Finset (Fin 16)) (i : Fin 8) : Finset (Fin 16) :=
  (C i).filter (fun cd =>
    ∀ r : Fin 4,
      ∃ yd ∈ Y (digitAt (bitPos i r - 11)),
        compatibleBit aL (bitPos i r - 11) (bitPos i r) yd cd)

/-- One simultaneous pruning step never deletes any assignment obeying
    the exact 32-bit rotation wiring and the old domain constraints. -/
theorem bitPruning_sound (aL : V 32)
    (Y C : Fin 8 → Finset (Fin 16))
    (c y : Fin 8 → Fin 16)
    (hw : jointRotationWiring aL c y)
    (hy : ∀ i, y i ∈ Y i)
    (hc : ∀ i, c i ∈ C i) :
    (∀ i, y i ∈ pruneOutputBits aL Y C i) ∧
    (∀ i, c i ∈ pruneIntermediateBits aL Y C i) := by
  have hwbits := (jointRotationWiring_iff_bits aL c y).mp hw
  constructor
  · intro i
    apply Finset.mem_filter.mpr
    refine ⟨hy i, ?_⟩
    intro r
    let src := bitPos i r
    let dst := src + 11
    refine ⟨c (digitAt dst), hc (digitAt dst), ?_⟩
    have hb := hwbits src
    rw [component_packDigits y src,
        component_packDigits c dst] at hb
    change
      compatibleBit aL src dst
        (y (digitAt src)) (c (digitAt dst)) at hb
    simpa only [src, dst, digitAt_bitPos] using hb

  · intro i
    apply Finset.mem_filter.mpr
    refine ⟨hc i, ?_⟩
    intro r
    let dst := bitPos i r
    let src := dst - 11
    refine ⟨y (digitAt src), hy (digitAt src), ?_⟩
    have hb := hwbits src
    have hdst : src + 11 = dst := by
      dsimp [src]
      simp
    rw [hdst] at hb
    rw [component_packDigits y src,
        component_packDigits c dst] at hb
    change
      compatibleBit aL src dst
        (y (digitAt src)) (c (digitAt dst)) at hb
    simpa only [src, dst, digitAt_bitPos] using hb

/-- The nibble domains supplied by the previously verified local pruning. -/
private def firstLocalDomains (k₀ aR : V 32)
    (i : Fin 8) : Finset (Fin 16) :=
  outputDigitDomain i (wordDigits k₀ i) (wordDigits aR i)

private def secondLocalDomains (k₁ aR bL : V 32) (i : Fin 8) : Finset (Fin 16) :=
  inputDiffDigitDomain i (wordDigits k₁ i) (wordDigits ((xor bL aR).rotateRight 11) i)

/-- A stronger, still sound necessary condition for coupled carry paths. -/
def bitPrunedJointConstraint
    (k₀ k₁ aL aR bL : V 32)
    (c y : Fin 8 → Fin 16) : Prop :=
  jointRotationWiring aL c y ∧
  (∀ i, y i ∈ pruneOutputBits aL
    (firstLocalDomains k₀ aR) (secondLocalDomains k₁ aR bL) i) ∧
  (∀ i, c i ∈ pruneIntermediateBits aL
    (firstLocalDomains k₀ aR) (secondLocalDomains k₁ aR bL) i)

/-- Any solution of the original locally relaxed CSP survives bit pruning. -/
theorem locallyPruned_implies_bitPruned
    (k₀ k₁ aL aR bL : V 32)
    (c y : Fin 8 → Fin 16)
    (h : locallyPrunedJointConstraint k₀ k₁ aL aR bL c y) :
    bitPrunedJointConstraint k₀ k₁ aL aR bL c y := by
  rcases h with ⟨hw, hy, hc⟩
  refine ⟨hw, ?_⟩
  exact bitPruning_sound aL
    (firstLocalDomains k₀ aR) (secondLocalDomains k₁ aR bL)
    c y hw hy hc

/-- A single empty pruned domain certifies that the three-round
    fixed-key differential is impossible. No enumeration of 32-bit
    intermediate differences is needed. -/
theorem xorDDT_rounds_three_zero_of_empty_bit_domain
    (k₀ k₁ k₂ aL aR bL bR : V 32)
    (hconf :
      (∃ i : Fin 8, pruneOutputBits aL
        (firstLocalDomains k₀ aR) (secondLocalDomains k₁ aR bL) i = ∅) ∨
      (∃ i : Fin 8, pruneIntermediateBits aL
        (firstLocalDomains k₀ aR) (secondLocalDomains k₁ aR bL) i = ∅)) :
    xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
      (aL, aR) (bL, bR) = 0 := by
  apply xorDDT_rounds_three_zero_of_no_localDomains
    k₀ k₁ k₂ aL aR bL bR
  rintro ⟨c, y, hlocal⟩
  have hp := locallyPruned_implies_bitPruned
    k₀ k₁ aL aR bL c y hlocal
  rcases hconf with ⟨i, hempty⟩ | ⟨i, hempty⟩
  · have hm := hp.2.1 i
    rw [hempty] at hm
    exact Finset.notMem_empty _ hm
  · have hm := hp.2.2 i
    rw [hempty] at hm
    exact Finset.notMem_empty _ hm

-- We formalize sound iteration, shrinking domains, and
-- an impossible-differential certificate; but NOT claim that
-- a particular fixed number of passes has reached a fixed point.

/-- A family of eight four-bit domains. -/
private abbrev BitDigitDomains := Fin 8 → Finset (Fin 16)

/-- Output domains of the first automaton and input-difference domains
    of the second automaton. -/
private abbrev BitDomainPair := BitDigitDomains × BitDigitDomains

/-- One *simultaneous* pass: both new domain families are computed
    using the old domains, not an in-place sequential update. -/
def pruneBitDomainPair (aL : V 32) (D : BitDomainPair) : BitDomainPair :=
  (fun i => pruneOutputBits aL D.1 D.2 i,
   fun i => pruneIntermediateBits aL D.1 D.2 i)

/-- Perform `n` passes of sound bit-domain pruning. -/
def iterateBitPruning (aL : V 32) (D : BitDomainPair) :
    Nat → BitDomainPair
  | 0 => D
  | n + 1 => pruneBitDomainPair aL (iterateBitPruning aL D n)

/-- A single pruning pass only removes digit values. -/
theorem pruneBitDomainPair_subset
    (aL : V 32) (D : BitDomainPair) :
    (∀ i, (pruneBitDomainPair aL D).1 i ⊆ D.1 i) ∧
    (∀ i, (pruneBitDomainPair aL D).2 i ⊆ D.2 i) := by
  constructor
  · intro i v hv
    exact (Finset.mem_filter.mp hv).1
  · intro i v hv
    exact (Finset.mem_filter.mp hv).1

/-- Domains cannot grow between consecutive passes. -/
theorem iterateBitPruning_succ_subset
    (aL : V 32) (D : BitDomainPair) (n : Nat) :
    (∀ i, (iterateBitPruning aL D (n + 1)).1 i ⊆
      (iterateBitPruning aL D n).1 i) ∧
    (∀ i, (iterateBitPruning aL D (n + 1)).2 i ⊆
      (iterateBitPruning aL D n).2 i) := by
  exact pruneBitDomainPair_subset aL (iterateBitPruning aL D n)

/-- Every assignment satisfying the exact rotation wiring and the
    initial nibble domains survives *any* number of passes. -/
theorem iterateBitPruning_sound
    (aL : V 32) (D : BitDomainPair)
    (c y : Fin 8 → Fin 16)
    (hw : jointRotationWiring aL c y)
    (hy : ∀ i, y i ∈ D.1 i)
    (hc : ∀ i, c i ∈ D.2 i) :
    ∀ n : Nat,
      (∀ i, y i ∈ (iterateBitPruning aL D n).1 i) ∧
      (∀ i, c i ∈ (iterateBitPruning aL D n).2 i) := by
  intro n
  induction n with
  | zero =>
      exact ⟨hy, hc⟩
  | succ n ih =>
      exact bitPruning_sound aL
        (iterateBitPruning aL D n).1
        (iterateBitPruning aL D n).2
        c y hw ih.1 ih.2

/-- The two domain families used by the first local relaxation. -/
def initialBitDomains
    (k₀ k₁ aR bL : V 32) : BitDomainPair :=
  (firstLocalDomains k₀ aR, secondLocalDomains k₁ aR bL)

/-- A relaxation obtained after `n` iterations of bit arc pruning. -/
def iteratedBitPrunedJointConstraint
    (k₀ k₁ aL aR bL : V 32) (n : Nat)
    (c y : Fin 8 → Fin 16) : Prop :=
  jointRotationWiring aL c y ∧
  (∀ i, y i ∈
    (iterateBitPruning aL (initialBitDomains k₀ k₁ aR bL) n).1 i) ∧
  (∀ i, c i ∈
    (iterateBitPruning aL (initialBitDomains k₀ k₁ aR bL) n).2 i)

/-- Pruning for any number of passes preserves every solution of the
    previously verified nibble-local CSP. -/
theorem locallyPruned_implies_iteratedBitPruned
    (k₀ k₁ aL aR bL : V 32)
    (c y : Fin 8 → Fin 16) (n : Nat)
    (h : locallyPrunedJointConstraint k₀ k₁ aL aR bL c y) :
    iteratedBitPrunedJointConstraint k₀ k₁ aL aR bL n c y := by
  rcases h with ⟨hw, hy, hc⟩
  have hkeep := iterateBitPruning_sound
    aL (initialBitDomains k₀ k₁ aR bL) c y
    hw hy hc n
  exact ⟨hw, hkeep.1, hkeep.2⟩

/-- In particular every *real* coupled pair of carry paths survives
    arbitrary iterations of this relaxation. -/
theorem jointCarryConstraint_implies_iteratedBitPruned
    (k₀ k₁ aL aR bL : V 32)
    (c y : Fin 8 → Fin 16) (n : Nat)
    (h : jointCarryConstraint k₀ k₁ aL aR bL c y) :
    iteratedBitPrunedJointConstraint k₀ k₁ aL aR bL n c y := by
  exact locallyPruned_implies_iteratedBitPruned
    k₀ k₁ aL aR bL c y n
    (jointCarryConstraint_implies_localDomains
      k₀ k₁ aL aR bL c y h)

/-- An empty domain after ANY number of pruning passes is a sound
    certificate of an impossible fixed-key three-round XOR difference.
    No enumeration of 32-bit words is needed in the proof. -/
theorem xorDDT_rounds_three_zero_of_empty_iteratedBitDomain
    (k₀ k₁ k₂ aL aR bL bR : V 32) (n : Nat)
    (hconf :
      (∃ i : Fin 8,
        (iterateBitPruning aL
          (initialBitDomains k₀ k₁ aR bL) n).1 i = ∅) ∨
      (∃ i : Fin 8,
        (iterateBitPruning aL
          (initialBitDomains k₀ k₁ aR bL) n).2 i = ∅)) :
    xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
      (aL, aR) (bL, bR) = 0 := by
  apply xorDDT_rounds_three_zero_of_no_localDomains
    k₀ k₁ k₂ aL aR bL bR
  rintro ⟨c, y, hlocal⟩
  have hp := locallyPruned_implies_iteratedBitPruned
    k₀ k₁ aL aR bL c y n hlocal
  rcases hp with ⟨_, hy, hc⟩
  rcases hconf with ⟨i, hempty⟩ | ⟨i, hempty⟩
  · have hm := hy i
    rw [hempty] at hm
    exact (Finset.notMem_empty (y i)) hm
  · have hm := hc i
    rw [hempty] at hm
    exact (Finset.notMem_empty (c i)) hm

/-- If an iteration is stable, all later iterations remain stable.
    This statement does not assert that a given bound already stabilizes. -/
theorem iterateBitPruning_stays_fixed
    (aL : V 32) (D : BitDomainPair) (n : Nat)
    (hfix : iterateBitPruning aL D (n + 1) =
      iterateBitPruning aL D n) :
    ∀ m : Nat,
      iterateBitPruning aL D (n + m) =
        iterateBitPruning aL D n := by
  intro m
  induction m with
  | zero =>
      rfl
  | succ m ih =>
      calc
        iterateBitPruning aL D (n + (m + 1)) =
            pruneBitDomainPair aL
              (iterateBitPruning aL D (n + m)) := by
                rw [Nat.add_succ]
                rfl
        _ = pruneBitDomainPair aL
              (iterateBitPruning aL D n) := by rw [ih]
        _ = iterateBitPruning aL D (n + 1) := rfl
        _ = iterateBitPruning aL D n := hfix

--- 256 passes convergence

/-- The total number of remaining four-bit values in the two families
    of eight domains.  This is a natural-valued termination measure. -/
private def bitDomainMass (D : BitDomainPair) : Nat :=
  ∑ i : Fin 8, ((D.1 i).card + (D.2 i).card)

/-- Componentwise containment implies a nonincreasing mass. -/
private theorem bitDomainMass_le (D E : BitDomainPair)
    (hY : ∀ i, D.1 i ⊆ E.1 i)
    (hC : ∀ i, D.2 i ⊆ E.2 i) :
    bitDomainMass D ≤ bitDomainMass E := by
  unfold bitDomainMass
  apply Finset.sum_le_sum
  intro i _
  exact Nat.add_le_add
    (Finset.card_le_card (hY i))
    (Finset.card_le_card (hC i))

/-- If every domain only shrinks, equal total cardinality forces
    equality of all 16 domains. -/
private theorem bitDomainPair_eq_of_mass_eq (D E : BitDomainPair)
    (hY : ∀ i, D.1 i ⊆ E.1 i)
    (hC : ∀ i, D.2 i ⊆ E.2 i)
    (hsize : bitDomainMass D = bitDomainMass E) : D = E := by
  have hpoint : ∀ i : Fin 8,
      (D.1 i).card + (D.2 i).card =
        (E.1 i).card + (E.2 i).card := by
    have hle : ∀ i ∈ (Finset.univ : Finset (Fin 8)),
        (D.1 i).card + (D.2 i).card ≤
          (E.1 i).card + (E.2 i).card := by
      intro i _
      exact Nat.add_le_add
        (Finset.card_le_card (hY i))
        (Finset.card_le_card (hC i))
    unfold bitDomainMass at hsize
    have hs := (Finset.sum_eq_sum_iff_of_le hle).mp hsize
    intro i
    exact hs i (Finset.mem_univ i)
  apply Prod.ext
  · funext i
    apply Finset.eq_of_subset_of_card_le (hY i)
    have heq := hpoint i
    have hc := Finset.card_le_card (hC i)
    omega
  · funext i
    apply Finset.eq_of_subset_of_card_le (hC i)
    have heq := hpoint i
    have hy := Finset.card_le_card (hY i)
    omega

/-- A pass which actually changes the domains strictly decreases
    their total cardinality. -/
private theorem bitDomainMass_prune_lt_of_ne (aL : V 32)
    (D : BitDomainPair)
    (hne : pruneBitDomainPair aL D ≠ D) :
    bitDomainMass (pruneBitDomainPair aL D) < bitDomainMass D := by
  obtain ⟨hY, hC⟩ := pruneBitDomainPair_subset aL D
  have hle := bitDomainMass_le
    (pruneBitDomainPair aL D) D hY hC
  have hneq : bitDomainMass (pruneBitDomainPair aL D) ≠
      bitDomainMass D := by
    intro hmass
    exact hne (bitDomainPair_eq_of_mass_eq
      (pruneBitDomainPair aL D) D hY hC hmass)
  omega

/-- There are at most 8 * 16 * 2 = 256 values across all domains. -/
private theorem bitDomainMass_le_256 (D : BitDomainPair) :
    bitDomainMass D ≤ 256 := by
  have hbound (i : Fin 8) :
      (D.1 i).card + (D.2 i).card ≤ 32 := by
    have hY : (D.1 i).card ≤ 16 := by
      have h := Finset.card_le_card (Finset.subset_univ (D.1 i))
      simpa using h
    have hC : (D.2 i).card ≤ 16 := by
      have h := Finset.card_le_card (Finset.subset_univ (D.2 i))
      simpa using h
    omega
  calc
    bitDomainMass D =
        ∑ i : Fin 8, ((D.1 i).card + (D.2 i).card) := rfl
    _ ≤ ∑ _i : Fin 8, (32 : Nat) := by
      apply Finset.sum_le_sum
      intro i _
      exact hbound i
    _ = 256 := by norm_num

/-- Moving the first pruning pass from the iteration count into the
    initial state.  Proved once, without opening any nibble filters. -/
private theorem iterateBitPruning_shift (aL : V 32)
    (D : BitDomainPair) (n : Nat) :
    iterateBitPruning aL D (n + 1) =
      iterateBitPruning aL (pruneBitDomainPair aL D) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      calc
        iterateBitPruning aL D ((n + 1) + 1) =
            pruneBitDomainPair aL (iterateBitPruning aL D (n + 1)) := rfl
        _ = pruneBitDomainPair aL
              (iterateBitPruning aL (pruneBitDomainPair aL D) n) := by
              rw [ih]
        _ = iterateBitPruning aL
              (pruneBitDomainPair aL D) (n + 1) := rfl

/-- Abstract countdown argument specialized to our previously proved
    strictly decreasing measure.  At most `n` passes are needed if the
    initial mass is at most `n`. -/
private theorem iterateBitPruning_stable_of_mass (aL : V 32) :
    ∀ n : Nat, ∀ D : BitDomainPair,
      bitDomainMass D ≤ n →
      iterateBitPruning aL D (n + 1) =
        iterateBitPruning aL D n := by
  intro n
  induction n with
  | zero =>
      intro D hbound
      by_cases hfix : pruneBitDomainPair aL D = D
      · exact hfix
      · have hdrop := bitDomainMass_prune_lt_of_ne aL D hfix
        omega
  | succ n ih =>
      intro D hbound
      by_cases hfix : pruneBitDomainPair aL D = D
      · have hbase : iterateBitPruning aL D (0 + 1) =
            iterateBitPruning aL D 0 := hfix
        have hstay := iterateBitPruning_stays_fixed aL D 0 hbase
        calc
          iterateBitPruning aL D ((n + 1) + 1) =
              iterateBitPruning aL D 0 := by
                simpa only [Nat.zero_add] using hstay ((n + 1) + 1)
          _ = iterateBitPruning aL D (n + 1) := by
                simpa only [Nat.zero_add] using (hstay (n + 1)).symm
      · have hdrop := bitDomainMass_prune_lt_of_ne aL D hfix
        have hsmaller : bitDomainMass (pruneBitDomainPair aL D) ≤ n := by
          omega
        calc
          iterateBitPruning aL D ((n + 1) + 1) =
              iterateBitPruning aL (pruneBitDomainPair aL D) (n + 1) :=
                iterateBitPruning_shift aL D (n + 1)
          _ = iterateBitPruning aL (pruneBitDomainPair aL D) n :=
                ih (pruneBitDomainPair aL D) hsmaller
          _ = iterateBitPruning aL D (n + 1) :=
                (iterateBitPruning_shift aL D n).symm

/-- The 256th pruning result is a genuine fixed point. -/
theorem iterateBitPruning_fixed_256 (aL : V 32)
    (D : BitDomainPair) :
    iterateBitPruning aL D (256 + 1) =
      iterateBitPruning aL D 256 := by
  exact iterateBitPruning_stable_of_mass aL 256 D
    (bitDomainMass_le_256 D)

/-- The result of the certified, bounded propagation procedure. -/
def bitPruningFixed (aL : V 32) (D : BitDomainPair) : BitDomainPair :=
  iterateBitPruning aL D 256

/-- Running one further propagation pass cannot change the result. -/
theorem pruneBitDomainPair_fixed (aL : V 32) (D : BitDomainPair) :
    pruneBitDomainPair aL (bitPruningFixed aL D) =
      bitPruningFixed aL D := by
  change iterateBitPruning aL D (256 + 1) =
    iterateBitPruning aL D 256
  exact iterateBitPruning_fixed_256 aL D

/-- After 256 passes the domains remain unchanged forever. -/
theorem iterateBitPruning_after_256 (aL : V 32)
    (D : BitDomainPair) (m : Nat) :
    iterateBitPruning aL D (256 + m) =
      bitPruningFixed aL D := by
  unfold bitPruningFixed
  apply iterateBitPruning_stays_fixed aL D 256
  exact iterateBitPruning_fixed_256 aL D

/-- A genuine joint solution survives the *complete* propagation. -/
theorem jointCarryConstraint_implies_fixedBitPruned
    (k₀ k₁ aL aR bL : V 32)
    (c y : Fin 8 → Fin 16)
    (h : jointCarryConstraint k₀ k₁ aL aR bL c y) :
    iteratedBitPrunedJointConstraint k₀ k₁ aL aR bL 256 c y :=
  jointCarryConstraint_implies_iteratedBitPruned
    k₀ k₁ aL aR bL c y 256 h

/-- An empty domain at the guaranteed fixed point certifies an
    impossible three-round differential, without checking further passes. -/
theorem xorDDT_rounds_three_zero_of_empty_fixedBitDomain
    (k₀ k₁ k₂ aL aR bL bR : V 32)
    (hconf :
      (∃ i : Fin 8,
        (bitPruningFixed aL
          (initialBitDomains k₀ k₁ aR bL)).1 i = ∅) ∨
      (∃ i : Fin 8,
        (bitPruningFixed aL
          (initialBitDomains k₀ k₁ aR bL)).2 i = ∅)) :
    xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
      (aL, aR) (bL, bR) = 0 := by
  apply xorDDT_rounds_three_zero_of_empty_iteratedBitDomain
    k₀ k₁ k₂ aL aR bL bR 256
  simpa only [bitPruningFixed] using hconf

/-- Public representation used by external certificate producers. -/
abbrev BitPruningDomains : Type :=
  (Fin 8 → Finset (Fin 16)) × (Fin 8 → Finset (Fin 16))

/-- An explicit contradiction at one of the sixteen domain positions. -/
def verifyEmptyBitPruningDomain (D : BitPruningDomains) : Bool :=
  decide ((∃ i : Fin 8, D.1 i = ∅) ∨
          (∃ i : Fin 8, D.2 i = ∅))

/-! ## 2. Nibble-grouped rotation-wiring arc consistency -/

/-- For a Y-nibble candidate, each *destination nibble* must provide one
    common C-nibble value supporting ALL corresponding Y bits, rather than
    allowing a different C-nibble value for every source bit. -/
def pruneGroupedOutput (aL : V 32)
    (Y C : Fin 8 → Finset (Fin 16)) (i : Fin 8) : Finset (Fin 16) :=
  (Y i).filter (fun yd =>
    ∀ r : Fin 4,
      ∃ cd ∈ C (digitAt (bitPos i r + 11)),
        ∀ q : Fin 4,
          digitAt (bitPos i q + 11) = digitAt (bitPos i r + 11) →
            compatibleBit aL (bitPos i q) (bitPos i q + 11) yd cd)

/-- Symmetrically, one common Y-nibble value must support all bits of
    a candidate C nibble originating in the same Y nibble. -/
def pruneGroupedIntermediate (aL : V 32)
    (Y C : Fin 8 → Finset (Fin 16)) (i : Fin 8) : Finset (Fin 16) :=
  (C i).filter (fun cd =>
    ∀ r : Fin 4,
      ∃ yd ∈ Y (digitAt (bitPos i r - 11)),
        ∀ q : Fin 4,
          digitAt (bitPos i q - 11) = digitAt (bitPos i r - 11) →
            compatibleBit aL (bitPos i q - 11) (bitPos i q) yd cd)

/-- Grouped filtering is at least as strong as the original bit filtering. -/
theorem pruneGroupedOutput_subset_pruneOutputBits
    (aL : V 32) (Y C : Fin 8 → Finset (Fin 16)) (i : Fin 8) :
    pruneGroupedOutput aL Y C i ⊆ pruneOutputBits aL Y C i := by
  intro yd h
  obtain ⟨hmem, hgroup⟩ := Finset.mem_filter.mp h
  apply Finset.mem_filter.mpr
  refine ⟨hmem, ?_⟩
  intro r
  obtain ⟨cd, hcd, hcompat⟩ := hgroup r
  exact ⟨cd, hcd, hcompat r rfl⟩

theorem pruneGroupedIntermediate_subset_pruneIntermediateBits (aL : V 32)
    (Y C : Fin 8 → Finset (Fin 16)) (i : Fin 8) :
    pruneGroupedIntermediate aL Y C i ⊆ pruneIntermediateBits aL Y C i := by
  intro cd h
  obtain ⟨hmem, hgroup⟩ := Finset.mem_filter.mp h
  apply Finset.mem_filter.mpr
  refine ⟨hmem, ?_⟩
  intro r
  obtain ⟨yd, hyd, hcompat⟩ := hgroup r
  exact ⟨yd, hyd, hcompat r rfl⟩

/-- Every actual assignment satisfying the 32-bit wiring survives grouped
    filtering. Proof directly reuses the previously proved wiring bit lemma. -/
theorem groupedPruning_sound (aL : V 32)
    (Y C : Fin 8 → Finset (Fin 16))
    (c y : Fin 8 → Fin 16)
    (hw : jointRotationWiring aL c y)
    (hy : ∀ i, y i ∈ Y i)
    (hc : ∀ i, c i ∈ C i) :
    (∀ i, y i ∈ pruneGroupedOutput aL Y C i) ∧
    (∀ i, c i ∈ pruneGroupedIntermediate aL Y C i) := by
  have hwbits := (jointRotationWiring_iff_bits aL c y).mp hw
  constructor
  · intro i
    apply Finset.mem_filter.mpr
    refine ⟨hy i, ?_⟩
    intro r
    let dst := bitPos i r + 11
    refine ⟨c (digitAt dst), hc (digitAt dst), ?_⟩
    intro q hq
    have hb := hwbits (bitPos i q)
    rw [component_packDigits y (bitPos i q),
        component_packDigits c (bitPos i q + 11)] at hb
    change compatibleBit aL (bitPos i q) (bitPos i q + 11)
      (y (digitAt (bitPos i q)))
      (c (digitAt (bitPos i q + 11))) at hb
    rw [digitAt_bitPos] at hb
    change digitAt (bitPos i q + 11) = digitAt dst at hq
    rw [hq] at hb
    exact hb
  · intro i
    apply Finset.mem_filter.mpr
    refine ⟨hc i, ?_⟩
    intro r
    let src := bitPos i r - 11
    refine ⟨y (digitAt src), hy (digitAt src), ?_⟩
    intro q hq
    have hb := hwbits (bitPos i q - 11)
    have hdst : (bitPos i q - 11) + 11 = bitPos i q := by simp
    rw [hdst] at hb
    rw [component_packDigits y (bitPos i q - 11),
        component_packDigits c (bitPos i q)] at hb
    change compatibleBit aL (bitPos i q - 11) (bitPos i q)
      (y (digitAt (bitPos i q - 11)))
      (c (digitAt (bitPos i q))) at hb
    rw [digitAt_bitPos] at hb
    change digitAt (bitPos i q - 11) = digitAt src at hq
    rw [hq] at hb
    exact hb

/-- One simultaneous grouped pass. -/
def pruneGroupedDomainPair (aL : V 32)
    (D : BitPruningDomains) : BitPruningDomains :=
  (fun i => pruneGroupedOutput aL D.1 D.2 i,
   fun i => pruneGroupedIntermediate aL D.1 D.2 i)

/-- Iterate grouped propagation, preserving all true wiring assignments. -/
def iterateGroupedPruning (aL : V 32) (D : BitPruningDomains) :
    Nat → BitPruningDomains
  | 0 => D
  | n + 1 => pruneGroupedDomainPair aL
      (iterateGroupedPruning aL D n)

theorem iterateGroupedPruning_sound (aL : V 32) (D : BitPruningDomains) (c y : Fin 8 → Fin 16)
    (hw : jointRotationWiring aL c y) (hy : ∀ i, y i ∈ D.1 i) (hc : ∀ i, c i ∈ D.2 i) :
    ∀ n : Nat,
      (∀ i, y i ∈ (iterateGroupedPruning aL D n).1 i) ∧
        (∀ i, c i ∈ (iterateGroupedPruning aL D n).2 i) := by
  intro n
  induction n with
  | zero => exact ⟨hy, hc⟩
  | succ n ih =>
    exact
      groupedPruning_sound aL (iterateGroupedPruning aL D n).1 (iterateGroupedPruning aL D n).2 c y
        hw ih.1 ih.2

/-- A Boolean grouped-propagation test. False is inconclusive. -/
def groupedContradiction (k₀ k₁ aL aR bL : V 32)
    (passes : Nat := 8) : Bool :=
  verifyEmptyBitPruningDomain
    (iterateGroupedPruning aL (initialBitDomains k₀ k₁ aR bL) passes)

/-- Unlike the generator, this decision procedure proves a contradiction
    directly using groupedPruning_sound and the established three-round
    reduction. No separate trace storage is necessary. -/
theorem xorDDT_rounds_three_zero_of_groupedContradiction
    (k₀ k₁ k₂ aL aR bL bR : V 32) (passes : Nat)
    (h : groupedContradiction k₀ k₁ aL aR bL passes = true) :
    xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
      (aL, aR) (bL, bR) = 0 := by
  apply xorDDT_rounds_three_zero_of_no_localDomains
    k₀ k₁ k₂ aL aR bL bR
  rintro ⟨c, y, hw, hy, hc⟩
  have hkeep := iterateGroupedPruning_sound aL
    (initialBitDomains k₀ k₁ aR bL) c y hw hy hc passes
  have hconf :
      (∃ i : Fin 8,
        (iterateGroupedPruning aL (initialBitDomains k₀ k₁ aR bL) passes).1 i = ∅) ∨
      (∃ i : Fin 8,
        (iterateGroupedPruning aL (initialBitDomains k₀ k₁ aR bL) passes).2 i = ∅) := by
    simpa only [groupedContradiction, verifyEmptyBitPruningDomain,
      decide_eq_true_eq] using h
  rcases hconf with ⟨i, hempty⟩ | ⟨i, hempty⟩
  · have hm := hkeep.1 i
    rw [hempty] at hm
    exact Finset.notMem_empty _ hm
  · have hm := hkeep.2 i
    rw [hempty] at hm
    exact Finset.notMem_empty _ hm

end Magma.Pruning
