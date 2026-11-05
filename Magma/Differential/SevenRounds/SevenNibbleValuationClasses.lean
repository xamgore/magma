module
import all Init.Data.Range.Basic
public import Magma.Differential.SevenRounds.SevenTopNibbleImpossible
public import Magma.Differential.RoundFunction.FirstActiveNibbleInvariant
import Std.Tactic.BVDecide

set_option maxHeartbeats 2000000

@[expose] public section
namespace Magma.DifanSevenNibbleValuationClasses

open Magma Magma.CarryAutomaton Magma.MultiRoundDDT
open Magma.DifanFirstActiveNibbleInvariant
open Magma.DifanSevenTopNibble

private abbrev Word := V 32

/-- The first nonzero 4-bit digit is at nibble index i, low bit first.
This is a decidable mask predicate, independent of keys and base words. -/
def activeAt (w : Word) (i : Nat) : Prop :=
  (w &&& (BitVec.ofNat 32 ((16 ^ i) - 1))) = 0#32 ∧
  (w &&& (BitVec.ofNat 32 (15 * 16 ^ i))) ≠ 0#32

/-- Convert the already proved digit-stream first-active predicate to
the small concrete bit-mask form used in the finite SAT closure. -/
private theorem activeAt_of_first (w : Word) (i : Fin 8)
    (h : FirstActiveNibbleAt w i) : activeAt w i.val := by
  have hpref (j : Fin 8) (hj : j.val < i.val) :
      Magma.Internal.nibble w j = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact h.1 j hj
  have hnone : Magma.Internal.nibble w i ≠ 0#4 := by
    intro hz
    apply h.2
    change (Magma.Internal.nibble w i).toFin = 0
    rw [hz]
    decide
  have h0 : 0 < i.val → Magma.Internal.nibble w (0 : Fin 8) = 0#4 :=
    hpref (0 : Fin 8)
  have h1 : 1 < i.val → Magma.Internal.nibble w (1 : Fin 8) = 0#4 :=
    hpref (1 : Fin 8)
  have h2 : 2 < i.val → Magma.Internal.nibble w (2 : Fin 8) = 0#4 :=
    hpref (2 : Fin 8)
  have h3 : 3 < i.val → Magma.Internal.nibble w (3 : Fin 8) = 0#4 :=
    hpref (3 : Fin 8)
  have h4 : 4 < i.val → Magma.Internal.nibble w (4 : Fin 8) = 0#4 :=
    hpref (4 : Fin 8)
  have h5 : 5 < i.val → Magma.Internal.nibble w (5 : Fin 8) = 0#4 :=
    hpref (5 : Fin 8)
  have h6 : 6 < i.val → Magma.Internal.nibble w (6 : Fin 8) = 0#4 :=
    hpref (6 : Fin 8)
  have h7 : 7 < i.val → Magma.Internal.nibble w (7 : Fin 8) = 0#4 :=
    hpref (7 : Fin 8)
  fin_cases i
  all_goals
    simp only [activeAt, Magma.Internal.nibble, substring] at *
    norm_num at *
    bv_decide

/-- A *necessary*, never sufficient, one-round g derivative condition. -/
def possible (d e : Word) : Prop :=
  (d = 0#32 ∧ e = 0#32) ∨
  (activeAt d 0 ∧ activeAt (e.rotateRight 11) 0) ∨
  (activeAt d 1 ∧ activeAt (e.rotateRight 11) 1) ∨
  (activeAt d 2 ∧ activeAt (e.rotateRight 11) 2) ∨
  (activeAt d 3 ∧ activeAt (e.rotateRight 11) 3) ∨
  (activeAt d 4 ∧ activeAt (e.rotateRight 11) 4) ∨
  (activeAt d 5 ∧ activeAt (e.rotateRight 11) 5) ∨
  (activeAt d 6 ∧ activeAt (e.rotateRight 11) 6) ∨
  (activeAt d 7 ∧ activeAt (e.rotateRight 11) 7)

/-- Every nonzero 32-bit word has a first active 4-bit digit.
We use existing RFC nibble extraction and the established
wordDigitsEquiv; there is no key enumeration here. -/
private theorem exists_first (d : Word) (hd : d ≠ 0#32) :
    ∃ i : Fin 8, FirstActiveNibbleAt d i := by
  classical
  have hex : ∃ i : Fin 8, wordDigits d i ≠ 0 := by
    by_contra h
    push Not at h
    have hz : wordDigits d = wordDigits (0#32) := by
      funext i
      have hz : wordDigits (0#32) i = 0 := by fin_cases i <;> decide
      exact (h i).trans hz.symm
    exact hd (wordDigitsEquiv.injective hz)
  let s : Finset (Fin 8) := Finset.univ.filter (fun i => wordDigits d i ≠ 0)
  have hs : s.Nonempty := by
    obtain ⟨i, hi⟩ := hex
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  let i : Fin 8 := s.min' hs
  refine ⟨i, ?_, ?_⟩
  · intro u hu
    by_contra hn
    have humem : u ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩
    have hmin := Finset.min'_le s u humem
    exact (not_lt_of_ge hmin) hu
  · exact (Finset.mem_filter.mp (Finset.min'_mem s hs)).2

/-- An *actual* RFC Magma derivative satisfies the little
difference-only nibble valuation predicate. -/
theorem possible_of_real_g (k x d : Word) :
    possible d (gDifference k x d) := by
  by_cases hd : d = 0#32
  · unfold possible
    left
    constructor
    · exact hd
    · subst d
      simp [gDifference, Magma.xor, BitVec.xor_zero]
  · obtain ⟨i, hi⟩ := exists_first d hd
    have hp := Magma.DifanFirstActiveNibbleInvariant.firstActiveNibble_preserved
      k d x i hi
    have ha : activeAt d i.val := activeAt_of_first d i hi
    have hb : activeAt
        ((gDifference k x d).rotateRight 11) i.val :=
      activeAt_of_first _ i hp
    fin_cases i <;>
      (unfold possible; tauto)

/-- The six families detected by the independent difference-only Z3 scan. -/
def sixClasses (a b : Word) : Prop :=
  (activeAt a 5 ∧ activeAt b 6) ∨
  (activeAt a 6 ∧ activeAt b 5) ∨
  (activeAt a 6 ∧ activeAt b 6) ∨
  (activeAt a 6 ∧ activeAt b 7) ∨
  (activeAt a 7 ∧ activeAt b 6) ∨
  (activeAt a 7 ∧ activeAt b 7)

/-- Pure finite bitvector obstruction: none of the real base states,
round keys, or S-box tables appear here. -/
theorem no_five_valuation_chain (a b p q t : Word)
    (h0 : possible a p)
    (h1 : possible p (a ^^^ q))
    (h2 : possible q (p ^^^ t))
    (h3 : possible t (q ^^^ b))
    (h4 : possible b t)
    (hclass : sixClasses a b) : False := by
  unfold possible sixClasses at *
  unfold activeAt at *
  norm_num at *
  bv_decide

/-- Full key-universal FIVE-round inner obstruction, certified for
all six first-active-nibble classes. This theorem is stronger than
the high-high only family: both endpoint words can have arbitrarily
many active higher-order nibbles. -/
theorem opposite_five_core_zero_sixClasses
    (keys : Fin 5 → Word) (a b : Word) (hclass : sixClasses a b) :
    xorDDT_rounds 5 keys (0#32, a) (b, 0#32) = 0 := by
  apply Magma.DifanSevenTopNibble.opposite_five_core_zero_of_no_local_chain
    keys a b
  intro k0 k1 k2 k3 k4 x1 x2 x3 x4 x5 p q t h0 h1 h2 h3 h4
  apply no_five_valuation_chain a b p q t
  · rw [← h0]
    exact possible_of_real_g k0 x1 a
  · rw [← h1]
    exact possible_of_real_g k1 x2 p
  · rw [← h2]
    exact possible_of_real_g k2 x3 q
  · rw [← h3]
    exact possible_of_real_g k3 x4 t
  · rw [← h4]
    exact possible_of_real_g k4 x5 b
  · exact hclass

/-- MAIN GENERAL RESULT: all 1,908,225 nonzero (a,b) endpoint pairs
within the six disjoint first-nibble-index classes are impossible
in seven genuine RFC Magma Feistel rounds for ANY round keys.
The proof applies uniformly, without enumerating those pairs. -/
theorem seven_round_zero_six_nibble_classes
    (keys : Fin 7 → Word) (a b : Word) (hclass : sixClasses a b) :
    xorDDT_rounds 7 keys (a, 0#32) (0#32, b) = 0 := by
  rw [Magma.DifanFirstRoundDeletion.twoSided_boundary_ddt_eq_inner
    5 keys a b]
  exact opposite_five_core_zero_sixClasses
    (fun i : Fin 5 => keys i.castSucc.succ) a b hclass

/-- Number of DISTINCT nonzero ordered endpoint pairs described
by the six disjoint classes: a first active nibble i has
15 * 16^(7-i) possible 32-bit word values. -/
theorem six_class_pair_count_arithmetic :
    (15 * 16 ^ 2) * (15 * 16 ^ 1) +
    (15 * 16 ^ 1) * (15 * 16 ^ 2) +
    (15 * 16 ^ 1) * (15 * 16 ^ 1) +
    (15 * 16 ^ 1) * (15 * 16 ^ 0) +
    (15 * 16 ^ 0) * (15 * 16 ^ 1) +
    (15 * 16 ^ 0) * (15 * 16 ^ 0) = (1908225 : Nat) := by
  norm_num

/-- A concrete difference-only seven-derivative chain survives the
SIX-CLASS *valuation* abstraction once it is extended to the
seven-round INNER core of a NINE-round outer differential.
This is NOT a genuine Magma 9-round key/base witness:
it is a certified counterexample to trying to prove a
nine-round zero with this WEAK abstraction alone. -/
theorem nine_high_high_valuation_relaxation_has_path :
    possible (0x80000000#32) (0x00000680#32) ∧
    possible (0x00000680#32) (0x80000000#32 ^^^ 0x0AA90606#32) ∧
    possible (0x0AA90606#32) (0x00000680#32 ^^^ 0x00304EB0#32) ∧
    possible (0x00304EB0#32) (0x0AA90606#32 ^^^ 0x0AA80006#32) ∧
    possible (0x0AA80006#32) (0x00304EB0#32 ^^^ 0x00000100#32) ∧
    possible (0x00000100#32) (0x0AA80006#32 ^^^ 0x80000000#32) ∧
    possible (0x80000000#32) (0x00000100#32) := by
  unfold possible activeAt
  norm_num

end Magma.DifanSevenNibbleValuationClasses
