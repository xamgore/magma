module

import all Init.Data.Range.Basic
public import Magma.Differential.RoundFunction.GBaseTaggedCarryStep

@[expose] public section

/-!
# Whole-word reconstruction from actual tagged Magma carry steps

The existing one-nibble tagged transition emits BOTH the base S-box
digit and the substituted XOR derivative digit under the SAME incoming
carry pair. This module shows that, when fed the genuine carry pairs
of a 32-bit base word, all eight digits reconstruct the actual Magma
round function and derivative. The outgoing carries are certified too.

The result is exact and pointwise, with NO independence assumption.
It is a prerequisite for an exact correlated multi-round transfer
matrix; that matrix is not built by this theorem alone.
-/

namespace Magma.Composition.TaggedCarryWord

open Magma
open Magma.Internal
open Magma.GProperties
open Magma.CarryAutomaton
open Magma.DifanGBaseTaggedCarryStep

private abbrev Word := V 32

/-- The pair of outputs at nibble i on a genuine 32-bit trajectory. -/
def actualTaggedDigits (k d x : Word) (i : Fin 8) :
    Fin 16 × Fin 16 :=
  (taggedCarryStep i (wordDigits k i) (wordDigits d i)
    (wordDigits x i) (wordCarryPair k d x i.val)).1

/-- The BASE digit emitted by the tagged transition is precisely
    the corresponding nibble of the real, unrotated t(x+k). -/
theorem actualTagged_base_digit (k d x : Word) (i : Fin 8) :
    (actualTaggedDigits k d x i).1 =
      wordDigits (t (modShift k x)) i := by
  rw [wordDigits_t]
  change (π i (BitVec.ofNat 4 (outputDigit (wordDigits x i)
    (wordDigits k i) (wordCarryPair k d x i.val).1).val)).toFin =
    (π i (nibble (modShift k x) i)).toFin
  change (π i (BitVec.ofNat 4 (outputDigit (wordDigits x i)
    (wordDigits k i) (incomingCarry (wordDigitStream x)
      (wordDigitStream k) i.val)).val)).toFin = _
  rw [← wordDigits_modShift k x i]
  simp only [wordDigits, BitVec.ofNat_finVal, BitVec.ofFin_toFin]

/-- The DIFFERENCE digit uses the same carry pair and equals
    the true unrotated substituted XOR derivative. -/
theorem actualTagged_diff_digit (k d x : Word) (i : Fin 8) :
    (actualTaggedDigits k d x i).2 =
      localSBoxDifference k d x i := by
  unfold actualTaggedDigits taggedCarryStep
  exact congrArg Prod.fst
    (sboxCarryStep_word_correct k d x i)

/-- The outgoing carry pair of each actual tagged transition
    is the true incoming pair at the next nibble. -/
theorem actualTagged_next_carries (k d x : Word) (i : Fin 8) :
    (taggedCarryStep i (wordDigits k i) (wordDigits d i)
      (wordDigits x i) (wordCarryPair k d x i.val)).2 =
    wordCarryPair k d x (i.val + 1) := by
  exact congrArg Prod.snd (sboxCarryStep_word_correct k d x i)

/-- Concatenation of all eight BASE emitted nibbles yields the
    exact pre-rotation S-box word t(x+k). -/
theorem pack_actualTagged_base (k d x : Word) :
    packDigits (fun i => (actualTaggedDigits k d x i).1) =
      t (modShift k x) := by
  calc
    packDigits (fun i => (actualTaggedDigits k d x i).1) =
        packDigits (wordDigits (t (modShift k x))) := by
      congr 1
      funext i
      exact actualTagged_base_digit k d x i
    _ = t (modShift k x) := wordDigitsEquiv.left_inv _

/-- The tagged base outputs, after RFC's rotate-left-11, are
    the EXACT 32-bit Magma round function g, for arbitrary
    round key k, base x and XOR input difference d. -/
theorem rot11_pack_actualTagged_base (k d x : Word) :
    rot11 (packDigits (fun i => (actualTaggedDigits k d x i).1)) =
      g k x := by
  rw [pack_actualTagged_base]
  exact (g_as_modShift k x).symm

/-- Every tagged DIFFERENCE digit is the corresponding nibble of
    the actual pre-rotation XOR difference of both substituted words. -/
theorem actualTagged_diff_word_digit (k d x : Word) (i : Fin 8) :
    (actualTaggedDigits k d x i).2 =
      wordDigits (xor (t (modShift k (xor x d)))
        (t (modShift k x))) i := by
  rw [actualTagged_diff_digit]
  change xorDigit
      (π i (nibble (modShift k (xor x d)) i)).toFin
      (π i (nibble (modShift k x) i)).toFin = _
  rw [wordDigits_xor]
  rw [wordDigits_t, wordDigits_t]

/-- Repacking ALL eight differential outputs yields the genuine
    32-bit pre-rotation XOR derivative, including every carry. -/
theorem pack_actualTagged_difference (k d x : Word) :
    packDigits (fun i => (actualTaggedDigits k d x i).2) =
      xor (t (modShift k (xor x d))) (t (modShift k x)) := by
  calc
    packDigits (fun i => (actualTaggedDigits k d x i).2) =
        packDigits (wordDigits
          (xor (t (modShift k (xor x d))) (t (modShift k x)))) := by
      congr 1
      funext i
      exact actualTagged_diff_word_digit k d x i
    _ = _ := wordDigitsEquiv.left_inv _

/-- Applying the RFC rotation to the tagged DIFFERENCE output
    yields exactly the real g XOR derivative. Both derivatives
    and the base output have now been reconstructed from the same
    concrete tagged steps. -/
theorem rot11_pack_actualTagged_difference (k d x : Word) :
    rot11 (packDigits (fun i => (actualTaggedDigits k d x i).2)) =
      xor (g k (xor x d)) (g k x) := by
  rw [pack_actualTagged_difference, ← rot11_xor]
  rw [g_as_modShift, g_as_modShift]


/-! ## An executable eight-step carry trace with both recorded outputs -/

private abbrev TaggedDigit := Fin 16 × Fin 16

/-- A genuine streaming implementation: process the first n
    nibbles from least to most significant, starting with carry
    pair (0,0). Each step consumes the PREVIOUS step's carry pair
    and stores both S-box outputs in one finite observation array.
    This is meaningful for n ≤ 8; later steps are no-ops. -/
def taggedPrefix (k d x : Word) : Nat →
    (CarryState × (Fin 8 → Option TaggedDigit))
  | 0 => ((0, 0), fun _ => none)
  | n + 1 =>
      let prev := taggedPrefix k d x n
      if hn : n < 8 then
        let i : Fin 8 := ⟨n, hn⟩
        let step := taggedCarryStep i
          (wordDigits k i) (wordDigits d i) (wordDigits x i)
          prev.1
        (step.2, Function.update prev.2 i (some step.1))
      else prev

/-- The executable prefix has the ACTUAL two incoming carries,
    and every visited nibble has exactly the genuine tagged output. -/
theorem taggedPrefix_correct (k d x : Word) (n : Nat)
    (hn : n ≤ 8) :
    (taggedPrefix k d x n).1 = wordCarryPair k d x n ∧
    ∀ i : Fin 8, i.val < n →
      (taggedPrefix k d x n).2 i =
        some (actualTaggedDigits k d x i) := by
  induction n with
  | zero =>
      constructor
      · rfl
      · intro i hi
        omega
  | succ n ih =>
      have hn8 : n < 8 := by omega
      have hnprev : n ≤ 8 := by omega
      obtain ⟨hc, ho⟩ := ih hnprev
      constructor
      · simp only [taggedPrefix, dite_eq_left hn8]
        rw [hc]
        exact actualTagged_next_carries k d x ⟨n, hn8⟩
      · intro i hi
        by_cases hidx : i = (⟨n, hn8⟩ : Fin 8)
        · subst i
          simp only [taggedPrefix, dite_eq_left hn8]
          rw [hc]
          simp [actualTaggedDigits]
        · have hval : i.val ≠ n := by
            intro heq
            apply hidx
            exact Fin.ext heq
          have hprev : i.val < n := by omega
          simp only [taggedPrefix, dite_eq_left hn8]
          rw [Function.update_of_ne hidx]
          exact ho i hprev

/-- After exactly eight successive local carry steps, the two
    complete emitted 32-bit words equal the real unrotated
    substitution and its XOR difference. -/
theorem taggedPrefix_eight_words (k d x : Word) :
    let trace := taggedPrefix k d x 8
    (trace.1 = wordCarryPair k d x 8) ∧
    (packDigits (fun i => ((trace.2 i).getD (0, 0)).1) =
      t (modShift k x)) ∧
    (packDigits (fun i => ((trace.2 i).getD (0, 0)).2) =
      xor (t (modShift k (xor x d))) (t (modShift k x))) := by
  have h := taggedPrefix_correct k d x 8 (by omega)
  have hall (i : Fin 8) :
      (taggedPrefix k d x 8).2 i =
        some (actualTaggedDigits k d x i) :=
    h.2 i (by omega)
  have hbase :
      (fun i : Fin 8 =>
          (((taggedPrefix k d x 8).2 i).getD (0, 0)).1) =
      (fun i : Fin 8 => (actualTaggedDigits k d x i).1) := by
    funext i
    rw [hall i]
    rfl
  have hdiff :
      (fun i : Fin 8 =>
          (((taggedPrefix k d x 8).2 i).getD (0, 0)).2) =
      (fun i : Fin 8 => (actualTaggedDigits k d x i).2) := by
    funext i
    rw [hall i]
    rfl
  exact ⟨h.1, by rw [hbase]; exact pack_actualTagged_base k d x,
    by rw [hdiff]; exact pack_actualTagged_difference k d x⟩

/-- After rotating both assembled streams, the actual eight-step
    automaton emits the Magma round function g and its actual XOR
    derivative, with no omitted correlation or independent carry. -/
theorem taggedPrefix_eight_g (k d x : Word) :
    let trace := taggedPrefix k d x 8
    rot11 (packDigits (fun i => ((trace.2 i).getD (0, 0)).1)) =
      g k x ∧
    rot11 (packDigits (fun i => ((trace.2 i).getD (0, 0)).2)) =
      xor (g k (xor x d)) (g k x) := by
  have h := taggedPrefix_eight_words k d x
  dsimp only at h ⊢
  constructor
  · rw [h.2.1]
    exact (g_as_modShift k x).symm
  · rw [h.2.2, ← rot11_xor, g_as_modShift, g_as_modShift]

end Magma.Composition.TaggedCarryWord
