module

public import Magma.Differential.RoundFunction.Rotate11Nibble

set_option maxHeartbeats 3000000

@[expose] public section

/-!
# Whole-word interpretation of the local joint tagged triple

The new joint carry transfer propagates two *different* S-box tag
streams together: the derivative E from the first g, and the actual
base U from the middle g. The same r_nibble is reused by the first
and third derivative, and every carry pair is kept correlated.

This theorem proves that the local rotated-digit acceptance predicate
is equivalent to the two full 32-bit correlated derivative equations.
This is a semantic foundation, NOT a Lean proof that the Rust
HashMap aggregation preserves multiplicities (that is separate).
-/

namespace Magma.Composition.JointTaggedAcceptance

open Magma
open Magma.CarryAutomaton
open Magma.Composition.TaggedCarryWord
open Magma.Composition.Rotate11Nibble

private abbrev Word := V 32

/-- A true 32-bit round derivative, with the input XOR difference first. -/
def diffG (k d x : Word) : Word :=
  xor (g k (xor x d)) (g k x)

/-- Record the BASE S-box tag stream of an eight-step actual carry trace. -/
def baseTags (k d x : Word) : Fin 8 → Fin 16 :=
  fun i => (((taggedPrefix k d x 8).2 i).getD (0, 0)).1

/-- Record the derivative tag stream on the SAME eight-step carry trace. -/
def derivativeTags (k d x : Word) : Fin 8 → Fin 16 :=
  fun i => (((taggedPrefix k d x 8).2 i).getD (0, 0)).2

/-- Reassemble a rotated word directly from the local two-source tag wiring. -/
def rotatedTagsWord (tags : Fin 8 → Fin 16) : Word :=
  packDigits (fun i => rotatedTagDigit tags i)

/-- Eight exact BASE digits reconstruct the original 32-bit g word. -/
theorem rotated_baseTags_eq_g (k d x : Word) :
    rotatedTagsWord (baseTags k d x) = g k x := by
  unfold rotatedTagsWord
  calc
    packDigits (fun i => rotatedTagDigit (baseTags k d x) i) =
        packDigits (wordDigits (g k x)) := by
      congr 1
      funext i
      exact rotated_recorded_base_exact k d x i
    _ = g k x := wordDigitsEquiv.left_inv _

/-- Eight exact derivative digits reconstruct the true XOR derivative. -/
theorem rotated_derivativeTags_eq_diffG (k d x : Word) :
    rotatedTagsWord (derivativeTags k d x) = diffG k d x := by
  unfold rotatedTagsWord
  calc
    packDigits (fun i => rotatedTagDigit (derivativeTags k d x) i) =
        packDigits (wordDigits (diffG k d x)) := by
      congr 1
      funext i
      exact rotated_recorded_derivative_exact k d x i
    _ = diffG k d x := wordDigitsEquiv.left_inv _

/-- The eight local comparisons with a TARGET word are equivalent
    to a genuine 32-bit derivative equality. -/
theorem rotated_derivativeTags_eq_word_iff (k d x target : Word) :
    (∀ i : Fin 8,
      rotatedTagDigit (derivativeTags k d x) i =
        wordDigits target i) ↔
      diffG k d x = target := by
  constructor
  · intro hall
    have h :
        rotatedTagsWord (derivativeTags k d x) = target := by
      unfold rotatedTagsWord
      calc
        packDigits (fun i => rotatedTagDigit (derivativeTags k d x) i) =
            packDigits (wordDigits target) := by
          congr 1
          funext i
          exact hall i
        _ = target := wordDigitsEquiv.left_inv _
    rw [rotated_derivativeTags_eq_diffG] at h
    exact h
  · intro heq i
    calc
      rotatedTagDigit (derivativeTags k d x) i =
          wordDigits (diffG k d x) i :=
        rotated_recorded_derivative_exact k d x i
      _ = wordDigits target i :=
        congrArg (fun w : Word => wordDigits w i) heq

/-- Comparing two local rotated tag streams is precisely comparing
    the two whole-word g derivatives: nothing is lost by nibble splitting. -/
theorem rotated_derivativeTags_eq_iff
    (k d x k' d' x' : Word) :
    (∀ i : Fin 8,
      rotatedTagDigit (derivativeTags k d x) i =
      rotatedTagDigit (derivativeTags k' d' x') i) ↔
      diffG k d x = diffG k' d' x' := by
  constructor
  · intro hall
    apply (rotated_derivativeTags_eq_word_iff
        k d x (diffG k' d' x')).mp
    intro i
    calc
      rotatedTagDigit (derivativeTags k d x) i =
          rotatedTagDigit (derivativeTags k' d' x') i := hall i
      _ = wordDigits (diffG k' d' x') i :=
        rotated_recorded_derivative_exact k' d' x' i
  · intro h i
    calc
      rotatedTagDigit (derivativeTags k d x) i =
          wordDigits (diffG k d x) i :=
        rotated_recorded_derivative_exact k d x i
      _ = wordDigits (diffG k' d' x') i :=
        congrArg (fun w : Word => wordDigits w i) h
      _ = rotatedTagDigit (derivativeTags k' d' x') i :=
        (rotated_recorded_derivative_exact k' d' x' i).symm

/-- Reconstruct the first g difference from its recorded E stream. -/
def firstDifferenceFromTags (k₁ a r : Word) : Word :=
  rotatedTagsWord (derivativeTags k₁ a r)

/-- Reconstruct the middle g BASE output from its recorded U stream. -/
def middleBaseFromTags (k₂ z : Word) : Word :=
  rotatedTagsWord (baseTags k₂ 0 z)

theorem firstDifferenceFromTags_eq (k₁ a r : Word) :
    firstDifferenceFromTags k₁ a r = diffG k₁ a r := by
  exact rotated_derivativeTags_eq_diffG k₁ a r

theorem middleBaseFromTags_eq (k₂ z : Word) :
    middleBaseFromTags k₂ z = g k₂ z := by
  exact rotated_baseTags_eq_g k₂ 0 z

/-- Acceptance in the *local* eight-nibble tagged triple. The
    rotated first E stream determines the second input difference;
    the rotated middle U stream determines the third BASE input.
    Both resulting output differences are compared per nibble. -/
def JointTaggedAccept (k₁ k₂ k₃ a b r z : Word) : Prop :=
  let c := firstDifferenceFromTags k₁ a r
  let h := middleBaseFromTags k₂ z
  (∀ i : Fin 8,
    rotatedTagDigit (derivativeTags k₂ c z) i =
      wordDigits (xor a b) i) ∧
  (∀ i : Fin 8,
    rotatedTagDigit (derivativeTags k₃ b (xor r h)) i =
      rotatedTagDigit (derivativeTags k₁ a r) i)

/-- The local eight-nibble acceptance predicate is EXACTLY the
    correlated three-derivative condition on two real base words.
    This is a general symbolic theorem for arbitrary 32-bit keys,
    differences and bases, not an instance-specific witness. -/
theorem jointTaggedAccept_iff_real
    (k₁ k₂ k₃ a b r z : Word) :
    JointTaggedAccept k₁ k₂ k₃ a b r z ↔
      (diffG k₂ (diffG k₁ a r) z = xor a b ∧
       diffG k₃ b (xor r (g k₂ z)) = diffG k₁ a r) := by
  simp only [JointTaggedAccept, firstDifferenceFromTags_eq,
    middleBaseFromTags_eq]
  constructor
  · rintro ⟨hmid, hend⟩
    exact ⟨(rotated_derivativeTags_eq_word_iff
        k₂ (diffG k₁ a r) z (xor a b)).mp hmid,
      (rotated_derivativeTags_eq_iff
        k₃ b (xor r (g k₂ z)) k₁ a r).mp hend⟩
  · rintro ⟨hmid, hend⟩
    exact ⟨(rotated_derivativeTags_eq_word_iff
        k₂ (diffG k₁ a r) z (xor a b)).mpr hmid,
      (rotated_derivativeTags_eq_iff
        k₃ b (xor r (g k₂ z)) k₁ a r).mpr hend⟩

end Magma.Composition.JointTaggedAcceptance
