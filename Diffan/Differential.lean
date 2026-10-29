module

public import Diffan.DifferenceSpace
import all Init.Data.Range.Basic

@[expose] public section

/-!
# Diffan.Differential — exact DDT, support, and certified counters

`ddt` is the specification. An optimized algorithm belongs in a `CertifiedDDT`
instance only after its correctness is proved. No assumptions about independence.
-/

namespace Diffan

/-- A request for the transition from input difference `a` to output difference `b`. -/
structure Transition (A B : Type*) where
  input : A
  output : B

/-- A transition selected by predicates on its input and output differences.
    Restriction changes the *query domain*, not the underlying DDT. -/
abbrev RestrictedTransition {A B : Type*}
    (inputClass : A → Prop) (outputClass : B → Prop) :=
  {t : Transition A B // inputClass t.input ∧ outputClass t.output}

/-- Output difference of `f`, for an input with base point `x` and difference `a`. -/
def derivative {X Y A B : Type*}
    (sx : DifferenceSpace X A)
    (sy : DifferenceSpace Y B)
    (f : X → Y) (a : A) (x : X) : B :=
  sy.diff (f x) (f (sx.shift x a))

/-- An identity transformation preserves the input difference. -/
theorem derivative_id {X A : Type*}
    (s : DifferenceSpace X A) (a : A) (x : X) :
    derivative s s (fun y => y) a x = a := by
  exact s.diff_shift x a

/-- The derivative chain rule at a *specific intermediate state*.
    The base point `f x` cannot generally be discarded. -/
theorem derivative_comp {X Y Z A B C : Type*}
    (sx : DifferenceSpace X A)
    (sy : DifferenceSpace Y B)
    (sz : DifferenceSpace Z C)
    (f : X → Y) (g : Y → Z)
    (a : A) (x : X) :
    derivative sx sz (g ∘ f) a x = derivative sy sz g (derivative sx sy f a x) (f x) := by
  unfold derivative
  simp only [Function.comp_apply]
  rw [sy.shift_diff]

/-- Exact difference distribution count for a finite input space.
    We count *input states*, not pairs of states and not probabilities. -/
def ddt {X Y A B : Type*} [Fintype X] [DecidableEq B]
    (sx : DifferenceSpace X A) (sy : DifferenceSpace Y B)
    (f : X → Y) (a : A) (b : B) : Nat :=
  ((Finset.univ : Finset X).filter (fun x => derivative sx sy f a x = b)).card

/-- A difference transition is supported when at least one base point realizes it. -/
def support {X Y A B : Type*}
    (sx : DifferenceSpace X A) (sy : DifferenceSpace Y B)
    (f : X → Y) (a : A) (b : B) : Prop :=
  ∃ x, derivative sx sy f a x = b

/-- Zero DDT and lack of support are the same mathematical statement. -/
theorem ddt_eq_zero_iff {X Y A B : Type*} [Fintype X] [DecidableEq B]
    (sx : DifferenceSpace X A) (sy : DifferenceSpace Y B)
    (f : X → Y) (a : A) (b : B) :
    ddt sx sy f a b = 0 ↔ ¬ support sx sy f a b := by
  simp [ddt, support, Finset.card_eq_zero]

/-- A keyed family is just a function selecting a transformation for each key. -/
abbrev KeyedFamily (K X Y : Type*) := K → X → Y

/-- The true, mathematical DDT of a member of a keyed family. -/
def keyedDDT {K X Y A B : Type*} [Fintype X] [DecidableEq B]
    (sx : DifferenceSpace X A) (sy : DifferenceSpace Y B)
    (family : KeyedFamily K X Y) (k : K) (a : A) (b : B) : Nat :=
  ddt sx sy (family k) a b

/-- A fast DDT evaluator bundled with a correctness proof.
    `compute` need not use finite enumeration at all. -/
structure CertifiedDDT {K X Y A B : Type*}
    [Fintype X] [DecidableEq B]
    (sx : DifferenceSpace X A) (sy : DifferenceSpace Y B)
    (family : KeyedFamily K X Y) where
  compute : K → A → B → Nat
  correct : ∀ k a b, compute k a b = keyedDDT sx sy family k a b

end Diffan
