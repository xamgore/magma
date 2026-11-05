module

public import Diffan.Core.Differential
import all Init.Data.Range.Basic

@[expose] public section

/-!
# StateDifference — a base state paired with a difference

The pair `(x, a)` means the concrete ordered state pair
`(x, sx.shift x a)`. We *must* preserve the base state when propagating
through nonlinear functions. Otherwise two supported difference transitions
may fail to correspond to the same concrete trajectory.

A `StateDifference` has no redundant invariant: it is a convenient bundled
representation of `X × Δ`, equipped with precise transport and conversion
operations. `toPairEquiv` proves it encodes exactly the same information as
an ordered pair of concrete states.
-/

namespace Diffan

/-- The base state at which a difference is evaluated. -/
structure StateDifference (X Δ : Type*) where
  base : X
  delta : Δ
  deriving Fintype

namespace StateDifference

/-- Recover the two concrete states represented by a base and difference. -/
def toPair {X Δ : Type*} (sx : DifferenceSpace X Δ)
    (p : StateDifference X Δ) : X × X :=
  (p.base, sx.shift p.base p.delta)

/-- Recover a state-with-difference from two concrete states. -/
def ofPair {X Δ : Type*} (sx : DifferenceSpace X Δ)
    (xy : X × X) : StateDifference X Δ :=
  ⟨xy.1, sx.diff xy.1 xy.2⟩

/-- No information is lost by switching between state/difference and
concrete-state-pair coordinates. -/
def toPairEquiv {X Δ : Type*} (sx : DifferenceSpace X Δ) :
    StateDifference X Δ ≃ X × X where
  toFun := toPair sx
  invFun := ofPair sx
  left_inv := by
    rintro ⟨x, a⟩
    change StateDifference.mk x (sx.diff x (sx.shift x a)) =
      StateDifference.mk x a
    rw [sx.diff_shift]
  right_inv := by
    rintro ⟨x, y⟩
    change (x, sx.shift x (sx.diff x y)) = (x, y)
    rw [sx.shift_diff]

/-- Propagate the *real* base state and its difference through a map.
Unlike a DDT coefficient, this is a deterministic operation. -/
def transport {X Y A B : Type*}
    (sx : DifferenceSpace X A) (sy : DifferenceSpace Y B)
    (f : X → Y) (p : StateDifference X A) : StateDifference Y B :=
  ⟨f p.base, derivative sx sy f p.delta p.base⟩

/-- The base state after transport is exactly the function output. -/
@[simp] theorem transport_base {X Y A B : Type*}
    (sx : DifferenceSpace X A) (sy : DifferenceSpace Y B)
    (f : X → Y) (p : StateDifference X A) :
    (transport sx sy f p).base = f p.base := rfl

/-- Transport of the ordered pair is the pointwise image of BOTH states. -/
theorem toPair_transport {X Y A B : Type*}
    (sx : DifferenceSpace X A) (sy : DifferenceSpace Y B)
    (f : X → Y) (p : StateDifference X A) :
    (transport sx sy f p).toPair sy =
      (f (p.toPair sx).1, f (p.toPair sx).2) := by
  rcases p with ⟨x, a⟩
  apply Prod.ext
  · rfl
  · exact sy.shift_diff (f x) (f (sx.shift x a))

/-- Transport is *exactly* compositional; its intermediate base is `f x`.
No assumption on independence or on marginal DDT counts. -/
theorem transport_comp {X Y Z A B C : Type*}
    (sx : DifferenceSpace X A) (sy : DifferenceSpace Y B)
    (sz : DifferenceSpace Z C)
    (f : X → Y) (g : Y → Z) (p : StateDifference X A) :
    transport sy sz g (transport sx sy f p) =
      transport sx sz (g ∘ f) p := by
  rcases p with ⟨x, a⟩
  change
    StateDifference.mk (g (f x))
        (derivative sy sz g (derivative sx sy f a x) (f x)) =
      StateDifference.mk (g (f x))
        (derivative sx sz (g ∘ f) a x)
  rw [derivative_comp sx sy sz f g a x]

/-- A fixed input pair determines one concrete trajectory even for the identity map. -/
@[simp] theorem transport_id {X A : Type*}
    (s : DifferenceSpace X A) (p : StateDifference X A) :
    transport s s (fun x => x) p = p := by
  cases p
  simp only [transport, derivative_id]

/-- Recovering both concrete states uses the inverse of the state map;
    the difference-space coordinate equivalence alone does not supply it. -/
@[simp] theorem transport_symm_transport {X Y A B : Type*}
    (sx : DifferenceSpace X A) (sy : DifferenceSpace Y B)
    (f : X ≃ Y) (p : StateDifference X A) :
    transport sy sx f.symm (transport sx sy f p) = p := by
  rcases p with ⟨x, a⟩
  simp [transport, derivative, sy.shift_diff, sx.diff_shift]

@[simp]
theorem transport_transport_symm {X Y A B : Type*} (sx : DifferenceSpace X A)
    (sy : DifferenceSpace Y B) (f : X ≃ Y) (p : StateDifference Y B) :
    transport sx sy f (transport sy sx f.symm p) = p :=
  transport_symm_transport sy sx f.symm p

/-- A bijection of state spaces restores the whole input pair uniquely.
    The inverse transports both output states through `f.symm`. -/
def transportEquiv {X Y A B : Type*}
    (sx : DifferenceSpace X A) (sy : DifferenceSpace Y B)
    (f : X ≃ Y) : StateDifference X A ≃ StateDifference Y B where
  toFun := transport sx sy f
  invFun := transport sy sx f.symm
  left_inv := transport_symm_transport sx sy f
  right_inv := transport_transport_symm sx sy f

end StateDifference

end Diffan
