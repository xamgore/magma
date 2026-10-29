module

public import Diffan.StateDifference
public import Diffan.Differential
import all Init.Data.Range.Basic

@[expose] public section

/-!
# State transformations with fixed difference conventions

A `DifferentialMap` fixes the source and target difference spaces as type
parameters of a state transformation. Its derivative, DDT and support use
the common mathematical specifications from `Diffan.Differential`.

Composition requires the same difference convention on the intermediate
state space. The derivative is evaluated at the actual intermediate state;
counts of intermediate trajectories require their own cardinality proofs.
-/

namespace Diffan

/-- A state transformation whose input and output difference conventions
are fixed by the source and target indices. -/
structure DifferentialMap {X Y A B : Type*}
    (sx : DifferenceSpace X A) (sy : DifferenceSpace Y B) where
  toFun : X → Y

namespace DifferentialMap

/-- Identity map for a fixed difference-space structure. -/
def id {X A : Type*} (sx : DifferenceSpace X A) :
    DifferentialMap sx sx := ⟨fun x => x⟩

/-- Apply a map to its input state. -/
def apply {X Y A B : Type*}
    {sx : DifferenceSpace X A} {sy : DifferenceSpace Y B}
    (f : DifferentialMap sx sy) (x : X) : Y := f.toFun x

/-- Apply an input difference at a *particular* base state. -/
def derivative {X Y A B : Type*}
    {sx : DifferenceSpace X A} {sy : DifferenceSpace Y B}
    (f : DifferentialMap sx sy) (a : A) (x : X) : B :=
  Diffan.derivative sx sy f.toFun a x

/-- Exact finite cardinality of the fiber selected by `a → b`. -/
def ddt {X Y A B : Type*} [Fintype X] [DecidableEq B]
    {sx : DifferenceSpace X A} {sy : DifferenceSpace Y B}
    (f : DifferentialMap sx sy) (a : A) (b : B) : Nat :=
  Diffan.ddt sx sy f.toFun a b

/-- A transition is supported if one actual base state witnesses it. -/
def support {X Y A B : Type*}
    {sx : DifferenceSpace X A} {sy : DifferenceSpace Y B}
    (f : DifferentialMap sx sy) (a : A) (b : B) : Prop :=
  Diffan.support sx sy f.toFun a b

/-- Pair-preserving, exact transport (not a marginal transition). -/
def transport {X Y A B : Type*}
    {sx : DifferenceSpace X A} {sy : DifferenceSpace Y B}
    (f : DifferentialMap sx sy) (p : StateDifference X A) :
    StateDifference Y B :=
  StateDifference.transport sx sy f.toFun p

/-- Execute `f`, then `g`. -/
def comp {X Y Z A B C : Type*}
    {sx : DifferenceSpace X A} {sy : DifferenceSpace Y B}
    {sz : DifferenceSpace Z C}
    (f : DifferentialMap sx sy) (g : DifferentialMap sy sz) :
    DifferentialMap sx sz := ⟨g.toFun ∘ f.toFun⟩

/-- Derivatives compose at the actual intermediate state. -/
theorem derivative_comp {X Y Z A B C : Type*}
    {sx : DifferenceSpace X A} {sy : DifferenceSpace Y B}
    {sz : DifferenceSpace Z C}
    (f : DifferentialMap sx sy) (g : DifferentialMap sy sz)
    (a : A) (x : X) :
    (f.comp g).derivative a x =
      g.derivative (f.derivative a x) (f.toFun x) := by
  exact Diffan.derivative_comp sx sy sz f.toFun g.toFun a x

/-- Bundle a composed pair's concrete state and difference. -/
theorem transport_comp {X Y Z A B C : Type*}
    {sx : DifferenceSpace X A} {sy : DifferenceSpace Y B}
    {sz : DifferenceSpace Z C}
    (f : DifferentialMap sx sy) (g : DifferentialMap sy sz)
    (p : StateDifference X A) :
    g.transport (f.transport p) = (f.comp g).transport p := by
  exact StateDifference.transport_comp sx sy sz f.toFun g.toFun p

/-- The common DDT specification lets a certified counter apply to the
    bundled transformation as well as its underlying state function. -/
theorem ddt_eq_unbundled {X Y A B : Type*}
    [Fintype X] [DecidableEq B]
    {sx : DifferenceSpace X A} {sy : DifferenceSpace Y B}
    (f : DifferentialMap sx sy) (a : A) (b : B) :
    f.ddt a b = Diffan.ddt sx sy f.toFun a b := rfl

end DifferentialMap

end Diffan
