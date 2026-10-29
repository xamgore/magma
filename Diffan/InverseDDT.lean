module

import all Init.Data.Range.Basic
public import Diffan.StateDifference
public import Diffan.Differential

@[expose] public section

/-!
# Inverse DDT — exact forward/backward fiber correspondence

A bijection `f : X ≃ Y` maps a concrete witness for `a → b` in `f`
to a concrete witness for `b → a` in `f.symm`. This is a *bijection
of the actual input fibers*, not a claim that a differential path can
be reconstructed from a difference alone.

Transporting the base state through `f` pairs each forward witness with
exactly one inverse witness.
-/

namespace Diffan

/-- Exact correspondence of forward and inverse differential witnesses.
    A witness is a concrete base state, not only the input difference. -/
def inverseDDTFiberEquiv {X Y A B : Type*}
    (sx : DifferenceSpace X A) (sy : DifferenceSpace Y B)
    (f : X ≃ Y) (a : A) (b : B) :
    {x : X // derivative sx sy (f : X → Y) a x = b} ≃
    {y : Y // derivative sy sx (f.symm : Y → X) b y = a} where
  toFun w := ⟨f w.1, by
    have h := congrArg StateDifference.delta
      (StateDifference.transport_symm_transport sx sy f
        (⟨w.1, a⟩ : StateDifference X A))
    change derivative sy sx (f.symm : Y → X)
      (derivative sx sy (f : X → Y) a w.1) (f w.1) = a at h
    rw [w.2] at h
    exact h⟩
  invFun w := ⟨f.symm w.1, by
    have h := congrArg StateDifference.delta
      (StateDifference.transport_transport_symm sx sy f
        (⟨w.1, b⟩ : StateDifference Y B))
    change derivative sx sy (f : X → Y)
      (derivative sy sx (f.symm : Y → X) b w.1) (f.symm w.1) = b at h
    rw [w.2] at h
    exact h⟩
  left_inv := by
    intro w
    apply Subtype.ext
    exact f.left_inv w.1
  right_inv := by
    intro w
    apply Subtype.ext
    exact f.right_inv w.1

/-- For every bijection, the number of forward `a → b` witnesses equals
    the number of inverse `b → a` witnesses. -/
theorem ddt_equiv_symm {X Y A B : Type*}
    [Fintype X] [Fintype Y] [DecidableEq A] [DecidableEq B]
    (sx : DifferenceSpace X A) (sy : DifferenceSpace Y B)
    (f : X ≃ Y) (a : A) (b : B) :
    ddt sx sy (f : X → Y) a b =
      ddt sy sx (f.symm : Y → X) b a := by
  classical
  calc
    ddt sx sy (f : X → Y) a b =
        Fintype.card {x : X // derivative sx sy (f : X → Y) a x = b} := by
      simp [ddt, Fintype.card_subtype]
    _ = Fintype.card
          {y : Y // derivative sy sx (f.symm : Y → X) b y = a} :=
      Fintype.card_congr (inverseDDTFiberEquiv sx sy f a b)
    _ = ddt sy sx (f.symm : Y → X) b a := by
      simp [ddt, Fintype.card_subtype]

/-- Possible forward differences are exactly possible reverse differences,
    with input and output exchanged. -/
theorem support_equiv_symm {X Y A B : Type*}
    (sx : DifferenceSpace X A) (sy : DifferenceSpace Y B)
    (f : X ≃ Y) (a : A) (b : B) :
    support sx sy (f : X → Y) a b ↔
      support sy sx (f.symm : Y → X) b a := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨f x, (inverseDDTFiberEquiv sx sy f a b ⟨x, hx⟩).2⟩
  · rintro ⟨y, hy⟩
    exact ⟨f.symm y, ((inverseDDTFiberEquiv sx sy f a b).symm ⟨y, hy⟩).2⟩

end Diffan
