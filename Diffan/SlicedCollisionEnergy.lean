module
public import Diffan.Differential
import all Init.Data.Range.Basic

@[expose] public section

/-!
# Aggregate half-zero differential slice as projected collision energy

For ANY block map f : (W×W)->(W×W), let
  m_f(r,y) = #{l : (f(l,r)).left = y}.
Then the sum of all ordered left-output collisions at
a fixed input right half r is

  E_f = sum_{r,y} m_f(r,y)^2
      = sum_{r,l,l'} [f(l,r).left=f(l',r).left].

For W=(BitVec n), reparametrize l' = l XOR a and
b= f(l',r).right XOR f(l,r).right to recognize
  E_f = sum_{a,b} D_f((a,0),(0,b)).

This first file proves the generic fiber-square part,
a genuine reduction to half-output projection statistics.
It does not claim the 2^64 RFC codebook is efficient to build.
-/

namespace Diffan.SlicedCollisionEnergy

variable {W : Type*} [Fintype W] [DecidableEq W]

def projectedLeft (f : W × W → W × W) (r l : W) : W :=
  (f (l,r)).1

def fiberMass (f : W × W → W × W) (r y : W) : Nat :=
  ∑ l : W, if projectedLeft f r l = y then 1 else 0

def baseCollisionEnergy (f : W × W → W × W) : Nat :=
  ∑ r : W, ∑ l : W, ∑ lp : W,
    if projectedLeft f r l = projectedLeft f r lp then 1 else 0

def projectedFiberEnergy (f : W × W → W × W) : Nat :=
  ∑ r : W, ∑ y : W, (fiberMass f r y)^2

private theorem delta_pair_sum (p q : W) :
    (∑ y : W, (if p = y then 1 else 0) *
      (if q = y then 1 else 0)) = (if p = q then 1 else 0) := by
  classical
  by_cases hp : p = q
  · subst q
    simp
  · simp [hp]

theorem collision_energy_eq_fiber_squares
    (f : W × W → W × W) :
    baseCollisionEnergy f = projectedFiberEnergy f := by
  classical
  unfold baseCollisionEnergy projectedFiberEnergy
  apply Finset.sum_congr rfl
  intro r _
  calc
    (∑ l : W, ∑ lp : W,
      if projectedLeft f r l = projectedLeft f r lp then 1 else 0) =
      ∑ l : W, ∑ lp : W, ∑ y : W,
        (if projectedLeft f r l = y then 1 else 0) *
        (if projectedLeft f r lp = y then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro l _
          apply Finset.sum_congr rfl
          intro lp _
          exact (delta_pair_sum (projectedLeft f r l)
            (projectedLeft f r lp)).symm
    _ = ∑ y : W, ∑ l : W, ∑ lp : W,
        (if projectedLeft f r l = y then 1 else 0) *
        (if projectedLeft f r lp = y then 1 else 0) := by
          calc
            (∑ l : W, ∑ lp : W, ∑ y : W,
                (if projectedLeft f r l = y then 1 else 0) *
                (if projectedLeft f r lp = y then 1 else 0)) =
                ∑ l : W, ∑ y : W, ∑ lp : W,
                  (if projectedLeft f r l = y then 1 else 0) *
                  (if projectedLeft f r lp = y then 1 else 0) := by
                    apply Finset.sum_congr rfl
                    intro l _
                    rw [Finset.sum_comm]
            _ = ∑ y : W, ∑ l : W, ∑ lp : W,
                  (if projectedLeft f r l = y then 1 else 0) *
                  (if projectedLeft f r lp = y then 1 else 0) := by
                    rw [Finset.sum_comm]
    _ = ∑ y : W, (fiberMass f r y)^2 := by
          apply Finset.sum_congr rfl
          intro y _
          simp only [fiberMass, pow_two]
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro l _
          rw [Finset.mul_sum]

/-- A generic exact elimination of a FUNCTIONAL output label b:
choosing b and a witness x with q(x)=(a,b) carries
precisely the same information as choosing x with
the first output component fixed to a.

This applies to the aggregate half-zero differential
slice, where b is the OTHER 32-bit output-difference
component. It does NOT assume independent round DDTs. -/
def outputLabelFiberEquiv
    {X A B : Type*} (q : X → A × B) (a : A) :
    (Σ b : B, {x : X // q x = (a,b)}) ≃
    {x : X // (q x).1 = a} where
  toFun := fun p =>
    ⟨p.2.1, congrArg Prod.fst p.2.2⟩
  invFun := fun p =>
    ⟨(q p.1).2, ⟨p.1, Prod.ext p.2 rfl⟩⟩
  left_inv := by
    rintro ⟨b, ⟨x, h⟩⟩
    have hb : (q x).2 = b := congrArg Prod.snd h
    cases hb
    rfl
  right_inv := by
    intro p
    apply Subtype.ext
    rfl

/-- Exact Nat count law: summing all b removes the
dependent output coordinate and retains ONLY the
first-coordinate predicate, no false multiplier. -/
theorem sum_output_label_eliminates
    {X A B : Type*} [Fintype X] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (q : X → A × B) (a : A) :
    (∑ b : B, Fintype.card {x : X // q x = (a,b)}) =
      Fintype.card {x : X // (q x).1 = a} := by
  classical
  rw [← Fintype.card_sigma]
  exact Fintype.card_congr (outputLabelFiberEquiv q a)

end Diffan.SlicedCollisionEnergy
