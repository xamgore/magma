module

import all Init.Data.Range.Basic
public import Magma.Differential.FourRounds.FourRoundIntrinsicRectangularity

@[expose] public section

/-!
# Exact four-round midpoint equations for arbitrary boundary differences

The special boundary slice `(aL,0) -> (0,bR)` has a rectangular
middle-base fiber. Here all four boundary half-differences are arbitrary.
We reconstruct the two *outer* differences as well as the two inner ones,
without treating intermediate DDT factors as independent.

Each equation uses the same scheduled 256-bit master key. In particular,
the four equations are pointwise constraints on the SAME two-word base
and two-word difference at the midpoint.
-/

namespace Magma.DiffanFourRoundGeneralBoundaryEquations

open Magma
open Magma.MultiRoundDDT
open Magma.DiffanFourRoundScheduledMiddleFibers
open Magma.DiffanFourRoundForcedMiddleDifference
open Magma.DiffanFourRoundIntrinsicRectangularity

private abbrev Word :=
  V 32

private abbrev Master :=
  V 256

private abbrev RoundState :=
  Word × Word

private abbrev Point :=
  Diffan.StateDifference RoundState RoundState

private theorem xor_unwind (u v w : Word) (h : u = v ^^^ w) : w = v ^^^ u := by
  calc
    w = (v ^^^ v) ^^^ w := by simp only [BitVec.xor_self, BitVec.zero_xor]
    _ = v ^^^ (v ^^^ w) := by rw [BitVec.xor_assoc]
    _ = v ^^^ u := congrArg (fun z : Word => v ^^^ z) h.symm

private theorem xor_right_eq_iff (u a b : Word) : u ^^^ a = b ↔ u = b ^^^ a := by
  constructor
  · intro h
    have hh := congrArg (fun z : Word => z ^^^ a) h
    simpa only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero] using hh
  · intro h
    rw [h]
    simp only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

private theorem step_base_right (k : Word) (p : Point) :
    (step k p).base.2 = g k p.base.2 ^^^ p.base.1 :=
  rfl

private theorem step_right (k : Word) (p : Point) :
    (step k p).delta.2 = gDifference k p.base.2 p.delta.2 ^^^ p.delta.1 := by
  rw [step_delta]
  rfl

/-- Recover the LEFT input difference from the *complete* midpoint.
The right input difference is reconstructed in `prefix_input_right`. -/
theorem prefix_input_left (master : Master) (mid : Point) :
    ((left master).symm mid).delta.1 =
      gDifference (roundKey master (0 : Fin 32))
        (mid.base.2 ^^^ g (roundKey master (1 : Fin 32)) mid.base.1)
        (((left master).symm mid).delta.2) ^^^ mid.delta.1 := by
  let p : Point := (left master).symm mid
  let z : Point := step (roundKey master (0 : Fin 32)) p
  have heq : step (roundKey master (1 : Fin 32)) z = mid := by
    change step (roundKey master (1 : Fin 32))
      (step (roundKey master (0 : Fin 32)) ((left master).symm mid)) = mid
    rw [← left_eq_two_steps]
    exact (left master).apply_symm_apply mid
  have hzRight : z.base.2 = mid.base.1 := by
    have hh := congrArg (fun q : Point => q.base.1) heq
    change z.base.2 = mid.base.1 at hh
    exact hh
  have hzBase : z.base.1 =
      mid.base.2 ^^^ g (roundKey master (1 : Fin 32)) mid.base.1 := by
    have hh := congrArg (fun q : Point => q.base.2) heq
    change g (roundKey master (1 : Fin 32)) z.base.2 ^^^ z.base.1 =
      mid.base.2 at hh
    rw [hzRight] at hh
    calc
      z.base.1 =
          (g (roundKey master (1 : Fin 32)) mid.base.1 ^^^ z.base.1) ^^^
            g (roundKey master (1 : Fin 32)) mid.base.1 := by
              calc
                z.base.1 =
                    (g (roundKey master (1 : Fin 32)) mid.base.1 ^^^
                      g (roundKey master (1 : Fin 32)) mid.base.1) ^^^ z.base.1 := by
                        simp only [BitVec.xor_self, BitVec.zero_xor]
                _ = (g (roundKey master (1 : Fin 32)) mid.base.1 ^^^ z.base.1) ^^^
                    g (roundKey master (1 : Fin 32)) mid.base.1 := by ac_rfl
      _ = mid.base.2 ^^^ g (roundKey master (1 : Fin 32)) mid.base.1 :=
        congrArg
          (fun w : Word => w ^^^ g (roundKey master (1 : Fin 32)) mid.base.1) hh
  have hzLeft : z.delta.2 = mid.delta.1 := by
    have hh := congrArg (fun q : Point => q.delta.1) heq
    rw [step_left] at hh
    exact hh
  have hfirst : z.delta.2 =
      gDifference (roundKey master (0 : Fin 32)) p.base.2 p.delta.2 ^^^
        p.delta.1 := step_right _ p
  have hsolve := xor_unwind z.delta.2
    (gDifference (roundKey master (0 : Fin 32)) p.base.2 p.delta.2)
    p.delta.1 hfirst
  change p.delta.1 = _
  calc
    p.delta.1 =
        gDifference (roundKey master (0 : Fin 32)) p.base.2 p.delta.2 ^^^
          z.delta.2 := hsolve
    _ = gDifference (roundKey master (0 : Fin 32))
          (mid.base.2 ^^^ g (roundKey master (1 : Fin 32)) mid.base.1)
          p.delta.2 ^^^ mid.delta.1 := by
            have hbase : p.base.2 = z.base.1 := rfl
            rw [hbase, hzBase, hzLeft]

/-- Recover the RIGHT output difference from the complete midpoint.
The left output difference is given by `suffix_output_left`. -/
theorem suffix_output_right (master : Master) (mid : Point) :
    (right master mid).delta.2 =
      gDifference (roundKey master (3 : Fin 32))
        (g (roundKey master (2 : Fin 32)) mid.base.2 ^^^ mid.base.1)
        ((right master mid).delta.1) ^^^ mid.delta.2 := by
  let z : Point := step (roundKey master (2 : Fin 32)) mid
  have hbase : z.base.2 =
      g (roundKey master (2 : Fin 32)) mid.base.2 ^^^ mid.base.1 := rfl
  have hleft : z.delta.1 = mid.delta.2 := step_left _ mid
  have hright : z.delta.2 =
      gDifference (roundKey master (2 : Fin 32)) mid.base.2 mid.delta.2 ^^^
        mid.delta.1 := step_right _ mid
  have hout : (right master mid).delta.1 = z.delta.2 := by
    rw [right_eq_two_steps]
    exact step_left _ z
  have hlast : (right master mid).delta.2 =
      gDifference (roundKey master (3 : Fin 32)) z.base.2 z.delta.2 ^^^
        z.delta.1 := by
    rw [right_eq_two_steps]
    exact step_right _ z
  calc
    (right master mid).delta.2 =
        gDifference (roundKey master (3 : Fin 32)) z.base.2 z.delta.2 ^^^
          z.delta.1 := hlast
    _ = gDifference (roundKey master (3 : Fin 32))
          (g (roundKey master (2 : Fin 32)) mid.base.2 ^^^ mid.base.1)
          ((right master mid).delta.1) ^^^ mid.delta.2 := by
            rw [hbase, hleft, ← hout]

/-- Both input half-differences, expressed using ONLY the midpoint. -/
theorem reconstructed_input_delta (master : Master) (mid : Point) :
    ((left master).symm mid).delta =
      (gDifference (roundKey master (0 : Fin 32))
          (mid.base.2 ^^^ g (roundKey master (1 : Fin 32)) mid.base.1)
          (gDifference (roundKey master (1 : Fin 32)) mid.base.1
              mid.delta.1 ^^^ mid.delta.2) ^^^ mid.delta.1,
       gDifference (roundKey master (1 : Fin 32)) mid.base.1
         mid.delta.1 ^^^ mid.delta.2) := by
  apply Prod.ext
  · rw [prefix_input_left, prefix_input_right]
  · exact prefix_input_right master mid

/-- Both output half-differences in the same middle coordinates. -/
theorem reconstructed_output_delta (master : Master) (mid : Point) :
    (right master mid).delta =
      (gDifference (roundKey master (2 : Fin 32)) mid.base.2
          mid.delta.2 ^^^ mid.delta.1,
       gDifference (roundKey master (3 : Fin 32))
         (g (roundKey master (2 : Fin 32)) mid.base.2 ^^^ mid.base.1)
         (gDifference (roundKey master (2 : Fin 32)) mid.base.2
           mid.delta.2 ^^^ mid.delta.1) ^^^ mid.delta.2) := by
  apply Prod.ext
  · exact suffix_output_left master mid
  · rw [suffix_output_right, suffix_output_left]

/-- Genuine unmasked endpoint compatibility for arbitrary boundary
half-differences is equivalent to matching two *explicit* midpoint formulas. -/
theorem general_boundary_exact (master : Master) (a b : RoundState)
    (mid : Point) :
    middleCondition master (inputMasked a (0#32))
      (outputMasked b (0#32)) (fun _ => True) mid ↔
      (gDifference (roundKey master (0 : Fin 32))
          (mid.base.2 ^^^ g (roundKey master (1 : Fin 32)) mid.base.1)
          (gDifference (roundKey master (1 : Fin 32)) mid.base.1
            mid.delta.1 ^^^ mid.delta.2) ^^^ mid.delta.1,
        gDifference (roundKey master (1 : Fin 32)) mid.base.1
          mid.delta.1 ^^^ mid.delta.2) = a ∧
      (gDifference (roundKey master (2 : Fin 32)) mid.base.2
          mid.delta.2 ^^^ mid.delta.1,
        gDifference (roundKey master (3 : Fin 32))
          (g (roundKey master (2 : Fin 32)) mid.base.2 ^^^ mid.base.1)
          (gDifference (roundKey master (2 : Fin 32)) mid.base.2
            mid.delta.2 ^^^ mid.delta.1) ^^^ mid.delta.2) = b := by
  change
    ((((left master).symm mid).delta = a ∧
      (((left master).symm mid).base.2 &&& (0#32)) = (0#32)) ∧
      True ∧
      ((right master mid).delta = b ∧
        ((right master mid).base.1 &&& (0#32)) = (0#32))) ↔ _
  simp only [BitVec.and_zero, true_and, and_true]
  rw [reconstructed_input_delta, reconstructed_output_delta]

/-- Pure XOR algebra behind the four boundary equations. The two
inner derivatives determine the right input and left output halves;
the outer derivatives then constrain the remaining two halves. -/
private theorem nested_boundary_iff
    (p q : Word → Word) (e f c d aL aR bL bR : Word) :
    ((p (e ^^^ d) ^^^ c, e ^^^ d) = (aL, aR) ∧
      (f ^^^ c, q (f ^^^ c) ^^^ d) = (bL, bR)) ↔
    e = aR ^^^ d ∧ f = bL ^^^ c ∧
      p aR = aL ^^^ c ∧ q bL = bR ^^^ d := by
  constructor
  · rintro ⟨hi, ho⟩
    have he : e ^^^ d = aR := congrArg Prod.snd hi
    have hf : f ^^^ c = bL := congrArg Prod.fst ho
    have hp : p (e ^^^ d) ^^^ c = aL := congrArg Prod.fst hi
    have hq : q (f ^^^ c) ^^^ d = bR := congrArg Prod.snd ho
    rw [he] at hp
    rw [hf] at hq
    exact ⟨(xor_right_eq_iff e d aR).mp he,
      (xor_right_eq_iff f c bL).mp hf,
      (xor_right_eq_iff (p aR) c aL).mp hp,
      (xor_right_eq_iff (q bL) d bR).mp hq⟩
  · rintro ⟨he, hf, hp, hq⟩
    have he' : e ^^^ d = aR := (xor_right_eq_iff e d aR).mpr he
    have hf' : f ^^^ c = bL := (xor_right_eq_iff f c bL).mpr hf
    constructor
    · apply Prod.ext
      · change p (e ^^^ d) ^^^ c = aL
        rw [he']
        exact (xor_right_eq_iff (p aR) c aL).mpr hp
      · exact he'
    · apply Prod.ext
      · exact hf'
      · change q (f ^^^ c) ^^^ d = bR
        rw [hf']
        exact (xor_right_eq_iff (q bL) d bR).mpr hq

/-- The complete four-equation constraint on a real four-round midpoint.
All four scheduled round keys share one master key.

With `mid = ((u,v),(c,d))`, the inner equations constrain one base word
each, but the two outer equations involve BOTH base words. This is the
precise place where intrinsic coordinate coupling can arise. -/
theorem general_boundary_four_equations
    (master : Master) (aL aR bL bR u v c d : Word) :
    middleCondition master
      (inputMasked (aL, aR) (0#32))
      (outputMasked (bL, bR) (0#32)) (fun _ => True)
      (⟨(u, v), (c, d)⟩ : Point) ↔
    gDifference (roundKey master (1 : Fin 32)) u c = aR ^^^ d ∧
    gDifference (roundKey master (2 : Fin 32)) v d = bL ^^^ c ∧
    gDifference (roundKey master (0 : Fin 32))
      (v ^^^ g (roundKey master (1 : Fin 32)) u) aR = aL ^^^ c ∧
    gDifference (roundKey master (3 : Fin 32))
      (g (roundKey master (2 : Fin 32)) v ^^^ u) bL = bR ^^^ d := by
  rw [general_boundary_exact]
  change
    ((gDifference (roundKey master (0 : Fin 32))
        (v ^^^ g (roundKey master (1 : Fin 32)) u)
        (gDifference (roundKey master (1 : Fin 32)) u c ^^^ d) ^^^ c,
      gDifference (roundKey master (1 : Fin 32)) u c ^^^ d) = (aL, aR) ∧
     (gDifference (roundKey master (2 : Fin 32)) v d ^^^ c,
       gDifference (roundKey master (3 : Fin 32))
         (g (roundKey master (2 : Fin 32)) v ^^^ u)
         (gDifference (roundKey master (2 : Fin 32)) v d ^^^ c) ^^^ d) =
         (bL, bR)) ↔ _
  exact nested_boundary_iff
    (gDifference (roundKey master (0 : Fin 32))
      (v ^^^ g (roundKey master (1 : Fin 32)) u))
    (gDifference (roundKey master (3 : Fin 32))
      (g (roundKey master (2 : Fin 32)) v ^^^ u))
    (gDifference (roundKey master (1 : Fin 32)) u c)
    (gDifference (roundKey master (2 : Fin 32)) v d)
    c d aL aR bL bR

/-- The exact, full-middle equation fiber for arbitrary four boundary
half-differences. Keeping the same `(u,v,c,d)` retains all correlations. -/
abbrev boundaryEquationFiber (master : Master)
    (aL aR bL bR : Word) : Type :=
  {mid : Point //
    gDifference (roundKey master (1 : Fin 32))
      mid.base.1 mid.delta.1 = aR ^^^ mid.delta.2 ∧
    gDifference (roundKey master (2 : Fin 32))
      mid.base.2 mid.delta.2 = bL ^^^ mid.delta.1 ∧
    gDifference (roundKey master (0 : Fin 32))
      (mid.base.2 ^^^ g (roundKey master (1 : Fin 32)) mid.base.1)
      aR = aL ^^^ mid.delta.1 ∧
    gDifference (roundKey master (3 : Fin 32))
      (g (roundKey master (2 : Fin 32)) mid.base.2 ^^^ mid.base.1)
      bL = bR ^^^ mid.delta.2}

/-- Exact (not overapproximated) correspondence with all genuine
midpoint conditions from two two-round scheduled segments. -/
def generalEquationEquiv (master : Master)
    (aL aR bL bR : Word) :
    middleFiber master
      (inputMasked (aL, aR) (0#32))
      (outputMasked (bL, bR) (0#32)) (fun _ => True) ≃
    boundaryEquationFiber master aL aR bL bR where
  toFun := by
    intro w
    rcases w with ⟨⟨⟨u, v⟩, ⟨c, d⟩⟩, h⟩
    exact ⟨⟨(u, v), (c, d)⟩,
      (general_boundary_four_equations master aL aR bL bR u v c d).mp h⟩
  invFun := by
    intro w
    rcases w with ⟨⟨⟨u, v⟩, ⟨c, d⟩⟩, h⟩
    exact ⟨⟨(u, v), (c, d)⟩,
      (general_boundary_four_equations master aL aR bL bR u v c d).mpr h⟩
  left_inv := by
    intro w
    apply Subtype.ext
    rfl
  right_inv := by
    intro w
    apply Subtype.ext
    rfl

/-- A direct equivalence from genuine joined endpoint witnesses to the
four-equation fiber. This avoids comparing the huge enumerated `Fintype`
instances of an intermediate middle fiber when proving cardinalities. -/
def generalJoinedEquiv (master : Master)
    (aL aR bL bR : Word) :
    joined master
      (inputMasked (aL, aR) (0#32))
      (outputMasked (bL, bR) (0#32)) (fun _ => True) ≃
    boundaryEquationFiber master aL aR bL bR := by
  refine Equiv.trans (Diffan.Meet.fiberEquiv (left master) (right master)
    (fun p => inputMasked (aL, aR) (0#32) p ∧
      (fun _ : Point => True) ((left master) p))
    (outputMasked (bL, bR) (0#32))).symm ?_
  exact (endpointsToMiddle master
    (inputMasked (aL, aR) (0#32))
    (outputMasked (bL, bR) (0#32)) (fun _ => True)).trans
    (generalEquationEquiv master aL aR bL bR)

open scoped Classical in
/-- Exact four-round count under one master key and arbitrary input/output
half-differences. All four derivative constraints describe the same path. -/
theorem general_fourRound_exact_equation_count (master : Master)
    (aL aR bL bR : Word) :
    Fintype.card (joined master
      (inputMasked (aL, aR) (0#32))
      (outputMasked (bL, bR) (0#32)) (fun _ => True)) =
    Fintype.card (boundaryEquationFiber master aL aR bL bR) := by
  classical
  exact Fintype.card_congr
    (generalJoinedEquiv master aL aR bL bR)

end Magma.DiffanFourRoundGeneralBoundaryEquations
