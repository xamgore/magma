module

import all Init.Data.Range.Basic
public import Magma.Differential.Windows.ScheduledMeetFiberTransport
public import Magma.Differential.Bridges.DiffanRoundDDTBridge
import Std.Tactic.BVDecide

@[expose] public section

/-!
# Actual state/difference propagation of a left-input XOR translation

The preceding fiber-transport certificate always supplies *some* induced
output equivalence.  Here we identify it pointwise for one Feistel round,
and give the exact state-dependent correction for the second round.

These statements concern ordinary G rounds, not the terminal GStar.
-/

namespace Magma.DiffanFeistelDeltaPropagation

open Magma
open Magma.DiffanReverseRound
open Magma.DiffanScheduledMeetFiberTransport

private abbrev Word :=
  V 32

private abbrev RoundState :=
  Word × Word

private abbrev Point :=
  Diffan.StateDifference RoundState RoundState

/-- Concrete propagation of a state-and-difference pair through one G round. -/
def roundPoint (k : Word) (p : Point) : Point :=
  Diffan.StateDifference.transport roundXor roundXor (G k) p

/-- Translate only the right component of the *difference*, not the base. -/
def shiftRightDelta (t : Word) (p : Point) : Point :=
  ⟨p.base, (p.delta.1, p.delta.2 ^^^ t)⟩

/-- The full one-round derivative, including the concrete base state. -/
theorem roundPoint_formula (k : Word) (p : Point) :
    roundPoint k p =
      ⟨G k p.base,
        (p.delta.2,
          (g k (p.base.2 ^^^ p.delta.2) ^^^ g k p.base.2) ^^^ p.delta.1)⟩ := by
  rcases p with ⟨⟨L, R⟩, ⟨aL, aR⟩⟩
  change (⟨G k (L, R),
    Diffan.derivative roundXor roundXor (G k) (aL, aR) (L, R)⟩ : Point) = _
  rw [Magma.DiffanRoundDDTBridge.derivative_G_eq_feistel,
      Magma.FeistelDDT.feistelXorDiff_eq]
  rfl

/-- The left-difference translation becomes a right-difference translation
    after one ordinary Feistel round. This holds for all keys, base states,
    input differences, and translation masks. -/
theorem first_round_shift (k t : Word) (p : Point) :
    roundPoint k (shiftInputLeftDelta t p) =
      shiftRightDelta t (roundPoint k p) := by
  rcases p with ⟨⟨L, R⟩, ⟨aL, aR⟩⟩
  simp only [roundPoint_formula]
  change
    (⟨G k (L, R),
      (aR, ((g k (R ^^^ aR) ^^^ g k R) ^^^ (aL ^^^ t)))⟩ : Point) =
    ⟨G k (L, R),
      (aR, (((g k (R ^^^ aR) ^^^ g k R) ^^^ aL) ^^^ t))⟩
  simp only [BitVec.xor_assoc]

/-- The exact extra effect on the second-round right output difference.
    It is a finite difference of the *real* g[k] at the actual midpoint. -/
def secondCorrection (k t : Word) (mid : Point) : Word :=
  g k (mid.base.2 ^^^ (mid.delta.2 ^^^ t)) ^^^
    g k (mid.base.2 ^^^ mid.delta.2)

/-- Moving the RIGHT input difference of a round changes both output
    differences. The left changes by t, while the right changes by the
    nonlinear correction, which is generally state-dependent. -/
theorem second_round_shift (k t : Word) (mid : Point) :
    roundPoint k (shiftRightDelta t mid) =
      ⟨(roundPoint k mid).base,
        ((roundPoint k mid).delta.1 ^^^ t,
         (roundPoint k mid).delta.2 ^^^ secondCorrection k t mid)⟩ := by
  rcases mid with ⟨⟨L, R⟩, ⟨aL, aR⟩⟩
  simp only [roundPoint_formula]
  change
    (⟨G k (L, R),
      (aR ^^^ t,
        ((g k (R ^^^ (aR ^^^ t)) ^^^ g k R) ^^^ aL))⟩ : Point) =
    ⟨G k (L, R),
      (aR ^^^ t,
        (((g k (R ^^^ aR) ^^^ g k R) ^^^ aL) ^^^
          (g k (R ^^^ (aR ^^^ t)) ^^^ g k (R ^^^ aR))))⟩
  have hcorrect :
      ((g k (R ^^^ (aR ^^^ t)) ^^^ g k R) ^^^ aL) =
        (((g k (R ^^^ aR) ^^^ g k R) ^^^ aL) ^^^
          (g k (R ^^^ (aR ^^^ t)) ^^^ g k (R ^^^ aR))) := by
    calc
      _ = (g k (R ^^^ aR) ^^^ g k (R ^^^ aR)) ^^^
          ((g k (R ^^^ (aR ^^^ t)) ^^^ g k R) ^^^ aL) := by
        rw [BitVec.xor_self, BitVec.zero_xor]
      _ = _ := by ac_rfl
  rw [hcorrect]

/-- Execute two ordinary Feistel rounds on the same concrete state pair. -/
def twoRoundPoint (k₀ k₁ : Word) (p : Point) : Point :=
  roundPoint k₁ (roundPoint k₀ p)

/-- Exact two-round transport: the first output half has a constant XOR
    translation, but the second has a correction evaluated at the actual
    intermediate state. -/
theorem two_round_shift (k₀ k₁ t : Word) (p : Point) :
    twoRoundPoint k₀ k₁ (shiftInputLeftDelta t p) =
      ⟨(twoRoundPoint k₀ k₁ p).base,
        ((twoRoundPoint k₀ k₁ p).delta.1 ^^^ t,
         (twoRoundPoint k₀ k₁ p).delta.2 ^^^
           secondCorrection k₁ t (roundPoint k₀ p))⟩ := by
  change
    roundPoint k₁ (roundPoint k₀ (shiftInputLeftDelta t p)) =
      ⟨(roundPoint k₁ (roundPoint k₀ p)).base,
        ((roundPoint k₁ (roundPoint k₀ p)).delta.1 ^^^ t,
         (roundPoint k₁ (roundPoint k₀ p)).delta.2 ^^^
           secondCorrection k₁ t (roundPoint k₀ p))⟩
  rw [first_round_shift]
  exact second_round_shift k₁ t (roundPoint k₀ p)

/-- If g[k] has a constant derivative in direction t, the second-round
    correction is uniform over *all* actual midpoint pairs. -/
theorem correction_of_constant_derivative (k t u : Word)
    (h : ∀ x : Word, g k (x ^^^ t) ^^^ g k x = u)
    (mid : Point) : secondCorrection k t mid = u := by
  rcases mid with ⟨⟨L, R⟩, ⟨aL, aR⟩⟩
  change g k (R ^^^ (aR ^^^ t)) ^^^ g k (R ^^^ aR) = u
  rw [← BitVec.xor_assoc]
  exact h (R ^^^ aR)

/-- Conversely, if the correction is uniform on all state/difference pairs,
    then g[k] really has a constant derivative. Only one simple family of
    midpoint pairs is needed for the converse. -/
theorem correction_uniform_iff_g_constant_derivative (k t u : Word) :
    (∀ mid : Point, secondCorrection k t mid = u) ↔
      (∀ x : Word, g k (x ^^^ t) ^^^ g k x = u) := by
  constructor
  · intro h x
    have hx := h (⟨(0#32, x), (0#32, 0#32)⟩ : Point)
    simpa only [secondCorrection, BitVec.xor_zero, BitVec.zero_xor] using hx
  · intro h mid
    exact correction_of_constant_derivative k t u h mid

/-- An exact, state-independent two-round output translation follows
    from a constant derivative of the SECOND g, not from the parity of
    the FIRST key or from a symmetry of marginal DDT entries. -/
theorem two_round_uniform_of_constant_derivative
    (k₀ k₁ t u : Word)
    (h : ∀ x : Word, g k₁ (x ^^^ t) ^^^ g k₁ x = u)
    (p : Point) :
    twoRoundPoint k₀ k₁ (shiftInputLeftDelta t p) =
      ⟨(twoRoundPoint k₀ k₁ p).base,
        ((twoRoundPoint k₀ k₁ p).delta.1 ^^^ t,
         (twoRoundPoint k₀ k₁ p).delta.2 ^^^ u)⟩ := by
  rw [two_round_shift,
      correction_of_constant_derivative k₁ t u h (roundPoint k₀ p)]

/-- The first-round law also holds at an actual scheduled round index,
    because the round key is selected from one master key. -/
theorem scheduled_first_round_shift
    (master : V 256) (i : Fin 32) (t : Word) (p : Point) :
    roundPoint (roundKey master i) (shiftInputLeftDelta t p) =
      shiftRightDelta t (roundPoint (roundKey master i) p) :=
  first_round_shift (roundKey master i) t p

end Magma.DiffanFeistelDeltaPropagation
