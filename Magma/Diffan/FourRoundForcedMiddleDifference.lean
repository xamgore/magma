module

import all Init.Data.Range.Basic
public import Magma.Diffan.FourRoundScheduledMiddleFibers
public import Magma.Diffan.DiffanRoundDDTBridge

@[expose] public section

/-!
# Four scheduled Magma rounds: the entire middle difference is forced

For four *ordinary* Feistel rounds with input difference `(aL,0)` and
output difference `(0,bR)`, the midpoint after two rounds has exactly
`(aL,bR)` as its difference. This is pointwise: it holds for every
actual base state and every common 256-bit master key.

Consequently a constrained full-middle StateDifference fiber is
canonically equivalent to a fiber over the 64-bit *base state only*.
This is an exact reduction, not the multiplication of marginal DDTs.
-/

namespace Magma.DiffanFourRoundForcedMiddleDifference

open Magma
open Magma.DiffanReverseRound
open Magma.DiffanFourRoundScheduledMiddleFibers

private abbrev Word :=
  V 32

private abbrev Master :=
  V 256

private abbrev RoundState :=
  Word × Word

private abbrev Point :=
  Diffan.StateDifference RoundState RoundState

/-- Transport both states of a differential pair by one ordinary Feistel round. -/
def step (k : Word) (p : Point) : Point :=
  Diffan.StateDifference.transport roundXor roundXor (G k) p

/-- The exact one-round difference law, at the actual base state. -/
theorem step_delta (k : Word) (p : Point) :
    (step k p).delta =
      (p.delta.2,
        (g k (p.base.2 ^^^ p.delta.2) ^^^ g k p.base.2) ^^^ p.delta.1) := by
  change Diffan.derivative roundXor roundXor (G k) p.delta p.base = _
  rw [Magma.DiffanRoundDDTBridge.derivative_G_eq_feistel]
  exact Magma.FeistelDDT.feistelXorDiff_eq k
    p.delta.1 p.delta.2 p.base.1 p.base.2

theorem step_left (k : Word) (p : Point) : (step k p).delta.1 = p.delta.2 := by rw [step_delta]

theorem step_right_of_zero_right (k : Word) (p : Point) (h : p.delta.2 = (0#32)) :
    (step k p).delta.2 = p.delta.1 := by
  rw [step_delta]
  change (g k (p.base.2 ^^^ p.delta.2) ^^^ g k p.base.2) ^^^ p.delta.1 = p.delta.1
  rw [h]
  simp only [BitVec.xor_zero, BitVec.xor_self, BitVec.zero_xor]

/-- After two rounds an input difference `(aL,0)` forces the left half
of the middle difference to equal `aL`, independently of both keys. -/
theorem two_steps_left_of_zero_input_right
    (k₀ k₁ : Word) (p : Point) (h : p.delta.2 = (0#32)) :
    (step k₁ (step k₀ p)).delta.1 = p.delta.1 := by
  rw [step_left]
  exact step_right_of_zero_right k₀ p h

/-- For a two-round suffix, zero final LEFT difference forces the
final right difference to equal the initial right difference. -/
theorem two_steps_right_of_zero_output_left
    (k₂ k₃ : Word) (mid : Point)
    (h : (step k₃ (step k₂ mid)).delta.1 = (0#32)) :
    (step k₃ (step k₂ mid)).delta.2 = mid.delta.2 := by
  have hz : (step k₂ mid).delta.2 = (0#32) := by
    rw [step_left] at h
    exact h
  calc
    (step k₃ (step k₂ mid)).delta.2 = (step k₂ mid).delta.1 :=
      step_right_of_zero_right k₃ (step k₂ mid) hz
    _ = mid.delta.2 := step_left k₂ mid

/-! ## Linking the formulas to the true 256-bit key schedule -/

private theorem firstTwo_run (master : Master) (x : RoundState) :
    (Magma.DiffanScheduledMeet.scheduledRounds master firstTwo).forward.run x =
      G (roundKey master (1 : Fin 32)) (G (roundKey master (0 : Fin 32)) x) := by
  rfl

private theorem secondTwo_run (master : Master) (x : RoundState) :
    (Magma.DiffanScheduledMeet.scheduledRounds master secondTwo).forward.run x =
      G (roundKey master (3 : Fin 32)) (G (roundKey master (2 : Fin 32)) x) := by
  rfl

/-- The abstract left half is exactly two concrete single-step transports. -/
theorem left_eq_two_steps (master : Master) (p : Point) :
    left master p =
      step (roundKey master (1 : Fin 32))
        (step (roundKey master (0 : Fin 32)) p) := by
  change
    Diffan.StateDifference.transport roundXor roundXor
      (Magma.DiffanScheduledMeet.scheduledRounds master firstTwo).forward.run p = _
  have hrun :
      (Magma.DiffanScheduledMeet.scheduledRounds master firstTwo).forward.run =
        (G (roundKey master (1 : Fin 32))) ∘
          (G (roundKey master (0 : Fin 32))) := by
    funext x
    exact firstTwo_run master x
  rw [hrun]
  exact (Diffan.StateDifference.transport_comp roundXor roundXor roundXor
    (G (roundKey master (0 : Fin 32)))
    (G (roundKey master (1 : Fin 32))) p).symm

/-- And similarly the right half is the next two rounds of the same key. -/
theorem right_eq_two_steps (master : Master) (p : Point) :
    right master p =
      step (roundKey master (3 : Fin 32))
        (step (roundKey master (2 : Fin 32)) p) := by
  change
    Diffan.StateDifference.transport roundXor roundXor
      (Magma.DiffanScheduledMeet.scheduledRounds master secondTwo).forward.run p = _
  have hrun :
      (Magma.DiffanScheduledMeet.scheduledRounds master secondTwo).forward.run =
        (G (roundKey master (3 : Fin 32))) ∘
          (G (roundKey master (2 : Fin 32))) := by
    funext x
    exact secondTwo_run master x
  rw [hrun]
  exact (Diffan.StateDifference.transport_comp roundXor roundXor roundXor
    (G (roundKey master (2 : Fin 32)))
    (G (roundKey master (3 : Fin 32))) p).symm

/-- Pointwise forcing: full midpoint difference, not merely one bit. -/
theorem forced_middle_difference (master : Master) (aL bR : Word)
    (mid : Point)
    (hin : ((left master).symm mid).delta = (aL, 0#32))
    (hout : (right master mid).delta = (0#32, bR)) :
    mid.delta = (aL, bR) := by
  let initial : Point := (left master).symm mid
  have hleft : (left master initial).delta.1 = initial.delta.1 := by
    rw [left_eq_two_steps]
    apply two_steps_left_of_zero_input_right
    simpa [initial] using congrArg Prod.snd hin
  have hmid : left master initial = mid := (left master).apply_symm_apply mid
  have hl : mid.delta.1 = aL := by
    rw [hmid] at hleft
    exact hleft.trans (congrArg Prod.fst hin)
  have houtzero : (right master mid).delta.1 = (0#32) :=
    (congrArg Prod.fst hout)
  have hright : (right master mid).delta.2 = mid.delta.2 := by
    rw [right_eq_two_steps]
    apply two_steps_right_of_zero_output_left
    simpa only [← right_eq_two_steps] using houtzero
  have hr : mid.delta.2 = bR := hright.symm.trans (congrArg Prod.snd hout)
  exact Prod.ext hl hr

/-- Input/output masked constraints force the same complete middle
    difference, regardless of the intermediate predicate `R`. -/
theorem masked_middle_delta (master : Master) (aL bR : Word)
    (inputMask outputMask : Word) (R : Point → Prop)
    (mid : Point)
    (h : middleCondition master
      (inputMasked (aL, 0#32) inputMask)
      (outputMasked (0#32, bR) outputMask) R mid) :
    mid.delta = (aL, bR) := by
  exact forced_middle_difference master aL bR mid h.1.1 h.2.2.1

/-- Only base states need to be counted: the midpoint difference is fixed
by the endpoint differences. Any genuine midpoint condition is retained. -/
abbrev baseFiber (master : Master) (aL bR : Word)
    (inputMask outputMask : Word) (R : Point → Prop) : Type _ :=
  {base : RoundState // middleCondition master
    (inputMasked (aL, 0#32) inputMask)
    (outputMasked (0#32, bR) outputMask) R
    ⟨base, (aL, bR)⟩}

/-- Lossless reduction from a 128-bit StateDifference middle point to
its 64-bit concrete base state in this particular four-round slice. -/
def middleBaseEquiv (master : Master) (aL bR : Word)
    (inputMask outputMask : Word) (R : Point → Prop) :
    middleFiber master
      (inputMasked (aL, 0#32) inputMask)
      (outputMasked (0#32, bR) outputMask) R ≃
    baseFiber master aL bR inputMask outputMask R where
  toFun := by
    intro w
    obtain ⟨⟨base, delta⟩, h⟩ := w
    have hd : delta = (aL, bR) :=
      masked_middle_delta master aL bR inputMask outputMask R ⟨base, delta⟩ h
    subst delta
    exact ⟨base, h⟩
  invFun := fun w => ⟨⟨w.1, (aL, bR)⟩, w.2⟩
  left_inv := by
    rintro ⟨⟨base, delta⟩, h⟩
    apply Subtype.ext
    have hd : delta = (aL, bR) :=
      masked_middle_delta master aL bR inputMask outputMask R ⟨base, delta⟩ h
    cases hd
    rfl
  right_inv := by
    intro w
    apply Subtype.ext
    rfl

open scoped Classical in
/-- The exact four-round *constrained* count can be written with a
single 64-bit base state and a fixed middle difference `(aL,bR)`. -/
theorem fourRound_exact_base_count (master : Master) (aL bR : Word)
    (inputMask outputMask : Word) (R : Point → Prop) :
    Fintype.card (joined master
      (inputMasked (aL, 0#32) inputMask)
      (outputMasked (0#32, bR) outputMask) R) =
    Fintype.card (baseFiber master aL bR inputMask outputMask R) := by
  classical
  calc
    _ = Fintype.card (middleFiber master
          (inputMasked (aL, 0#32) inputMask)
          (outputMasked (0#32, bR) outputMask) R) :=
      joined_card_eq_middle_card master _ _ _
    _ = _ := Fintype.card_congr
      (middleBaseEquiv master aL bR inputMask outputMask R)

/-- The earlier one-bit split is always deterministic on the genuine
four-round fiber of this zero-boundary slice. -/
theorem forced_bit_label (master : Master) (aL bR : Word)
    (inputMask outputMask : Word) (R : Point → Prop)
    (mid : Point)
    (h : middleCondition master
      (inputMasked (aL, 0#32) inputMask)
      (outputMasked (0#32, bR) outputMask) R mid) :
    bitLabel mid = decide ((aL &&& (0x00001000#32)) ≠ (0#32)) := by
  unfold bitLabel
  rw [masked_middle_delta master aL bR inputMask outputMask R mid h]

end Magma.DiffanFourRoundForcedMiddleDifference
