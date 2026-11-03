module
import all Init.Data.Range.Basic
public import Magma.Diffan.IndependentRoundSupport

@[expose] public section

/-!
# An explicitly speculative model for nine-round key-schedule coupling

The outer slice at ordinary rounds 20..28 reduces EXACTLY to the
seven inner rounds 21..27. RFC key indices for these inner rounds:

  [5, 6, 7, 7, 6, 5, 4].

The seven base words below are independent, while repeated key
indices are represented by shared 32-bit key variables.

This is an experimental SAT *relaxation*, not a certified description
of all real trajectories. The missing soundness bridge is stated
explicitly as a hypothesis when proving a conditional zero rule.
No sorry or axiom is promoted into the core library.
-/

namespace Magma.NinePlus

open Magma
open Magma.MultiRoundDDT
open Magma.DiffanFiveRoundUniversalSupport

private abbrev Word := V 32
private abbrev State := FeistelState

/-- A genuine local Magma differential with a FIXED key,
    but independently chosen base word. -/
def SupportAt (k d out : Word) : Prop :=
  ∃ x : Word, gDifference k x d = out

/-- The 7-round inner difference stream:
    [0, a, p, q, r, t, u, s, 0].
    All 7 g-derivatives have independent keys and bases. -/
def IndependentSeven (a s : Word) : Prop :=
  ∃ p q r t u : Word,
    anyKeyGSupport a p ∧
    anyKeyGSupport p (Magma.xor q a) ∧
    anyKeyGSupport q (Magma.xor r p) ∧
    anyKeyGSupport r (Magma.xor t q) ∧
    anyKeyGSupport t (Magma.xor u r) ∧
    anyKeyGSupport u (Magma.xor s t) ∧
    anyKeyGSupport s u

/-- Same local base freedom, but with RFC key indices
    [5,6,7,7,6,5,4] shared at corresponding occurrences. -/
def LinkedSeven (a s : Word) : Prop :=
  ∃ k4 k5 k6 k7 p q r t u : Word,
    SupportAt k5 a p ∧
    SupportAt k6 p (Magma.xor q a) ∧
    SupportAt k7 q (Magma.xor r p) ∧
    SupportAt k7 r (Magma.xor t q) ∧
    SupportAt k6 t (Magma.xor u r) ∧
    SupportAt k5 u (Magma.xor s t) ∧
    SupportAt k4 s u

/-- The key-linked relation is provably a subset of the fully
    independent local-support relation. Strictness on any actual
    endpoint pair remains an empirical and theoretical question. -/
theorem linked_implies_independent (a s : Word) :
    LinkedSeven a s → IndependentSeven a s := by
  rintro ⟨k4, k5, k6, k7, p, q, r, t, u,
    h0, h1, h2, h3, h4, h5, h6⟩
  refine ⟨p, q, r, t, u, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := h0
    exact ⟨k5, x, hx⟩
  · obtain ⟨x, hx⟩ := h1
    exact ⟨k6, x, hx⟩
  · obtain ⟨x, hx⟩ := h2
    exact ⟨k7, x, hx⟩
  · obtain ⟨x, hx⟩ := h3
    exact ⟨k7, x, hx⟩
  · obtain ⟨x, hx⟩ := h4
    exact ⟨k6, x, hx⟩
  · obtain ⟨x, hx⟩ := h5
    exact ⟨k5, x, hx⟩
  · obtain ⟨x, hx⟩ := h6
    exact ⟨k4, x, hx⟩

/-- A PAIR on which a linked-key filter has strictly more power. -/
def GainsFromKeyCoupling (a s : Word) : Prop :=
  IndependentSeven a s ∧ ¬ LinkedSeven a s

/-- The actual master-key-schedule semantics of the nine ordinary
    Feistel rounds beginning with RFC round 20. -/
def Window20Keys (master : V 256) : Fin 9 → Word :=
  fun i => roundKey master ⟨i.val + 20, by omega⟩

/-- Conditional soundness bridge, intentionally NOT assumed globally.
    The hypothesis must be established before a linked-SAT UNSAT
    can be called an actual nine-round differential exclusion. -/
theorem nine_round_zero_if_linked_model_sound
    (master : V 256) (a s : Word)
    (sound : ∀ base : State,
      multiRoundDelta 9 (Window20Keys master) base
        (a, 0#32) = (0#32, s) → LinkedSeven a s)
    (hno : ¬ LinkedSeven a s) :
    xorDDT_rounds 9 (Window20Keys master)
      (a, 0#32) (0#32, s) = 0 := by
  unfold xorDDT_rounds
  apply Finset.card_eq_zero.mpr
  ext base
  have hbad : multiRoundDelta 9 (Window20Keys master) base
      (a, 0#32) ≠ (0#32, s) := by
    intro h
    exact hno (sound base h)
  simp [hbad]

end Magma.NinePlus
