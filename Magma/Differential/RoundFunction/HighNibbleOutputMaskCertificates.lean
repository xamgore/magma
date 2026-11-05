module

import all Init.Data.Range.Basic
public import Magma.Differential.RoundFunction.AutomaticOutputMasks
import Std.Tactic.BVDecide

@[expose] public section

/-!
# Exact maximal output masks for all nonzero shifts in the top input nibble

The structural extractor of AutomaticOutputMasks proves soundness for all
32-bit directions. Here a *small finite witness certificate* proves the
converse for an entire 15-direction family: shifts supported in the highest
nibble. All keys and all input bases are quantified, but the necessity
certificate needs only key zero and at most two input bases per direction.

-/

namespace Magma.DifanHighNibbleOutputMaskCertificates

open Magma Magma.Internal Magma.GProperties
open Magma.DifanAutomaticOutputMasks

private abbrev Word :=
  V 32

/-- One concrete difference between two evaluations of g[k]. -/
def outputDifference (s : Word) (p : Word × Word) : Word :=
  g p.1 (p.2 ^^^ s) ^^^ g p.1 p.2

/-- Pure bitvector plumbing, kept apart from the large executable Magma definition. -/
private theorem masked_xor_zero (u v mask : Word)
    (h : (u &&& mask) = (v &&& mask)) :
    ((u ^^^ v) &&& mask) = 0#32 := by
  bv_decide

private theorem masked_subset (u v big small : Word) (heq : (u &&& big) = (v &&& big))
    (hsub : (small &&& (~~~big)) = 0#32) : (u &&& small) = (v &&& small) := by bv_decide

private theorem or_disjoint (u v m : Word) (hu : (u &&& m) = 0#32) (hv : (v &&& m) = 0#32) :
    ((u ||| v) &&& m) = 0#32 := by bv_decide

private theorem and_comm_zero (u v : Word) (h : (u &&& v) = 0#32) : (v &&& u) = 0#32 := by bv_decide

/-- Bitwise union of the differences observed in a finite witness list. -/
def witnessCoverage (s : Word) : List (Word × Word) → Word
  | [] => 0#32
  | p :: tail => outputDifference s p ||| witnessCoverage s tail

/-- Every witnessed changed bit must be absent from a universally invariant
mask. This fact uses no Magma-specific properties of g. -/
theorem witnessCoverage_disjoint_of_universal (s m : Word)
    (witnesses : List (Word × Word))
    (hm : ∀ k x : Word,
      (g k (x ^^^ s) &&& m) = (g k x &&& m)) :
    (witnessCoverage s witnesses &&& m) = 0#32 := by
  induction witnesses with
  | nil =>
      simp only [witnessCoverage, BitVec.zero_and]
  | cons p rest ih =>
      have hp : (outputDifference s p &&& m) = 0#32 := by
        have hh := hm p.1 p.2
        change ((g p.1 (p.2 ^^^ s) ^^^ g p.1 p.2) &&& m) = 0#32
        exact masked_xor_zero _ _ m hh
      change ((outputDifference s p ||| witnessCoverage s rest) &&& m) = 0#32
      exact or_disjoint _ _ m hp ih

/-- A finite cover of all bits outside the mask protected by the structural extractor
is a complete, trusted maximality certificate. -/
theorem universalMask_iff_of_coverage (s m : Word)
    (witnesses : List (Word × Word))
    (hcover : witnessCoverage s witnesses = ~~~ (guaranteedMask s)) :
    (∀ k x : Word,
      (g k (x ^^^ s) &&& m) = (g k x &&& m)) ↔
      (m &&& (~~~ (guaranteedMask s))) = 0#32 := by
  constructor
  · intro hm
    have h := witnessCoverage_disjoint_of_universal s m witnesses hm
    rw [hcover] at h
    exact and_comm_zero _ _ h
  · intro hsub k x
    exact masked_subset _ _ (guaranteedMask s) m
      (guaranteedMask_sound k x s) hsub

/-- Explicit witnesses indexed by the high input nibble (1..15).
Key-zero base points suffice to witness every unprotected output bit. -/
def highNibbleWitnesses (s : Word) : List (Word × Word) :=
  match s.toNat / 268435456 with
  | 1 => [(0x00000000#32, 0x00000000#32), (0x00000000#32, 0x60000000#32)]
  | 2 => [(0x00000000#32, 0x00000000#32)]
  | 3 => [(0x00000000#32, 0x00000000#32), (0x00000000#32, 0x40000000#32)]
  | 4 => [(0x00000000#32, 0x00000000#32), (0x00000000#32, 0x30000000#32)]
  | 5 => [(0x00000000#32, 0x10000000#32), (0x00000000#32, 0x20000000#32)]
  | 6 => [(0x00000000#32, 0x80000000#32)]
  | 7 => [(0x00000000#32, 0x10000000#32)]
  | 8 => [(0x00000000#32, 0x00000000#32), (0x00000000#32, 0x30000000#32)]
  | 9 => [(0x00000000#32, 0x00000000#32), (0x00000000#32, 0x10000000#32)]
  | 10 => [(0x00000000#32, 0x70000000#32)]
  | 11 => [(0x00000000#32, 0x00000000#32), (0x00000000#32, 0x10000000#32)]
  | 12 => [(0x00000000#32, 0x30000000#32)]
  | 13 => [(0x00000000#32, 0x40000000#32)]
  | 14 => [(0x00000000#32, 0x00000000#32), (0x00000000#32, 0x10000000#32)]
  | 15 => [(0x00000000#32, 0x50000000#32)]
  | _ => []

/-- Certified coverage for direction 0x10000000#32 (2 base witness(es)). -/
private theorem highNibble_coverage_1 :
    witnessCoverage (0x10000000#32) (highNibbleWitnesses (0x10000000#32)) =
      (0x00000780#32) := by
  have h0 : outputDifference (0x10000000#32) (0x00000000#32, 0x00000000#32) = 0x00000300#32 := by decide
  have h1 : outputDifference (0x10000000#32) (0x00000000#32, 0x60000000#32) = 0x00000580#32 := by decide
  change (outputDifference (0x10000000#32) (0x00000000#32, 0x00000000#32) ||| (outputDifference (0x10000000#32) (0x00000000#32, 0x60000000#32) ||| (0#32))) = (0x00000780#32)
  rw [h0]
  rw [h1]
  decide

/-- Certified coverage for direction 0x20000000#32 (1 base witness(es)). -/
private theorem highNibble_coverage_2 :
    witnessCoverage (0x20000000#32) (highNibbleWitnesses (0x20000000#32)) =
      (0x00000780#32) := by
  have h0 : outputDifference (0x20000000#32) (0x00000000#32, 0x00000000#32) = 0x00000780#32 := by decide
  change (outputDifference (0x20000000#32) (0x00000000#32, 0x00000000#32) ||| (0#32)) = (0x00000780#32)
  rw [h0]
  decide

/-- Certified coverage for direction 0x30000000#32 (2 base witness(es)). -/
private theorem highNibble_coverage_3 :
    witnessCoverage (0x30000000#32) (highNibbleWitnesses (0x30000000#32)) =
      (0x00000780#32) := by
  have h0 : outputDifference (0x30000000#32) (0x00000000#32, 0x00000000#32) = 0x00000600#32 := by decide
  have h1 : outputDifference (0x30000000#32) (0x00000000#32, 0x40000000#32) = 0x00000180#32 := by decide
  change (outputDifference (0x30000000#32) (0x00000000#32, 0x00000000#32) ||| (outputDifference (0x30000000#32) (0x00000000#32, 0x40000000#32) ||| (0#32))) = (0x00000780#32)
  rw [h0]
  rw [h1]
  decide

/-- Certified coverage for direction 0x40000000#32 (2 base witness(es)). -/
private theorem highNibble_coverage_4 :
    witnessCoverage (0x40000000#32) (highNibbleWitnesses (0x40000000#32)) =
      (0x00000780#32) := by
  have h0 : outputDifference (0x40000000#32) (0x00000000#32, 0x00000000#32) = 0x00000080#32 := by decide
  have h1 : outputDifference (0x40000000#32) (0x00000000#32, 0x30000000#32) = 0x00000700#32 := by decide
  change (outputDifference (0x40000000#32) (0x00000000#32, 0x00000000#32) ||| (outputDifference (0x40000000#32) (0x00000000#32, 0x30000000#32) ||| (0#32))) = (0x00000780#32)
  rw [h0]
  rw [h1]
  decide

/-- Certified coverage for direction 0x50000000#32 (2 base witness(es)). -/
private theorem highNibble_coverage_5 :
    witnessCoverage (0x50000000#32) (highNibbleWitnesses (0x50000000#32)) =
      (0x00000780#32) := by
  have h0 : outputDifference (0x50000000#32) (0x00000000#32, 0x10000000#32) = 0x00000380#32 := by decide
  have h1 : outputDifference (0x50000000#32) (0x00000000#32, 0x20000000#32) = 0x00000680#32 := by decide
  change (outputDifference (0x50000000#32) (0x00000000#32, 0x10000000#32) ||| (outputDifference (0x50000000#32) (0x00000000#32, 0x20000000#32) ||| (0#32))) = (0x00000780#32)
  rw [h0]
  rw [h1]
  decide

/-- Certified coverage for direction 0x60000000#32 (1 base witness(es)). -/
private theorem highNibble_coverage_6 :
    witnessCoverage (0x60000000#32) (highNibbleWitnesses (0x60000000#32)) =
      (0x00000780#32) := by
  have h0 : outputDifference (0x60000000#32) (0x00000000#32, 0x80000000#32) = 0x00000780#32 := by decide
  change (outputDifference (0x60000000#32) (0x00000000#32, 0x80000000#32) ||| (0#32)) = (0x00000780#32)
  rw [h0]
  decide

/-- Certified coverage for direction 0x70000000#32 (1 base witness(es)). -/
private theorem highNibble_coverage_7 :
    witnessCoverage (0x70000000#32) (highNibbleWitnesses (0x70000000#32)) =
      (0x00000780#32) := by
  have h0 : outputDifference (0x70000000#32) (0x00000000#32, 0x10000000#32) = 0x00000780#32 := by decide
  change (outputDifference (0x70000000#32) (0x00000000#32, 0x10000000#32) ||| (0#32)) = (0x00000780#32)
  rw [h0]
  decide

/-- Certified coverage for direction 0x80000000#32 (2 base witness(es)). -/
private theorem highNibble_coverage_8 :
    witnessCoverage (0x80000000#32) (highNibbleWitnesses (0x80000000#32)) =
      (0x00000780#32) := by
  have h0 : outputDifference (0x80000000#32) (0x00000000#32, 0x00000000#32) = 0x00000280#32 := by decide
  have h1 : outputDifference (0x80000000#32) (0x00000000#32, 0x30000000#32) = 0x00000580#32 := by decide
  change (outputDifference (0x80000000#32) (0x00000000#32, 0x00000000#32) ||| (outputDifference (0x80000000#32) (0x00000000#32, 0x30000000#32) ||| (0#32))) = (0x00000780#32)
  rw [h0]
  rw [h1]
  decide

/-- Certified coverage for direction 0x90000000#32 (2 base witness(es)). -/
private theorem highNibble_coverage_9 :
    witnessCoverage (0x90000000#32) (highNibbleWitnesses (0x90000000#32)) =
      (0x00000780#32) := by
  have h0 : outputDifference (0x90000000#32) (0x00000000#32, 0x00000000#32) = 0x00000700#32 := by decide
  have h1 : outputDifference (0x90000000#32) (0x00000000#32, 0x10000000#32) = 0x00000180#32 := by decide
  change (outputDifference (0x90000000#32) (0x00000000#32, 0x00000000#32) ||| (outputDifference (0x90000000#32) (0x00000000#32, 0x10000000#32) ||| (0#32))) = (0x00000780#32)
  rw [h0]
  rw [h1]
  decide

/-- Certified coverage for direction 0xA0000000#32 (1 base witness(es)). -/
private theorem highNibble_coverage_A :
    witnessCoverage (0xA0000000#32) (highNibbleWitnesses (0xA0000000#32)) =
      (0x00000780#32) := by
  have h0 : outputDifference (0xA0000000#32) (0x00000000#32, 0x70000000#32) = 0x00000780#32 := by decide
  change (outputDifference (0xA0000000#32) (0x00000000#32, 0x70000000#32) ||| (0#32)) = (0x00000780#32)
  rw [h0]
  decide

/-- Certified coverage for direction 0xB0000000#32 (2 base witness(es)). -/
private theorem highNibble_coverage_B :
    witnessCoverage (0xB0000000#32) (highNibbleWitnesses (0xB0000000#32)) =
      (0x00000780#32) := by
  have h0 : outputDifference (0xB0000000#32) (0x00000000#32, 0x00000000#32) = 0x00000380#32 := by decide
  have h1 : outputDifference (0xB0000000#32) (0x00000000#32, 0x10000000#32) = 0x00000680#32 := by decide
  change (outputDifference (0xB0000000#32) (0x00000000#32, 0x00000000#32) ||| (outputDifference (0xB0000000#32) (0x00000000#32, 0x10000000#32) ||| (0#32))) = (0x00000780#32)
  rw [h0]
  rw [h1]
  decide

/-- Certified coverage for direction 0xC0000000#32 (1 base witness(es)). -/
private theorem highNibble_coverage_C :
    witnessCoverage (0xC0000000#32) (highNibbleWitnesses (0xC0000000#32)) =
      (0x00000780#32) := by
  have h0 : outputDifference (0xC0000000#32) (0x00000000#32, 0x30000000#32) = 0x00000780#32 := by decide
  change (outputDifference (0xC0000000#32) (0x00000000#32, 0x30000000#32) ||| (0#32)) = (0x00000780#32)
  rw [h0]
  decide

/-- Certified coverage for direction 0xD0000000#32 (1 base witness(es)). -/
private theorem highNibble_coverage_D :
    witnessCoverage (0xD0000000#32) (highNibbleWitnesses (0xD0000000#32)) =
      (0x00000780#32) := by
  have h0 : outputDifference (0xD0000000#32) (0x00000000#32, 0x40000000#32) = 0x00000780#32 := by decide
  change (outputDifference (0xD0000000#32) (0x00000000#32, 0x40000000#32) ||| (0#32)) = (0x00000780#32)
  rw [h0]
  decide

/-- Certified coverage for direction 0xE0000000#32 (2 base witness(es)). -/
private theorem highNibble_coverage_E :
    witnessCoverage (0xE0000000#32) (highNibbleWitnesses (0xE0000000#32)) =
      (0x00000780#32) := by
  have h0 : outputDifference (0xE0000000#32) (0x00000000#32, 0x00000000#32) = 0x00000500#32 := by decide
  have h1 : outputDifference (0xE0000000#32) (0x00000000#32, 0x10000000#32) = 0x00000280#32 := by decide
  change (outputDifference (0xE0000000#32) (0x00000000#32, 0x00000000#32) ||| (outputDifference (0xE0000000#32) (0x00000000#32, 0x10000000#32) ||| (0#32))) = (0x00000780#32)
  rw [h0]
  rw [h1]
  decide

/-- Certified coverage for direction 0xF0000000#32 (1 base witness(es)). -/
private theorem highNibble_coverage_F :
    witnessCoverage (0xF0000000#32) (highNibbleWitnesses (0xF0000000#32)) =
      (0x00000780#32) := by
  have h0 : outputDifference (0xF0000000#32) (0x00000000#32, 0x50000000#32) = 0x00000780#32 := by decide
  change (outputDifference (0xF0000000#32) (0x00000000#32, 0x50000000#32) ||| (0#32)) = (0x00000780#32)
  rw [h0]
  decide

/-- Bitblasted 4-bit classification: nonzero shifts confined to the
top nibble are exactly these fifteen 32-bit words. -/
private theorem highNibble_cases (s : Word)
    (hlow : (s &&& (0x0FFFFFFF#32)) = 0#32)
    (hne : s ≠ 0#32) :
    s = 0x10000000#32 ∨
    s = 0x20000000#32 ∨
    s = 0x30000000#32 ∨
    s = 0x40000000#32 ∨
    s = 0x50000000#32 ∨
    s = 0x60000000#32 ∨
    s = 0x70000000#32 ∨
    s = 0x80000000#32 ∨
    s = 0x90000000#32 ∨
    s = 0xA0000000#32 ∨
    s = 0xB0000000#32 ∨
    s = 0xC0000000#32 ∨
    s = 0xD0000000#32 ∨
    s = 0xE0000000#32 ∨
    s = 0xF0000000#32 := by
  bv_decide

/-- The structural extractor protects precisely the other 28 bits for
every nonzero shift confined to the highest input nibble. -/
theorem highNibble_guaranteedMask (s : Word)
    (hlow : (s &&& (0x0FFFFFFF#32)) = 0#32)
    (hne : s ≠ 0#32) :
    guaranteedMask s = (0xFFFFF87F#32) := by
  rcases highNibble_cases s hlow hne with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals subst s ; decide

/-- Uniform witness coverage for every one of the 15 high-nibble shifts. -/
theorem highNibble_full_coverage (s : Word)
    (hlow : (s &&& (0x0FFFFFFF#32)) = 0#32)
    (hne : s ≠ 0#32) :
    witnessCoverage s (highNibbleWitnesses s) =
      ~~~ (guaranteedMask s) := by
  rcases highNibble_cases s hlow hne with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst s
    rw [show (~~~ (guaranteedMask (0x10000000#32))) = (0x00000780#32) from by decide]
    exact highNibble_coverage_1
  · subst s
    rw [show (~~~ (guaranteedMask (0x20000000#32))) = (0x00000780#32) from by decide]
    exact highNibble_coverage_2
  · subst s
    rw [show (~~~ (guaranteedMask (0x30000000#32))) = (0x00000780#32) from by decide]
    exact highNibble_coverage_3
  · subst s
    rw [show (~~~ (guaranteedMask (0x40000000#32))) = (0x00000780#32) from by decide]
    exact highNibble_coverage_4
  · subst s
    rw [show (~~~ (guaranteedMask (0x50000000#32))) = (0x00000780#32) from by decide]
    exact highNibble_coverage_5
  · subst s
    rw [show (~~~ (guaranteedMask (0x60000000#32))) = (0x00000780#32) from by decide]
    exact highNibble_coverage_6
  · subst s
    rw [show (~~~ (guaranteedMask (0x70000000#32))) = (0x00000780#32) from by decide]
    exact highNibble_coverage_7
  · subst s
    rw [show (~~~ (guaranteedMask (0x80000000#32))) = (0x00000780#32) from by decide]
    exact highNibble_coverage_8
  · subst s
    rw [show (~~~ (guaranteedMask (0x90000000#32))) = (0x00000780#32) from by decide]
    exact highNibble_coverage_9
  · subst s
    rw [show (~~~ (guaranteedMask (0xA0000000#32))) = (0x00000780#32) from by decide]
    exact highNibble_coverage_A
  · subst s
    rw [show (~~~ (guaranteedMask (0xB0000000#32))) = (0x00000780#32) from by decide]
    exact highNibble_coverage_B
  · subst s
    rw [show (~~~ (guaranteedMask (0xC0000000#32))) = (0x00000780#32) from by decide]
    exact highNibble_coverage_C
  · subst s
    rw [show (~~~ (guaranteedMask (0xD0000000#32))) = (0x00000780#32) from by decide]
    exact highNibble_coverage_D
  · subst s
    rw [show (~~~ (guaranteedMask (0xE0000000#32))) = (0x00000780#32) from by decide]
    exact highNibble_coverage_E
  · subst s
    rw [show (~~~ (guaranteedMask (0xF0000000#32))) = (0x00000780#32) from by decide]
    exact highNibble_coverage_F

/-- Complete output-mask classification for any nonzero direction
supported in the uppermost nibble. No larger mask can be invariant for
all keys and all input bases. -/
theorem highNibble_universalMask_iff (s m : Word)
    (hlow : (s &&& (0x0FFFFFFF#32)) = 0#32)
    (hne : s ≠ 0#32) :
    (∀ k x : Word,
      (g k (x ^^^ s) &&& m) = (g k x &&& m)) ↔
      (m &&& (0x00000780#32)) = 0#32 := by
  have hc := highNibble_full_coverage s hlow hne
  have hg := highNibble_guaranteedMask s hlow hne
  have h := universalMask_iff_of_coverage s m (highNibbleWitnesses s) hc
  rw [hg] at h
  have hcomp : (~~~ (0xFFFFF87F#32)) = (0x00000780#32) := by decide
  rw [hcomp] at h
  exact h

end Magma.DifanHighNibbleOutputMaskCertificates
