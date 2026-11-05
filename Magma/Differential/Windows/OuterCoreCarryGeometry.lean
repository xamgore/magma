module
import all Init.Data.Range.Basic
public import Magma.Differential.FiveRounds.CorrelatedFiveMacro
public import Magma.Differential.SevenRounds.SixSevenOuterReduction

@[expose] public section

/-!
# Two-variable, four-round diamond inside a six-round outer slice

Removing the first and last of six ordinary Feistel rounds leaves
(0,a) -> (s,0) for four inner rounds. Every key-free difference path
through these four rounds has the uniquely shaped differences

  (0,a) -> (a,p) -> (p,q) -> (q,s) -> (s,0).

By the definition of roundAllowed, its four edges are precisely
keyFreePossible a p,
keyFreePossible p (q XOR a),
keyFreePossible q (s XOR p),
keyFreePossible s q.

All four are necessary, but the carry automaton allows independent
local nibble keys: this is a sound OUTER impossibility filter,
not a sufficient condition for a real Magma trajectory.
-/

namespace Magma.DifanOuterCoreCarryGeometry

open Magma
open Magma.MultiRoundDDT
open Magma.DifanKeyFreeCarryAutomaton
open Magma.DifanKeyFreeRoundTransducer
open Magma.DifanCorrelatedFiveMacro
open Magma.DifanFirstRoundDeletion

private abbrev Word :=
  V 32

/-- Two unknown 32-bit differences, with no redundant 64-bit states. -/
def FourDiamond (a s : Word) : Prop :=
  ∃ p q : Word,
    roundAllowed (0#32, a) (a, p) ∧
    roundAllowed (a, p) (p, q) ∧
    roundAllowed (p, q) (q, s) ∧
    roundAllowed (q, s) (s, 0#32)

/-- The precise shape of every path through four Feistel rounds.
    This is an equivalence of key-free SUPPORT relations, not a DDT
    factorization. -/
theorem fourCore_path_iff_diamond (a s : Word) :
    Path 4 (0#32, a) (s, 0#32) ↔ FourDiamond a s := by
  constructor
  · intro h
    obtain ⟨t3, hpre3, hfour⟩ := Path.split (m := 3) (n := 1) h
    obtain ⟨t2, hpre2, hthree⟩ := Path.split (m := 2) (n := 1) hpre3
    obtain ⟨t1, hone, htwo⟩ := Path.split (m := 1) (n := 1) hpre2
    have hr1 := (path_one_iff (0#32, a) t1).mp hone
    have hr2 := (path_one_iff t1 t2).mp htwo
    have hr3 := (path_one_iff t2 t3).mp hthree
    have hr4 := (path_one_iff t3 (s, 0#32)).mp hfour
    rcases t1 with ⟨l1, p⟩
    rcases t2 with ⟨l2, q⟩
    rcases t3 with ⟨l3, r⟩
    have e1 : l1 = a := hr1.1
    have e2 : l2 = p := hr2.1
    have e3 : l3 = q := hr3.1
    have e4 : s = r := hr4.1
    subst l1
    subst l2
    subst l3
    subst r
    exact ⟨p, q, hr1, hr2, hr3, hr4⟩
  · rintro ⟨p, q, hr1, hr2, hr3, hr4⟩
    exact Path.snoc
      (Path.snoc (Path.snoc (Path.snoc (Path.zero (0#32, a)) hr1) hr2) hr3) hr4

/-- Any impossible two-variable diamond refutes all six-round outer
    differentials for ANY fixed sequence of six keys. -/
theorem sixRound_outer_zero_of_no_diamond
    (keys : Fin 6 → Word) (a s : Word) (hno : ¬ FourDiamond a s) :
    xorDDT_rounds 6 keys (a, 0#32) (0#32, s) = 0 := by
  rw [twoSided_boundary_ddt_eq_inner 4 keys a s]
  apply ddt_zero_of_no_keyFreePath
  intro hp
  exact hno ((fourCore_path_iff_diamond a s).mp hp)

/-- Three unknown intermediate 32-bit differences of the FIVE-round
    core inside a seven-round outer differential. -/
def FivePentagon (a s : Word) : Prop :=
  ∃ p q r : Word,
    roundAllowed (0#32, a) (a, p) ∧
    roundAllowed (a, p) (p, q) ∧
    roundAllowed (p, q) (q, r) ∧
    roundAllowed (q, r) (r, s) ∧
    roundAllowed (r, s) (s, 0#32)

/-- The entire five-round relaxed support path is equivalent to an
    explicit three-word pentagon. -/
theorem fiveCore_path_iff_pentagon (a s : Word) :
    Path 5 (0#32, a) (s, 0#32) ↔ FivePentagon a s := by
  constructor
  · intro h
    obtain ⟨t4, hpre4, hfive⟩ := Path.split (m := 4) (n := 1) h
    obtain ⟨t3, hpre3, hfour⟩ := Path.split (m := 3) (n := 1) hpre4
    obtain ⟨t2, hpre2, hthree⟩ := Path.split (m := 2) (n := 1) hpre3
    obtain ⟨t1, hone, htwo⟩ := Path.split (m := 1) (n := 1) hpre2
    have hr1 := (path_one_iff (0#32, a) t1).mp hone
    have hr2 := (path_one_iff t1 t2).mp htwo
    have hr3 := (path_one_iff t2 t3).mp hthree
    have hr4 := (path_one_iff t3 t4).mp hfour
    have hr5 := (path_one_iff t4 (s, 0#32)).mp hfive
    rcases t1 with ⟨l1, p⟩
    rcases t2 with ⟨l2, q⟩
    rcases t3 with ⟨l3, r⟩
    rcases t4 with ⟨l4, t⟩
    have e1 : l1 = a := hr1.1
    have e2 : l2 = p := hr2.1
    have e3 : l3 = q := hr3.1
    have e4 : l4 = r := hr4.1
    have e5 : s = t := hr5.1
    subst l1
    subst l2
    subst l3
    subst l4
    subst t
    exact ⟨p, q, r, hr1, hr2, hr3, hr4, hr5⟩
  · rintro ⟨p, q, r, hr1, hr2, hr3, hr4, hr5⟩
    exact Path.snoc
      (Path.snoc
        (Path.snoc
          (Path.snoc
            (Path.snoc (Path.zero (0#32, a)) hr1) hr2) hr3) hr4) hr5

/-- For seven outer rounds, excluding every three-word pentagon
    yields a valid key-independent zero DDT certificate. -/
theorem sevenRound_outer_zero_of_no_pentagon
    (keys : Fin 7 → Word) (a s : Word) (hno : ¬ FivePentagon a s) :
    xorDDT_rounds 7 keys (a, 0#32) (0#32, s) = 0 := by
  rw [twoSided_boundary_ddt_eq_inner 5 keys a s]
  apply ddt_zero_of_no_keyFreePath
  intro hp
  exact hno ((fiveCore_path_iff_pentagon a s).mp hp)

/-- Swap the two Feistel half-differences. -/
def swapDiff (x : FeistelState) : FeistelState := (x.2, x.1)

/-- A single key-free round edge reverses when the two halves are
    swapped. The same round-function derivative is used in reverse. -/
theorem roundAllowed_reverse {a b : FeistelState}
    (h : roundAllowed a b) :
    roundAllowed (swapDiff b) (swapDiff a) := by
  rcases a with ⟨al, ar⟩
  rcases b with ⟨bl, br⟩
  rcases h with ⟨hleft, hright⟩
  change bl = ar at hleft
  change keyFreePossible ar (Magma.xor br al) = true at hright
  change ar = bl ∧ keyFreePossible bl (Magma.xor al br) = true
  constructor
  · exact hleft.symm
  · rw [hleft]
    have hc : Magma.xor al br = Magma.xor br al := by
      change al ^^^ br = br ^^^ al
      exact BitVec.xor_comm al br
    rw [hc]
    exact hright

/-- Reversing any abstract n-round support path preserves validity,
    with endpoints swapped by J. No intermediate base states or fixed
    schedule are asserted to be preserved. -/
theorem reverse_path {n : Nat} {a b : FeistelState}
    (h : Path n a b) :
    Path n (swapDiff b) (swapDiff a) := by
  induction h with
  | zero a =>
      exact Path.zero (swapDiff a)
  | snoc hp hs ih =>
      have hsingle := Path.snoc (Path.zero _) (roundAllowed_reverse hs)
      have happend := Path.append hsingle ih
      simpa only [Nat.add_comm] using happend

/-- The four-edge diamond is symmetric under swapping a and s. -/
theorem fourDiamond_symmetric (a s : Word) :
    FourDiamond a s ↔ FourDiamond s a := by
  constructor
  · intro h
    have hp := (fourCore_path_iff_diamond a s).mpr h
    exact (fourCore_path_iff_diamond s a).mp (by
      simpa [swapDiff] using reverse_path hp)
  · intro h
    have hp := (fourCore_path_iff_diamond s a).mpr h
    exact (fourCore_path_iff_diamond a s).mp (by
      simpa [swapDiff] using reverse_path hp)

/-- The five-edge pentagon has the same endpoint reversal symmetry. -/
theorem fivePentagon_symmetric (a s : Word) :
    FivePentagon a s ↔ FivePentagon s a := by
  constructor
  · intro h
    have hp := (fiveCore_path_iff_pentagon a s).mpr h
    exact (fiveCore_path_iff_pentagon s a).mp (by
      simpa [swapDiff] using reverse_path hp)
  · intro h
    have hp := (fiveCore_path_iff_pentagon s a).mpr h
    exact (fiveCore_path_iff_pentagon a s).mp (by
      simpa [swapDiff] using reverse_path hp)

end Magma.DifanOuterCoreCarryGeometry
