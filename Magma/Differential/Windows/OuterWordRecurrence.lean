module
import all Init.Data.Range.Basic
public import Magma.Differential.Windows.OuterCoreCarryGeometry
public import Magma.Differential.Windows.FirstRoundDeletion

@[expose] public section

/-!
# All-length word-recurrence transducer for Magma Feistel differences

A key-free path through n Feistel rounds is described by a second-order
recurrence on ONE stream of 32-bit difference words:

    d_(i+2) = d_i XOR c_i,
    keyFreePossible d_(i+1) c_i = true.

The constraint is necessary for actual Magma rounds, but not sufficient
because the nibble-local carry choices forget round-key/base correlations.

For the OUTER slice of (n+2) rounds the initial recurrence values are
(d0,d1)=(0,a), and the final pair is (dn,d(n+1))=(s,0).
Thus the only unconstrained words are d2,...,d(n-1): n-2 words,
rather than n unrelated 64-bit intermediate states.

This is a theorem for ARBITRARY n, independent of round-key schedule.
-/

namespace Magma.DifanOuterWordRecurrence

open Magma
open Magma.MultiRoundDDT
open Magma.DifanKeyFreeCarryAutomaton
open Magma.DifanKeyFreeRoundTransducer
open Magma.DifanOuterCoreCarryGeometry
open Magma.DifanFirstRoundDeletion

private abbrev Word :=
  V 32

private abbrev State :=
  FeistelState

/-- N consecutive difference steps with no redundant 64-bit state
    variables. At each extension x,y -> y,z only the derivative
    y -> z XOR x is tested by the certified local carry automaton. -/
inductive WordChain : Nat → Word → Word → Word → Word → Prop
  | zero (a b : Word) : WordChain 0 a b a b
  | snoc {n : Nat} {a b x y z : Word}
      (h : WordChain n a b x y)
      (hstep : keyFreePossible y (Magma.xor z x) = true) :
      WordChain (n + 1) a b y z

/-- Every key-free Feistel path induces a stream of words obeying
    the second-order recurrence. -/
theorem wordChain_of_path {n : Nat} {a b : State}
    (h : Path n a b) :
    WordChain n a.1 a.2 b.1 b.2 := by
  induction h with
  | zero a => exact WordChain.zero a.1 a.2
  | @snoc n a b c hpre hstep ih =>
      rcases b with ⟨x, y⟩
      rcases c with ⟨z, t⟩
      rcases hstep with ⟨hleft, hright⟩
      change z = y at hleft
      subst z
      exact WordChain.snoc ih hright

/-- Conversely, every recurrence word stream lifts to exactly the
    corresponding key-free path (NOT necessarily a real Magma path). -/
theorem path_of_wordChain {n : Nat} {a b x y : Word}
    (h : WordChain n a b x y) :
    Path n (a,b) (x,y) := by
  induction h with
  | zero a b => exact Path.zero (a,b)
  | snoc hp hs ih => exact Path.snoc ih ⟨rfl, hs⟩

/-- A complete and kernel-proved characterization of *key-free*
    n-round feasibility using only the 32-bit recurrence. -/
theorem path_iff_wordChain (n : Nat) (a b x y : Word) :
    Path n (a,b) (x,y) ↔ WordChain n a b x y :=
  ⟨wordChain_of_path, path_of_wordChain⟩

/-- The generic outer recurrence for any n+2 ordinary rounds. -/
def OuterChain (n : Nat) (a s : Word) : Prop :=
  WordChain n (0#32) a s (0#32)

/-- EXACT shape of the relaxed support condition on the inner n rounds
    of an (n+2)-round OUTER difference, for arbitrary n. -/
theorem innerPath_iff_outerChain (n : Nat) (a s : Word) :
    Path n (0#32,a) (s,0#32) ↔ OuterChain n a s :=
  path_iff_wordChain n (0#32) a s (0#32)

/-- For every length n+2, a failed recurrence condition provides a
    key-independent and master-schedule-independent DDT zero proof. -/
theorem outer_zero_of_no_wordChain
    (n : Nat) (keys : Fin (n + 2) → Word) (a s : Word)
    (hno : ¬ OuterChain n a s) :
    xorDDT_rounds (n + 2) keys (a,0#32) (0#32,s) = 0 := by
  rw [twoSided_boundary_ddt_eq_inner n keys a s]
  apply ddt_zero_of_no_keyFreePath
  intro hp
  exact hno ((innerPath_iff_outerChain n a s).mp hp)

/-- The all-length recurrence respects Feistel reversal.
    Under reversed round keys this becomes an actual DDT symmetry,
    but this theorem only concerns the relaxed carry support. -/
theorem wordChain_reverse {n : Nat} {a b x y : Word}
    (h : WordChain n a b x y) :
    WordChain n y x b a := by
  have hp := (path_iff_wordChain n a b x y).mpr h
  have hr := reverse_path hp
  exact (path_iff_wordChain n y x b a).mp (by
    simpa [swapDiff] using hr)

/-- For all core lengths, existence of a relaxed outer path is
    symmetric under swapping input/output nonzero half differences. -/
theorem outerChain_symmetric (n : Nat) (a s : Word) :
    OuterChain n a s ↔ OuterChain n s a := by
  constructor
  · exact wordChain_reverse
  · exact wordChain_reverse

end Magma.DifanOuterWordRecurrence
