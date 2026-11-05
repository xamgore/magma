module
import all Init.Data.Range.Basic
public import Magma.Differential.RoundFunction.KeyFreeCarryAutomaton

@[expose] public section

/-!
# Key-free full-round difference transducer for arbitrary lengths

A *necessary* edge from (aL,aR) to (bL,bR) has bL=aR and
the certified eight-nibble carry automaton must admit the
round-function difference aR -> (bR XOR aL).

The graph over-approximates real Feistel difference propagation:
each edge is allowed an independent local key/base; edges are not
claimed jointly realizable. It works for BOTH active halves and for
any number of ordinary Feistel rounds, not merely the outer 5-round
case. No key-schedule independence or Markov assumption is used.
-/

namespace Magma.DifanKeyFreeRoundTransducer

open Magma
open Magma.MultiRoundDDT
open Magma.FeistelDDT
open Magma.DifanKeyFreeCarryAutomaton
open Magma.DifanFiveRoundUniversalSupport

private abbrev Word :=
  V 32

/-- A sound key-free overapproximation of a single Feistel round. -/
def roundAllowed (a b : FeistelState) : Prop :=
  b.1 = a.2 ∧
  keyFreePossible a.2 (Magma.xor b.2 a.1) = true

/-- Every actual one-round Magma difference belongs to the key-free
    relation, even when BOTH input halves are active. -/
theorem roundAllowed_of_feistel
    (k dL dR L R : Word) :
    roundAllowed (dL, dR) (feistelXorDiff k dL dR L R) := by
  rw [feistelXorDiff_eq]
  constructor
  · rfl
  · have h := keyFreePossible_of_anyKeyGSupport dR
      (gDifference k R dR) ⟨k, R, rfl⟩
    change keyFreePossible dR
      (Magma.xor (Magma.xor (gDifference k R dR) dL) dL) = true
    have hc (u v : Word) : Magma.xor (Magma.xor u v) v = u := by
      change (u ^^^ v) ^^^ v = u
      rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
    rw [hc]
    exact h

/-- Concatenatable unweighted n-round transition relation.
    Only 64-bit *differences* are stored, not 64-bit base states. -/
inductive Path : Nat → FeistelState → FeistelState → Prop
  | zero (a : FeistelState) : Path 0 a a
  | snoc {n : Nat} {a b c : FeistelState} :
      Path n a b → roundAllowed b c → Path (n + 1) a c

/-- Soundness for all n, all five-round windows and all round keys. -/
theorem path_of_actual_delta
    (n : Nat) (keys : Fin n → Word) (start delta : FeistelState) :
    Path n delta (multiRoundDelta n keys start delta) := by
  induction n with
  | zero =>
      simpa only [multiRoundDelta_zero] using Path.zero delta
  | succ n ih =>
      rw [multiRoundDelta_succ]
      exact Path.snoc
        (ih (fun i => keys i.castSucc))
        (roundAllowed_of_feistel
          (keys (Fin.last n))
          (multiRoundDelta n (fun i => keys i.castSucc) start delta).1
          (multiRoundDelta n (fun i => keys i.castSucc) start delta).2
          (iterateG n (fun i => keys i.castSucc) start).1
          (iterateG n (fun i => keys i.castSucc) start).2)

/-- Concatenation of abstract paths. A true n-round path must
    satisfy the same relation as a composition of shorter windows. -/
theorem Path.append {m n : Nat} {a b c : FeistelState}
    (h : Path m a b) (h' : Path n b c) :
    Path (m + n) a c := by
  induction h' with
  | zero =>
      simpa only [Nat.add_zero] using h
  | snoc hp hs ih =>
      simpa only [Nat.add_succ] using Path.snoc (ih h) hs

/-- General kernel-certified impossible-differential criterion:
    absence of a key-free difference path rules out every actual
    n-round Magma trajectory, for all fixed round keys. -/
theorem ddt_zero_of_no_keyFreePath
    (n : Nat) (keys : Fin n → Word)
    (a b : FeistelState) (hno : ¬ Path n a b) :
    xorDDT_rounds n keys a b = 0 := by
  unfold xorDDT_rounds
  apply Finset.card_eq_zero.mpr
  ext base
  have hz : multiRoundDelta n keys base a ≠ b := by
    intro hb
    apply hno
    rw [← hb]
    exact path_of_actual_delta n keys base a
  simp [hz]

/-- Useful for 5+n windows: any abstract n-round endpoint must be
    compatible with a five-round prefix or suffix path. No Markov
    factorization or independence of round keys is asserted. -/
theorem path_five_plus {n : Nat} {a mid b : FeistelState}
    (h5 : Path 5 a mid) (hn : Path n mid b) :
    Path (5 + n) a b :=
  Path.append h5 hn

/-- Reverse of concatenation: an abstract path of length m+n
    can be split at ANY prescribed round boundary. -/
theorem Path.split {m n : Nat} {a c : FeistelState}
    (h : Path (m + n) a c) :
    ∃ b : FeistelState, Path m a b ∧ Path n b c := by
  induction n generalizing c with
  | zero =>
      refine ⟨c, ?_, Path.zero c⟩
      simpa only [Nat.add_zero] using h
  | succ n ih =>
      have h' : Path ((m + n) + 1) a c := by
        simpa only [Nat.add_succ] using h
      cases h' with
      | snoc hp hs =>
          obtain ⟨b, hb, hc⟩ := ih hp
          exact ⟨b, hb, Path.snoc hc hs⟩

/-- A genuine (m+5+r)-round differential must pass through two
    compatible boundary differences of a five-round window.
    A verified absence of such a path rules out the entire window,
    irrespective of repeated master-key words in the schedule.

    This is a *sound* cut rule, not a DDT product formula. -/
theorem ddt_zero_of_no_five_window_cut
    (m r : Nat) (keys : Fin (m + 5 + r) → Word)
    (a b : FeistelState)
    (hno : ∀ u v : FeistelState,
      Path m a u → Path 5 u v → Path r v b → False) :
    xorDDT_rounds (m + 5 + r) keys a b = 0 := by
  apply ddt_zero_of_no_keyFreePath
  intro h
  obtain ⟨v, hprefix, hsuffix⟩ :=
    Path.split (m := m + 5) (n := r) h
  obtain ⟨u, hleft, hmiddle⟩ :=
    Path.split (m := m) (n := 5) hprefix
  exact hno u v hleft hmiddle hsuffix

end Magma.DifanKeyFreeRoundTransducer
