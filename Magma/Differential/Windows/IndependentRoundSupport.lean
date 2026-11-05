module
import all Init.Data.Range.Basic
public import Magma.Differential.Windows.OuterWordRecurrence
public import Magma.Differential.FiveRounds.CorrelatedFiveMacro

@[expose] public section

/-!
# Genuine one-round support, with no assumed inter-round independence

This strengthens OuterWordRecurrence by requiring a *real* Magma
round-function derivative at every abstract edge. Each edge may
independently choose its own round key and right-half base word.
Thus even this condition remains an overapproximation of real
multi-round Magma trajectories.

Z3 experiments on outer eight-round cells use precisely this
six-edge key/base-independent necessary condition. Only the
soundness direction is kernel-proved here; SAT/UNSAT computations
are not imported as axioms or proofs.
-/
namespace Magma.DiffanIndependentRoundSupport

open Magma
open Magma.FeistelDDT
open Magma.MultiRoundDDT
open Magma.DiffanFiveRoundUniversalSupport
open Magma.DiffanCorrelatedFiveMacro
open Magma.DiffanFirstRoundDeletion

private abbrev Word := V 32
private abbrev State := FeistelState
private abbrev Labeled := State × State

/-- A chain of n real *local* round-function supports, with
    independent key/base witnesses at each different round. -/
inductive IndependentChain : Nat → Word → Word → Word → Word → Prop
  | zero (a b : Word) : IndependentChain 0 a b a b
  | snoc {n : Nat} {a b x y z : Word}
      (h : IndependentChain n a b x y)
      (hstep : anyKeyGSupport y (Magma.xor z x)) :
      IndependentChain (n+1) a b y z

/-- Every genuine Feistel difference step has a genuine one-round
    function derivative as its local witness. -/
private theorem local_support_of_feistel
    (k dL dR L R : Word) :
    anyKeyGSupport dR
      (Magma.xor (feistelXorDiff k dL dR L R).2 dL) := by
  refine ⟨k, R, ?_⟩
  rw [feistelXorDiff_eq]
  change ((g k (Magma.xor R dR)) ^^^ (g k R)) =
    (((g k (Magma.xor R dR)) ^^^ (g k R)) ^^^ dL) ^^^ dL
  rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

/-- An actual correlated multi-round trace satisfies our exact
    local-support chain. No Markov assumption is used. -/
theorem chain_of_correlated {n : Nat} {p q : Labeled}
    (h : Correlated n p q) :
    IndependentChain n p.2.1 p.2.2 q.2.1 q.2.2 := by
  induction h with
  | zero p =>
      exact IndependentChain.zero p.2.1 p.2.2
  | @snoc n p q h k ih =>
      rcases q with ⟨⟨L,R⟩, ⟨dL,dR⟩⟩
      change IndependentChain (n + 1) p.2.1 p.2.2
        (feistelXorDiff k dL dR L R).1
        (feistelXorDiff k dL dR L R).2
      rw [feistelXorDiff_eq]
      apply IndependentChain.snoc ih
      simpa only [feistelXorDiff_eq, Prod.snd] using
        (local_support_of_feistel k dL dR L R)

/-- All actual n-round Magma derivatives satisfy the
    independent-per-round-key/base relaxation. -/
theorem chain_of_actual (n : Nat) (keys : Fin n → Word)
    (base delta : State) :
    IndependentChain n delta.1 delta.2
      (multiRoundDelta n keys base delta).1
      (multiRoundDelta n keys base delta).2 :=
  chain_of_correlated (Correlated.ofActual n keys base delta)

/-- Necessary condition on the n-round inner core of an outer
    (n+2)-round differential. Stronger than keyFreePossible in
    logical form; the independent keys and bases remain unconstrained. -/
def OuterIndependentChain (n : Nat) (a s : Word) : Prop :=
  IndependentChain n (0#32) a s (0#32)

/-- Absence of any independent *real* one-round supports already
    proves the original Magma DDT zero for EVERY fixed sequence
    of n+2 round keys (and hence every RFC master schedule). -/
theorem outer_zero_of_no_independent_chain (n : Nat)
    (keys : Fin (n+2) → Word) (a s : Word)
    (hno : ¬ OuterIndependentChain n a s) :
    xorDDT_rounds (n+2) keys (a, 0#32) (0#32, s) = 0 := by
  rw [twoSided_boundary_ddt_eq_inner n keys a s]
  unfold xorDDT_rounds
  apply Finset.card_eq_zero.mpr
  ext base
  have hfail :
      multiRoundDelta n
        (fun i : Fin n => keys i.castSucc.succ)
        base (0#32, a) ≠ (s, 0#32) := by
    intro h
    apply hno
    have hw := chain_of_actual n
      (fun i : Fin n => keys i.castSucc.succ)
      base (0#32, a)
    rw [h] at hw
    exact hw
  simp [hfail]

/-- Six genuine independent local g-differences, linked through
    exactly four 32-bit intermediate XOR-difference words. -/
def SixIndependentCore (a s : Word) : Prop :=
  ∃ p q r t : Word,
    anyKeyGSupport a p ∧
    anyKeyGSupport p (Magma.xor q a) ∧
    anyKeyGSupport q (Magma.xor r p) ∧
    anyKeyGSupport r (Magma.xor t q) ∧
    anyKeyGSupport t (Magma.xor s r) ∧
    anyKeyGSupport s t


/-- The exact six-round independent-support recurrence is the
    four-word conjunction passed to the Z3 bitvector experiment.
    This iff does not assert that independent round bases can be
    coupled to form one actual Feistel trajectory. -/
theorem six_chain_iff_four_words (a s : Word) :
    OuterIndependentChain 6 a s ↔ SixIndependentCore a s := by
  constructor
  · intro h
    change IndependentChain 6 (0#32) a s (0#32) at h
    cases h with
    | @snoc _ _ _ t _ _ hfive hs5 =>
      cases hfive with
      | @snoc _ _ _ r _ _ hfour hs4 =>
        cases hfour with
        | @snoc _ _ _ q _ _ hthree hs3 =>
          cases hthree with
          | @snoc _ _ _ p _ _ htwo hs2 =>
            cases htwo with
            | snoc hone hs1 =>
              cases hone with
              | snoc hzero hs0 =>
                cases hzero
                refine ⟨p, q, r, t, ?_, ?_, ?_, ?_, ?_, ?_⟩
                · simpa [Magma.xor] using hs0
                · exact hs1
                · exact hs2
                · exact hs3
                · exact hs4
                · simpa [Magma.xor] using hs5
  · rintro ⟨p, q, r, t, hs0, hs1, hs2, hs3, hs4, hs5⟩
    have hzero : IndependentChain 0 (0#32) a (0#32) a :=
      IndependentChain.zero (0#32) a
    have hone : IndependentChain 1 (0#32) a a p :=
      IndependentChain.snoc hzero (by
        simpa [Magma.xor] using hs0)
    have htwo : IndependentChain 2 (0#32) a p q :=
      IndependentChain.snoc hone hs1
    have hthree : IndependentChain 3 (0#32) a q r :=
      IndependentChain.snoc htwo hs2
    have hfour : IndependentChain 4 (0#32) a r t :=
      IndependentChain.snoc hthree hs3
    have hfive : IndependentChain 5 (0#32) a t s :=
      IndependentChain.snoc hfour hs4
    exact IndependentChain.snoc hfive (by
      simpa [Magma.xor] using hs5)

/-- The strong eight-round outer obstruction that matches the Z3
    model: if the six independent real one-round supports cannot be
    jointly satisfied, the 8-round DDT is zero for ALL round keys. -/
theorem eight_round_outer_zero_of_no_six_local_support
    (keys : Fin 8 → Word) (a s : Word)
    (hno : ¬ SixIndependentCore a s) :
    xorDDT_rounds 8 keys (a, 0#32) (0#32, s) = 0 := by
  exact outer_zero_of_no_independent_chain 6 keys a s
    (fun h => hno ((six_chain_iff_four_words a s).mp h))


/-- The six true-local-support constraints reverse exactly under
    exchanging the two OUTER active words. This does not assert that
    a single master key remains unchanged under reversal. -/
theorem six_independent_core_symmetric (a s : Word) :
    SixIndependentCore a s ↔ SixIndependentCore s a := by
  have hxor (x y : Word) : Magma.xor x y = Magma.xor y x := by
    change x ^^^ y = y ^^^ x
    exact BitVec.xor_comm x y
  have hreverse (x y : Word) (h : SixIndependentCore x y) :
      SixIndependentCore y x := by
    obtain ⟨p, q, r, t, h0, h1, h2, h3, h4, h5⟩ := h
    refine ⟨t, r, q, p, h5, ?_, ?_, ?_, ?_, h0⟩
    · rw [hxor r y]
      exact h4
    · rw [hxor q t]
      exact h3
    · rw [hxor p r]
      exact h2
    · rw [hxor x q]
      exact h1
  exact ⟨hreverse a s, hreverse s a⟩

/-- Restrict a 32-bit difference to a nonzero 4-bit value in one
    selected nibble and ZERO in all other nibbles. -/
def OnlyActiveNibble (i : Fin 8) (x : Word) : Prop :=
  x ≠ (0#32) ∧
    x.toNat % 16 ^ i.val = 0 ∧
    x.toNat < 16 ^ (i.val + 1)

/-- A local-support rejection for an entire 15-by-15 rectangle
    of input and output nibble values. This is the obligation to
    discharge by a kernel-checked nibble/carry certificate. -/
def RejectNibbleRectangle (i j : Fin 8) : Prop :=
  ∀ a s : Word, OnlyActiveNibble i a →
    OnlyActiveNibble j s → ¬ SixIndependentCore a s

/-- One rectangle theorem implies its reverse under Feistel symmetry.
    Thus the five experimentally found 8-round forbidden rectangles
    require at most THREE independent local-support certifications. -/
theorem reject_rectangle_symmetric (i j : Fin 8) :
    RejectNibbleRectangle i j ↔ RejectNibbleRectangle j i := by
  constructor
  · intro h s a hs ha hc
    exact h a s ha hs
      ((six_independent_core_symmetric s a).mp hc)
  · intro h a s ha hs hc
    exact h s a hs ha
      ((six_independent_core_symmetric a s).mp hc)

/-- A certified local-support rectangle excludes all actual eight-
    round Magma outer transitions in that rectangle, for EVERY fixed
    sequence of eight round keys and every RFC master key schedule. -/
theorem eight_round_zero_of_rejected_rectangle
    (keys : Fin 8 → Word) (i j : Fin 8) (a s : Word)
    (hrect : RejectNibbleRectangle i j)
    (ha : OnlyActiveNibble i a)
    (hs : OnlyActiveNibble j s) :
    xorDDT_rounds 8 keys (a, 0#32) (0#32, s) = 0 :=
  eight_round_outer_zero_of_no_six_local_support keys a s
    (hrect a s ha hs)


/-- For all five observed forbidden nibble rectangles, it suffices
    to certify just the three geometrically distinct ones. The
    three hypotheses are deliberately explicit: Z3 results have not
    been promoted to kernel-checked UNSAT certificates. -/
theorem five_rectangles_of_three_certificates
    (h57 : RejectNibbleRectangle (5 : Fin 8) (7 : Fin 8))
    (h67 : RejectNibbleRectangle (6 : Fin 8) (7 : Fin 8))
    (h77 : RejectNibbleRectangle (7 : Fin 8) (7 : Fin 8)) :
    RejectNibbleRectangle (5 : Fin 8) (7 : Fin 8) ∧
    RejectNibbleRectangle (6 : Fin 8) (7 : Fin 8) ∧
    RejectNibbleRectangle (7 : Fin 8) (5 : Fin 8) ∧
    RejectNibbleRectangle (7 : Fin 8) (6 : Fin 8) ∧
    RejectNibbleRectangle (7 : Fin 8) (7 : Fin 8) := by
  exact ⟨h57, h67, (reject_rectangle_symmetric 5 7).mp h57,
    (reject_rectangle_symmetric 6 7).mp h67, h77⟩

end Magma.DiffanIndependentRoundSupport
