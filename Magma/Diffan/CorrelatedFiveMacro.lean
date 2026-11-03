module
import all Init.Data.Range.Basic
public import Magma.Diffan.KeyFreeRoundTransducer
public import Magma.Diffan.FirstActiveNibbleInvariant
public import Magma.Diffan.ThreeRoundMiddleDiagonal
public import Magma.Diffan.PairedCarryRefutation
public import Magma.Diffan.SparsePositiveWitnesses

set_option maxRecDepth 8192
set_option linter.constructorNameAsVariable false

@[expose] public section

/-!
# A sound five-round macro-edge for arbitrary windows

A local key-free Feistel edge forgets correlations between round bases.
A correlated trace below remembers the base and difference at every
round. Its five-round segment can therefore be reified as an actual
five-round Magma differential for some five keys and a base.

On (a,0)->(0,b), this incorporates known structural impossibilities
and kernel-verified paired-carry refutations into cuts m+5+r.
-/

namespace Magma.DiffanCorrelatedFiveMacro

open Magma
open Magma.FeistelDDT
open Magma.MultiRoundDDT
open Magma.DiffanKeyFreeRoundTransducer
open Magma.DiffanFiveRoundCoreDefect
open Magma.DiffanFirstActiveNibbleInvariant
open Magma.DiffanThreeRoundMiddleDiagonal
open Magma.DiffanPairedCarryRefutation

private abbrev Word :=
  V 32

private abbrev State :=
  FeistelState

private abbrev Labeled :=
  State × State

/-- Traces with compatible 64-bit base states. Keys may vary by round. -/
inductive Correlated : Nat → Labeled → Labeled → Prop
  | zero (p : Labeled) : Correlated 0 p p
  | snoc {n : Nat} {p q : Labeled} (h : Correlated n p q) (k : Word) :
      Correlated (n + 1) p
        (G k q.1,
         feistelXorDiff k q.2.1 q.2.2 q.1.1 q.1.2)

/-- Every true n-round trajectory gives a correlated trace. -/
theorem Correlated.ofActual
    (n : Nat) (keys : Fin n → Word)
    (base delta : State) :
    Correlated n (base, delta)
      (iterateG n keys base, multiRoundDelta n keys base delta) := by
  induction n with
  | zero =>
      rw [iterateG_zero, multiRoundDelta_zero]
      exact Correlated.zero (base, delta)
  | succ n ih =>
      rw [iterateG_succ, multiRoundDelta_succ]
      exact Correlated.snoc
        (ih (fun i => keys i.castSucc)) (keys (Fin.last n))

/-- Exact traces split at any round boundary. -/
theorem Correlated.split {m n : Nat} {p r : Labeled}
    (h : Correlated (m + n) p r) :
    ∃ q : Labeled, Correlated m p q ∧ Correlated n q r := by
  induction n generalizing r with
  | zero =>
      exact ⟨r, by simpa using h, Correlated.zero r⟩
  | succ n ih =>
      have h' : Correlated ((m + n) + 1) p r := by
        simpa only [Nat.add_succ] using h
      cases h' with
      | snoc hp k =>
          obtain ⟨q, hleft, hright⟩ := ih hp
          exact ⟨q, hleft, Correlated.snoc hright k⟩

/-- Forgetting base states yields the previous key-free transducer. -/
theorem Correlated.toPath {n : Nat} {p q : Labeled}
    (h : Correlated n p q) :
    Path n p.2 q.2 := by
  induction h with
  | zero p => exact Path.zero p.2
  | snoc h k ih =>
      exact Path.snoc ih
        (roundAllowed_of_feistel k _ _ _ _)

/-- Reify an exact trace into n actual consecutive Magma rounds. -/
theorem Correlated.reify {n : Nat} {p q : Labeled}
    (h : Correlated n p q) :
    ∃ keys : Fin n → Word,
      iterateG n keys p.1 = q.1 ∧
      multiRoundDelta n keys p.1 p.2 = q.2 := by
  induction h with
  | zero p =>
      exact ⟨Fin.elim0, by simp only [iterateG_zero],
        by simp only [multiRoundDelta_zero]⟩
  | snoc h k ih =>
      obtain ⟨keys, hb, hd⟩ := ih
      refine ⟨Fin.snoc keys k, ?_, ?_⟩
      · rw [iterateG_succ]
        simp only [Fin.snoc_castSucc, Fin.snoc_last]
        rw [hb]
      · rw [multiRoundDelta_succ]
        simp only [Fin.snoc_castSucc, Fin.snoc_last]
        rw [hb, hd]

/-- Exclusions already established for the outer five-round slice. -/
def OuterForbidden (a b : State) : Prop :=
  a.2 = (0#32) ∧ b.1 = (0#32) ∧
    ((a.1 = b.2 ∧ a.1 ≠ (0#32)) ∨
     (∃ i j : Fin 8, FirstActiveNibbleAt a.1 i ∧
       FirstActiveNibbleAt b.2 j ∧ i ≠ j) ∨
     refutesTriple a.1 b.2 = true)

/-- Exact correlated three-round core support, with arbitrary
    independent inner round keys and TWO coupled base coordinates.
    Unlike a product of one-round DDT entries, this retains their
    base-state correlation and the final-round coupling constraint. -/
def OuterCoupled (a s : Word) : Prop :=
  ∃ k₁ k₂ k₃ R Z : Word,
    threeRoundCoupled k₁ k₂ k₃ (0#32) a s (0#32) R Z

/-- The five-round macro also requires a valid three-round
    *correlated* core on its outer special slice. -/
def Macro5 (a b : State) : Prop :=
  Path 5 a b ∧ ¬ OuterForbidden a b ∧
    (a.2 = (0#32) → b.1 = (0#32) → OuterCoupled a.1 b.2)

private theorem outerForbidden_ddt_zero (k₀ k₁ k₂ k₃ k₄ : Word) (a b : State)
    (hf : OuterForbidden a b) : xorDDT_rounds 5 (fiveRoundKeys k₀ k₁ k₂ k₃ k₄) a b = 0 := by
  rcases a with ⟨al, ar⟩
  rcases b with ⟨bl, br⟩
  rcases hf with ⟨ha, hb, hs⟩
  change ar = (0#32) at ha
  change bl = (0#32) at hb
  subst ar
  subst bl
  rcases hs with hdiag | hdiff | hcert
  · rcases hdiag with ⟨heq, hne⟩
    change al = br at heq
    subst br
    exact fiveRound_diagonal_impossible k₀ k₁ k₂ k₃ k₄ al hne
  · obtain ⟨i, j, hai, hbj, hij⟩ := hdiff
    exact fiveRound_zero_of_distinct_firstActiveNibble k₀ k₁ k₂ k₃ k₄ al br i j hai hbj hij
  · exact refutesTriple_sound al br hcert k₀ k₁ k₂ k₃ k₄

private theorem no_outerForbidden_of_actual (keys : Fin 5 → Word) (base a b : State)
    (h : multiRoundDelta 5 keys base a = b) : ¬OuterForbidden a b := by
  intro hf
  let k₀ := keys 0
  let k₁ := keys 1
  let k₂ := keys 2
  let k₃ := keys 3
  let k₄ := keys 4
  have heq : keys = fiveRoundKeys k₀ k₁ k₂ k₃ k₄ := by
    funext i
    fin_cases i <;> rfl
  have hpos : 0 < xorDDT_rounds 5 (fiveRoundKeys k₀ k₁ k₂ k₃ k₄) a b := by
    exact
      Magma.DiffanSparsePositiveWitnesses.ddt_pos_of_concrete_base k₀ k₁ k₂ k₃ k₄ a b base
        (by
          rw [← heq]; exact h)
  have hz := outerForbidden_ddt_zero k₀ k₁ k₂ k₃ k₄ a b hf
  omega

/-- A generic finite-support lemma is proved without elaborating any
    enormous 64-bit Finset. Its instances merely re-use the proof. -/
private theorem filtered_card_pos_iff {α : Type} [Fintype α]
    (pred : α → Prop) [DecidablePred pred] :
    0 < ((Finset.univ : Finset α).filter pred).card ↔
      ∃ x : α, pred x := by
  constructor
  · intro h
    obtain ⟨x, hx⟩ := Finset.card_pos.mp h
    exact ⟨x, (Finset.mem_filter.mp hx).2⟩
  · rintro ⟨x, hx⟩
    apply Finset.card_pos.mpr
    exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩⟩

/-- Every real five-round outer differential induces the exact
    coupled three-round core. The two outer keys disappear. -/
theorem outerCoupled_of_actual
    (keys : Fin 5 → Word) (base a b : State)
    (ha : a.2 = (0#32)) (hb : b.1 = (0#32))
    (hd : multiRoundDelta 5 keys base a = b) :
    OuterCoupled a.1 b.2 := by
  let k₀ := keys 0
  let k₁ := keys 1
  let k₂ := keys 2
  let k₃ := keys 3
  let k₄ := keys 4
  have heq : keys = fiveRoundKeys k₀ k₁ k₂ k₃ k₄ := by
    funext i
    fin_cases i <;> rfl
  have hp : 0 < xorDDT_rounds 5
      (fiveRoundKeys k₀ k₁ k₂ k₃ k₄) a b := by
    exact Magma.DiffanSparsePositiveWitnesses.ddt_pos_of_concrete_base
      k₀ k₁ k₂ k₃ k₄ a b base (by rw [← heq]; exact hd)
  have hasa : a = (a.1, 0#32) := by
    cases a with
    | mk l r =>
        change (l, r) = (l, 0#32)
        exact congrArg (fun t : Word => (l, t)) ha
  have hasb : b = (0#32, b.2) := by
    cases b with
    | mk l r =>
        change (l, r) = (0#32, r)
        exact congrArg (fun t : Word => (t, r)) hb
  rw [hasa, hasb] at hp
  rw [fiveRound_eq_threeCore, xorDDT_rounds_three] at hp
  have hcore : ∃ q : State,
      threeRoundCoupled k₁ k₂ k₃ (0#32) a.1 b.2 (0#32) q.1 q.2 := by
    classical
    change 0 < ((Finset.univ : Finset State).filter
      (fun q => threeRoundCoupled k₁ k₂ k₃
        (0#32) a.1 b.2 (0#32) q.1 q.2)).card at hp
    exact (filtered_card_pos_iff _).mp hp
  rcases hcore with ⟨⟨R, Z⟩, hc⟩
  exact ⟨k₁, k₂, k₃, R, Z, hc⟩

/-- Exact key-free existence for a five-round outer transition is
    EQUIVALENT to satisfiability of the correlated three-round core.
    No Markov DDT independence approximation is made. -/
theorem outerCoupled_iff_exists_five
    (a s : Word) :
    OuterCoupled a s ↔
      ∃ k₀ k₁ k₂ k₃ k₄ base : Word,
        ∃ baser : Word,
          multiRoundDelta 5 (fiveRoundKeys k₀ k₁ k₂ k₃ k₄)
            (base, baser) (a, 0#32) = (0#32, s) := by
  constructor
  · rintro ⟨k₁, k₂, k₃, R, Z, hc⟩
    have hcount : 0 < threeRoundCoupledCount
        k₁ k₂ k₃ (0#32) a s (0#32) := by
      classical
      change 0 < ((Finset.univ : Finset State).filter
        (fun q => threeRoundCoupled k₁ k₂ k₃
          (0#32) a s (0#32) q.1 q.2)).card
      apply (filtered_card_pos_iff _).mpr
      exact ⟨(R, Z), hc⟩
    have hp : 0 < xorDDT_rounds 5
        (fiveRoundKeys (0#32) k₁ k₂ k₃ (0#32))
        (a, 0#32) (0#32, s) := by
      rw [fiveRound_eq_threeCore, xorDDT_rounds_three]
      exact hcount
    have hbase : ∃ base : State,
        multiRoundDelta 5 (fiveRoundKeys (0#32) k₁ k₂ k₃ (0#32))
          base (a, 0#32) = (0#32, s) := by
      classical
      change 0 < ((Finset.univ : Finset State).filter
        (fun base => multiRoundDelta 5
          (fiveRoundKeys (0#32) k₁ k₂ k₃ (0#32))
          base (a, 0#32) = (0#32, s))).card at hp
      exact (filtered_card_pos_iff _).mp hp
    obtain ⟨⟨bl, br⟩, hd⟩ := hbase
    exact ⟨0#32, k₁, k₂, k₃, 0#32, bl, br, hd⟩
  · rintro ⟨k₀, k₁, k₂, k₃, k₄, basel, baser, hd⟩
    exact outerCoupled_of_actual
      (fiveRoundKeys k₀ k₁ k₂ k₃ k₄)
      (basel, baser) (a, 0#32) (0#32, s) rfl rfl hd

/-- Any correlated five-round window has a refined macro-edge. -/
theorem Correlated.macro5 {p q : Labeled}
    (h : Correlated 5 p q) : Macro5 p.2 q.2 := by
  obtain ⟨keys, _, hd⟩ := Correlated.reify h
  refine ⟨Correlated.toPath h,
    no_outerForbidden_of_actual keys p.1 p.2 q.2 hd, ?_⟩
  intro ha hb
  exact outerCoupled_of_actual keys p.1 p.2 q.2 ha hb hd

/-- The refined cut for any m+5+r-round path. -/
def RefinedWindow (m r : Nat) (a b : State) : Prop :=
  ∃ u v : State,
    Path m a u ∧ Macro5 u v ∧ Path r v b

/-- Every actual path passes through a refined window. -/
theorem refinedWindow_of_actual (m r : Nat)
    (keys : Fin (m + 5 + r) → Word)
    (base a : State) :
    RefinedWindow m r a
      (multiRoundDelta (m + 5 + r) keys base a) := by
  have h := Correlated.ofActual (m + 5 + r) keys base a
  obtain ⟨q, hprefix, hsuffix⟩ :=
    Correlated.split (m := m + 5) (n := r) h
  obtain ⟨p, hleft, hfive⟩ :=
    Correlated.split (m := m) (n := 5) hprefix
  exact ⟨p.2, q.2,
    Correlated.toPath hleft, Correlated.macro5 hfive,
    Correlated.toPath hsuffix⟩

/-- A sound stronger cut rule, not a DDT independence factorization. -/
theorem ddt_zero_of_no_refined_five_window
    (m r : Nat) (keys : Fin (m + 5 + r) → Word)
    (a b : State) (hno : ¬ RefinedWindow m r a b) :
    xorDDT_rounds (m + 5 + r) keys a b = 0 := by
  unfold xorDDT_rounds
  apply Finset.card_eq_zero.mpr
  ext base
  have hz : multiRoundDelta (m + 5 + r) keys base a ≠ b := by
    intro heq
    apply hno
    rw [← heq]
    exact refinedWindow_of_actual m r keys base a
  simp [hz]

/-- Exact support of the coupled core is symmetric under swapping the
    outer differences when the round-key order is allowed to reverse. -/
theorem outerCoupled_symmetric (a s : Word) :
    OuterCoupled a s ↔ OuterCoupled s a := by
  have one_way (x y : Word) (h : OuterCoupled x y) :
      OuterCoupled y x := by
    obtain ⟨k₀, k₁, k₂, k₃, k₄, bl, br, hw⟩ :=
      (outerCoupled_iff_exists_five x y).mp h
    have hp : 0 < xorDDT_rounds 5
        (fiveRoundKeys k₀ k₁ k₂ k₃ k₄)
        (x, 0#32) (0#32, y) :=
      Magma.DiffanSparsePositiveWitnesses.ddt_pos_of_concrete_base
        k₀ k₁ k₂ k₃ k₄ (x, 0#32) (0#32, y) (bl, br) hw
    rw [Magma.DiffanFiveRoundDDTReverse.outer_ddt_reverse] at hp
    have hbase : ∃ base : State,
        multiRoundDelta 5 (fiveRoundKeys k₄ k₃ k₂ k₁ k₀)
          base (y, 0#32) = (0#32, x) := by
      classical
      change 0 < ((Finset.univ : Finset State).filter
        (fun base => multiRoundDelta 5
          (fiveRoundKeys k₄ k₃ k₂ k₁ k₀)
          base (y, 0#32) = (0#32, x))).card at hp
      exact (filtered_card_pos_iff _).mp hp
    obtain ⟨⟨L,R⟩, hrev⟩ := hbase
    exact (outerCoupled_iff_exists_five y x).mpr
      ⟨k₄, k₃, k₂, k₁, k₀, L, R, hrev⟩
  exact ⟨one_way a s, one_way s a⟩

/-- An abstract one-round path is exactly one key-free edge. -/
theorem path_one_iff (a b : State) :
    Path 1 a b ↔ roundAllowed a b := by
  constructor
  · intro h
    cases h with
    | snoc hp hs =>
        cases hp
        exact hs
  · intro h
    exact Path.snoc (Path.zero a) h

/-- A zero-round path can only preserve its difference. -/
theorem path_zero_iff (a b : State) :
    Path 0 a b ↔ a = b := by
  constructor
  · intro h
    cases h
    rfl
  · intro h
    subst b
    exact Path.zero a

/-- Search-ready six-round form: every compatible first-round
    intermediate difference would require a valid refined 5-edge. -/
theorem sixRound_zero_of_no_one_five
    (keys : Fin 6 → Word) (a b : State)
    (hno : ∀ u : State, roundAllowed a u → Macro5 u b → False) :
    xorDDT_rounds 6 keys a b = 0 := by
  apply ddt_zero_of_no_refined_five_window
    (m := 1) (r := 0)
  rintro ⟨u, v, hfirst, hmacro, hlast⟩
  have hv : v = b := (path_zero_iff v b).mp hlast
  subst v
  exact hno u ((path_one_iff a u).mp hfirst) hmacro

/-- Search-ready seven-round form with one key-free round on each
    side of the *correlated* five-round middle window. -/
theorem sevenRound_zero_of_no_one_five_one
    (keys : Fin 7 → Word) (a b : State)
    (hno : ∀ u v : State, roundAllowed a u →
      Macro5 u v → roundAllowed v b → False) :
    xorDDT_rounds 7 keys a b = 0 := by
  apply ddt_zero_of_no_refined_five_window
    (m := 1) (r := 1)
  rintro ⟨u, v, hfirst, hmacro, hlast⟩
  exact hno u v ((path_one_iff a u).mp hfirst)
    hmacro ((path_one_iff v b).mp hlast)

/-- Exact CHARACTERIZATION of universal outer impossibility for all
    five independent round keys. It is NOT an assertion that the
    existential core is decidable efficiently. -/
theorem universal_outer_zero_iff_no_coupled (a s : Word) :
    (∀ k₀ k₁ k₂ k₃ k₄ : Word,
      xorDDT_rounds 5 (fiveRoundKeys k₀ k₁ k₂ k₃ k₄)
        (a, 0#32) (0#32, s) = 0) ↔
    ¬ OuterCoupled a s := by
  constructor
  · intro hall hcore
    obtain ⟨k₀,k₁,k₂,k₃,k₄,bl,br,hd⟩ :=
      (outerCoupled_iff_exists_five a s).mp hcore
    have hp : 0 < xorDDT_rounds 5
        (fiveRoundKeys k₀ k₁ k₂ k₃ k₄)
        (a, 0#32) (0#32, s) :=
      Magma.DiffanSparsePositiveWitnesses.ddt_pos_of_concrete_base
        k₀ k₁ k₂ k₃ k₄ (a, 0#32) (0#32, s) (bl, br) hd
    have hz := hall k₀ k₁ k₂ k₃ k₄
    omega
  · intro hno k₀ k₁ k₂ k₃ k₄
    unfold xorDDT_rounds
    apply Finset.card_eq_zero.mpr
    ext base
    have hz : multiRoundDelta 5
        (fiveRoundKeys k₀ k₁ k₂ k₃ k₄)
        base (a, 0#32) ≠ (0#32, s) := by
      intro hd
      exact hno (outerCoupled_of_actual
        (fiveRoundKeys k₀ k₁ k₂ k₃ k₄)
        base (a, 0#32) (0#32, s) rfl rfl hd)
    simp [hz]

/-- The refined cut includes only paths admitted by the earlier
    local key-free transducer, and may exclude more via correlation. -/
theorem refinedWindow_implies_keyFreePath
    (m r : Nat) (a b : State)
    (h : RefinedWindow m r a b) :
    Path (m + 5 + r) a b := by
  obtain ⟨u, v, hpre, ⟨hfive, _, _⟩, hpost⟩ := h
  exact Path.append (Path.append hpre hfive) hpost

end Magma.DiffanCorrelatedFiveMacro
