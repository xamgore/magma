module

import all Init.Data.Range.Basic
public import Magma.Differential.Windows.ScheduledCorrectionHomogeneity
import Std.Tactic.BVDecide

@[expose] public section

/-!
# Paired real midpoint fibers for the second-round correction

For an XOR direction t, the local correction at right midpoint base R is
identical to its correction at R XOR t, regardless of the master key.
This is a *pointwise* symmetry of an XOR derivative, not the earlier
translation symmetry of a complete DDT row.

The obstruction is reachability: R XOR t might fail the genuine prefix/suffix
endpoint constraints. We formulate a sufficient condition that both endpoints
remain admissible, then show every nonempty correction slice contains at least
two different real midpoint bases when t is nonzero.

A finite endpoint-selected example proves that the hypothesis can hold with
exactly two admissible midpoint bases and with a uniform correction. The
chosen endpoint predicate depends on the prefix and master key: it is a
mathematical witness, NOT an assertion that an observable key-independent
constraint with this property has been found.

-/

namespace Magma.DiffanScheduledCorrectionPartnerFibers

open Magma
open Magma.DiffanFeistelDeltaPropagation
open Magma.DiffanScheduledCorrectionReachability
open Magma.DiffanScheduledCorrectionHomogeneity
open Magma.DiffanScheduledMeet

private abbrev Word :=
  V 32

private abbrev Master :=
  V 256

private abbrev Point :=
  Diffan.StateDifference (Word × Word) (Word × Word)

/-- An XOR derivative has the same value at x and x XOR t.
    The key and the function g are completely unrestricted here. -/
theorem correction_partner (k t L aL d R : Word) :
    secondCorrection k t (middleAt L aL d (R ^^^ t)) =
      secondCorrection k t (middleAt L aL d R) := by
  change
    g k ((R ^^^ t) ^^^ (d ^^^ t)) ^^^ g k ((R ^^^ t) ^^^ d) =
      g k (R ^^^ (d ^^^ t)) ^^^ g k (R ^^^ d)
  have hfirst : (R ^^^ t) ^^^ (d ^^^ t) = R ^^^ d := by
    bv_decide
  have hsecond : (R ^^^ t) ^^^ d = R ^^^ (d ^^^ t) := by
    bv_decide
  rw [hfirst, hsecond]
  exact BitVec.xor_comm _ _

/-- Endpoint-by-endpoint preservation is sufficient to keep the full
    scheduled midpoint admissible after translating its right base. -/
theorem admitted_partner_of_endpoint_stability
    («prefix» suffix : List (Fin 32)) (master : Master)
    (P Q : Point → Prop) (L aL d t : Word)
    (hP : ∀ R, P ((leftEquiv «prefix» master).symm (middleAt L aL d R)) →
      P ((leftEquiv «prefix» master).symm (middleAt L aL d (R ^^^ t))))
    (hQ : ∀ R, Q (rightEquiv suffix master (middleAt L aL d R)) →
      Q (rightEquiv suffix master (middleAt L aL d (R ^^^ t)))) :
    ∀ R, admittedAt «prefix» suffix master P Q L aL d R →
      admittedAt «prefix» suffix master P Q L aL d (R ^^^ t) := by
  intro R h
  exact ⟨hP R h.1, hQ R h.2⟩

/-- These two right bases are distinct for a nonzero direction. -/
private theorem xor_partner_ne (R t : Word) (ht : t ≠ 0#32) :
    R ≠ R ^^^ t := by
  intro heq
  have hh := congrArg (fun u : Word => R ^^^ u) heq
  have hz : (0#32) = t := by
    simpa only [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
      using hh
  exact ht hz.symm

/-- The elementary two-element subset of a correction fiber. -/
def partnerBases (R t : Word) : Finset Word := {R, R ^^^ t}

private theorem partnerBases_card (R t : Word) (ht : t ≠ 0#32) : (partnerBases R t).card = 2 := by
  have hne := xor_partner_ne R t ht
  simp [partnerBases, hne]

/-- If every admitted right midpoint base brings along its XOR partner,
    each positive restricted correction coefficient is at least two.
    Both midpoints meet the same real prefix/suffix constraints and use
    the same 256-bit master key. -/
theorem positive_slice_has_two_real_midpoints
    («prefix» suffix : List (Fin 32)) (master : Master) (i : Fin 32)
    (P Q : Point → Prop) (L aL d t b : Word)
    (ht : t ≠ 0#32)
    (hclosed : ∀ R, admittedAt «prefix» suffix master P Q L aL d R →
      admittedAt «prefix» suffix master P Q L aL d (R ^^^ t))
    (hpos : 0 < scheduledCorrectionCount «prefix» suffix master i
      P Q L aL d t b) :
    2 ≤ scheduledCorrectionCount «prefix» suffix master i
      P Q L aL d t b := by
  classical
  obtain ⟨R, hR, hcorr⟩ :=
    (positive_iff_admitted_midpoint «prefix» suffix master i P Q
      L aL d t b).mp hpos
  have hsub : partnerBases R t ⊆
      (admittedBases «prefix» suffix master P Q L aL d).filter
        (fun x => secondCorrection (roundKey master i) t
          (middleAt L aL d x) = b) := by
    intro x hx
    simp only [partnerBases, Finset.mem_insert,
      Finset.mem_singleton] at hx
    rcases hx with hx | hx
    · subst x
      exact Finset.mem_filter.mpr
        ⟨(mem_admittedBases «prefix» suffix master P Q L aL d R).mpr hR,
          hcorr⟩
    · subst x
      exact Finset.mem_filter.mpr
        ⟨(mem_admittedBases «prefix» suffix master P Q L aL d
            (R ^^^ t)).mpr (hclosed R hR),
          (correction_partner (roundKey master i) t L aL d R).trans hcorr⟩
  have hle := Finset.card_le_card hsub
  rw [partnerBases_card R t ht] at hle
  rw [scheduledCount_as_filter]
  exact hle

/-- Stability of the two endpoint predicates ensures that each positive
    correction slice contains an XOR-related pair of midpoint bases. -/
theorem positive_slice_has_two_of_endpoint_stability
    («prefix» suffix : List (Fin 32)) (master : Master) (i : Fin 32)
    (P Q : Point → Prop) (L aL d t b : Word)
    (ht : t ≠ 0#32)
    (hP : ∀ R, P ((leftEquiv «prefix» master).symm (middleAt L aL d R)) →
      P ((leftEquiv «prefix» master).symm (middleAt L aL d (R ^^^ t))))
    (hQ : ∀ R, Q (rightEquiv suffix master (middleAt L aL d R)) →
      Q (rightEquiv suffix master (middleAt L aL d (R ^^^ t))))
    (hpos : 0 < scheduledCorrectionCount «prefix» suffix master i
      P Q L aL d t b) :
    2 ≤ scheduledCorrectionCount «prefix» suffix master i
      P Q L aL d t b := by
  exact positive_slice_has_two_real_midpoints
    «prefix» suffix master i P Q L aL d t b ht
    (admitted_partner_of_endpoint_stability
      «prefix» suffix master P Q L aL d t hP hQ) hpos

/-- Choose actual initial states through a prefix pullback. The fixed
    three midpoint coordinates L,aL,d are imposed by the count, while S
    constrains the remaining real right midpoint base. -/
def initialRightBaseIn («prefix» : List (Fin 32)) (master : Master)
    (S : Finset Word) : Point → Prop :=
  fun initial => ((leftEquiv «prefix» master) initial).base.2 ∈ S

/-- The prefix inverse recovers exactly the prescribed midpoint right base.
    This does not assert that such conditions are publicly observable. -/
theorem selected_admitted_iff
    («prefix» suffix : List (Fin 32)) (master : Master)
    (S : Finset Word) (L aL d R : Word) :
    admittedAt «prefix» suffix master
      (initialRightBaseIn «prefix» master S) (fun _ => True)
      L aL d R ↔ R ∈ S := by
  simp [admittedAt, initialRightBaseIn, middleAt]

/-- On this deliberately constructed endpoint condition, the *real*
    admissible midpoint set is precisely S, rather than a DDT support
    overapproximation. -/
theorem selected_admittedBases_eq
    («prefix» suffix : List (Fin 32)) (master : Master)
    (S : Finset Word) (L aL d : Word) :
    admittedBases «prefix» suffix master
      (initialRightBaseIn «prefix» master S) (fun _ => True)
      L aL d = S := by
  classical
  ext R
  exact (mem_admittedBases «prefix» suffix master
    (initialRightBaseIn «prefix» master S) (fun _ => True)
    L aL d R).trans
    (selected_admitted_iff «prefix» suffix master S L aL d R)

/-- Pulling back the endpoint condition restricts the correction count
    exactly to the prescribed finite set of right bases. -/
theorem selected_count_eq
    («prefix» suffix : List (Fin 32)) (master : Master) (i : Fin 32)
    (S : Finset Word) (L aL d t b : Word) :
    scheduledCorrectionCount «prefix» suffix master i
      (initialRightBaseIn «prefix» master S) (fun _ => True)
      L aL d t b =
        (S.filter (fun R => secondCorrection (roundKey master i) t
          (middleAt L aL d R) = b)).card := by
  rw [scheduledCount_as_filter,
    selected_admittedBases_eq «prefix» suffix master S L aL d]

/-- A non-singleton homogeneous real midpoint slice exists for every
    master key and nonzero direction. The constructed endpoint restriction
    deliberately selects a pair of XOR-related right bases. -/
theorem paired_endpoint_slice_exact_two
    («prefix» suffix : List (Fin 32)) (master : Master) (i : Fin 32)
    (L aL d R t : Word) (ht : t ≠ 0#32) :
    scheduledCorrectionCount «prefix» suffix master i
      (initialRightBaseIn «prefix» master (partnerBases R t))
      (fun _ => True) L aL d t
      (secondCorrection (roundKey master i) t (middleAt L aL d R)) = 2 := by
  classical
  rw [selected_count_eq]
  have hfilter : (partnerBases R t).filter
      (fun x => secondCorrection (roundKey master i) t
        (middleAt L aL d x) =
        secondCorrection (roundKey master i) t (middleAt L aL d R)) =
      partnerBases R t := by
    ext x
    simp only [Finset.mem_filter]
    constructor
    · intro hx
      exact hx.1
    · intro hx
      refine ⟨hx, ?_⟩
      simp only [partnerBases, Finset.mem_insert,
        Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · rfl
      · exact correction_partner (roundKey master i) t L aL d R
  rw [hfilter]
  exact partnerBases_card R t ht

/-- Every other correction value is absent from the same two-midpoint slice. -/
theorem paired_endpoint_other_slice_zero
    («prefix» suffix : List (Fin 32)) (master : Master) (i : Fin 32)
    (L aL d R t b : Word)
    (hne : b ≠ secondCorrection (roundKey master i) t (middleAt L aL d R)) :
    scheduledCorrectionCount «prefix» suffix master i
      (initialRightBaseIn «prefix» master (partnerBases R t))
      (fun _ => True) L aL d t b = 0 := by
  classical
  rw [selected_count_eq]
  have hfilter : (partnerBases R t).filter
      (fun x => secondCorrection (roundKey master i) t
        (middleAt L aL d x) = b) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    rcases Finset.mem_filter.mp hx with ⟨hmem, heq⟩
    simp only [partnerBases, Finset.mem_insert,
      Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl
    · exact hne (heq.symm)
    · have hbase : secondCorrection (roundKey master i) t
          (middleAt L aL d R) = b :=
        (correction_partner (roundKey master i) t L aL d R).symm.trans heq
      exact hne (hbase.symm)
  rw [hfilter]
  rfl

end Magma.DiffanScheduledCorrectionPartnerFibers
