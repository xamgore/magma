module

import all Init.Data.Range.Basic
public import Diffan.Fibers.MiddleObservation
public import Diffan.Core.Constraints
public import Magma.Differential.Windows.ScheduledMeet
public import Magma.Differential.Windows.ScheduledWindowLeftSymmetries

@[expose] public section

/-!
# Sound midpoint filters for actual scheduled Magma rounds

A prefix and a suffix both use round keys derived from one 256-bit master.
Every projected label is computed from the actual middle pair of executions.
A mismatching projection excludes a real meet; a matching projection is only
an overapproximation until the full base state and difference are checked.

These filters are not assertions that local DDT translations lift to a
longer-round DDT symmetry. That would need an intertwining equivalence on
concrete trajectory fibers, not only a symmetry of marginal DDT entries.
-/

namespace Magma.DiffanScheduledMiddleObservation

open Magma
open Magma.DiffanScheduledMeet
open Magma.DiffanScheduledWindowLeftSymmetries
open Magma.DiffanThreeRoundLeftTranslationAudit (leftMask)

private abbrev Word :=
  V 32

private abbrev Master :=
  V 256

private abbrev RoundState :=
  Word × Word

private abbrev Point :=
  Diffan.StateDifference RoundState RoundState

/-- Exact midpoint agreement for two scheduled segments using one master. -/
def exactMeets («prefix» suffix : List (Fin 32))
    (master : Master) (initial final : Point) : Prop :=
  Diffan.Meet.meets (leftEquiv «prefix» master) (rightEquiv suffix master)
    initial final

/-- Equality of the actual 64-bit middle base state. -/
def baseMatches («prefix» suffix : List (Fin 32))
    (master : Master) (initial final : Point) : Prop :=
  Diffan.MiddleObservation.baseMeets
    (leftEquiv «prefix» master) (rightEquiv suffix master) initial final

/-- Equality of both 32-bit middle differences, without the base. -/
def deltaMatches («prefix» suffix : List (Fin 32))
    (master : Master) (initial final : Point) : Prop :=
  Diffan.MiddleObservation.differenceMeets
    (leftEquiv «prefix» master) (rightEquiv suffix master) initial final

/-- The full meet is equivalent to the conjunction of the two fields.
    The base state identifies which concrete trajectories meet. -/
theorem exact_iff_base_and_delta
    («prefix» suffix : List (Fin 32)) (master : Master)
    (initial final : Point) :
    exactMeets «prefix» suffix master initial final ↔
      baseMatches «prefix» suffix master initial final ∧
        deltaMatches «prefix» suffix master initial final := by
  exact Diffan.MiddleObservation.exact_iff_base_and_difference
    (leftEquiv «prefix» master) (rightEquiv suffix master) initial final

/-- Observe the selected bits in each half of the middle difference. -/
def maskedDelta (maskL maskR : Word) (p : Point) : Word × Word :=
  (p.delta.1 &&& maskL, p.delta.2 &&& maskR)

/-- A cheap necessary condition for an actual joint trajectory. -/
def maskedMatches («prefix» suffix : List (Fin 32))
    (maskL maskR : Word) (master : Master) (initial final : Point) : Prop :=
  Diffan.MiddleObservation.observedMeets
    (leftEquiv «prefix» master) (rightEquiv suffix master)
    (maskedDelta maskL maskR) initial final

/-- Exact agreement passes through every bit mask. -/
theorem exact_implies_masked («prefix» suffix : List (Fin 32))
    (maskL maskR : Word) (master : Master) (initial final : Point)
    (h : exactMeets «prefix» suffix master initial final) :
    maskedMatches «prefix» suffix maskL maskR master initial final := by
  exact Diffan.MiddleObservation.exact_implies_observed
    (leftEquiv «prefix» master) (rightEquiv suffix master)
    (maskedDelta maskL maskR) initial final h

/-- Disagreement on even one observed bit rules out that master key
    for those concrete endpoints and the selected round segments. -/
theorem mismatch_excludes_exact («prefix» suffix : List (Fin 32))
    (maskL maskR : Word) (master : Master) (initial final : Point)
    (h : ¬ maskedMatches «prefix» suffix maskL maskR master initial final) :
    ¬ exactMeets «prefix» suffix master initial final := by
  exact Diffan.MiddleObservation.no_exact_of_observation_mismatch
    (leftEquiv «prefix» master) (rightEquiv suffix master)
    (maskedDelta maskL maskR) initial final h

/-- Master keys whose reconstructed midpoints agree on the selected bits. -/
def candidateMasters («prefix» suffix : List (Fin 32))
    (maskL maskR : Word) (initial final : Point) :
    Diffan.KeyConstraint Master :=
  fun master => maskedMatches «prefix» suffix maskL maskR master initial final

/-- Every master key admitting an exact joined trajectory passes the filter. -/
theorem exact_master_in_candidates («prefix» suffix : List (Fin 32))
    (maskL maskR : Word) (master : Master) (initial final : Point)
    (h : exactMeets «prefix» suffix master initial final) :
    candidateMasters «prefix» suffix maskL maskR initial final master := by
  exact exact_implies_masked «prefix» suffix maskL maskR master initial final h

/-- All-window local symmetry restricts the source-word parities, while
    an exact meet places the same master key in the midpoint candidate set. -/
theorem local_symmetry_and_exact_implies_candidate
    («prefix» suffix : List (Fin 32))
    (maskL maskR : Word) (master : Master) (initial final : Point)
    (hlocal : ∀ start : Fin 30, universalAt master start leftMask)
    (hexact : exactMeets «prefix» suffix master initial final) :
    (∀ i : Fin 8, (baseRoundKey master i).toNat % 2 = 0) ∧
      candidateMasters «prefix» suffix maskL maskR initial final master := by
  exact ⟨(all_windows_iff_eight_source_words_even master).mp hlocal,
    exact_master_in_candidates «prefix» suffix maskL maskR master initial final hexact⟩

end Magma.DiffanScheduledMiddleObservation
