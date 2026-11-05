module

import all Init.Data.Range.Basic
public import Difan.Fibers.ObservedGraphJoin

@[expose] public section

/-!
# Exact observations certified on an indexed active support

An index type can parametrise a large but structured class of possible
common bases. Prove that every positive-weight base lies in the image
of `point`, and check each indexed representative.

The certificate is *independent* of the counting weights. At each indexed
base, either the two reconstructed full states match, or the observation
already distinguishes them.  The indexing need not be injective.
-/

namespace Difan.IndexedSupportExactness

variable {Base Middle Label Index : Type*}
variable [Fintype Base] [DecidableEq Middle] [DecidableEq Label]
open Difan.ObservedGraphJoin

/-- An image-supported graph join is exact when every indexed base is
fully compatible or explicitly rejected by the compressed observation. -/
theorem observed_exact_of_indexed_support
    (observe : Middle → Label) (left right : Base → Middle)
    (weight : Base → Nat) (point : Index → Base)
    (hsupport : ∀ b, 0 < weight b → ∃ i, b = point i)
    (hcheck : ∀ i, left (point i) = right (point i) ∨
      observe (left (point i)) ≠ observe (right (point i))) :
    observedMass observe left right weight = exactMass left right weight := by
  classical
  apply observed_exact_of_active_agreement observe left right weight
  intro b hb hobs
  obtain ⟨i, rfl⟩ := hsupport b hb
  rcases hcheck i with heq | hno
  · exact heq
  · exact False.elim (hno hobs)

/-- In particular the masked join makes no hidden false matches on the
indexed support, regardless of the actual multiplicities of paths. -/
theorem hidden_zero_of_indexed_support
    (observe : Middle → Label) (left right : Base → Middle)
    (weight : Base → Nat) (point : Index → Base)
    (hsupport : ∀ b, 0 < weight b → ∃ i, b = point i)
    (hcheck : ∀ i, left (point i) = right (point i) ∨
      observe (left (point i)) ≠ observe (right (point i))) :
    hiddenMass observe left right weight = 0 := by
  classical
  apply (observed_exact_iff_hidden_zero observe left right weight).mp
  exact observed_exact_of_indexed_support observe left right weight point
    hsupport hcheck

end Difan.IndexedSupportExactness
