module

import all Init.Data.Range.Basic
public import Diffan.Core.CoordinateSeparation
public import Magma.Differential.Core.MultiRoundDDT

@[expose] public section

/-!
# Three-round Magma factorization through separated coordinates

For a zero left output difference, the three-round witness condition
reduces to a two-round condition. The bijection
`(L, R) ↦ (R, g[k₀](R) xor L)` then separates it into two predicates,
each depending on one 32-bit coordinate. Their product describes every
64-bit witness exactly and yields the fixed-key DDT factorization.
-/

namespace Magma.DiffanThreeRoundCoordinateCertificate

open Magma
open Magma.MultiRoundDDT
open Magma.CarryAutomaton

private abbrev Word :=
  V 32

private abbrev State :=
  FeistelState

/-- The first DDT fiber in the separated input coordinate `R`. -/
def firstFiber (k₀ aL aR bR : Word) (R : Word) : Prop :=
  gDifference k₀ R aR = xor bR aL

/-- The second DDT fiber in the separated input coordinate `Z`.
    The zero output-left difference forces the first argument of the
    second round-function DDT to be `bR`. -/
def secondFiber (k₁ aR bR : Word) (Z : Word) : Prop :=
  gDifference k₁ Z bR = xor (0#32) aR

/-- The decisive, pointwise certificate: after the bijective coordinate
    change `(L,R) ↦ (R, g[k₀](R) xor L)`, the FULL 3-round predicate is
    equivalent to two independent-coordinate predicates.

    This is the nontrivial hypothesis of `CoordinateSeparation.fiberEquiv`.
    The two-round condition and the zero-left reduction supply this separation. -/
theorem zeroLeft_separates
    (k₀ k₁ k₂ aL aR bR : Word) (start : State) :
    (multiRoundDelta 3 (threeRoundKeys k₀ k₁ k₂)
        start (aL, aR) = (0#32, bR)) ↔
      firstFiber k₀ aL aR bR (twoRoundCoordinates k₀ start).1 ∧
      secondFiber k₁ aR bR (twoRoundCoordinates k₀ start).2 := by
  rcases start with ⟨L, R⟩
  change
    (multiRoundDelta 3 (threeRoundKeys k₀ k₁ k₂)
       (L, R) (aL, aR) = (0#32, bR)) ↔
    (gDifference k₀ R aR = xor bR aL ∧
      gDifference k₁ (xor (g k₀ R) L) bR = xor (0#32) aR)
  exact (threeRound_zero_left_iff_twoRound k₀ k₁ k₂ aL aR bR (L, R)).trans
    (twoRoundCondition k₀ k₁ aL aR bR (0#32) L R)

/-- Each pair of local witnesses determines one full input state through
    the inverse coordinate map. -/
def zeroLeft_fiberEquiv (k₀ k₁ k₂ aL aR bR : Word) :
    {start : State //
      multiRoundDelta 3 (threeRoundKeys k₀ k₁ k₂)
        start (aL, aR) = (0#32, bR)} ≃
      {R : Word // firstFiber k₀ aL aR bR R} ×
      {Z : Word // secondFiber k₁ aR bR Z} :=
  Diffan.CoordinateSeparation.fiberEquiv
    (twoRoundCoordinates k₀)
    (fun start => multiRoundDelta 3 (threeRoundKeys k₀ k₁ k₂)
      start (aL, aR) = (0#32, bR))
    (firstFiber k₀ aL aR bR)
    (secondFiber k₁ aR bR)
    (zeroLeft_separates k₀ k₁ k₂ aL aR bR)

/-! ## Exact cardinalities of the two separated fibers

The subtype cardinalities are first expressed as filtered finite sets.
Equality then follows from pointwise membership, allowing the elaborator
to compare predicates without unfolding computational `Fintype` instances
for `BitVec 32`.
-/

open scoped Classical in
/-- The first coordinate constraint counts the corresponding round-function differential. -/
theorem firstFiber_card (k₀ aL aR bR : Word) :
    Fintype.card {R : Word // firstFiber k₀ aL aR bR R} =
      xorDDT_g k₀ aR (xor bR aL) := by
  classical
  calc
    Fintype.card {R : Word // firstFiber k₀ aL aR bR R} =
        ((Finset.univ : Finset Word).filter
          (firstFiber k₀ aL aR bR)).card :=
      Fintype.card_subtype (firstFiber k₀ aL aR bR)
    _ = xorDDT_g k₀ aR (xor bR aL) := by
      unfold xorDDT_g
      apply congrArg Finset.card
      ext R
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        firstFiber, gDifference]

open scoped Classical in
/-- The second coordinate constraint counts the differential from `bR` to
    `aR`; this uses exactly the same symbolic filtering argument. -/
theorem secondFiber_card (k₁ aR bR : Word) :
    Fintype.card {Z : Word // secondFiber k₁ aR bR Z} =
      xorDDT_g k₁ bR aR := by
  classical
  have hz : xor (0#32) aR = aR := by
    change (0#32) ^^^ aR = aR
    exact BitVec.zero_xor
  calc
    Fintype.card {Z : Word // secondFiber k₁ aR bR Z} =
        ((Finset.univ : Finset Word).filter
          (secondFiber k₁ aR bR)).card :=
      Fintype.card_subtype (secondFiber k₁ aR bR)
    _ = xorDDT_g k₁ bR aR := by
      unfold xorDDT_g
      apply congrArg Finset.card
      ext Z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        secondFiber, gDifference, hz]

/-- Separation in bijective coordinates justifies multiplying the two local
    witness counts at fixed round keys. -/
theorem threeRound_factorization_via_coordinates
    (k₀ k₁ k₂ aL aR bR : Word) :
    xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
      (aL, aR) (0#32, bR) =
      xorDDT_g k₀ aR (xor bR aL) * xorDDT_g k₁ bR aR := by
  classical
  calc
    xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
        (aL, aR) (0#32, bR) =
      Fintype.card {start : State //
        multiRoundDelta 3 (threeRoundKeys k₀ k₁ k₂)
          start (aL, aR) = (0#32, bR)} := by
        simp only [xorDDT_rounds, Fintype.card_subtype]
    _ = Fintype.card {R : Word // firstFiber k₀ aL aR bR R} *
        Fintype.card {Z : Word // secondFiber k₁ aR bR Z} := by
          rw [← Fintype.card_prod]
          exact Fintype.card_congr (zeroLeft_fiberEquiv k₀ k₁ k₂ aL aR bR)
    _ = _ := by
      rw [firstFiber_card, secondFiber_card]

end Magma.DiffanThreeRoundCoordinateCertificate
