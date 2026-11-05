module

import all Init.Data.Range.Basic
public import Diffan.Symmetry.AutomaticXorOrbits
public import Magma.Differential.EightRounds.ZeroKeyEightGenericSymmetry

@[expose] public section

/-!
# Automatically discovered XOR orbits of the zero-key Magma column

No list of translation masks or representatives is supplied to the
algorithm: the only input is the already-certified eight-word support.
The generic BitVec theorem proves that the resulting tiling is free.
The known Magma stabilizer classification identifies its two shifts,
so there are exactly four canonical representatives.

The quantitative identity reduces the single-round DDT-column mass to
one value per orbit.
-/

namespace Magma.DiffanZeroKeyEightAutomaticOrbits

open Magma
open Magma.CarryAutomaton
open Magma.DiffanZeroKeyEightColumn
open Magma.DiffanZeroKeyEightGenericSymmetry

private abbrev Word :=
  V 32

private theorem column_nonempty : zeroColumnSupport.Nonempty :=
  ⟨0x00300000#32, by decide +kernel⟩

/-- The automatic XOR stabilizer search recovers the established two masks. -/
theorem automatic_shifts_exact :
    Diffan.AutomaticXorOrbits.shifts zeroColumnSupport =
      ({0#32, 0x00500000#32} : Finset Word) := by
  change Diffan.FiniteSupportSymmetry.stabilizers
    zeroColumnSupport xor = _
  exact generic_stabilizers_exact

/-- The support is tiled by its canonical representatives and XOR shifts. -/
theorem automatic_column_tiling :
    Diffan.FiniteTranslationOrbits.OrbitTiling
      zeroColumnSupport
      (Diffan.AutomaticXorOrbits.representatives zeroColumnSupport)
      (Diffan.AutomaticXorOrbits.shifts zeroColumnSupport)
      (fun c t => c ^^^ t) :=
  Diffan.AutomaticXorOrbits.automatic_tiling zeroColumnSupport column_nonempty

/-- Eight supported input differences reduce automatically to four
    canonical representatives. -/
theorem automatic_representatives_card :
    (Diffan.AutomaticXorOrbits.representatives zeroColumnSupport).card = 4 := by
  have h := Diffan.AutomaticXorOrbits.card_eq
    zeroColumnSupport column_nonempty
  rw [zeroColumnSupport_card, automatic_shifts_exact] at h
  have htwo : ({0#32, 0x00500000#32} : Finset Word).card = 2 := by
    decide
  rw [htwo] at h
  omega

/-- Every DDT weight in the zero-key output-one column equals 2^29
    on the certified support, hence in particular every discovered
    translation preserves the actual weight function. -/
private theorem column_weight_invariant
    (c : Word) (hc : c ∈ zeroColumnSupport)
    (t : Word)
    (ht : t ∈ Diffan.AutomaticXorOrbits.shifts zeroColumnSupport) :
    xorDDT_g (0#32) (c ^^^ t) (1#32) =
      xorDDT_g (0#32) c (1#32) := by
  have hstable :=
    (Diffan.AutomaticXorOrbits.mem_shifts_iff
      zeroColumnSupport column_nonempty t).mp ht
  have hct : c ^^^ t ∈ zeroColumnSupport := by
    rw [← hstable]
    exact Finset.mem_image.mpr ⟨c, hc, rfl⟩
  rw [zeroKey_outputOne_exact, ite_eq_left hct,
      zeroKey_outputOne_exact, ite_eq_left hc]

/-- The reduced sum is exactly four copies of the certified column weight. -/
theorem reduced_column_mass_exact :
    (∑ r ∈ Diffan.AutomaticXorOrbits.representatives zeroColumnSupport,
      xorDDT_g (0#32) r (1#32)) = 4 * 2 ^ 29 := by
  have hsubset :
      ∀ r ∈ Diffan.AutomaticXorOrbits.representatives zeroColumnSupport,
        r ∈ zeroColumnSupport := by
    intro r hr
    exact ((Diffan.CanonicalTranslationOrbits.mem_canonicalRepresentatives_iff
      zeroColumnSupport
      (Diffan.AutomaticXorOrbits.shifts zeroColumnSupport)
      (fun c t => c ^^^ t) BitVec.toNat r).mp hr).1
  calc
    (∑ r ∈ Diffan.AutomaticXorOrbits.representatives zeroColumnSupport,
      xorDDT_g (0#32) r (1#32)) =
        ∑ r ∈ Diffan.AutomaticXorOrbits.representatives zeroColumnSupport,
          (2 ^ 29 : Nat) := by
        apply Finset.sum_congr rfl
        intro r hr
        rw [zeroKey_outputOne_exact, ite_eq_left (hsubset r hr)]
    _ = 4 * 2 ^ 29 := by
      simp [automatic_representatives_card]

/-- Each of the eight supported inputs contributes the same column weight. -/
private theorem full_column_mass_exact :
    (∑ c ∈ zeroColumnSupport, xorDDT_g (0#32) c (1#32)) =
      8 * 2 ^ 29 := by
  calc
    _ = ∑ c ∈ zeroColumnSupport, (2 ^ 29 : Nat) := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [zeroKey_outputOne_exact, ite_eq_left hc]
    _ = zeroColumnSupport.card * 2 ^ 29 := by simp
    _ = 8 * 2 ^ 29 := by rw [zeroColumnSupport_card]

/-- Each canonical representative accounts for two supported inputs of equal
    DDT weight, so the representative sum is half the full column mass. -/
theorem exact_column_mass_by_automatic_orbits :
    (∑ c ∈ zeroColumnSupport, xorDDT_g (0#32) c (1#32)) =
      (Diffan.AutomaticXorOrbits.shifts zeroColumnSupport).card *
        (∑ r ∈ Diffan.AutomaticXorOrbits.representatives zeroColumnSupport,
          xorDDT_g (0#32) r (1#32)) := by
  have htwo :
      ({0#32, 0x00500000#32} : Finset Word).card = 2 := by
    decide
  calc
    _ = 8 * 2 ^ 29 := full_column_mass_exact
    _ = (Diffan.AutomaticXorOrbits.shifts zeroColumnSupport).card *
          (4 * 2 ^ 29) := by
      rw [automatic_shifts_exact, htwo]
      omega
    _ = (Diffan.AutomaticXorOrbits.shifts zeroColumnSupport).card *
          (∑ r ∈ Diffan.AutomaticXorOrbits.representatives zeroColumnSupport,
            xorDDT_g (0#32) r (1#32)) := by
      rw [reduced_column_mass_exact]

end Magma.DiffanZeroKeyEightAutomaticOrbits
