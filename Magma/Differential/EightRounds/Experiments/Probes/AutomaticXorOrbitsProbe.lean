module

import all Init.Data.Range.Basic
public import Difan.Symmetry.AutomaticXorOrbits
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

namespace Magma.DifanZeroKeyEightAutomaticOrbits

open Magma
open Magma.CarryAutomaton
open Magma.DifanZeroKeyEightColumn
open Magma.DifanZeroKeyEightGenericSymmetry

private abbrev Word := V 32

private theorem column_nonempty : zeroColumnSupport.Nonempty :=
  ⟨0x00300000#32, by decide +kernel⟩

/-- The automatic XOR stabilizer search recovers the established two masks. -/
theorem automatic_shifts_exact :
    Difan.AutomaticXorOrbits.shifts zeroColumnSupport =
      ({0#32, 0x00500000#32} : Finset Word) := by
  change Difan.FiniteSupportSymmetry.stabilizers
    zeroColumnSupport xor = _
  exact generic_stabilizers_exact

/-- The support is tiled by its canonical representatives and XOR shifts. -/
theorem automatic_column_tiling :
    Difan.FiniteTranslationOrbits.OrbitTiling
      zeroColumnSupport
      (Difan.AutomaticXorOrbits.representatives zeroColumnSupport)
      (Difan.AutomaticXorOrbits.shifts zeroColumnSupport)
      (fun c t => c ^^^ t) :=
  Difan.AutomaticXorOrbits.automatic_tiling zeroColumnSupport column_nonempty

/-- Eight supported input differences reduce automatically to four
    canonical representatives. -/
theorem automatic_representatives_card :
    (Difan.AutomaticXorOrbits.representatives zeroColumnSupport).card = 4 := by
  have h := Difan.AutomaticXorOrbits.card_eq
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
    (ht : t ∈ Difan.AutomaticXorOrbits.shifts zeroColumnSupport) :
    xorDDT_g (0#32) (c ^^^ t) (1#32) =
      xorDDT_g (0#32) c (1#32) := by
  have hstable :=
    (Difan.AutomaticXorOrbits.mem_shifts_iff
      zeroColumnSupport column_nonempty t).mp ht
  have hct : c ^^^ t ∈ zeroColumnSupport := by
    rw [← hstable]
    exact Finset.mem_image.mpr ⟨c, hc, rfl⟩
  rw [zeroKey_outputOne_exact, if_pos hct,
      zeroKey_outputOne_exact, if_pos hc]

/-- The column mass is twice the sum over the four canonical representatives. -/
set_option maxHeartbeats 5000 in
set_option maxRecDepth 100 in
set_option trace.profiler true in
set_option trace.profiler.threshold 10 in
set_option diagnostics true in
set_option diagnostics.threshold 100 in
set_option trace.Meta.synthInstance true in
theorem exact_column_mass_by_automatic_orbits :
    (∑ c ∈ zeroColumnSupport, xorDDT_g (0#32) c (1#32)) =
      (Difan.AutomaticXorOrbits.shifts zeroColumnSupport).card *
        (∑ r ∈ Difan.AutomaticXorOrbits.representatives zeroColumnSupport,
          xorDDT_g (0#32) r (1#32)) := by
  apply Difan.AutomaticXorOrbits.invariant_sum_eq
    zeroColumnSupport column_nonempty
      (fun c => xorDDT_g (0#32) c (1#32))
  exact column_weight_invariant


end Magma.DifanZeroKeyEightAutomaticOrbits
