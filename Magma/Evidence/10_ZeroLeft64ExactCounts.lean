module

public import Magma.Evidence.«08_ZeroLeftSupport»
import all Init.Data.Range.Basic

@[expose] public section

/-!
# 10: exact DDT counts for all 64 predicted pairs

Iteration 08 enumerated pairs using two four-bit S-box tables, and iteration
09 connected the three-round DDT to sixteen exact local factors. Here every
choice `w ∈ W`, `u ∈ U` is certified for first two keys zero, input right
difference one, and an arbitrary third key:

`bR = w * 2^20`, `aL = w * 2^20 + u * 2^11`,

`DDT₃((aL, 1), (0, bR)) = 2 * 16^7 * 2 * 16^7 = 2^58`.

The shifted terms occupy disjoint bits. The proof checks 64 small products
of four-bit DDT entries, without enumerating 32-bit or 64-bit states. The list
has no duplicate pairs, so `sixty_four_certified_pairs` certifies 64 distinct
pairs with identical exact counts, uniformly over the third key.

Iteration 08 is imported to reuse its definitions and proved list length; it
contains no executable experiments. Earlier search profiles are not imported.

Build explicitly with `lake build Magma/Evidence/10_ZeroLeft64ExactCounts.lean`.
-/

open Magma.Internal Magma.MultiRoundDDT Magma.Evidence.ZeroLeftSupport

namespace Magma.Evidence.ZeroLeft64Exact

/-- All eight-by-eight parameter choices have exact count `2^58`.
    Importantly, each goal below is a *small*, fixed product of eight
    4-bit S-box DDT entries; no `Finset FeistelState` is evaluated. -/
theorem exact_count_for_UW
    (k₂ : V 32) (w u : Nat)
    (hw : w ∈ W) (hu : u ∈ U) :
    xorDDT_rounds 3 (threeRoundKeys (0#32) (0#32) k₂)
      (BitVec.ofNat 32 (w * 2^20 + u * 2^11), 1#32)
      (0#32, BitVec.ofNat 32 (w * 2^20)) = 2^58 := by
  have hw' :
      w = 3 ∨ w = 6 ∨ w = 8 ∨ w = 9 ∨
      w = 10 ∨ w = 12 ∨ w = 13 ∨ w = 15 := by
    simpa [W] using hw
  have hu' :
      u = 2 ∨ u = 3 ∨ u = 4 ∨ u = 6 ∨
      u = 8 ∨ u = 10 ∨ u = 14 ∨ u = 15 := by
    simpa [U] using hu
  rcases hw' with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    rcases hu' with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    rw [zeroLeft_three_round_exact_sbox_product] <;>
    decide +kernel

/-- Every element of the original enumerated list has DDT exactly `2^58`.
    This converts a 64-case computation into one reusable theorem. -/
theorem predictedPairs_exact_count
    (k₂ aL bR : V 32)
    (hp : (aL, bR) ∈ predictedPairs) :
    xorDDT_rounds 3 (threeRoundKeys (0#32) (0#32) k₂)
      (aL, 1#32) (0#32, bR) = 2^58 := by
  unfold predictedPairs at hp
  rcases List.mem_flatMap.mp hp with ⟨w, hw, hwu⟩
  rcases List.mem_map.mp hwu with ⟨u, hu, hpair⟩
  have hc := exact_count_for_UW k₂ w u hw hu
  have ha : BitVec.ofNat 32 (w * 2^20 + u * 2^11) = aL :=
    (Prod.mk.inj hpair).1
  have hb : BitVec.ofNat 32 (w * 2^20) = bR :=
    (Prod.mk.inj hpair).2
  rw [ha, hb] at hc
  exact hc

/-- In particular all enumerated pairs have strictly positive DDT. -/
theorem predictedPairs_possible
    (k₂ aL bR : V 32)
    (hp : (aL, bR) ∈ predictedPairs) :
    0 < xorDDT_rounds 3 (threeRoundKeys (0#32) (0#32) k₂)
      (aL, 1#32) (0#32, bR) := by
  rw [predictedPairs_exact_count k₂ aL bR hp]
  norm_num

/-- The parametrization has no duplicate pairs: all 64 entries
    correspond to different input/output difference pairs. -/
theorem predictedPairs_nodup : predictedPairs.Nodup := by
  decide +kernel

/-- A compact public statement: there are 64 distinct *certified*
    pairs, and every one has the same exact count. Note that this is
    an inclusion, not yet the converse (all other pairs impossible). -/
theorem sixty_four_certified_pairs (k₂ : V 32) :
    predictedPairs.length = 64 ∧
    predictedPairs.Nodup ∧
    (∀ aL bR : V 32, (aL, bR) ∈ predictedPairs →
      xorDDT_rounds 3 (threeRoundKeys (0#32) (0#32) k₂)
        (aL, 1#32) (0#32, bR) = 2^58) := by
  refine ⟨predictedPairs_length, predictedPairs_nodup, ?_⟩
  intro aL bR hp
  exact predictedPairs_exact_count k₂ aL bR hp

end Magma.Evidence.ZeroLeft64Exact
