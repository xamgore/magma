module
public import Diffan.Composition.ExactBaseJoin
public import Diffan.Observables.SlicedCollisionEnergy
public import Magma.Differential.FullCipher.FullScheduleXorSymmetries
import all Init.Data.Range.Basic
import Magma.Differential.Bridges.DiffanRoundDDTBridge

set_option maxRecDepth 2048
set_option maxHeartbeats 1000000
set_option linter.constructorNameAsVariable false

@[expose] public section

/-!
# The original user's half-zero 64-bit differential slices:
# full actual RFC Magma, fixed key, EXACT conditional 16/16 join

This is the inverse/reversed-key reflected second-half
factorization:
    C32 = Q16 o H²,
    Q16 = H^-1 o J o H.

For a fixed master key K and arbitrary word differences a,b,
the genuine native RFC XOR-DDT entry at (a,0) -> (0,b)
is equal to a sum over actual 16-round midpoint BASES u.
At each u, the midpoint difference is FUNCTIONALLY fixed by
the inverse prefix, and the suffix must use that SAME u.

Critically: the intermediate difference need NOT have
a zero word even though BOTH endpoints do. A zero-half
projection AT THE CUT is generally not exact.

This is a precise reusable law for full 32 rounds; it
does not claim that evaluating the 2^64-base sum is
efficient without a proven compression.
-/

namespace Magma.DiffanFull32SlicedJoin

open Magma Magma.Internal Magma.MultiRoundDDT
open Magma.DiffanFullScheduleConjugacy
open Magma.DiffanFullScheduleXorSymmetries

private abbrev W := V 32
private abbrev S := FeistelState

/-- The half-zero input slice is special for a genuine
ordinary RFC Feistel G step, regardless of Sbox, carries,
rotation, input base or round key:

    derivative G_k at (a,0) = (0,a).

This is a key-independent EXACT transport, and the reason
to keep zero-half endpoint slices as first-class objects.
It is NOT stable under a second generic Feistel round. -/
theorem one_round_half_zero_free
    (k a : W) (x : S) :
    Diffan.derivative pairXor pairXor (G k)
      (a,0#32) x = (0#32,a) := by
  change Diffan.derivative
      Magma.DiffanReverseRound.roundXor
      Magma.DiffanReverseRound.roundXor (G k)
      (a,0#32) x = (0#32,a)
  rw [Magma.DiffanRoundDDTBridge.derivative_G_eq_feistel]
  rw [Magma.FeistelDDT.feistelXorDiff_eq]
  rcases x with ⟨l,r⟩
  change (0#32, (g k (r ^^^ 0#32) ^^^ g k r) ^^^ a) =
    (0#32,a)
  simp only [BitVec.xor_zero, BitVec.xor_self,
    BitVec.zero_xor]

def forward16 (keys : Fin 8 → W) : S ≃ S :=
  (HE keys).trans (HE keys)

theorem forward16_apply (keys : Fin 8 → W) (p : S) :
    forward16 keys p = H keys (H keys p) := rfl

theorem native_32_eq_two_middles (keys : Fin 8 → W) :
    C keys = Q16 keys ∘ forward16 keys := by
  funext p
  rfl

/-- For ANY full 64-bit XOR input/output differences,
the whole C32 DDT exactly equals ONE state-conditioned
join of the 16-round forward and reflected blocks. -/
theorem c32_ddt_eq_base_join
    (keys : Fin 8 → W) (alpha beta : S) :
    Diffan.ddt pairXor pairXor (C keys) alpha beta =
      Diffan.ExactBaseJoin.count pairXor
        (forward16 keys) (Q16 keys) alpha beta := by
  rw [native_32_eq_two_middles]
  exact Diffan.ExactBaseJoin.ddt_comp_eq_exactBaseJoin
    pairXor (forward16 keys) (Q16 keys) alpha beta

/-- The first *genuine aggregation* of the user's slice:
SUM over all right-word output differences b eliminates
the functional b completely. What remains is ONLY a
left-output collision at equal input right halves.

This applies to ANY real 64-bit transformation f,
including all 32 true RFC rounds with a fixed key.
It is not an equality of scalar DDT PRODUCTS. -/
theorem sum_halfzero_output_label_eliminates
    (f : S → S) (a : W) :
    (∑ b : W, Diffan.ddt pairXor pairXor f
      (a,0#32) (0#32,b)) =
      Fintype.card {x : S //
        (Diffan.derivative pairXor pairXor f
          (a,0#32) x).1 = 0#32} := by
  classical
  calc
    (∑ b : W, Diffan.ddt pairXor pairXor f
      (a,0#32) (0#32,b)) =
        ∑ b : W, Fintype.card {x : S //
          Diffan.derivative pairXor pairXor f
            (a,0#32) x = (0#32,b)} := by
      apply Finset.sum_congr rfl
      intro b _
      simp only [Diffan.ddt, Fintype.card_subtype]
    _ = Fintype.card {x : S //
        (Diffan.derivative pairXor pairXor f
          (a,0#32) x).1 = 0#32} :=
      Diffan.SlicedCollisionEnergy.sum_output_label_eliminates
        (fun x : S => Diffan.derivative pairXor pairXor f
          (a,0#32) x) (0#32)

/-- The remaining condition has NO differential output word:
it asks whether a 32-bit left-output projection collides
when input LEFT is XOR-shifted and input RIGHT is held fixed. -/
theorem projected_left_collision_iff
    (f : S → S) (a : W) (x : S) :
    (Diffan.derivative pairXor pairXor f
      (a,0#32) x).1 = 0#32 ↔
      (f x).1 = (f (x.1 ^^^ a, x.2)).1 := by
  have hz : Magma.xor x.2 (0#32) = x.2 := by
    change x.2 ^^^ (0#32) = x.2
    exact BitVec.xor_zero
  change Magma.xor (f x).1
    (f (Magma.xor x.1 a, Magma.xor x.2 (0#32))).1 = 0#32 ↔
      (f x).1 = (f (x.1 ^^^ a, x.2)).1
  rw [hz]
  change (f x).1 ^^^ (f (x.1 ^^^ a,x.2)).1 = 0#32 ↔
    (f x).1 = (f (x.1 ^^^ a,x.2)).1
  exact BitVec.xor_eq_zero_iff

/-- The actual FULL 32-round native RFC (fixed secret key):
a whole ROW-AGGREGATE of half-zero DDT entries is a single
projection-collision count, regardless of Sboxes and carries.

This is one exact simpler DIFFERENTIAL TYPE. It still
requires an efficient way to count these 32-bit collisions;
the theorem alone does not give a sub-2^64 algorithm. -/
theorem rfc_full32_halfzero_aggregated
    (K : V 256) (a : W) :
    (∑ b : W, Diffan.ddt pairXor pairXor
      (fun p : S => split 32 32 (encrypt K (pack p)))
      (a,0#32) (0#32,b)) =
      Fintype.card {x : S //
        (split 32 32 (encrypt K (pack x))).1 =
        (split 32 32
          (encrypt K (pack (x.1 ^^^ a, x.2)))).1} := by
  rw [sum_halfzero_output_label_eliminates]
  apply Fintype.card_congr
  exact {
    toFun := fun x =>
      ⟨x.1, (projected_left_collision_iff _ a x.1).mp x.2⟩
    invFun := fun x =>
      ⟨x.1, (projected_left_collision_iff _ a x.1).mpr x.2⟩
    left_inv := by
      intro x
      apply Subtype.ext
      rfl
    right_inv := by
      intro x
      apply Subtype.ext
      rfl
  }

/-- The requested half-zero input/output slice, with a
and b arbitrary actual 32-bit XOR differences. -/
theorem c32_half_zero_slice
    (keys : Fin 8 → W) (a b : W) :
    Diffan.ddt pairXor pairXor (C keys)
      (a,0#32) (0#32,b) =
    Diffan.ExactBaseJoin.count pairXor
      (forward16 keys) (Q16 keys) (a,0#32) (0#32,b) :=
  c32_ddt_eq_base_join keys _ _

/-- Exactly the actual RFC 256-bit master key, true roundKey
schedule, and final GStar(no swap). Not a convenient toy
of a merely related Feistel function. -/
theorem rfc_c32_half_zero_slice
    (K : V 256) (a b : W) :
    Diffan.ddt pairXor pairXor
      (fun p : S => split 32 32 (encrypt K (pack p)))
      (a,0#32) (0#32,b) =
    Diffan.ExactBaseJoin.count pairXor
      (forward16 (master8 K)) (Q16 (master8 K))
      (a,0#32) (0#32,b) := by
  have h :
      (fun p : S => split 32 32 (encrypt K (pack p))) =
        C (master8 K) := by
    funext p
    exact rfc_encrypt_pair_eq_C K p
  rw [h]
  exact c32_half_zero_slice (master8 K) a b

/-- The midpoint base is the actual forward-16 output;
the ONLY compatible delta there is the functional prefix
derivative from the same original x. -/
theorem midpoint_base_and_delta (keys : Fin 8 → W)
    (a : W) (x : S) :
    Diffan.ExactBaseJoin.intermediateDelta pairXor
      (forward16 keys) (a,0#32) (forward16 keys x) =
      Diffan.derivative pairXor pairXor
        (forward16 keys) (a,0#32) x := by
  simp only [Diffan.ExactBaseJoin.intermediateDelta,
    (forward16 keys).symm_apply_apply]

/-- The LEFT-zero OR RIGHT-zero condition on a MIDPOINT
is a separate optional restriction, NOT an identity
following from half-zero ENDPOINTS. -/
def midpointHasZeroHalf (mu : S) : Prop :=
  mu.1 = 0#32 ∨ mu.2 = 0#32

noncomputable def clippedCount (keys : Fin 8 → W)
    (a b : W) : Nat := by
  classical
  exact ((Finset.univ : Finset S).filter (fun u =>
    midpointHasZeroHalf
      (Diffan.ExactBaseJoin.intermediateDelta
        pairXor (forward16 keys) (a,0#32) u) ∧
    Diffan.derivative pairXor pairXor (Q16 keys)
      (Diffan.ExactBaseJoin.intermediateDelta
        pairXor (forward16 keys) (a,0#32) u) u =
        (0#32,b))).card

/-- Dropping the non-zero-half midpoint cases can only
LOSE valid differential trajectories. How much is lost
is key- and difference-dependent, not universally zero. -/
theorem clippedCount_le_actual (keys : Fin 8 → W)
    (a b : W) :
    clippedCount keys a b ≤
      Diffan.ddt pairXor pairXor (C keys)
        (a,0#32) (0#32,b) := by
  classical
  rw [c32_half_zero_slice]
  unfold clippedCount Diffan.ExactBaseJoin.count
  apply Finset.card_le_card
  intro u hu
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
  exact hu.2

end Magma.DiffanFull32SlicedJoin
