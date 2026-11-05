module
import all Init.Data.Range.Basic
public import Magma.Differential.NinePlus.NineRoundAllOneHotTrajectory

set_option maxRecDepth 8192
set_option maxHeartbeats 20000000

@[expose] public section

namespace Magma.DiffanNineRoundAllOneHotPositive

open Magma
open Magma.MultiRoundDDT
open Magma.DiffanFiveRoundUniversalSupport
open Magma.DiffanNineRoundAllOneHotTrajectory

private theorem positive_of_real_delta (n : Nat) (keys : Fin n → V 32) (a b base : FeistelState)
    (h : multiRoundDelta n keys base a = b) : 0 < xorDDT_rounds n keys a b := by
  classical
  unfold xorDDT_rounds
  apply Finset.card_pos.mpr
  refine ⟨base, ?_⟩
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using h

/-- For EVERY pair of one-hot outer differences there exists
    a real RFC 8891 master key with positive nine-round DDT.
    All 1,024 trajectory certificates were checked by the kernel. -/
theorem all_oneHot_nine_round_positive (i j : Fin 32) :
    ∃ master : V 256,
      0 < xorDDT_rounds 9
        (fun k : Fin 9 => roundKey master ⟨k.val, by omega⟩)
        (oneHotDifference i, 0#32) (0#32, oneHotDifference j) := by
  obtain ⟨master, base, hd⟩ :=
    all_oneHot_nine_round_trajectory i j
  exact ⟨master, positive_of_real_delta 9 _ _ _ _ hd⟩

end Magma.DiffanNineRoundAllOneHotPositive
