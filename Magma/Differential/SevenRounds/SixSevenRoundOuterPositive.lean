module
import all Init.Data.Range.Basic
public import Magma.Differential.NinePlus.SparsePositiveWitnesses

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

@[expose] public section

/-! Kernel-checked positive 6- and 7-round outer differences.
    Concrete first-round schedule of RFC 8891 is checked in Lean.
    CNF/solver witnesses are not trusted in the Lean proof. -/

namespace Magma.DiffanSixSevenRoundOuterPositive

open Magma
open Magma.MultiRoundDDT

private abbrev Word :=
  V 32

/-- RFC 8891 master key found by SAT, independently replayed. -/
def sixMaster : V 256 := 0x018bd8cf58372183f53a7f9dbbc23a3f81aa96e1c93d04660000000000000000#256

def sixKeys : Fin 6 → Word :=
  ![0x018bd8cf#32, 0x58372183#32, 0xf53a7f9d#32, 0xbbc23a3f#32, 0x81aa96e1#32, 0xc93d0466#32]

theorem sixKeys_from_master :
    sixKeys = (fun i : Fin 6 => roundKey sixMaster ⟨i.val, by omega⟩) := by
  funext i
  fin_cases i <;> decide +kernel

private theorem six_base_step_0 :
    G (0x018bd8cf#32) (0xae933ecc#32, 0x036447e1#32) = (0x036447e1#32, 0x97c8de7c#32) := by
  decide +kernel

private theorem six_base_step_1 :
    G (0x58372183#32) (0x036447e1#32, 0x97c8de7c#32) = (0x97c8de7c#32, 0x66e3ca59#32) := by
  decide +kernel

private theorem six_base_step_2 :
    G (0xf53a7f9d#32) (0x97c8de7c#32, 0x66e3ca59#32) = (0x66e3ca59#32, 0x01470492#32) := by
  decide +kernel

private theorem six_base_step_3 :
    G (0xbbc23a3f#32) (0x66e3ca59#32, 0x01470492#32) = (0x01470492#32, 0xae55690b#32) := by
  decide +kernel

private theorem six_base_step_4 :
    G (0x81aa96e1#32) (0x01470492#32, 0xae55690b#32) = (0xae55690b#32, 0x64c703aa#32) := by
  decide +kernel

private theorem six_base_step_5 :
    G (0xc93d0466#32) (0xae55690b#32, 0x64c703aa#32) = (0x64c703aa#32, 0x68210e11#32) := by
  decide +kernel

private theorem six_base_full :
    iterateG 6 sixKeys (0xae933ecc#32, 0x036447e1#32) = (0x64c703aa#32, 0x68210e11#32) := by
  change
    G (0xc93d0466#32)
        (G (0x81aa96e1#32)
          (G (0xbbc23a3f#32)
            (G (0xf53a7f9d#32)
              (G (0x58372183#32) (G (0x018bd8cf#32) ((0xae933ecc#32, 0x036447e1#32))))))) =
      (0x64c703aa#32, 0x68210e11#32)
  rw [six_base_step_0, six_base_step_1, six_base_step_2, six_base_step_3, six_base_step_4,
    six_base_step_5]

private theorem six_altered_step_0 :
    G (0x018bd8cf#32) (0xae933ecd#32, 0x036447e1#32) = (0x036447e1#32, 0x97c8de7d#32) := by
  decide +kernel

private theorem six_altered_step_1 :
    G (0x58372183#32) (0x036447e1#32, 0x97c8de7d#32) = (0x97c8de7d#32, 0xbd3f26a3#32) := by
  decide +kernel

private theorem six_altered_step_2 :
    G (0xf53a7f9d#32) (0x97c8de7d#32, 0xbd3f26a3#32) = (0xbd3f26a3#32, 0xda9c3d68#32) := by
  decide +kernel

private theorem six_altered_step_3 :
    G (0xbbc23a3f#32) (0xbd3f26a3#32, 0xda9c3d68#32) = (0xda9c3d68#32, 0xae55692a#32) := by
  decide +kernel

private theorem six_altered_step_4 :
    G (0x81aa96e1#32) (0xda9c3d68#32, 0xae55692a#32) = (0xae55692a#32, 0x64c703aa#32) := by
  decide +kernel

private theorem six_altered_step_5 :
    G (0xc93d0466#32) (0xae55692a#32, 0x64c703aa#32) = (0x64c703aa#32, 0x68210e30#32) := by
  decide +kernel

private theorem six_altered_full :
    iterateG 6 sixKeys (0xae933ecd#32, 0x036447e1#32) = (0x64c703aa#32, 0x68210e30#32) := by
  change
    G (0xc93d0466#32)
        (G (0x81aa96e1#32)
          (G (0xbbc23a3f#32)
            (G (0xf53a7f9d#32)
              (G (0x58372183#32) (G (0x018bd8cf#32) ((0xae933ecd#32, 0x036447e1#32))))))) =
      (0x64c703aa#32, 0x68210e30#32)
  rw [six_altered_step_0, six_altered_step_1, six_altered_step_2, six_altered_step_3,
    six_altered_step_4, six_altered_step_5]

theorem sixRound_outer_trajectory :
    multiRoundDelta 6 sixKeys (0xae933ecc#32, 0x036447e1#32) (0x00000001#32, 0x00000000#32) =
      (0x00000000#32, 0x00000021#32) := by
  unfold multiRoundDelta
  have hx :
    stateXor (0xae933ecc#32, 0x036447e1#32) (0x00000001#32, 0x00000000#32) =
      (0xae933ecd#32, 0x036447e1#32) := by
    decide +kernel
  rw [hx, six_altered_full, six_base_full]
  decide +kernel

/-- RFC 8891 master key found by SAT, independently replayed. -/
def sevenMaster : V 256 := 0x6c45bdfc40cc77c3b54831837c7904edfce7c87196927ba395bbe19300000000#256

def sevenKeys : Fin 7 → Word :=
  ![0x6c45bdfc#32, 0x40cc77c3#32, 0xb5483183#32, 0x7c7904ed#32, 0xfce7c871#32, 0x96927ba3#32,
    0x95bbe193#32]

theorem sevenKeys_from_master :
    sevenKeys = (fun i : Fin 7 => roundKey sevenMaster ⟨i.val, by omega⟩) := by
  funext i
  fin_cases i <;> decide +kernel

private theorem seven_base_step_0 :
    G (0x6c45bdfc#32) (0x6456d8fe#32, 0x93bd4418#32) = (0x93bd4418#32, 0xb27a883c#32) := by
  decide +kernel

private theorem seven_base_step_1 :
    G (0x40cc77c3#32) (0x93bd4418#32, 0xb27a883c#32) = (0xb27a883c#32, 0x263acd34#32) := by
  decide +kernel

private theorem seven_base_step_2 :
    G (0xb5483183#32) (0xb27a883c#32, 0x263acd34#32) = (0x263acd34#32, 0x1fc94639#32) := by
  decide +kernel

private theorem seven_base_step_3 :
    G (0x7c7904ed#32) (0x263acd34#32, 0x1fc94639#32) = (0x1fc94639#32, 0x889b92d8#32) := by
  decide +kernel

private theorem seven_base_step_4 :
    G (0xfce7c871#32) (0x1fc94639#32, 0x889b92d8#32) = (0x889b92d8#32, 0xcded8474#32) := by
  decide +kernel

private theorem seven_base_step_5 :
    G (0x96927ba3#32) (0x889b92d8#32, 0xcded8474#32) = (0xcded8474#32, 0x36c7deed#32) := by
  decide +kernel

private theorem seven_base_step_6 :
    G (0x95bbe193#32) (0xcded8474#32, 0x36c7deed#32) = (0x36c7deed#32, 0x1c356099#32) := by
  decide +kernel

private theorem seven_base_full :
    iterateG 7 sevenKeys (0x6456d8fe#32, 0x93bd4418#32) = (0x36c7deed#32, 0x1c356099#32) := by
  change
    G (0x95bbe193#32)
        (G (0x96927ba3#32)
          (G (0xfce7c871#32)
            (G (0x7c7904ed#32)
              (G (0xb5483183#32)
                (G (0x40cc77c3#32) (G (0x6c45bdfc#32) ((0x6456d8fe#32, 0x93bd4418#32)))))))) =
      (0x36c7deed#32, 0x1c356099#32)
  rw [seven_base_step_0, seven_base_step_1, seven_base_step_2, seven_base_step_3, seven_base_step_4,
    seven_base_step_5, seven_base_step_6]

private theorem seven_altered_step_0 :
    G (0x6c45bdfc#32) (0x6456d8ff#32, 0x93bd4418#32) = (0x93bd4418#32, 0xb27a883d#32) := by
  decide +kernel

private theorem seven_altered_step_1 :
    G (0x40cc77c3#32) (0x93bd4418#32, 0xb27a883d#32) = (0xb27a883d#32, 0x7de62534#32) := by
  decide +kernel

private theorem seven_altered_step_2 :
    G (0xb5483183#32) (0xb27a883d#32, 0x7de62534#32) = (0x7de62534#32, 0x20294692#32) := by
  decide +kernel

private theorem seven_altered_step_3 :
    G (0x7c7904ed#32) (0x7de62534#32, 0x20294692#32) = (0x20294692#32, 0x53402ad8#32) := by
  decide +kernel

private theorem seven_altered_step_4 :
    G (0xfce7c871#32) (0x20294692#32, 0x53402ad8#32) = (0x53402ad8#32, 0xcded8455#32) := by
  decide +kernel

private theorem seven_altered_step_5 :
    G (0x96927ba3#32) (0x53402ad8#32, 0xcded8455#32) = (0xcded8455#32, 0x36c7deed#32) := by
  decide +kernel

private theorem seven_altered_step_6 :
    G (0x95bbe193#32) (0xcded8455#32, 0x36c7deed#32) = (0x36c7deed#32, 0x1c3560b8#32) := by
  decide +kernel

private theorem seven_altered_full :
    iterateG 7 sevenKeys (0x6456d8ff#32, 0x93bd4418#32) = (0x36c7deed#32, 0x1c3560b8#32) := by
  change
    G (0x95bbe193#32)
        (G (0x96927ba3#32)
          (G (0xfce7c871#32)
            (G (0x7c7904ed#32)
              (G (0xb5483183#32)
                (G (0x40cc77c3#32) (G (0x6c45bdfc#32) ((0x6456d8ff#32, 0x93bd4418#32)))))))) =
      (0x36c7deed#32, 0x1c3560b8#32)
  rw [seven_altered_step_0, seven_altered_step_1, seven_altered_step_2, seven_altered_step_3,
    seven_altered_step_4, seven_altered_step_5, seven_altered_step_6]

theorem sevenRound_outer_trajectory :
    multiRoundDelta 7 sevenKeys (0x6456d8fe#32, 0x93bd4418#32) (0x00000001#32, 0x00000000#32) =
      (0x00000000#32, 0x00000021#32) := by
  unfold multiRoundDelta
  have hx :
    stateXor (0x6456d8fe#32, 0x93bd4418#32) (0x00000001#32, 0x00000000#32) =
      (0x6456d8ff#32, 0x93bd4418#32) := by
    decide +kernel
  rw [hx, seven_altered_full, seven_base_full]
  decide +kernel

/-- Concrete n-round derivative is a positive DDT cell; no DDT enumeration. -/
private theorem pos_of_trajectory (n : Nat) (keys : Fin n → Word)
    (a b base : FeistelState)
    (h : multiRoundDelta n keys base a = b) :
    0 < xorDDT_rounds n keys a b := by
  classical
  unfold xorDDT_rounds
  apply Finset.card_pos.mpr
  refine ⟨base, ?_⟩
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using h

theorem sixRound_outer_positive :
    0 < xorDDT_rounds 6 sixKeys (0x00000001#32, 0#32) (0#32, 0x00000021#32) :=
  pos_of_trajectory 6 sixKeys (0x00000001#32, 0#32) (0#32, 0x00000021#32) _
    sixRound_outer_trajectory

/-- Positive with an actual RFC 8891 master key schedule. -/
theorem sixRound_master_positive :
    0 < xorDDT_rounds 6
      (fun i : Fin 6 => roundKey sixMaster ⟨i.val, by omega⟩)
      (0x00000001#32, 0#32) (0#32, 0x00000021#32) := by
  rw [← sixKeys_from_master]
  exact sixRound_outer_positive

theorem sevenRound_outer_positive :
    0 < xorDDT_rounds 7 sevenKeys (0x00000001#32, 0#32) (0#32, 0x00000021#32) :=
  pos_of_trajectory 7 sevenKeys (0x00000001#32, 0#32) (0#32, 0x00000021#32) _
    sevenRound_outer_trajectory

/-- Positive with an actual RFC 8891 master key schedule. -/
theorem sevenRound_master_positive :
    0 < xorDDT_rounds 7
      (fun i : Fin 7 => roundKey sevenMaster ⟨i.val, by omega⟩)
      (0x00000001#32, 0#32) (0#32, 0x00000021#32) := by
  rw [← sevenKeys_from_master]
  exact sevenRound_outer_positive

end Magma.DiffanSixSevenRoundOuterPositive
