module
import all Init.Data.Range.Basic
public import Magma.Differential.SevenRounds.SixSevenRoundOuterPositive
public import Magma.Differential.FiveRounds.FiveRoundUniversalSupport
set_option maxRecDepth 8192
set_option maxHeartbeats 20000000
@[expose] public section
namespace Magma.DiffanNineRoundPositiveRows
open Magma
open Magma.MultiRoundDDT
open Magma.DiffanFiveRoundUniversalSupport

/-- Kernel-checkable real RFC Magma trajectories: input bit 24,
    output bits 0..7. -/
theorem cell_24_00 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000e688000045148723eeb65820fc63fbb98813e2d3b664eb941632fba3#256) ⟨k.val, by omega⟩)
      (0x48e3b188#32, 0x3b189ab1#32)
      (0x01000000#32, 0#32)
      = (0#32, 0x00000001#32) := by
  decide +kernel

theorem cell_24_01 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000ccf45fff04206e3860e039b2c1fc5f406c535aa5bea65c5d80211167#256) ⟨k.val, by omega⟩)
      (0x90a5550e#32, 0xa3068069#32)
      (0x01000000#32, 0#32)
      = (0#32, 0x00000002#32) := by
  decide +kernel

theorem cell_24_02 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000002c0000092f4e725a96f3decad214f770a8fd661e131c1b4e10a505d#256) ⟨k.val, by omega⟩)
      (0x263f0728#32, 0xe6215578#32)
      (0x01000000#32, 0#32)
      = (0#32, 0x00000004#32) := by
  decide +kernel

theorem cell_24_03 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000000b6bff41e9e06a1f6c901b4180474fe03f48b78961535750c92e830a#256) ⟨k.val, by omega⟩)
      (0xad43981e#32, 0x09f01a18#32)
      (0x01000000#32, 0#32)
      = (0#32, 0x00000008#32) := by
  decide +kernel

theorem cell_24_04 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000003b4b0c67b2058e799de780d6e04a2ccd611b932028764a52624860e2#256) ⟨k.val, by omega⟩)
      (0x97505498#32, 0xb62d8c82#32)
      (0x01000000#32, 0#32)
      = (0#32, 0x00000010#32) := by
  decide +kernel

theorem cell_24_05 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000770000002935cfefe2fa900c34ebde6c979e78c0382aec99db423b90#256) ⟨k.val, by omega⟩)
      (0x43d69556#32, 0xeacfb7ef#32)
      (0x01000000#32, 0#32)
      = (0#32, 0x00000020#32) := by
  decide +kernel

theorem cell_24_06 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000001ade8bfcbf3b82651e5980080b62ea4ee0db6f93b7b39928f06bd070#256) ⟨k.val, by omega⟩)
      (0xabdfed62#32, 0x7b7c6f4d#32)
      (0x01000000#32, 0#32)
      = (0#32, 0x00000040#32) := by
  decide +kernel

theorem cell_24_07 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000001effffff23e51558485023ce019f5feaf83b189c562502ffdc9bab6f#256) ⟨k.val, by omega⟩)
      (0x995d1630#32, 0x7be133b0#32)
      (0x01000000#32, 0#32)
      = (0#32, 0x00000080#32) := by
  decide +kernel

end Magma.DiffanNineRoundPositiveRows
