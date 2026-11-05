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

/-- Kernel-checkable real RFC Magma trajectories: input bit 15,
    output bits 0..7. -/
theorem cell_15_00 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000085c29ffffed80fbd91b4358406f41f6a41577ffed75d10a376f1cf43#256) ⟨k.val, by omega⟩)
      (0xd2af7adf#32, 0x8a5d7ca5#32)
      (0x00008000#32, 0#32)
      = (0#32, 0x00000001#32) := by
  decide +kernel

theorem cell_15_01 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000fccc4fff35bfdefa3dff30165acda8006a409f1c2e06f50b6cd978b7#256) ⟨k.val, by omega⟩)
      (0x9123f615#32, 0x27920f87#32)
      (0x00008000#32, 0#32)
      = (0#32, 0x00000002#32) := by
  decide +kernel

theorem cell_15_02 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000006c6359f9e6676f4d6d3845b67c11a1222913e1aae43bf63acfaf39f9#256) ⟨k.val, by omega⟩)
      (0x6d4b6d70#32, 0x4e1c5f99#32)
      (0x00008000#32, 0#32)
      = (0#32, 0x00000004#32) := by
  decide +kernel

theorem cell_15_03 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000d3aa1fffa2deca5b132cd88375f6800e21ee5e2854482bdeb0a482c9#256) ⟨k.val, by omega⟩)
      (0x020d9bfd#32, 0x026797e8#32)
      (0x00008000#32, 0#32)
      = (0#32, 0x00000008#32) := by
  decide +kernel

theorem cell_15_04 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000eb846fff01d58987a5950ab020b1ac11773b2097a84874b11520cb70#256) ⟨k.val, by omega⟩)
      (0x2cdabc1b#32, 0x93b73625#32)
      (0x00008000#32, 0#32)
      = (0#32, 0x00000010#32) := by
  decide +kernel

theorem cell_15_05 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000ccd08000f564538f76519048a5524f09c6f34b560140cab3270110e0#256) ⟨k.val, by omega⟩)
      (0x3d647412#32, 0xad010dbd#32)
      (0x00008000#32, 0#32)
      = (0#32, 0x00000020#32) := by
  decide +kernel

theorem cell_15_06 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000028d1efff21880064afa4f3df9e5fb3f9375f105e2b274badbbf26ac7#256) ⟨k.val, by omega⟩)
      (0x90716f84#32, 0x8df870f0#32)
      (0x00008000#32, 0#32)
      = (0#32, 0x00000040#32) := by
  decide +kernel

theorem cell_15_07 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000e85863f9367753372162285e33bc2fa8044cebd80e4dc5f20d77b2d0#256) ⟨k.val, by omega⟩)
      (0x418a5999#32, 0xf0ae7251#32)
      (0x00008000#32, 0#32)
      = (0#32, 0x00000080#32) := by
  decide +kernel

end Magma.DiffanNineRoundPositiveRows
