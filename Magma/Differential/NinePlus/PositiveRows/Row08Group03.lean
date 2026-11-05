module
import all Init.Data.Range.Basic
public import Magma.Differential.SevenRounds.SixSevenRoundOuterPositive
public import Magma.Differential.FiveRounds.FiveRoundUniversalSupport
set_option maxRecDepth 8192
set_option maxHeartbeats 20000000
@[expose] public section
namespace Magma.DifanNineRoundPositiveRows
open Magma
open Magma.MultiRoundDDT
open Magma.DifanFiveRoundUniversalSupport

/-- Kernel-checkable real RFC Magma trajectories: input bit 8,
    output bits 24..31. -/
theorem cell_08_24 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000271f35000b70943102682f44d97129572846d0a0a4b0bcece5080008#256) ⟨k.val, by omega⟩)
      (0x7e95116e#32, 0x187f08c6#32)
      (0x00000100#32, 0#32)
      = (0#32, 0x01000000#32) := by
  decide +kernel

theorem cell_08_25 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000a66160ff2491ee3ca61748dc9b32075a3674376e2fdb0e67d77fd007#256) ⟨k.val, by omega⟩)
      (0x6600c10a#32, 0xd8c19d76#32)
      (0x00000100#32, 0#32)
      = (0#32, 0x02000000#32) := by
  decide +kernel

theorem cell_08_26 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000ef96a31e83ae2311a2c6ae227b5764d166c90c9239c465243626140a#256) ⟨k.val, by omega⟩)
      (0x5941a22a#32, 0x95c7228e#32)
      (0x00000100#32, 0#32)
      = (0#32, 0x04000000#32) := by
  decide +kernel

theorem cell_08_27 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000007ef122fe17477bb962847de08207673b811c0aefdb8f3de8d7cabf70#256) ⟨k.val, by omega⟩)
      (0xc5cbb372#32, 0x97ff835a#32)
      (0x00000100#32, 0#32)
      = (0#32, 0x08000000#32) := by
  decide +kernel

theorem cell_08_28 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000008089e4fffcf13b495c25ba51028ff936ca9eaa748c036f78ace1e522#256) ⟨k.val, by omega⟩)
      (0xc83192df#32, 0xfa3bd3ff#32)
      (0x00000100#32, 0#32)
      = (0#32, 0x10000000#32) := by
  decide +kernel

theorem cell_08_29 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000070ada4ff462ea4401e3a81a12f537bc9af30a0357ba3e0e13f60ffff#256) ⟨k.val, by omega⟩)
      (0x953ca34a#32, 0x0f0257de#32)
      (0x00000100#32, 0#32)
      = (0#32, 0x20000000#32) := by
  decide +kernel

theorem cell_08_30 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000fa4a2099b1dd22c448d27e6c2ea9daf48b4b427db2da3d5d7a104000#256) ⟨k.val, by omega⟩)
      (0x309efac0#32, 0xa9181001#32)
      (0x00000100#32, 0#32)
      = (0#32, 0x40000000#32) := by
  decide +kernel

theorem cell_08_31 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000006b3bc4f964bf6d632424b59b811c38eb34f67bfacbe95bc32c5ba5e3#256) ⟨k.val, by omega⟩)
      (0xb7cc5a0e#32, 0xfdbb29e0#32)
      (0x00000100#32, 0#32)
      = (0#32, 0x80000000#32) := by
  decide +kernel

end Magma.DifanNineRoundPositiveRows
