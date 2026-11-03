module
import all Init.Data.Range.Basic
public import Magma.Diffan.SixSevenRoundOuterPositive
public import Magma.Diffan.FiveRoundUniversalSupport
set_option maxRecDepth 8192
set_option maxHeartbeats 20000000
@[expose] public section
namespace Magma.DiffanNineRoundPositiveRows
open Magma
open Magma.MultiRoundDDT
open Magma.DiffanFiveRoundUniversalSupport

/-- Kernel-checkable real RFC Magma trajectories: input bit 13,
    output bits 24..31. -/
theorem cell_13_24 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000005c878fff80fb36640b3b80efabb275342256c53f48834946a0091d0d#256) ⟨k.val, by omega⟩)
      (0x5981a77d#32, 0xfd1cb538#32)
      (0x00002000#32, 0#32)
      = (0#32, 0x01000000#32) := by
  decide +kernel

theorem cell_13_25 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000002cc70fff61282c18729e34430227ce6fac808ffae85734ab96ffff81#256) ⟨k.val, by omega⟩)
      (0x4592a8fa#32, 0xf31642a8#32)
      (0x00002000#32, 0#32)
      = (0#32, 0x02000000#32) := by
  decide +kernel

theorem cell_13_26 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000009b1aa1bfd49b99bcb396ef4a830ea38c3856d3183eb765faf521f0a2#256) ⟨k.val, by omega⟩)
      (0xf3e0562a#32, 0x12a3df5f#32)
      (0x00002000#32, 0#32)
      = (0#32, 0x04000000#32) := by
  decide +kernel

theorem cell_13_27 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000002544afffd0e08fd822002a2683c7073ba92c1554960efcccd39e7d4f#256) ⟨k.val, by omega⟩)
      (0xe8bb42ef#32, 0x1ae85fef#32)
      (0x00002000#32, 0#32)
      = (0#32, 0x08000000#32) := by
  decide +kernel

theorem cell_13_28 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000880edfffb3c6f122e023d33e33eb167c4e5e2817886aa3fd9f97f8ff#256) ⟨k.val, by omega⟩)
      (0xb560c859#32, 0xef8f5f6e#32)
      (0x00002000#32, 0#32)
      = (0#32, 0x10000000#32) := by
  decide +kernel

theorem cell_13_29 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000005f262ffe8aa910490eb7a97d452a83d44e0183bbd7d01cf4d0179009#256) ⟨k.val, by omega⟩)
      (0x622ad458#32, 0xc57cf80d#32)
      (0x00002000#32, 0#32)
      = (0#32, 0x20000000#32) := by
  decide +kernel

theorem cell_13_30 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000003ebad000889628f6a1f84f6654570a31a46a177bfda452d050001800#256) ⟨k.val, by omega⟩)
      (0xd5d2b28f#32, 0x9768e4f5#32)
      (0x00002000#32, 0#32)
      = (0#32, 0x40000000#32) := by
  decide +kernel

theorem cell_13_31 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000082befff46deb4b31aea2a9ed4fb05fb5ec7d0f21ed61e13a54c76fe#256) ⟨k.val, by omega⟩)
      (0x4c9a871d#32, 0xf851addf#32)
      (0x00002000#32, 0#32)
      = (0#32, 0x80000000#32) := by
  decide +kernel

end Magma.DiffanNineRoundPositiveRows
