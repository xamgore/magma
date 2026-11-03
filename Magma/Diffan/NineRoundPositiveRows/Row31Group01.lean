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

/-- Kernel-checkable real RFC Magma trajectories: input bit 31,
    output bits 8..15. -/
theorem cell_31_08 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000003a16eb64cb854cb086b5b1bc8be8e9633d9c8df1cf1814434feabd00#256) ⟨k.val, by omega⟩)
      (0x5420de15#32, 0x05d6542f#32)
      (0x80000000#32, 0#32)
      = (0#32, 0x00000100#32) := by
  decide +kernel

theorem cell_31_09 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000ee9b83ecf21875133ed7f8b4cf1573ba528fda55237eaaaf983801cf#256) ⟨k.val, by omega⟩)
      (0x9806a724#32, 0xcd61762d#32)
      (0x80000000#32, 0#32)
      = (0#32, 0x00000200#32) := by
  decide +kernel

theorem cell_31_10 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000380f6ef34af0caa088ccdb966363ea2382e0640cb0563ab548266d00#256) ⟨k.val, by omega⟩)
      (0x25e4e74c#32, 0xddd351c2#32)
      (0x80000000#32, 0#32)
      = (0#32, 0x00000400#32) := by
  decide +kernel

theorem cell_31_11 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000f69566907c5e8440225901c7fe554a88a794be4288bb4e1c313b3cd0#256) ⟨k.val, by omega⟩)
      (0xd9d0988b#32, 0xc01fe23b#32)
      (0x80000000#32, 0#32)
      = (0#32, 0x00000800#32) := by
  decide +kernel

theorem cell_31_12 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000f789a9a5b4f805b548bbeccd1af5666d0e0d8d2d6b5c043d1fd9c800#256) ⟨k.val, by omega⟩)
      (0x5f1c3ef2#32, 0x8d332156#32)
      (0x80000000#32, 0#32)
      = (0#32, 0x00001000#32) := by
  decide +kernel

theorem cell_31_13 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000007305e00b824bff80f9690ef2f189243cca6c4353bbd953394322d000#256) ⟨k.val, by omega⟩)
      (0xe043f935#32, 0xf03ca336#32)
      (0x80000000#32, 0#32)
      = (0#32, 0x00002000#32) := by
  decide +kernel

theorem cell_31_14 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000d63d7b4bb87c71a852ec1a111d13144ecb504b0bd61c1e18b95e4000#256) ⟨k.val, by omega⟩)
      (0xbea47cc0#32, 0x465fdc0b#32)
      (0x80000000#32, 0#32)
      = (0#32, 0x00004000#32) := by
  decide +kernel

theorem cell_31_15 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000e0cc6b548704e467a93c9afe1d428f76830643f2e4223f422cd9b800#256) ⟨k.val, by omega⟩)
      (0x22fff6c8#32, 0x89a7ff19#32)
      (0x80000000#32, 0#32)
      = (0#32, 0x00008000#32) := by
  decide +kernel

end Magma.DiffanNineRoundPositiveRows
