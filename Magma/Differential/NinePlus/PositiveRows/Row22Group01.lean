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

/-- Kernel-checkable real RFC Magma trajectories: input bit 22,
    output bits 8..15. -/
theorem cell_22_08 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000225c2ffeb563313acb69f7623519be6a2e6ee87c77b1de32843924ff#256) ⟨k.val, by omega⟩)
      (0xbf577d1d#32, 0x5f73b64b#32)
      (0x00400000#32, 0#32)
      = (0#32, 0x00000100#32) := by
  decide +kernel

theorem cell_22_09 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000002cbf0ffff12f451bd6da63397dcfecc1190b7c0a02b7748a9785c5b8#256) ⟨k.val, by omega⟩)
      (0x71122db0#32, 0x459f5302#32)
      (0x00400000#32, 0#32)
      = (0#32, 0x00000200#32) := by
  decide +kernel

theorem cell_22_10 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000075deffffa47f7bc9feab6193163373f6204d48b0763fd9c35f0918f3#256) ⟨k.val, by omega⟩)
      (0xbec31e5a#32, 0xe337642b#32)
      (0x00400000#32, 0#32)
      = (0#32, 0x00000400#32) := by
  decide +kernel

theorem cell_22_11 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000b53000004096eddbb80adcad6a4ea3e0ce84a98ee0adb33246489500#256) ⟨k.val, by omega⟩)
      (0xc3ba3613#32, 0x405c22d5#32)
      (0x00400000#32, 0#32)
      = (0#32, 0x00000800#32) := by
  decide +kernel

theorem cell_22_12 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000000fcfffff822724e2534cec33dafff88d7da7d890ea15a612130629ff#256) ⟨k.val, by omega⟩)
      (0x6df8ac9f#32, 0x568cfcdb#32)
      (0x00400000#32, 0#32)
      = (0#32, 0x00001000#32) := by
  decide +kernel

theorem cell_22_13 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000aba59f4d73ec9ec037675f90a00ff895f0133e9f6156a9c8f6b41c00#256) ⟨k.val, by omega⟩)
      (0xe357e0a0#32, 0x498bd5ff#32)
      (0x00400000#32, 0#32)
      = (0#32, 0x00002000#32) := by
  decide +kernel

theorem cell_22_14 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000025ad26f9389393ec6d60b69561027540b18407546ee164c16b184900#256) ⟨k.val, by omega⟩)
      (0x7c9aca34#32, 0xbfbf429e#32)
      (0x00400000#32, 0#32)
      = (0#32, 0x00004000#32) := by
  decide +kernel

theorem cell_22_15 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000060b8d54ee1dcb05c4ba4b6d3182ae234e64ef57fec69530c9ec67570#256) ⟨k.val, by omega⟩)
      (0x42cb8490#32, 0xdfdc86d1#32)
      (0x00400000#32, 0#32)
      = (0#32, 0x00008000#32) := by
  decide +kernel

end Magma.DiffanNineRoundPositiveRows
