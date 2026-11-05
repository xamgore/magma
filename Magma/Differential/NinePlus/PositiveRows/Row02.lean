module
import all Init.Data.Range.Basic
public import Magma.Differential.NinePlus.PositiveRows.Row02Group00
public import Magma.Differential.NinePlus.PositiveRows.Row02Group01
public import Magma.Differential.NinePlus.PositiveRows.Row02Group02
public import Magma.Differential.NinePlus.PositiveRows.Row02Group03
@[expose] public section
namespace Magma.DifanNineRoundPositiveRows
open Magma
open Magma.MultiRoundDDT
open Magma.DifanFiveRoundUniversalSupport

/-- Every output bit j is reachable for input bit 2. -/
theorem row02 (j : Fin 32) :
    ∃ master : V 256, ∃ base : FeistelState,
      multiRoundDelta 9
        (fun k : Fin 9 => roundKey master ⟨k.val, by omega⟩)
        base (oneHotDifference (2 : Fin 32), 0#32)
        = (0#32, oneHotDifference j) := by
  fin_cases j
  · exact ⟨0x00000000a8f0ef0da0b4908fc4f05570c0c25cab8423e8842bca9e7086bf2c1b#256,
      (0x3c672e66#32, 0x32ac77eb#32), by simpa [oneHotDifference] using cell_02_00⟩
  · exact ⟨0x00000000145fa3b4aa755a15e99b0293065f8829bf775eab2fee15897067ec96#256,
      (0x83afa9c4#32, 0xe64629f8#32), by simpa [oneHotDifference] using cell_02_01⟩
  · exact ⟨0x00000000c6ff1e13dab5b17eeef73437d95b8b9e0cd654e64c20808be1231efc#256,
      (0x6316bec6#32, 0x23372876#32), by simpa [oneHotDifference] using cell_02_02⟩
  · exact ⟨0x00000000f13ca39f8917434697dc22237a42de71d49328ff79ee567f9b7445eb#256,
      (0xe4b12962#32, 0xab1b98a8#32), by simpa [oneHotDifference] using cell_02_03⟩
  · exact ⟨0x00000000ccffb6c6223773f88fd03c4e07702f7a00de6c7a1ad78dfbe339cd77#256,
      (0x7f2dde66#32, 0x2a69a0c3#32), by simpa [oneHotDifference] using cell_02_04⟩
  · exact ⟨0x00000000bdce20fa67c7a706a592c19e3708d97bb226ff3c2e3c335bdc8a80a0#256,
      (0xa67627c1#32, 0x000813fe#32), by simpa [oneHotDifference] using cell_02_05⟩
  · exact ⟨0x00000000a6406ea70f37f9a3526b8133b75cb127a1c01a687df106746119ba30#256,
      (0x73bf0143#32, 0x4e3d9f83#32), by simpa [oneHotDifference] using cell_02_06⟩
  · exact ⟨0x00000000d346e045aa6eed9c41c1ef86a2dde8958bede40b3700a305971a5fb2#256,
      (0x5a57bb4b#32, 0xc190f7d1#32), by simpa [oneHotDifference] using cell_02_07⟩
  · exact ⟨0x00000000e0e538967dfd7017c3434d686b570182404418f2aa34d7f1e4519900#256,
      (0x674d11f0#32, 0x3e50e6f4#32), by simpa [oneHotDifference] using cell_02_08⟩
  · exact ⟨0x00000000dce109f6d5c30d1f19a099680e5c9985a591916af371637d6145f300#256,
      (0x7c155016#32, 0xdec0d9b1#32), by simpa [oneHotDifference] using cell_02_09⟩
  · exact ⟨0x0000000035be5e943f48782cc60b4be742fdd3a7f17fc1a279256a45891613b0#256,
      (0x762623f9#32, 0x52a71cfc#32), by simpa [oneHotDifference] using cell_02_10⟩
  · exact ⟨0x00000000870151ac1f57f8c889f6d2f5b9afb756867def5435fa29fbaf528efc#256,
      (0x6c92c0cf#32, 0x3ed3071a#32), by simpa [oneHotDifference] using cell_02_11⟩
  · exact ⟨0x000000001a6bd47b83472d2231e62919f8d05c7cae6b7b04bd618849c13f508b#256,
      (0x9ae2553f#32, 0x3fa7d87e#32), by simpa [oneHotDifference] using cell_02_12⟩
  · exact ⟨0x0000000068ce9095f89f2718cfc9cb3ec34a8b229d26d0dfd4b4b32c6ff663ab#256,
      (0x543e2303#32, 0x6c7d8997#32), by simpa [oneHotDifference] using cell_02_13⟩
  · exact ⟨0x0000000048199e44157e85e4653c07b4aaeb9ddf4875e2f1e0dee85f2df3afe0#256,
      (0xec4ff1a0#32, 0x4e7c8033#32), by simpa [oneHotDifference] using cell_02_14⟩
  · exact ⟨0x0000000079c8cf5d90dca01ad2fa434564a0a73c1b839e502e2d03dee5327cff#256,
      (0x47dd1e5e#32, 0x380f37a5#32), by simpa [oneHotDifference] using cell_02_15⟩
  · exact ⟨0x00000000289ba7a488943f699ab0f910b79ff4c1ce27fe01ae7bd976095b1c0f#256,
      (0x5d57cba8#32, 0x11fa5eb3#32), by simpa [oneHotDifference] using cell_02_16⟩
  · exact ⟨0x00000000ae5f9ae3271473d5ef635f5e479eaff8cf53707c113a07c3b7d23010#256,
      (0xb36edf58#32, 0x809a7adb#32), by simpa [oneHotDifference] using cell_02_17⟩
  · exact ⟨0x00000000bb0afee530f85ea7d6c16124e73aefefa8e075cb4e4666f6c02b2000#256,
      (0xe8510db5#32, 0xc38beb1f#32), by simpa [oneHotDifference] using cell_02_18⟩
  · exact ⟨0x000000001dff061d014bc41fced057c7d05f12a7b51a66f03ae6fbe959069100#256,
      (0xe7e6d065#32, 0xe7f4681a#32), by simpa [oneHotDifference] using cell_02_19⟩
  · exact ⟨0x000000009507e783477084e9f6defa64e9c637493789fb010b46619ed45cdf1c#256,
      (0x5a7538dd#32, 0x09e85751#32), by simpa [oneHotDifference] using cell_02_20⟩
  · exact ⟨0x000000007fee08254135ae4d203265e3107fa49f0e319cd50ce33062bb3741a0#256,
      (0x85516bea#32, 0x64b2b68d#32), by simpa [oneHotDifference] using cell_02_21⟩
  · exact ⟨0x000000006a1df74ad3bd71155f649a1fdfd4e0a93ab0cf698d46ab6538bc1000#256,
      (0xbb7dede3#32, 0xadb8aaf0#32), by simpa [oneHotDifference] using cell_02_22⟩
  · exact ⟨0x000000005bece27e6bbbc8f12d4e6ccba9c669068effd9b6e18ac18c63a53732#256,
      (0x77585744#32, 0x50f3527f#32), by simpa [oneHotDifference] using cell_02_23⟩
  · exact ⟨0x000000000adb24c3a12aacde3d729b81b70d97269f7965ddb2cf94b13537fcf8#256,
      (0x99618734#32, 0x66d11356#32), by simpa [oneHotDifference] using cell_02_24⟩
  · exact ⟨0x000000006ec6219234e41a600d28ed507300be826ce633f6a4e63316bc1c00e0#256,
      (0x3b0a9264#32, 0x66299f07#32), by simpa [oneHotDifference] using cell_02_25⟩
  · exact ⟨0x000000007a353545eaf3ab50d32e2e2b342174fd92a063f93b3e596f292c626c#256,
      (0xcb088f1d#32, 0xe9aab3a9#32), by simpa [oneHotDifference] using cell_02_26⟩
  · exact ⟨0x00000000e16717e2ce0222a1ef0d37792fdf449e7c935aeca4355d76c3860f89#256,
      (0x1ba61f65#32, 0x28685ad8#32), by simpa [oneHotDifference] using cell_02_27⟩
  · exact ⟨0x00000000c1abfcd4461cc9ce49b490747f7e7e6fe6c1fc0c62862dca5d71778d#256,
      (0x34335dba#32, 0x32ab0c96#32), by simpa [oneHotDifference] using cell_02_28⟩
  · exact ⟨0x00000000c75497350973540a0e188a75b44b5f511e66aeb653126b31008fffc0#256,
      (0x2b738078#32, 0x045ef08a#32), by simpa [oneHotDifference] using cell_02_29⟩
  · exact ⟨0x00000000023df0ab1f2454c8414a84ef8546198ddb0d58237e61d53df6bc6f7d#256,
      (0x1ec93ee1#32, 0x74ed7902#32), by simpa [oneHotDifference] using cell_02_30⟩
  · exact ⟨0x000000005a81d3dbb88714728359c549eac81f7c241f5ac3378c522f84295ade#256,
      (0x8a7ba86d#32, 0x651cdfcc#32), by simpa [oneHotDifference] using cell_02_31⟩

end Magma.DifanNineRoundPositiveRows
