module
import all Init.Data.Range.Basic
public import Magma.Diffan.NineRoundPositiveRows.Row06Group00
public import Magma.Diffan.NineRoundPositiveRows.Row06Group01
public import Magma.Diffan.NineRoundPositiveRows.Row06Group02
public import Magma.Diffan.NineRoundPositiveRows.Row06Group03
@[expose] public section
namespace Magma.DiffanNineRoundPositiveRows
open Magma
open Magma.MultiRoundDDT
open Magma.DiffanFiveRoundUniversalSupport

/-- Every output bit j is reachable for input bit 6. -/
theorem row06 (j : Fin 32) :
    ∃ master : V 256, ∃ base : FeistelState,
      multiRoundDelta 9
        (fun k : Fin 9 => roundKey master ⟨k.val, by omega⟩)
        base (oneHotDifference (6 : Fin 32), 0#32)
        = (0#32, oneHotDifference j) := by
  fin_cases j
  · exact ⟨0x0000000082bf6fc1c2499e2c53ce87556619c6df6db7d252a0b48d9f552da667#256,
      (0x4c59c728#32, 0x210d2124#32), by simpa [oneHotDifference] using cell_06_00⟩
  · exact ⟨0x00000000923ede3002b62b9e675b7fda1bbad25cdfc98535707590540969a6c2#256,
      (0x5c49433b#32, 0x5d72c9e0#32), by simpa [oneHotDifference] using cell_06_01⟩
  · exact ⟨0x0000000089d0222f46c60d5ee94517301d5f1954ebd26d8b9319842d00bdbe49#256,
      (0x08a4fec2#32, 0xb2ba4901#32), by simpa [oneHotDifference] using cell_06_02⟩
  · exact ⟨0x00000000f9054fc0015cdac6c2eed5336d898d49fe044de65993115190d48f25#256,
      (0xb067bcb0#32, 0xc67a315f#32), by simpa [oneHotDifference] using cell_06_03⟩
  · exact ⟨0x000000000afe56d6c18cc62004ded6061bb4a81c2fe9737929533906684b0268#256,
      (0xf92cc76e#32, 0xd9ec125a#32), by simpa [oneHotDifference] using cell_06_04⟩
  · exact ⟨0x00000000f20ccdbfa3d3bfdccb19a1adcec42bf43c636b096271b877325e8b58#256,
      (0xcb2f2148#32, 0xb6d08013#32), by simpa [oneHotDifference] using cell_06_05⟩
  · exact ⟨0x00000000fcf6beb45d431f3d43ad95e11bdb59c309a0b7e6ce7e27423d5408cf#256,
      (0x6f77503b#32, 0xfa459173#32), by simpa [oneHotDifference] using cell_06_06⟩
  · exact ⟨0x00000000c2d4cdc00808db681f1015eae7fe00fc0d4ffcfa20116d4cc6680e74#256,
      (0x408304c7#32, 0x3de042e2#32), by simpa [oneHotDifference] using cell_06_07⟩
  · exact ⟨0x00000000a6684d8fde6927eb531ad13707e38476706811280e4ac9fe6674213f#256,
      (0x30634cee#32, 0x3e2be84e#32), by simpa [oneHotDifference] using cell_06_08⟩
  · exact ⟨0x0000000012fdd88eb58e46fe6c861395e284071793e8f142085476667b384d80#256,
      (0x2a359e03#32, 0xf15eda4b#32), by simpa [oneHotDifference] using cell_06_09⟩
  · exact ⟨0x000000007e2b69cf488906ac787088610e6306259168ea45099bbc75b2a530ff#256,
      (0x5a2269a7#32, 0x9324c8de#32), by simpa [oneHotDifference] using cell_06_10⟩
  · exact ⟨0x000000009d46bd40227ba03ccf644e122c781041bcc16091966fb21731398b20#256,
      (0x8f264ff5#32, 0xa9c0f19f#32), by simpa [oneHotDifference] using cell_06_11⟩
  · exact ⟨0x00000000833233df1ffdaf34afd67d5c991c27313b60441dbd92145707073370#256,
      (0x558b4c4c#32, 0x405f03dc#32), by simpa [oneHotDifference] using cell_06_12⟩
  · exact ⟨0x000000004f31151cef7901473df45dc48007dc33ea4c49b5fce4d5ea65f93000#256,
      (0x70b1a958#32, 0x17cf9599#32), by simpa [oneHotDifference] using cell_06_13⟩
  · exact ⟨0x00000000c9ec095ff8f29b9ab6d833f89de59297d8780c0f071b915c51eb5fe0#256,
      (0xb72f5e90#32, 0x45e32a45#32), by simpa [oneHotDifference] using cell_06_14⟩
  · exact ⟨0x00000000485f3ec4970d0a52ac7278028fb014c7e5ce76ab4459058a2e726190#256,
      (0x319ac650#32, 0x22877aac#32), by simpa [oneHotDifference] using cell_06_15⟩
  · exact ⟨0x00000000eb9dd32feafa7ac0ee36d524bf7f5f8d3f063e180dd86d176ae09ffe#256,
      (0xd5bd3aa1#32, 0xdf9a8093#32), by simpa [oneHotDifference] using cell_06_16⟩
  · exact ⟨0x00000000dd0934409922d94c03a340b5c59c51b1b743a865470fa0a76d5e0000#256,
      (0x2ee94340#32, 0x0fef4dff#32), by simpa [oneHotDifference] using cell_06_17⟩
  · exact ⟨0x00000000ce1d502fcd69b7f9f50f7a9fe9cdee3711ed46f05651c582642bffff#256,
      (0xdd2417fb#32, 0x40ee2fdb#32), by simpa [oneHotDifference] using cell_06_18⟩
  · exact ⟨0x000000009ff5b117bc3ab6214fd9f1fff3dbaaf17ed2eb16814be102302c4865#256,
      (0xafc64929#32, 0x90f76d1c#32), by simpa [oneHotDifference] using cell_06_19⟩
  · exact ⟨0x00000000b95c82d0b5caf56215c5e3b1ab4520e8d0c427deff0b8d984ceefac0#256,
      (0x017ac25f#32, 0x21b8603b#32), by simpa [oneHotDifference] using cell_06_20⟩
  · exact ⟨0x00000000705249d0432daa94027fc4f1922d7c31d95e4dd479604eabe1900000#256,
      (0x7e333a3e#32, 0x623a1c15#32), by simpa [oneHotDifference] using cell_06_21⟩
  · exact ⟨0x000000009160112fefb49ff86b04d9f8450fe306e08b0de911eabd2ec19ff80f#256,
      (0x5b9945e3#32, 0xb29edfd5#32), by simpa [oneHotDifference] using cell_06_22⟩
  · exact ⟨0x00000000afcc834e896267ef8c036a3001cac93e0816a57e3985edd8707fb410#256,
      (0x5fb9fc06#32, 0x09ae696c#32), by simpa [oneHotDifference] using cell_06_23⟩
  · exact ⟨0x00000000e0fe36104197f8462f1ae8de82d70bfd54c4d02280285d36a408800f#256,
      (0xbbc6436b#32, 0x5214e8ff#32), by simpa [oneHotDifference] using cell_06_24⟩
  · exact ⟨0x00000000301a241051e24a32165ad50c19b63f24c12c2c204609d1705f00000e#256,
      (0xaae386b6#32, 0xa5951f76#32), by simpa [oneHotDifference] using cell_06_25⟩
  · exact ⟨0x0000000045f48fbff0a774315a40b053fdf5811e40fcb46bfc55f9f58cfffcff#256,
      (0x3d710121#32, 0xf153d5a8#32), by simpa [oneHotDifference] using cell_06_26⟩
  · exact ⟨0x000000003b3a2daf4373fbf7b21f0b27dd7de2fa7cd92f8d1f20ca8b55bc0b00#256,
      (0x16014e31#32, 0x6af35e4d#32), by simpa [oneHotDifference] using cell_06_27⟩
  · exact ⟨0x0000000050e9553fcb7453beb186f89effa3ea756fad3aa702139f5facfb007c#256,
      (0x98ff7644#32, 0xcb2e6736#32), by simpa [oneHotDifference] using cell_06_28⟩
  · exact ⟨0x0000000095ada2b0ee1e629013e278dbf7581aca27b44bcb24d38b9c10180040#256,
      (0x6468bdbb#32, 0x0910aa60#32), by simpa [oneHotDifference] using cell_06_29⟩
  · exact ⟨0x0000000070eb8428588b3e2a2169d70eaac785689da9a33ed3948d9046abd400#256,
      (0x4a283b26#32, 0x0b5c9019#32), by simpa [oneHotDifference] using cell_06_30⟩
  · exact ⟨0x00000000964ea33fc119f6fcea8c9485887d2a1b3db9cd1acd3afc29816cb56c#256,
      (0xb00f7d6d#32, 0x7767fa71#32), by simpa [oneHotDifference] using cell_06_31⟩

end Magma.DiffanNineRoundPositiveRows
