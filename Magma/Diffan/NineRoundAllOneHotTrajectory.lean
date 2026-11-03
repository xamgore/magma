module
import all Init.Data.Range.Basic
public import Magma.Diffan.NineRoundPositiveRows.Row00
public import Magma.Diffan.NineRoundPositiveRows.Row01
public import Magma.Diffan.NineRoundPositiveRows.Row02
public import Magma.Diffan.NineRoundPositiveRows.Row03
public import Magma.Diffan.NineRoundPositiveRows.Row04
public import Magma.Diffan.NineRoundPositiveRows.Row05
public import Magma.Diffan.NineRoundPositiveRows.Row06
public import Magma.Diffan.NineRoundPositiveRows.Row07
public import Magma.Diffan.NineRoundPositiveRows.Row08
public import Magma.Diffan.NineRoundPositiveRows.Row09
public import Magma.Diffan.NineRoundPositiveRows.Row10
public import Magma.Diffan.NineRoundPositiveRows.Row11
public import Magma.Diffan.NineRoundPositiveRows.Row12
public import Magma.Diffan.NineRoundPositiveRows.Row13
public import Magma.Diffan.NineRoundPositiveRows.Row14
public import Magma.Diffan.NineRoundPositiveRows.Row15
public import Magma.Diffan.NineRoundPositiveRows.Row16
public import Magma.Diffan.NineRoundPositiveRows.Row17
public import Magma.Diffan.NineRoundPositiveRows.Row18
public import Magma.Diffan.NineRoundPositiveRows.Row19
public import Magma.Diffan.NineRoundPositiveRows.Row20
public import Magma.Diffan.NineRoundPositiveRows.Row21
public import Magma.Diffan.NineRoundPositiveRows.Row22
public import Magma.Diffan.NineRoundPositiveRows.Row23
public import Magma.Diffan.NineRoundPositiveRows.Row24
public import Magma.Diffan.NineRoundPositiveRows.Row25
public import Magma.Diffan.NineRoundPositiveRows.Row26
public import Magma.Diffan.NineRoundPositiveRows.Row27
public import Magma.Diffan.NineRoundPositiveRows.Row28
public import Magma.Diffan.NineRoundPositiveRows.Row29
public import Magma.Diffan.NineRoundPositiveRows.Row30
public import Magma.Diffan.NineRoundPositiveRows.Row31
set_option maxRecDepth 8192
set_option maxHeartbeats 20000000
@[expose] public section
namespace Magma.DiffanNineRoundAllOneHotTrajectory
open Magma
open Magma.MultiRoundDDT
open Magma.DiffanFiveRoundUniversalSupport
open Magma.DiffanNineRoundPositiveRows

/-- All 1,024 concrete nine-round trajectories are checked
    by Lean, with independent RFC master-key witnesses for
    each ordered pair of active bit positions. -/
theorem all_oneHot_nine_round_trajectory (i j : Fin 32) :
    ∃ master : V 256, ∃ base : FeistelState,
      multiRoundDelta 9
        (fun k : Fin 9 => roundKey master ⟨k.val, by omega⟩)
        base (oneHotDifference i, 0#32)
        = (0#32, oneHotDifference j) := by
  fin_cases i
  · exact row00 j
  · exact row01 j
  · exact row02 j
  · exact row03 j
  · exact row04 j
  · exact row05 j
  · exact row06 j
  · exact row07 j
  · exact row08 j
  · exact row09 j
  · exact row10 j
  · exact row11 j
  · exact row12 j
  · exact row13 j
  · exact row14 j
  · exact row15 j
  · exact row16 j
  · exact row17 j
  · exact row18 j
  · exact row19 j
  · exact row20 j
  · exact row21 j
  · exact row22 j
  · exact row23 j
  · exact row24 j
  · exact row25 j
  · exact row26 j
  · exact row27 j
  · exact row28 j
  · exact row29 j
  · exact row30 j
  · exact row31 j

end Magma.DiffanNineRoundAllOneHotTrajectory
