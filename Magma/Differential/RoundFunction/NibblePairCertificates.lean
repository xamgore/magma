module

public import Magma.Differential.FiveRounds.FiveRoundMiddleNibbleFilter
import Std.Tactic.BVDecide

set_option maxRecDepth 2048
@[expose] public section

/-! All 32 incompatible pairs of nibble indices, checked by Lean's
    bit-vector decision procedure, independently of the SAT matrix. -/

namespace Magma.DiffanNibblePairCertificates

open Magma
open Magma.CarryAutomaton
open Magma.DiffanFirstActiveNibbleInvariant
open Magma.DiffanFiveRoundMiddleNibbleFilter

abbrev Word := V 32

theorem incompatible_0_4 : NoCompatibleMiddleWord 0 4 := by
  intro c hc
  have hr := hc.1
  have hd := hc.2
  have hri : BitVec.extractLsb' 0 4 (c.rotateRight 11) ≠ 0#4 := by
    intro hz
    apply hr.2
    change (BitVec.extractLsb' 0 4 (c.rotateRight 11)).toFin = 0
    rw [hz]
    rfl
  have hdj : BitVec.extractLsb' 16 4 c ≠ 0#4 := by
    intro hz
    apply hd.2
    change (BitVec.extractLsb' 16 4 c).toFin = 0
    rw [hz]
    rfl
  have hdzero0 : BitVec.extractLsb' 0 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 0 (by decide)
  have hdzero1 : BitVec.extractLsb' 4 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 1 (by decide)
  have hdzero2 : BitVec.extractLsb' 8 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 2 (by decide)
  have hdzero3 : BitVec.extractLsb' 12 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 3 (by decide)
  bv_decide

theorem incompatible_0_5 : NoCompatibleMiddleWord 0 5 := by
  intro c hc
  have hr := hc.1
  have hd := hc.2
  have hri : BitVec.extractLsb' 0 4 (c.rotateRight 11) ≠ 0#4 := by
    intro hz
    apply hr.2
    change (BitVec.extractLsb' 0 4 (c.rotateRight 11)).toFin = 0
    rw [hz]
    rfl
  have hdj : BitVec.extractLsb' 20 4 c ≠ 0#4 := by
    intro hz
    apply hd.2
    change (BitVec.extractLsb' 20 4 c).toFin = 0
    rw [hz]
    rfl
  have hdzero0 : BitVec.extractLsb' 0 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 0 (by decide)
  have hdzero1 : BitVec.extractLsb' 4 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 1 (by decide)
  have hdzero2 : BitVec.extractLsb' 8 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 2 (by decide)
  have hdzero3 : BitVec.extractLsb' 12 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 3 (by decide)
  have hdzero4 : BitVec.extractLsb' 16 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 4 (by decide)
  bv_decide

theorem incompatible_0_6 : NoCompatibleMiddleWord 0 6 := by
  intro c hc
  have hr := hc.1
  have hd := hc.2
  have hri : BitVec.extractLsb' 0 4 (c.rotateRight 11) ≠ 0#4 := by
    intro hz
    apply hr.2
    change (BitVec.extractLsb' 0 4 (c.rotateRight 11)).toFin = 0
    rw [hz]
    rfl
  have hdj : BitVec.extractLsb' 24 4 c ≠ 0#4 := by
    intro hz
    apply hd.2
    change (BitVec.extractLsb' 24 4 c).toFin = 0
    rw [hz]
    rfl
  have hdzero0 : BitVec.extractLsb' 0 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 0 (by decide)
  have hdzero1 : BitVec.extractLsb' 4 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 1 (by decide)
  have hdzero2 : BitVec.extractLsb' 8 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 2 (by decide)
  have hdzero3 : BitVec.extractLsb' 12 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 3 (by decide)
  have hdzero4 : BitVec.extractLsb' 16 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 4 (by decide)
  have hdzero5 : BitVec.extractLsb' 20 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 5 (by decide)
  bv_decide

theorem incompatible_0_7 : NoCompatibleMiddleWord 0 7 := by
  intro c hc
  have hr := hc.1
  have hd := hc.2
  have hri : BitVec.extractLsb' 0 4 (c.rotateRight 11) ≠ 0#4 := by
    intro hz
    apply hr.2
    change (BitVec.extractLsb' 0 4 (c.rotateRight 11)).toFin = 0
    rw [hz]
    rfl
  have hdj : BitVec.extractLsb' 28 4 c ≠ 0#4 := by
    intro hz
    apply hd.2
    change (BitVec.extractLsb' 28 4 c).toFin = 0
    rw [hz]
    rfl
  have hdzero0 : BitVec.extractLsb' 0 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 0 (by decide)
  have hdzero1 : BitVec.extractLsb' 4 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 1 (by decide)
  have hdzero2 : BitVec.extractLsb' 8 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 2 (by decide)
  have hdzero3 : BitVec.extractLsb' 12 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 3 (by decide)
  have hdzero4 : BitVec.extractLsb' 16 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 4 (by decide)
  have hdzero5 : BitVec.extractLsb' 20 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 5 (by decide)
  have hdzero6 : BitVec.extractLsb' 24 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 6 (by decide)
  bv_decide

theorem incompatible_1_5 : NoCompatibleMiddleWord 1 5 := by
  intro c hc
  have hr := hc.1
  have hd := hc.2
  have hri : BitVec.extractLsb' 4 4 (c.rotateRight 11) ≠ 0#4 := by
    intro hz
    apply hr.2
    change (BitVec.extractLsb' 4 4 (c.rotateRight 11)).toFin = 0
    rw [hz]
    rfl
  have hdj : BitVec.extractLsb' 20 4 c ≠ 0#4 := by
    intro hz
    apply hd.2
    change (BitVec.extractLsb' 20 4 c).toFin = 0
    rw [hz]
    rfl
  have hrzero0 : BitVec.extractLsb' 0 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 0 (by decide)
  have hdzero0 : BitVec.extractLsb' 0 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 0 (by decide)
  have hdzero1 : BitVec.extractLsb' 4 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 1 (by decide)
  have hdzero2 : BitVec.extractLsb' 8 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 2 (by decide)
  have hdzero3 : BitVec.extractLsb' 12 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 3 (by decide)
  have hdzero4 : BitVec.extractLsb' 16 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 4 (by decide)
  bv_decide

theorem incompatible_1_6 : NoCompatibleMiddleWord 1 6 := by
  intro c hc
  have hr := hc.1
  have hd := hc.2
  have hri : BitVec.extractLsb' 4 4 (c.rotateRight 11) ≠ 0#4 := by
    intro hz
    apply hr.2
    change (BitVec.extractLsb' 4 4 (c.rotateRight 11)).toFin = 0
    rw [hz]
    rfl
  have hdj : BitVec.extractLsb' 24 4 c ≠ 0#4 := by
    intro hz
    apply hd.2
    change (BitVec.extractLsb' 24 4 c).toFin = 0
    rw [hz]
    rfl
  have hrzero0 : BitVec.extractLsb' 0 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 0 (by decide)
  have hdzero0 : BitVec.extractLsb' 0 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 0 (by decide)
  have hdzero1 : BitVec.extractLsb' 4 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 1 (by decide)
  have hdzero2 : BitVec.extractLsb' 8 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 2 (by decide)
  have hdzero3 : BitVec.extractLsb' 12 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 3 (by decide)
  have hdzero4 : BitVec.extractLsb' 16 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 4 (by decide)
  have hdzero5 : BitVec.extractLsb' 20 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 5 (by decide)
  bv_decide

theorem incompatible_1_7 : NoCompatibleMiddleWord 1 7 := by
  intro c hc
  have hr := hc.1
  have hd := hc.2
  have hri : BitVec.extractLsb' 4 4 (c.rotateRight 11) ≠ 0#4 := by
    intro hz
    apply hr.2
    change (BitVec.extractLsb' 4 4 (c.rotateRight 11)).toFin = 0
    rw [hz]
    rfl
  have hdj : BitVec.extractLsb' 28 4 c ≠ 0#4 := by
    intro hz
    apply hd.2
    change (BitVec.extractLsb' 28 4 c).toFin = 0
    rw [hz]
    rfl
  have hrzero0 : BitVec.extractLsb' 0 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 0 (by decide)
  have hdzero0 : BitVec.extractLsb' 0 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 0 (by decide)
  have hdzero1 : BitVec.extractLsb' 4 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 1 (by decide)
  have hdzero2 : BitVec.extractLsb' 8 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 2 (by decide)
  have hdzero3 : BitVec.extractLsb' 12 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 3 (by decide)
  have hdzero4 : BitVec.extractLsb' 16 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 4 (by decide)
  have hdzero5 : BitVec.extractLsb' 20 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 5 (by decide)
  have hdzero6 : BitVec.extractLsb' 24 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 6 (by decide)
  bv_decide

theorem incompatible_2_3 : NoCompatibleMiddleWord 2 3 := by
  intro c hc
  have hr := hc.1
  have hd := hc.2
  have hri : BitVec.extractLsb' 8 4 (c.rotateRight 11) ≠ 0#4 := by
    intro hz
    apply hr.2
    change (BitVec.extractLsb' 8 4 (c.rotateRight 11)).toFin = 0
    rw [hz]
    rfl
  have hdj : BitVec.extractLsb' 12 4 c ≠ 0#4 := by
    intro hz
    apply hd.2
    change (BitVec.extractLsb' 12 4 c).toFin = 0
    rw [hz]
    rfl
  have hrzero0 : BitVec.extractLsb' 0 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 0 (by decide)
  have hrzero1 : BitVec.extractLsb' 4 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 1 (by decide)
  have hdzero0 : BitVec.extractLsb' 0 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 0 (by decide)
  have hdzero1 : BitVec.extractLsb' 4 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 1 (by decide)
  have hdzero2 : BitVec.extractLsb' 8 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 2 (by decide)
  bv_decide

theorem incompatible_2_6 : NoCompatibleMiddleWord 2 6 := by
  intro c hc
  have hr := hc.1
  have hd := hc.2
  have hri : BitVec.extractLsb' 8 4 (c.rotateRight 11) ≠ 0#4 := by
    intro hz
    apply hr.2
    change (BitVec.extractLsb' 8 4 (c.rotateRight 11)).toFin = 0
    rw [hz]
    rfl
  have hdj : BitVec.extractLsb' 24 4 c ≠ 0#4 := by
    intro hz
    apply hd.2
    change (BitVec.extractLsb' 24 4 c).toFin = 0
    rw [hz]
    rfl
  have hrzero0 : BitVec.extractLsb' 0 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 0 (by decide)
  have hrzero1 : BitVec.extractLsb' 4 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 1 (by decide)
  have hdzero0 : BitVec.extractLsb' 0 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 0 (by decide)
  have hdzero1 : BitVec.extractLsb' 4 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 1 (by decide)
  have hdzero2 : BitVec.extractLsb' 8 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 2 (by decide)
  have hdzero3 : BitVec.extractLsb' 12 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 3 (by decide)
  have hdzero4 : BitVec.extractLsb' 16 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 4 (by decide)
  have hdzero5 : BitVec.extractLsb' 20 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 5 (by decide)
  bv_decide

theorem incompatible_2_7 : NoCompatibleMiddleWord 2 7 := by
  intro c hc
  have hr := hc.1
  have hd := hc.2
  have hri : BitVec.extractLsb' 8 4 (c.rotateRight 11) ≠ 0#4 := by
    intro hz
    apply hr.2
    change (BitVec.extractLsb' 8 4 (c.rotateRight 11)).toFin = 0
    rw [hz]
    rfl
  have hdj : BitVec.extractLsb' 28 4 c ≠ 0#4 := by
    intro hz
    apply hd.2
    change (BitVec.extractLsb' 28 4 c).toFin = 0
    rw [hz]
    rfl
  have hrzero0 : BitVec.extractLsb' 0 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 0 (by decide)
  have hrzero1 : BitVec.extractLsb' 4 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 1 (by decide)
  have hdzero0 : BitVec.extractLsb' 0 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 0 (by decide)
  have hdzero1 : BitVec.extractLsb' 4 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 1 (by decide)
  have hdzero2 : BitVec.extractLsb' 8 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 2 (by decide)
  have hdzero3 : BitVec.extractLsb' 12 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 3 (by decide)
  have hdzero4 : BitVec.extractLsb' 16 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 4 (by decide)
  have hdzero5 : BitVec.extractLsb' 20 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 5 (by decide)
  have hdzero6 : BitVec.extractLsb' 24 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 6 (by decide)
  bv_decide

theorem incompatible_3_3 : NoCompatibleMiddleWord 3 3 := by
  intro c hc
  have hr := hc.1
  have hd := hc.2
  have hri : BitVec.extractLsb' 12 4 (c.rotateRight 11) ≠ 0#4 := by
    intro hz
    apply hr.2
    change (BitVec.extractLsb' 12 4 (c.rotateRight 11)).toFin = 0
    rw [hz]
    rfl
  have hdj : BitVec.extractLsb' 12 4 c ≠ 0#4 := by
    intro hz
    apply hd.2
    change (BitVec.extractLsb' 12 4 c).toFin = 0
    rw [hz]
    rfl
  have hrzero0 : BitVec.extractLsb' 0 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 0 (by decide)
  have hrzero1 : BitVec.extractLsb' 4 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 1 (by decide)
  have hrzero2 : BitVec.extractLsb' 8 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 2 (by decide)
  have hdzero0 : BitVec.extractLsb' 0 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 0 (by decide)
  have hdzero1 : BitVec.extractLsb' 4 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 1 (by decide)
  have hdzero2 : BitVec.extractLsb' 8 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 2 (by decide)
  bv_decide

theorem incompatible_3_4 : NoCompatibleMiddleWord 3 4 := by
  intro c hc
  have hr := hc.1
  have hd := hc.2
  have hri : BitVec.extractLsb' 12 4 (c.rotateRight 11) ≠ 0#4 := by
    intro hz
    apply hr.2
    change (BitVec.extractLsb' 12 4 (c.rotateRight 11)).toFin = 0
    rw [hz]
    rfl
  have hdj : BitVec.extractLsb' 16 4 c ≠ 0#4 := by
    intro hz
    apply hd.2
    change (BitVec.extractLsb' 16 4 c).toFin = 0
    rw [hz]
    rfl
  have hrzero0 : BitVec.extractLsb' 0 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 0 (by decide)
  have hrzero1 : BitVec.extractLsb' 4 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 1 (by decide)
  have hrzero2 : BitVec.extractLsb' 8 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 2 (by decide)
  have hdzero0 : BitVec.extractLsb' 0 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 0 (by decide)
  have hdzero1 : BitVec.extractLsb' 4 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 1 (by decide)
  have hdzero2 : BitVec.extractLsb' 8 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 2 (by decide)
  have hdzero3 : BitVec.extractLsb' 12 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 3 (by decide)
  bv_decide

theorem incompatible_3_7 : NoCompatibleMiddleWord 3 7 := by
  intro c hc
  have hr := hc.1
  have hd := hc.2
  have hri : BitVec.extractLsb' 12 4 (c.rotateRight 11) ≠ 0#4 := by
    intro hz
    apply hr.2
    change (BitVec.extractLsb' 12 4 (c.rotateRight 11)).toFin = 0
    rw [hz]
    rfl
  have hdj : BitVec.extractLsb' 28 4 c ≠ 0#4 := by
    intro hz
    apply hd.2
    change (BitVec.extractLsb' 28 4 c).toFin = 0
    rw [hz]
    rfl
  have hrzero0 : BitVec.extractLsb' 0 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 0 (by decide)
  have hrzero1 : BitVec.extractLsb' 4 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 1 (by decide)
  have hrzero2 : BitVec.extractLsb' 8 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 2 (by decide)
  have hdzero0 : BitVec.extractLsb' 0 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 0 (by decide)
  have hdzero1 : BitVec.extractLsb' 4 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 1 (by decide)
  have hdzero2 : BitVec.extractLsb' 8 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 2 (by decide)
  have hdzero3 : BitVec.extractLsb' 12 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 3 (by decide)
  have hdzero4 : BitVec.extractLsb' 16 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 4 (by decide)
  have hdzero5 : BitVec.extractLsb' 20 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 5 (by decide)
  have hdzero6 : BitVec.extractLsb' 24 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 6 (by decide)
  bv_decide

theorem incompatible_4_3 : NoCompatibleMiddleWord 4 3 := by
  intro c hc
  have hr := hc.1
  have hd := hc.2
  have hri : BitVec.extractLsb' 16 4 (c.rotateRight 11) ≠ 0#4 := by
    intro hz
    apply hr.2
    change (BitVec.extractLsb' 16 4 (c.rotateRight 11)).toFin = 0
    rw [hz]
    rfl
  have hdj : BitVec.extractLsb' 12 4 c ≠ 0#4 := by
    intro hz
    apply hd.2
    change (BitVec.extractLsb' 12 4 c).toFin = 0
    rw [hz]
    rfl
  have hrzero0 : BitVec.extractLsb' 0 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 0 (by decide)
  have hrzero1 : BitVec.extractLsb' 4 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 1 (by decide)
  have hrzero2 : BitVec.extractLsb' 8 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 2 (by decide)
  have hrzero3 : BitVec.extractLsb' 12 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 3 (by decide)
  have hdzero0 : BitVec.extractLsb' 0 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 0 (by decide)
  have hdzero1 : BitVec.extractLsb' 4 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 1 (by decide)
  have hdzero2 : BitVec.extractLsb' 8 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 2 (by decide)
  bv_decide

theorem incompatible_4_4 : NoCompatibleMiddleWord 4 4 := by
  intro c hc
  have hr := hc.1
  have hd := hc.2
  have hri : BitVec.extractLsb' 16 4 (c.rotateRight 11) ≠ 0#4 := by
    intro hz
    apply hr.2
    change (BitVec.extractLsb' 16 4 (c.rotateRight 11)).toFin = 0
    rw [hz]
    rfl
  have hdj : BitVec.extractLsb' 16 4 c ≠ 0#4 := by
    intro hz
    apply hd.2
    change (BitVec.extractLsb' 16 4 c).toFin = 0
    rw [hz]
    rfl
  have hrzero0 : BitVec.extractLsb' 0 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 0 (by decide)
  have hrzero1 : BitVec.extractLsb' 4 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 1 (by decide)
  have hrzero2 : BitVec.extractLsb' 8 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 2 (by decide)
  have hrzero3 : BitVec.extractLsb' 12 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 3 (by decide)
  have hdzero0 : BitVec.extractLsb' 0 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 0 (by decide)
  have hdzero1 : BitVec.extractLsb' 4 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 1 (by decide)
  have hdzero2 : BitVec.extractLsb' 8 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 2 (by decide)
  have hdzero3 : BitVec.extractLsb' 12 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 3 (by decide)
  bv_decide

theorem incompatible_4_5 : NoCompatibleMiddleWord 4 5 := by
  intro c hc
  have hr := hc.1
  have hd := hc.2
  have hri : BitVec.extractLsb' 16 4 (c.rotateRight 11) ≠ 0#4 := by
    intro hz
    apply hr.2
    change (BitVec.extractLsb' 16 4 (c.rotateRight 11)).toFin = 0
    rw [hz]
    rfl
  have hdj : BitVec.extractLsb' 20 4 c ≠ 0#4 := by
    intro hz
    apply hd.2
    change (BitVec.extractLsb' 20 4 c).toFin = 0
    rw [hz]
    rfl
  have hrzero0 : BitVec.extractLsb' 0 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 0 (by decide)
  have hrzero1 : BitVec.extractLsb' 4 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 1 (by decide)
  have hrzero2 : BitVec.extractLsb' 8 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 2 (by decide)
  have hrzero3 : BitVec.extractLsb' 12 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 3 (by decide)
  have hdzero0 : BitVec.extractLsb' 0 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 0 (by decide)
  have hdzero1 : BitVec.extractLsb' 4 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 1 (by decide)
  have hdzero2 : BitVec.extractLsb' 8 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 2 (by decide)
  have hdzero3 : BitVec.extractLsb' 12 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 3 (by decide)
  have hdzero4 : BitVec.extractLsb' 16 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 4 (by decide)
  bv_decide

theorem incompatible_5_3 : NoCompatibleMiddleWord 5 3 := by
  intro c hc
  have hr := hc.1
  have hd := hc.2
  have hri : BitVec.extractLsb' 20 4 (c.rotateRight 11) ≠ 0#4 := by
    intro hz
    apply hr.2
    change (BitVec.extractLsb' 20 4 (c.rotateRight 11)).toFin = 0
    rw [hz]
    rfl
  have hdj : BitVec.extractLsb' 12 4 c ≠ 0#4 := by
    intro hz
    apply hd.2
    change (BitVec.extractLsb' 12 4 c).toFin = 0
    rw [hz]
    rfl
  have hrzero0 : BitVec.extractLsb' 0 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 0 (by decide)
  have hrzero1 : BitVec.extractLsb' 4 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 1 (by decide)
  have hrzero2 : BitVec.extractLsb' 8 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 2 (by decide)
  have hrzero3 : BitVec.extractLsb' 12 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 3 (by decide)
  have hrzero4 : BitVec.extractLsb' 16 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 4 (by decide)
  have hdzero0 : BitVec.extractLsb' 0 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 0 (by decide)
  have hdzero1 : BitVec.extractLsb' 4 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 1 (by decide)
  have hdzero2 : BitVec.extractLsb' 8 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 2 (by decide)
  bv_decide

theorem incompatible_5_4 : NoCompatibleMiddleWord 5 4 := by
  intro c hc
  have hr := hc.1
  have hd := hc.2
  have hri : BitVec.extractLsb' 20 4 (c.rotateRight 11) ≠ 0#4 := by
    intro hz
    apply hr.2
    change (BitVec.extractLsb' 20 4 (c.rotateRight 11)).toFin = 0
    rw [hz]
    rfl
  have hdj : BitVec.extractLsb' 16 4 c ≠ 0#4 := by
    intro hz
    apply hd.2
    change (BitVec.extractLsb' 16 4 c).toFin = 0
    rw [hz]
    rfl
  have hrzero0 : BitVec.extractLsb' 0 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 0 (by decide)
  have hrzero1 : BitVec.extractLsb' 4 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 1 (by decide)
  have hrzero2 : BitVec.extractLsb' 8 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 2 (by decide)
  have hrzero3 : BitVec.extractLsb' 12 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 3 (by decide)
  have hrzero4 : BitVec.extractLsb' 16 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 4 (by decide)
  have hdzero0 : BitVec.extractLsb' 0 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 0 (by decide)
  have hdzero1 : BitVec.extractLsb' 4 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 1 (by decide)
  have hdzero2 : BitVec.extractLsb' 8 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 2 (by decide)
  have hdzero3 : BitVec.extractLsb' 12 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 3 (by decide)
  bv_decide

theorem incompatible_5_5 : NoCompatibleMiddleWord 5 5 := by
  intro c hc
  have hr := hc.1
  have hd := hc.2
  have hri : BitVec.extractLsb' 20 4 (c.rotateRight 11) ≠ 0#4 := by
    intro hz
    apply hr.2
    change (BitVec.extractLsb' 20 4 (c.rotateRight 11)).toFin = 0
    rw [hz]
    rfl
  have hdj : BitVec.extractLsb' 20 4 c ≠ 0#4 := by
    intro hz
    apply hd.2
    change (BitVec.extractLsb' 20 4 c).toFin = 0
    rw [hz]
    rfl
  have hrzero0 : BitVec.extractLsb' 0 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 0 (by decide)
  have hrzero1 : BitVec.extractLsb' 4 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 1 (by decide)
  have hrzero2 : BitVec.extractLsb' 8 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 2 (by decide)
  have hrzero3 : BitVec.extractLsb' 12 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 3 (by decide)
  have hrzero4 : BitVec.extractLsb' 16 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 4 (by decide)
  have hdzero0 : BitVec.extractLsb' 0 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 0 (by decide)
  have hdzero1 : BitVec.extractLsb' 4 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 1 (by decide)
  have hdzero2 : BitVec.extractLsb' 8 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 2 (by decide)
  have hdzero3 : BitVec.extractLsb' 12 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 3 (by decide)
  have hdzero4 : BitVec.extractLsb' 16 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 4 (by decide)
  bv_decide

theorem incompatible_5_6 : NoCompatibleMiddleWord 5 6 := by
  intro c hc
  have hr := hc.1
  have hd := hc.2
  have hri : BitVec.extractLsb' 20 4 (c.rotateRight 11) ≠ 0#4 := by
    intro hz
    apply hr.2
    change (BitVec.extractLsb' 20 4 (c.rotateRight 11)).toFin = 0
    rw [hz]
    rfl
  have hdj : BitVec.extractLsb' 24 4 c ≠ 0#4 := by
    intro hz
    apply hd.2
    change (BitVec.extractLsb' 24 4 c).toFin = 0
    rw [hz]
    rfl
  have hrzero0 : BitVec.extractLsb' 0 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 0 (by decide)
  have hrzero1 : BitVec.extractLsb' 4 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 1 (by decide)
  have hrzero2 : BitVec.extractLsb' 8 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 2 (by decide)
  have hrzero3 : BitVec.extractLsb' 12 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 3 (by decide)
  have hrzero4 : BitVec.extractLsb' 16 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 4 (by decide)
  have hdzero0 : BitVec.extractLsb' 0 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 0 (by decide)
  have hdzero1 : BitVec.extractLsb' 4 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 1 (by decide)
  have hdzero2 : BitVec.extractLsb' 8 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 2 (by decide)
  have hdzero3 : BitVec.extractLsb' 12 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 3 (by decide)
  have hdzero4 : BitVec.extractLsb' 16 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 4 (by decide)
  have hdzero5 : BitVec.extractLsb' 20 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 5 (by decide)
  bv_decide

theorem incompatible_6_2 : NoCompatibleMiddleWord 6 2 := by
  intro c hc
  have hr := hc.1
  have hd := hc.2
  have hri : BitVec.extractLsb' 24 4 (c.rotateRight 11) ≠ 0#4 := by
    intro hz
    apply hr.2
    change (BitVec.extractLsb' 24 4 (c.rotateRight 11)).toFin = 0
    rw [hz]
    rfl
  have hdj : BitVec.extractLsb' 8 4 c ≠ 0#4 := by
    intro hz
    apply hd.2
    change (BitVec.extractLsb' 8 4 c).toFin = 0
    rw [hz]
    rfl
  have hrzero0 : BitVec.extractLsb' 0 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 0 (by decide)
  have hrzero1 : BitVec.extractLsb' 4 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 1 (by decide)
  have hrzero2 : BitVec.extractLsb' 8 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 2 (by decide)
  have hrzero3 : BitVec.extractLsb' 12 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 3 (by decide)
  have hrzero4 : BitVec.extractLsb' 16 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 4 (by decide)
  have hrzero5 : BitVec.extractLsb' 20 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 5 (by decide)
  have hdzero0 : BitVec.extractLsb' 0 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 0 (by decide)
  have hdzero1 : BitVec.extractLsb' 4 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 1 (by decide)
  bv_decide

theorem incompatible_6_3 : NoCompatibleMiddleWord 6 3 := by
  intro c hc
  have hr := hc.1
  have hd := hc.2
  have hri : BitVec.extractLsb' 24 4 (c.rotateRight 11) ≠ 0#4 := by
    intro hz
    apply hr.2
    change (BitVec.extractLsb' 24 4 (c.rotateRight 11)).toFin = 0
    rw [hz]
    rfl
  have hdj : BitVec.extractLsb' 12 4 c ≠ 0#4 := by
    intro hz
    apply hd.2
    change (BitVec.extractLsb' 12 4 c).toFin = 0
    rw [hz]
    rfl
  have hrzero0 : BitVec.extractLsb' 0 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 0 (by decide)
  have hrzero1 : BitVec.extractLsb' 4 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 1 (by decide)
  have hrzero2 : BitVec.extractLsb' 8 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 2 (by decide)
  have hrzero3 : BitVec.extractLsb' 12 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 3 (by decide)
  have hrzero4 : BitVec.extractLsb' 16 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 4 (by decide)
  have hrzero5 : BitVec.extractLsb' 20 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 5 (by decide)
  have hdzero0 : BitVec.extractLsb' 0 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 0 (by decide)
  have hdzero1 : BitVec.extractLsb' 4 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 1 (by decide)
  have hdzero2 : BitVec.extractLsb' 8 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 2 (by decide)
  bv_decide

theorem incompatible_6_4 : NoCompatibleMiddleWord 6 4 := by
  intro c hc
  have hr := hc.1
  have hd := hc.2
  have hri : BitVec.extractLsb' 24 4 (c.rotateRight 11) ≠ 0#4 := by
    intro hz
    apply hr.2
    change (BitVec.extractLsb' 24 4 (c.rotateRight 11)).toFin = 0
    rw [hz]
    rfl
  have hdj : BitVec.extractLsb' 16 4 c ≠ 0#4 := by
    intro hz
    apply hd.2
    change (BitVec.extractLsb' 16 4 c).toFin = 0
    rw [hz]
    rfl
  have hrzero0 : BitVec.extractLsb' 0 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 0 (by decide)
  have hrzero1 : BitVec.extractLsb' 4 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 1 (by decide)
  have hrzero2 : BitVec.extractLsb' 8 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 2 (by decide)
  have hrzero3 : BitVec.extractLsb' 12 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 3 (by decide)
  have hrzero4 : BitVec.extractLsb' 16 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 4 (by decide)
  have hrzero5 : BitVec.extractLsb' 20 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 5 (by decide)
  have hdzero0 : BitVec.extractLsb' 0 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 0 (by decide)
  have hdzero1 : BitVec.extractLsb' 4 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 1 (by decide)
  have hdzero2 : BitVec.extractLsb' 8 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 2 (by decide)
  have hdzero3 : BitVec.extractLsb' 12 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 3 (by decide)
  bv_decide

theorem incompatible_6_5 : NoCompatibleMiddleWord 6 5 := by
  intro c hc
  have hr := hc.1
  have hd := hc.2
  have hri : BitVec.extractLsb' 24 4 (c.rotateRight 11) ≠ 0#4 := by
    intro hz
    apply hr.2
    change (BitVec.extractLsb' 24 4 (c.rotateRight 11)).toFin = 0
    rw [hz]
    rfl
  have hdj : BitVec.extractLsb' 20 4 c ≠ 0#4 := by
    intro hz
    apply hd.2
    change (BitVec.extractLsb' 20 4 c).toFin = 0
    rw [hz]
    rfl
  have hrzero0 : BitVec.extractLsb' 0 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 0 (by decide)
  have hrzero1 : BitVec.extractLsb' 4 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 1 (by decide)
  have hrzero2 : BitVec.extractLsb' 8 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 2 (by decide)
  have hrzero3 : BitVec.extractLsb' 12 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 3 (by decide)
  have hrzero4 : BitVec.extractLsb' 16 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 4 (by decide)
  have hrzero5 : BitVec.extractLsb' 20 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 5 (by decide)
  have hdzero0 : BitVec.extractLsb' 0 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 0 (by decide)
  have hdzero1 : BitVec.extractLsb' 4 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 1 (by decide)
  have hdzero2 : BitVec.extractLsb' 8 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 2 (by decide)
  have hdzero3 : BitVec.extractLsb' 12 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 3 (by decide)
  have hdzero4 : BitVec.extractLsb' 16 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 4 (by decide)
  bv_decide

theorem incompatible_6_6 : NoCompatibleMiddleWord 6 6 := by
  intro c hc
  have hr := hc.1
  have hd := hc.2
  have hri : BitVec.extractLsb' 24 4 (c.rotateRight 11) ≠ 0#4 := by
    intro hz
    apply hr.2
    change (BitVec.extractLsb' 24 4 (c.rotateRight 11)).toFin = 0
    rw [hz]
    rfl
  have hdj : BitVec.extractLsb' 24 4 c ≠ 0#4 := by
    intro hz
    apply hd.2
    change (BitVec.extractLsb' 24 4 c).toFin = 0
    rw [hz]
    rfl
  have hrzero0 : BitVec.extractLsb' 0 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 0 (by decide)
  have hrzero1 : BitVec.extractLsb' 4 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 1 (by decide)
  have hrzero2 : BitVec.extractLsb' 8 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 2 (by decide)
  have hrzero3 : BitVec.extractLsb' 12 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 3 (by decide)
  have hrzero4 : BitVec.extractLsb' 16 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 4 (by decide)
  have hrzero5 : BitVec.extractLsb' 20 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 5 (by decide)
  have hdzero0 : BitVec.extractLsb' 0 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 0 (by decide)
  have hdzero1 : BitVec.extractLsb' 4 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 1 (by decide)
  have hdzero2 : BitVec.extractLsb' 8 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 2 (by decide)
  have hdzero3 : BitVec.extractLsb' 12 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 3 (by decide)
  have hdzero4 : BitVec.extractLsb' 16 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 4 (by decide)
  have hdzero5 : BitVec.extractLsb' 20 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 5 (by decide)
  bv_decide

theorem incompatible_6_7 : NoCompatibleMiddleWord 6 7 := by
  intro c hc
  have hr := hc.1
  have hd := hc.2
  have hri : BitVec.extractLsb' 24 4 (c.rotateRight 11) ≠ 0#4 := by
    intro hz
    apply hr.2
    change (BitVec.extractLsb' 24 4 (c.rotateRight 11)).toFin = 0
    rw [hz]
    rfl
  have hdj : BitVec.extractLsb' 28 4 c ≠ 0#4 := by
    intro hz
    apply hd.2
    change (BitVec.extractLsb' 28 4 c).toFin = 0
    rw [hz]
    rfl
  have hrzero0 : BitVec.extractLsb' 0 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 0 (by decide)
  have hrzero1 : BitVec.extractLsb' 4 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 1 (by decide)
  have hrzero2 : BitVec.extractLsb' 8 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 2 (by decide)
  have hrzero3 : BitVec.extractLsb' 12 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 3 (by decide)
  have hrzero4 : BitVec.extractLsb' 16 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 4 (by decide)
  have hrzero5 : BitVec.extractLsb' 20 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 5 (by decide)
  have hdzero0 : BitVec.extractLsb' 0 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 0 (by decide)
  have hdzero1 : BitVec.extractLsb' 4 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 1 (by decide)
  have hdzero2 : BitVec.extractLsb' 8 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 2 (by decide)
  have hdzero3 : BitVec.extractLsb' 12 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 3 (by decide)
  have hdzero4 : BitVec.extractLsb' 16 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 4 (by decide)
  have hdzero5 : BitVec.extractLsb' 20 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 5 (by decide)
  have hdzero6 : BitVec.extractLsb' 24 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 6 (by decide)
  bv_decide

theorem incompatible_7_0 : NoCompatibleMiddleWord 7 0 := by
  intro c hc
  have hr := hc.1
  have hd := hc.2
  have hri : BitVec.extractLsb' 28 4 (c.rotateRight 11) ≠ 0#4 := by
    intro hz
    apply hr.2
    change (BitVec.extractLsb' 28 4 (c.rotateRight 11)).toFin = 0
    rw [hz]
    rfl
  have hdj : BitVec.extractLsb' 0 4 c ≠ 0#4 := by
    intro hz
    apply hd.2
    change (BitVec.extractLsb' 0 4 c).toFin = 0
    rw [hz]
    rfl
  have hrzero0 : BitVec.extractLsb' 0 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 0 (by decide)
  have hrzero1 : BitVec.extractLsb' 4 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 1 (by decide)
  have hrzero2 : BitVec.extractLsb' 8 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 2 (by decide)
  have hrzero3 : BitVec.extractLsb' 12 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 3 (by decide)
  have hrzero4 : BitVec.extractLsb' 16 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 4 (by decide)
  have hrzero5 : BitVec.extractLsb' 20 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 5 (by decide)
  have hrzero6 : BitVec.extractLsb' 24 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 6 (by decide)
  bv_decide

theorem incompatible_7_3 : NoCompatibleMiddleWord 7 3 := by
  intro c hc
  have hr := hc.1
  have hd := hc.2
  have hri : BitVec.extractLsb' 28 4 (c.rotateRight 11) ≠ 0#4 := by
    intro hz
    apply hr.2
    change (BitVec.extractLsb' 28 4 (c.rotateRight 11)).toFin = 0
    rw [hz]
    rfl
  have hdj : BitVec.extractLsb' 12 4 c ≠ 0#4 := by
    intro hz
    apply hd.2
    change (BitVec.extractLsb' 12 4 c).toFin = 0
    rw [hz]
    rfl
  have hrzero0 : BitVec.extractLsb' 0 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 0 (by decide)
  have hrzero1 : BitVec.extractLsb' 4 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 1 (by decide)
  have hrzero2 : BitVec.extractLsb' 8 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 2 (by decide)
  have hrzero3 : BitVec.extractLsb' 12 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 3 (by decide)
  have hrzero4 : BitVec.extractLsb' 16 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 4 (by decide)
  have hrzero5 : BitVec.extractLsb' 20 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 5 (by decide)
  have hrzero6 : BitVec.extractLsb' 24 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 6 (by decide)
  have hdzero0 : BitVec.extractLsb' 0 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 0 (by decide)
  have hdzero1 : BitVec.extractLsb' 4 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 1 (by decide)
  have hdzero2 : BitVec.extractLsb' 8 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 2 (by decide)
  bv_decide

theorem incompatible_7_4 : NoCompatibleMiddleWord 7 4 := by
  intro c hc
  have hr := hc.1
  have hd := hc.2
  have hri : BitVec.extractLsb' 28 4 (c.rotateRight 11) ≠ 0#4 := by
    intro hz
    apply hr.2
    change (BitVec.extractLsb' 28 4 (c.rotateRight 11)).toFin = 0
    rw [hz]
    rfl
  have hdj : BitVec.extractLsb' 16 4 c ≠ 0#4 := by
    intro hz
    apply hd.2
    change (BitVec.extractLsb' 16 4 c).toFin = 0
    rw [hz]
    rfl
  have hrzero0 : BitVec.extractLsb' 0 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 0 (by decide)
  have hrzero1 : BitVec.extractLsb' 4 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 1 (by decide)
  have hrzero2 : BitVec.extractLsb' 8 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 2 (by decide)
  have hrzero3 : BitVec.extractLsb' 12 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 3 (by decide)
  have hrzero4 : BitVec.extractLsb' 16 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 4 (by decide)
  have hrzero5 : BitVec.extractLsb' 20 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 5 (by decide)
  have hrzero6 : BitVec.extractLsb' 24 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 6 (by decide)
  have hdzero0 : BitVec.extractLsb' 0 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 0 (by decide)
  have hdzero1 : BitVec.extractLsb' 4 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 1 (by decide)
  have hdzero2 : BitVec.extractLsb' 8 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 2 (by decide)
  have hdzero3 : BitVec.extractLsb' 12 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 3 (by decide)
  bv_decide

theorem incompatible_7_5 : NoCompatibleMiddleWord 7 5 := by
  intro c hc
  have hr := hc.1
  have hd := hc.2
  have hri : BitVec.extractLsb' 28 4 (c.rotateRight 11) ≠ 0#4 := by
    intro hz
    apply hr.2
    change (BitVec.extractLsb' 28 4 (c.rotateRight 11)).toFin = 0
    rw [hz]
    rfl
  have hdj : BitVec.extractLsb' 20 4 c ≠ 0#4 := by
    intro hz
    apply hd.2
    change (BitVec.extractLsb' 20 4 c).toFin = 0
    rw [hz]
    rfl
  have hrzero0 : BitVec.extractLsb' 0 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 0 (by decide)
  have hrzero1 : BitVec.extractLsb' 4 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 1 (by decide)
  have hrzero2 : BitVec.extractLsb' 8 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 2 (by decide)
  have hrzero3 : BitVec.extractLsb' 12 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 3 (by decide)
  have hrzero4 : BitVec.extractLsb' 16 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 4 (by decide)
  have hrzero5 : BitVec.extractLsb' 20 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 5 (by decide)
  have hrzero6 : BitVec.extractLsb' 24 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 6 (by decide)
  have hdzero0 : BitVec.extractLsb' 0 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 0 (by decide)
  have hdzero1 : BitVec.extractLsb' 4 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 1 (by decide)
  have hdzero2 : BitVec.extractLsb' 8 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 2 (by decide)
  have hdzero3 : BitVec.extractLsb' 12 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 3 (by decide)
  have hdzero4 : BitVec.extractLsb' 16 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 4 (by decide)
  bv_decide

theorem incompatible_7_6 : NoCompatibleMiddleWord 7 6 := by
  intro c hc
  have hr := hc.1
  have hd := hc.2
  have hri : BitVec.extractLsb' 28 4 (c.rotateRight 11) ≠ 0#4 := by
    intro hz
    apply hr.2
    change (BitVec.extractLsb' 28 4 (c.rotateRight 11)).toFin = 0
    rw [hz]
    rfl
  have hdj : BitVec.extractLsb' 24 4 c ≠ 0#4 := by
    intro hz
    apply hd.2
    change (BitVec.extractLsb' 24 4 c).toFin = 0
    rw [hz]
    rfl
  have hrzero0 : BitVec.extractLsb' 0 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 0 (by decide)
  have hrzero1 : BitVec.extractLsb' 4 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 1 (by decide)
  have hrzero2 : BitVec.extractLsb' 8 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 2 (by decide)
  have hrzero3 : BitVec.extractLsb' 12 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 3 (by decide)
  have hrzero4 : BitVec.extractLsb' 16 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 4 (by decide)
  have hrzero5 : BitVec.extractLsb' 20 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 5 (by decide)
  have hrzero6 : BitVec.extractLsb' 24 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 6 (by decide)
  have hdzero0 : BitVec.extractLsb' 0 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 0 (by decide)
  have hdzero1 : BitVec.extractLsb' 4 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 1 (by decide)
  have hdzero2 : BitVec.extractLsb' 8 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 2 (by decide)
  have hdzero3 : BitVec.extractLsb' 12 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 3 (by decide)
  have hdzero4 : BitVec.extractLsb' 16 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 4 (by decide)
  have hdzero5 : BitVec.extractLsb' 20 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 5 (by decide)
  bv_decide

theorem incompatible_7_7 : NoCompatibleMiddleWord 7 7 := by
  intro c hc
  have hr := hc.1
  have hd := hc.2
  have hri : BitVec.extractLsb' 28 4 (c.rotateRight 11) ≠ 0#4 := by
    intro hz
    apply hr.2
    change (BitVec.extractLsb' 28 4 (c.rotateRight 11)).toFin = 0
    rw [hz]
    rfl
  have hdj : BitVec.extractLsb' 28 4 c ≠ 0#4 := by
    intro hz
    apply hd.2
    change (BitVec.extractLsb' 28 4 c).toFin = 0
    rw [hz]
    rfl
  have hrzero0 : BitVec.extractLsb' 0 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 0 (by decide)
  have hrzero1 : BitVec.extractLsb' 4 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 1 (by decide)
  have hrzero2 : BitVec.extractLsb' 8 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 2 (by decide)
  have hrzero3 : BitVec.extractLsb' 12 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 3 (by decide)
  have hrzero4 : BitVec.extractLsb' 16 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 4 (by decide)
  have hrzero5 : BitVec.extractLsb' 20 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 5 (by decide)
  have hrzero6 : BitVec.extractLsb' 24 4 (c.rotateRight 11) = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hr.1 6 (by decide)
  have hdzero0 : BitVec.extractLsb' 0 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 0 (by decide)
  have hdzero1 : BitVec.extractLsb' 4 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 1 (by decide)
  have hdzero2 : BitVec.extractLsb' 8 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 2 (by decide)
  have hdzero3 : BitVec.extractLsb' 12 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 3 (by decide)
  have hdzero4 : BitVec.extractLsb' 16 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 4 (by decide)
  have hdzero5 : BitVec.extractLsb' 20 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 5 (by decide)
  have hdzero6 : BitVec.extractLsb' 24 4 c = 0#4 := by
    apply BitVec.eq_of_toFin_eq
    exact hd.1 6 (by decide)
  bv_decide


/-- Finite structural blacklist for the first-nibble indices. -/
def BadIndex (i j : Fin 8) : Prop :=
  (i = 0 ∧ j = 4)
    ∨ (i = 0 ∧ j = 5)
    ∨ (i = 0 ∧ j = 6)
    ∨ (i = 0 ∧ j = 7)
    ∨ (i = 1 ∧ j = 5)
    ∨ (i = 1 ∧ j = 6)
    ∨ (i = 1 ∧ j = 7)
    ∨ (i = 2 ∧ j = 3)
    ∨ (i = 2 ∧ j = 6)
    ∨ (i = 2 ∧ j = 7)
    ∨ (i = 3 ∧ j = 3)
    ∨ (i = 3 ∧ j = 4)
    ∨ (i = 3 ∧ j = 7)
    ∨ (i = 4 ∧ j = 3)
    ∨ (i = 4 ∧ j = 4)
    ∨ (i = 4 ∧ j = 5)
    ∨ (i = 5 ∧ j = 3)
    ∨ (i = 5 ∧ j = 4)
    ∨ (i = 5 ∧ j = 5)
    ∨ (i = 5 ∧ j = 6)
    ∨ (i = 6 ∧ j = 2)
    ∨ (i = 6 ∧ j = 3)
    ∨ (i = 6 ∧ j = 4)
    ∨ (i = 6 ∧ j = 5)
    ∨ (i = 6 ∧ j = 6)
    ∨ (i = 6 ∧ j = 7)
    ∨ (i = 7 ∧ j = 0)
    ∨ (i = 7 ∧ j = 3)
    ∨ (i = 7 ∧ j = 4)
    ∨ (i = 7 ∧ j = 5)
    ∨ (i = 7 ∧ j = 6)
    ∨ (i = 7 ∧ j = 7)

/-- All forbidden index pairs have kernel-checked bit-vector certificates. -/
theorem noCompatible_of_badIndex (i j : Fin 8) (h : BadIndex i j) :
    NoCompatibleMiddleWord i j := by
  unfold BadIndex at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals rcases h with ⟨rfl, rfl⟩
  all_goals first
    | exact incompatible_0_4
    | exact incompatible_0_5
    | exact incompatible_0_6
    | exact incompatible_0_7
    | exact incompatible_1_5
    | exact incompatible_1_6
    | exact incompatible_1_7
    | exact incompatible_2_3
    | exact incompatible_2_6
    | exact incompatible_2_7
    | exact incompatible_3_3
    | exact incompatible_3_4
    | exact incompatible_3_7
    | exact incompatible_4_3
    | exact incompatible_4_4
    | exact incompatible_4_5
    | exact incompatible_5_3
    | exact incompatible_5_4
    | exact incompatible_5_5
    | exact incompatible_5_6
    | exact incompatible_6_2
    | exact incompatible_6_3
    | exact incompatible_6_4
    | exact incompatible_6_5
    | exact incompatible_6_6
    | exact incompatible_6_7
    | exact incompatible_7_0
    | exact incompatible_7_3
    | exact incompatible_7_4
    | exact incompatible_7_5
    | exact incompatible_7_6
    | exact incompatible_7_7

/-- Certified second-stage five-round obstruction for any five key words. -/
theorem fiveRound_zero_of_badIndex
    (k₀ k₁ k₂ k₃ k₄ a s : Word) (i j : Fin 8)
    (ha : FirstActiveNibbleAt a i)
    (hm : FirstActiveNibbleAt ((Magma.xor s a).rotateRight 11) j)
    (hb : BadIndex i j) :
    Magma.MultiRoundDDT.xorDDT_rounds 5
      (Magma.DiffanFiveRoundCoreDefect.fiveRoundKeys k₀ k₁ k₂ k₃ k₄)
      (a, 0#32) (0#32, s) = 0 :=
  fiveRound_zero_of_no_compatible_middle k₀ k₁ k₂ k₃ k₄ a s i j
    ha hm (noCompatible_of_badIndex i j hb)

end Magma.DiffanNibblePairCertificates
