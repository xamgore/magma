module

import all Init.Data.Range.Basic
public import Magma.Differential.TwoRounds.TwoRoundRawOutputMasks
import Std.Tactic.BVDecide

@[expose] public section

/-!
# Automatically extracted guaranteed output masks for Magma g[k]

This is a sound, nibble-granularity, structure-aware extractor. It selects
the largest *prefix of complete untouched input nibbles* and rotates its
mask left by eleven. Global maximality for a direction additionally requires counterexample
witnesses for every omitted bit. For direction 0x00006000 a separate finite certificate
below proves that the structurally obtained mask really is optimal.

-/

namespace Magma.DifanAutomaticOutputMasks

open Magma Magma.Internal Magma.GProperties

private abbrev Word :=
  V 32

/-- Low 0 bit mask, including the empty/full cases. -/
private def low0 : Word := 0x00000000#32

/-- Rotation of low0, the output observation corresponding to that prefix. -/
private def out0 : Word := 0x00000000#32

/-- Low 4 bit mask, including the empty/full cases. -/
private def low1 : Word := 0x0000000F#32

/-- Rotation of low1, the output observation corresponding to that prefix. -/
private def out1 : Word := 0x00007800#32

/-- Low 8 bit mask, including the empty/full cases. -/
private def low2 : Word := 0x000000FF#32

/-- Rotation of low2, the output observation corresponding to that prefix. -/
private def out2 : Word := 0x0007F800#32

/-- Low 12 bit mask, including the empty/full cases. -/
private def low3 : Word := 0x00000FFF#32

/-- Rotation of low3, the output observation corresponding to that prefix. -/
private def out3 : Word := 0x007FF800#32

/-- Low 16 bit mask, including the empty/full cases. -/
private def low4 : Word := 0x0000FFFF#32

/-- Rotation of low4, the output observation corresponding to that prefix. -/
private def out4 : Word := 0x07FFF800#32

/-- Low 20 bit mask, including the empty/full cases. -/
private def low5 : Word := 0x000FFFFF#32

/-- Rotation of low5, the output observation corresponding to that prefix. -/
private def out5 : Word := 0x7FFFF800#32

/-- Low 24 bit mask, including the empty/full cases. -/
private def low6 : Word := 0x00FFFFFF#32

/-- Rotation of low6, the output observation corresponding to that prefix. -/
private def out6 : Word := 0xFFFFF807#32

/-- Low 28 bit mask, including the empty/full cases. -/
private def low7 : Word := 0x0FFFFFFF#32

/-- Rotation of low7, the output observation corresponding to that prefix. -/
private def out7 : Word := 0xFFFFF87F#32

/-- Low 32 bit mask, including the empty/full cases. -/
private def low8 : Word := 0xFFFFFFFF#32

/-- Rotation of low8, the output observation corresponding to that prefix. -/
private def out8 : Word := 0xFFFFFFFF#32

/-- Structural extractor: choose the maximal consecutive set of untouched
low input nibbles, then rotate the corresponding mask by 11 positions.
It is an underapproximation of globally invariant output bits. -/
def guaranteedMask (s : Word) : Word :=
  if s = 0#32 then out8
  else if (s &&& low7) = 0#32 then out7
  else if (s &&& low6) = 0#32 then out6
  else if (s &&& low5) = 0#32 then out5
  else if (s &&& low4) = 0#32 then out4
  else if (s &&& low3) = 0#32 then out3
  else if (s &&& low2) = 0#32 then out2
  else if (s &&& low1) = 0#32 then out1
  else out0

/-- The machine-word addition agrees with Magma's modular shift. -/
private theorem modShift_eq_add (k x : Word) : modShift k x = x + k := by
  apply BitVec.eq_of_toNat_eq
  rw [Magma.CarryAutomaton.modShift_toNat_bridge, BitVec.toNat_add]
  simp only [show (16 : Nat) ^ 8 = 2 ^ 32 from by decide]

/-- S-box independence on the lowest 1 nibbles. -/
private theorem substitution_low1 (u v : Word)
    (h : (u &&& low1) = (v &&& low1)) :
    (Magma.t u &&& low1) = (Magma.t v &&& low1) := by
  unfold low1 at *
  have hi0 : nibble u (0 : Fin 8) = nibble v (0 : Fin 8) := by
    change BitVec.extractLsb' 0 4 u = BitVec.extractLsb' 0 4 v
    bv_decide
  have ho0 : nibble (Magma.t u) (0 : Fin 8) =
      nibble (Magma.t v) (0 : Fin 8) := by
    simpa only [t_substitutes_components] using
      congrArg (π (0 : Fin 8)) hi0
  change BitVec.extractLsb' 0 4 (Magma.t u) =
    BitVec.extractLsb' 0 4 (Magma.t v) at ho0
  bv_decide

/-- Guaranteed conservation of the 4-bit nibble prefix of g[k]. -/
private theorem g_low1_safe (k x s : Word)
    (hs : (s &&& low1) = 0#32) :
    (g k (x ^^^ s) &&& out1) = (g k x &&& out1) := by
  have ha : (((x ^^^ s) + k) &&& low1) =
      ((x + k) &&& low1) := by
    unfold low1 at *
    bv_decide
  have hb := substitution_low1 ((x ^^^ s) + k) (x + k) ha
  have hc :
      ((Magma.t ((x ^^^ s) + k)).rotateLeft 11 &&& out1) =
        ((Magma.t (x + k)).rotateLeft 11 &&& out1) := by
    unfold low1 out1 at *
    bv_decide
  simpa only [g_as_modShift, modShift_eq_add, rot11] using hc

/-- S-box independence on the lowest 2 nibbles. -/
private theorem substitution_low2 (u v : Word)
    (h : (u &&& low2) = (v &&& low2)) :
    (Magma.t u &&& low2) = (Magma.t v &&& low2) := by
  unfold low2 at *
  have hi0 : nibble u (0 : Fin 8) = nibble v (0 : Fin 8) := by
    change BitVec.extractLsb' 0 4 u = BitVec.extractLsb' 0 4 v
    bv_decide
  have ho0 : nibble (Magma.t u) (0 : Fin 8) =
      nibble (Magma.t v) (0 : Fin 8) := by
    simpa only [t_substitutes_components] using
      congrArg (π (0 : Fin 8)) hi0
  change BitVec.extractLsb' 0 4 (Magma.t u) =
    BitVec.extractLsb' 0 4 (Magma.t v) at ho0
  have hi1 : nibble u (1 : Fin 8) = nibble v (1 : Fin 8) := by
    change BitVec.extractLsb' 4 4 u = BitVec.extractLsb' 4 4 v
    bv_decide
  have ho1 : nibble (Magma.t u) (1 : Fin 8) =
      nibble (Magma.t v) (1 : Fin 8) := by
    simpa only [t_substitutes_components] using
      congrArg (π (1 : Fin 8)) hi1
  change BitVec.extractLsb' 4 4 (Magma.t u) =
    BitVec.extractLsb' 4 4 (Magma.t v) at ho1
  bv_decide

/-- Guaranteed conservation of the 8-bit nibble prefix of g[k]. -/
private theorem g_low2_safe (k x s : Word)
    (hs : (s &&& low2) = 0#32) :
    (g k (x ^^^ s) &&& out2) = (g k x &&& out2) := by
  have ha : (((x ^^^ s) + k) &&& low2) =
      ((x + k) &&& low2) := by
    unfold low2 at *
    bv_decide
  have hb := substitution_low2 ((x ^^^ s) + k) (x + k) ha
  have hc :
      ((Magma.t ((x ^^^ s) + k)).rotateLeft 11 &&& out2) =
        ((Magma.t (x + k)).rotateLeft 11 &&& out2) := by
    unfold low2 out2 at *
    bv_decide
  simpa only [g_as_modShift, modShift_eq_add, rot11] using hc

/-- S-box independence on the lowest 3 nibbles. -/
private theorem substitution_low3 (u v : Word)
    (h : (u &&& low3) = (v &&& low3)) :
    (Magma.t u &&& low3) = (Magma.t v &&& low3) := by
  unfold low3 at *
  have hi0 : nibble u (0 : Fin 8) = nibble v (0 : Fin 8) := by
    change BitVec.extractLsb' 0 4 u = BitVec.extractLsb' 0 4 v
    bv_decide
  have ho0 : nibble (Magma.t u) (0 : Fin 8) =
      nibble (Magma.t v) (0 : Fin 8) := by
    simpa only [t_substitutes_components] using
      congrArg (π (0 : Fin 8)) hi0
  change BitVec.extractLsb' 0 4 (Magma.t u) =
    BitVec.extractLsb' 0 4 (Magma.t v) at ho0
  have hi1 : nibble u (1 : Fin 8) = nibble v (1 : Fin 8) := by
    change BitVec.extractLsb' 4 4 u = BitVec.extractLsb' 4 4 v
    bv_decide
  have ho1 : nibble (Magma.t u) (1 : Fin 8) =
      nibble (Magma.t v) (1 : Fin 8) := by
    simpa only [t_substitutes_components] using
      congrArg (π (1 : Fin 8)) hi1
  change BitVec.extractLsb' 4 4 (Magma.t u) =
    BitVec.extractLsb' 4 4 (Magma.t v) at ho1
  have hi2 : nibble u (2 : Fin 8) = nibble v (2 : Fin 8) := by
    change BitVec.extractLsb' 8 4 u = BitVec.extractLsb' 8 4 v
    bv_decide
  have ho2 : nibble (Magma.t u) (2 : Fin 8) =
      nibble (Magma.t v) (2 : Fin 8) := by
    simpa only [t_substitutes_components] using
      congrArg (π (2 : Fin 8)) hi2
  change BitVec.extractLsb' 8 4 (Magma.t u) =
    BitVec.extractLsb' 8 4 (Magma.t v) at ho2
  bv_decide

/-- Guaranteed conservation of the 12-bit nibble prefix of g[k]. -/
private theorem g_low3_safe (k x s : Word)
    (hs : (s &&& low3) = 0#32) :
    (g k (x ^^^ s) &&& out3) = (g k x &&& out3) := by
  have ha : (((x ^^^ s) + k) &&& low3) =
      ((x + k) &&& low3) := by
    unfold low3 at *
    bv_decide
  have hb := substitution_low3 ((x ^^^ s) + k) (x + k) ha
  have hc :
      ((Magma.t ((x ^^^ s) + k)).rotateLeft 11 &&& out3) =
        ((Magma.t (x + k)).rotateLeft 11 &&& out3) := by
    unfold low3 out3 at *
    bv_decide
  simpa only [g_as_modShift, modShift_eq_add, rot11] using hc

/-- S-box independence on the lowest 4 nibbles. -/
private theorem substitution_low4 (u v : Word)
    (h : (u &&& low4) = (v &&& low4)) :
    (Magma.t u &&& low4) = (Magma.t v &&& low4) := by
  unfold low4 at *
  have hi0 : nibble u (0 : Fin 8) = nibble v (0 : Fin 8) := by
    change BitVec.extractLsb' 0 4 u = BitVec.extractLsb' 0 4 v
    bv_decide
  have ho0 : nibble (Magma.t u) (0 : Fin 8) =
      nibble (Magma.t v) (0 : Fin 8) := by
    simpa only [t_substitutes_components] using
      congrArg (π (0 : Fin 8)) hi0
  change BitVec.extractLsb' 0 4 (Magma.t u) =
    BitVec.extractLsb' 0 4 (Magma.t v) at ho0
  have hi1 : nibble u (1 : Fin 8) = nibble v (1 : Fin 8) := by
    change BitVec.extractLsb' 4 4 u = BitVec.extractLsb' 4 4 v
    bv_decide
  have ho1 : nibble (Magma.t u) (1 : Fin 8) =
      nibble (Magma.t v) (1 : Fin 8) := by
    simpa only [t_substitutes_components] using
      congrArg (π (1 : Fin 8)) hi1
  change BitVec.extractLsb' 4 4 (Magma.t u) =
    BitVec.extractLsb' 4 4 (Magma.t v) at ho1
  have hi2 : nibble u (2 : Fin 8) = nibble v (2 : Fin 8) := by
    change BitVec.extractLsb' 8 4 u = BitVec.extractLsb' 8 4 v
    bv_decide
  have ho2 : nibble (Magma.t u) (2 : Fin 8) =
      nibble (Magma.t v) (2 : Fin 8) := by
    simpa only [t_substitutes_components] using
      congrArg (π (2 : Fin 8)) hi2
  change BitVec.extractLsb' 8 4 (Magma.t u) =
    BitVec.extractLsb' 8 4 (Magma.t v) at ho2
  have hi3 : nibble u (3 : Fin 8) = nibble v (3 : Fin 8) := by
    change BitVec.extractLsb' 12 4 u = BitVec.extractLsb' 12 4 v
    bv_decide
  have ho3 : nibble (Magma.t u) (3 : Fin 8) =
      nibble (Magma.t v) (3 : Fin 8) := by
    simpa only [t_substitutes_components] using
      congrArg (π (3 : Fin 8)) hi3
  change BitVec.extractLsb' 12 4 (Magma.t u) =
    BitVec.extractLsb' 12 4 (Magma.t v) at ho3
  bv_decide

/-- Guaranteed conservation of the 16-bit nibble prefix of g[k]. -/
private theorem g_low4_safe (k x s : Word)
    (hs : (s &&& low4) = 0#32) :
    (g k (x ^^^ s) &&& out4) = (g k x &&& out4) := by
  have ha : (((x ^^^ s) + k) &&& low4) =
      ((x + k) &&& low4) := by
    unfold low4 at *
    bv_decide
  have hb := substitution_low4 ((x ^^^ s) + k) (x + k) ha
  have hc :
      ((Magma.t ((x ^^^ s) + k)).rotateLeft 11 &&& out4) =
        ((Magma.t (x + k)).rotateLeft 11 &&& out4) := by
    unfold low4 out4 at *
    bv_decide
  simpa only [g_as_modShift, modShift_eq_add, rot11] using hc

/-- S-box independence on the lowest 5 nibbles. -/
private theorem substitution_low5 (u v : Word)
    (h : (u &&& low5) = (v &&& low5)) :
    (Magma.t u &&& low5) = (Magma.t v &&& low5) := by
  unfold low5 at *
  have hi0 : nibble u (0 : Fin 8) = nibble v (0 : Fin 8) := by
    change BitVec.extractLsb' 0 4 u = BitVec.extractLsb' 0 4 v
    bv_decide
  have ho0 : nibble (Magma.t u) (0 : Fin 8) =
      nibble (Magma.t v) (0 : Fin 8) := by
    simpa only [t_substitutes_components] using
      congrArg (π (0 : Fin 8)) hi0
  change BitVec.extractLsb' 0 4 (Magma.t u) =
    BitVec.extractLsb' 0 4 (Magma.t v) at ho0
  have hi1 : nibble u (1 : Fin 8) = nibble v (1 : Fin 8) := by
    change BitVec.extractLsb' 4 4 u = BitVec.extractLsb' 4 4 v
    bv_decide
  have ho1 : nibble (Magma.t u) (1 : Fin 8) =
      nibble (Magma.t v) (1 : Fin 8) := by
    simpa only [t_substitutes_components] using
      congrArg (π (1 : Fin 8)) hi1
  change BitVec.extractLsb' 4 4 (Magma.t u) =
    BitVec.extractLsb' 4 4 (Magma.t v) at ho1
  have hi2 : nibble u (2 : Fin 8) = nibble v (2 : Fin 8) := by
    change BitVec.extractLsb' 8 4 u = BitVec.extractLsb' 8 4 v
    bv_decide
  have ho2 : nibble (Magma.t u) (2 : Fin 8) =
      nibble (Magma.t v) (2 : Fin 8) := by
    simpa only [t_substitutes_components] using
      congrArg (π (2 : Fin 8)) hi2
  change BitVec.extractLsb' 8 4 (Magma.t u) =
    BitVec.extractLsb' 8 4 (Magma.t v) at ho2
  have hi3 : nibble u (3 : Fin 8) = nibble v (3 : Fin 8) := by
    change BitVec.extractLsb' 12 4 u = BitVec.extractLsb' 12 4 v
    bv_decide
  have ho3 : nibble (Magma.t u) (3 : Fin 8) =
      nibble (Magma.t v) (3 : Fin 8) := by
    simpa only [t_substitutes_components] using
      congrArg (π (3 : Fin 8)) hi3
  change BitVec.extractLsb' 12 4 (Magma.t u) =
    BitVec.extractLsb' 12 4 (Magma.t v) at ho3
  have hi4 : nibble u (4 : Fin 8) = nibble v (4 : Fin 8) := by
    change BitVec.extractLsb' 16 4 u = BitVec.extractLsb' 16 4 v
    bv_decide
  have ho4 : nibble (Magma.t u) (4 : Fin 8) =
      nibble (Magma.t v) (4 : Fin 8) := by
    simpa only [t_substitutes_components] using
      congrArg (π (4 : Fin 8)) hi4
  change BitVec.extractLsb' 16 4 (Magma.t u) =
    BitVec.extractLsb' 16 4 (Magma.t v) at ho4
  bv_decide

/-- Guaranteed conservation of the 20-bit nibble prefix of g[k]. -/
private theorem g_low5_safe (k x s : Word)
    (hs : (s &&& low5) = 0#32) :
    (g k (x ^^^ s) &&& out5) = (g k x &&& out5) := by
  have ha : (((x ^^^ s) + k) &&& low5) =
      ((x + k) &&& low5) := by
    unfold low5 at *
    bv_decide
  have hb := substitution_low5 ((x ^^^ s) + k) (x + k) ha
  have hc :
      ((Magma.t ((x ^^^ s) + k)).rotateLeft 11 &&& out5) =
        ((Magma.t (x + k)).rotateLeft 11 &&& out5) := by
    unfold low5 out5 at *
    bv_decide
  simpa only [g_as_modShift, modShift_eq_add, rot11] using hc

/-- S-box independence on the lowest 6 nibbles. -/
private theorem substitution_low6 (u v : Word)
    (h : (u &&& low6) = (v &&& low6)) :
    (Magma.t u &&& low6) = (Magma.t v &&& low6) := by
  unfold low6 at *
  have hi0 : nibble u (0 : Fin 8) = nibble v (0 : Fin 8) := by
    change BitVec.extractLsb' 0 4 u = BitVec.extractLsb' 0 4 v
    bv_decide
  have ho0 : nibble (Magma.t u) (0 : Fin 8) =
      nibble (Magma.t v) (0 : Fin 8) := by
    simpa only [t_substitutes_components] using
      congrArg (π (0 : Fin 8)) hi0
  change BitVec.extractLsb' 0 4 (Magma.t u) =
    BitVec.extractLsb' 0 4 (Magma.t v) at ho0
  have hi1 : nibble u (1 : Fin 8) = nibble v (1 : Fin 8) := by
    change BitVec.extractLsb' 4 4 u = BitVec.extractLsb' 4 4 v
    bv_decide
  have ho1 : nibble (Magma.t u) (1 : Fin 8) =
      nibble (Magma.t v) (1 : Fin 8) := by
    simpa only [t_substitutes_components] using
      congrArg (π (1 : Fin 8)) hi1
  change BitVec.extractLsb' 4 4 (Magma.t u) =
    BitVec.extractLsb' 4 4 (Magma.t v) at ho1
  have hi2 : nibble u (2 : Fin 8) = nibble v (2 : Fin 8) := by
    change BitVec.extractLsb' 8 4 u = BitVec.extractLsb' 8 4 v
    bv_decide
  have ho2 : nibble (Magma.t u) (2 : Fin 8) =
      nibble (Magma.t v) (2 : Fin 8) := by
    simpa only [t_substitutes_components] using
      congrArg (π (2 : Fin 8)) hi2
  change BitVec.extractLsb' 8 4 (Magma.t u) =
    BitVec.extractLsb' 8 4 (Magma.t v) at ho2
  have hi3 : nibble u (3 : Fin 8) = nibble v (3 : Fin 8) := by
    change BitVec.extractLsb' 12 4 u = BitVec.extractLsb' 12 4 v
    bv_decide
  have ho3 : nibble (Magma.t u) (3 : Fin 8) =
      nibble (Magma.t v) (3 : Fin 8) := by
    simpa only [t_substitutes_components] using
      congrArg (π (3 : Fin 8)) hi3
  change BitVec.extractLsb' 12 4 (Magma.t u) =
    BitVec.extractLsb' 12 4 (Magma.t v) at ho3
  have hi4 : nibble u (4 : Fin 8) = nibble v (4 : Fin 8) := by
    change BitVec.extractLsb' 16 4 u = BitVec.extractLsb' 16 4 v
    bv_decide
  have ho4 : nibble (Magma.t u) (4 : Fin 8) =
      nibble (Magma.t v) (4 : Fin 8) := by
    simpa only [t_substitutes_components] using
      congrArg (π (4 : Fin 8)) hi4
  change BitVec.extractLsb' 16 4 (Magma.t u) =
    BitVec.extractLsb' 16 4 (Magma.t v) at ho4
  have hi5 : nibble u (5 : Fin 8) = nibble v (5 : Fin 8) := by
    change BitVec.extractLsb' 20 4 u = BitVec.extractLsb' 20 4 v
    bv_decide
  have ho5 : nibble (Magma.t u) (5 : Fin 8) =
      nibble (Magma.t v) (5 : Fin 8) := by
    simpa only [t_substitutes_components] using
      congrArg (π (5 : Fin 8)) hi5
  change BitVec.extractLsb' 20 4 (Magma.t u) =
    BitVec.extractLsb' 20 4 (Magma.t v) at ho5
  bv_decide

/-- Guaranteed conservation of the 24-bit nibble prefix of g[k]. -/
private theorem g_low6_safe (k x s : Word)
    (hs : (s &&& low6) = 0#32) :
    (g k (x ^^^ s) &&& out6) = (g k x &&& out6) := by
  have ha : (((x ^^^ s) + k) &&& low6) =
      ((x + k) &&& low6) := by
    unfold low6 at *
    bv_decide
  have hb := substitution_low6 ((x ^^^ s) + k) (x + k) ha
  have hc :
      ((Magma.t ((x ^^^ s) + k)).rotateLeft 11 &&& out6) =
        ((Magma.t (x + k)).rotateLeft 11 &&& out6) := by
    unfold low6 out6 at *
    bv_decide
  simpa only [g_as_modShift, modShift_eq_add, rot11] using hc

/-- S-box independence on the lowest 7 nibbles. -/
private theorem substitution_low7 (u v : Word)
    (h : (u &&& low7) = (v &&& low7)) :
    (Magma.t u &&& low7) = (Magma.t v &&& low7) := by
  unfold low7 at *
  have hi0 : nibble u (0 : Fin 8) = nibble v (0 : Fin 8) := by
    change BitVec.extractLsb' 0 4 u = BitVec.extractLsb' 0 4 v
    bv_decide
  have ho0 : nibble (Magma.t u) (0 : Fin 8) =
      nibble (Magma.t v) (0 : Fin 8) := by
    simpa only [t_substitutes_components] using
      congrArg (π (0 : Fin 8)) hi0
  change BitVec.extractLsb' 0 4 (Magma.t u) =
    BitVec.extractLsb' 0 4 (Magma.t v) at ho0
  have hi1 : nibble u (1 : Fin 8) = nibble v (1 : Fin 8) := by
    change BitVec.extractLsb' 4 4 u = BitVec.extractLsb' 4 4 v
    bv_decide
  have ho1 : nibble (Magma.t u) (1 : Fin 8) =
      nibble (Magma.t v) (1 : Fin 8) := by
    simpa only [t_substitutes_components] using
      congrArg (π (1 : Fin 8)) hi1
  change BitVec.extractLsb' 4 4 (Magma.t u) =
    BitVec.extractLsb' 4 4 (Magma.t v) at ho1
  have hi2 : nibble u (2 : Fin 8) = nibble v (2 : Fin 8) := by
    change BitVec.extractLsb' 8 4 u = BitVec.extractLsb' 8 4 v
    bv_decide
  have ho2 : nibble (Magma.t u) (2 : Fin 8) =
      nibble (Magma.t v) (2 : Fin 8) := by
    simpa only [t_substitutes_components] using
      congrArg (π (2 : Fin 8)) hi2
  change BitVec.extractLsb' 8 4 (Magma.t u) =
    BitVec.extractLsb' 8 4 (Magma.t v) at ho2
  have hi3 : nibble u (3 : Fin 8) = nibble v (3 : Fin 8) := by
    change BitVec.extractLsb' 12 4 u = BitVec.extractLsb' 12 4 v
    bv_decide
  have ho3 : nibble (Magma.t u) (3 : Fin 8) =
      nibble (Magma.t v) (3 : Fin 8) := by
    simpa only [t_substitutes_components] using
      congrArg (π (3 : Fin 8)) hi3
  change BitVec.extractLsb' 12 4 (Magma.t u) =
    BitVec.extractLsb' 12 4 (Magma.t v) at ho3
  have hi4 : nibble u (4 : Fin 8) = nibble v (4 : Fin 8) := by
    change BitVec.extractLsb' 16 4 u = BitVec.extractLsb' 16 4 v
    bv_decide
  have ho4 : nibble (Magma.t u) (4 : Fin 8) =
      nibble (Magma.t v) (4 : Fin 8) := by
    simpa only [t_substitutes_components] using
      congrArg (π (4 : Fin 8)) hi4
  change BitVec.extractLsb' 16 4 (Magma.t u) =
    BitVec.extractLsb' 16 4 (Magma.t v) at ho4
  have hi5 : nibble u (5 : Fin 8) = nibble v (5 : Fin 8) := by
    change BitVec.extractLsb' 20 4 u = BitVec.extractLsb' 20 4 v
    bv_decide
  have ho5 : nibble (Magma.t u) (5 : Fin 8) =
      nibble (Magma.t v) (5 : Fin 8) := by
    simpa only [t_substitutes_components] using
      congrArg (π (5 : Fin 8)) hi5
  change BitVec.extractLsb' 20 4 (Magma.t u) =
    BitVec.extractLsb' 20 4 (Magma.t v) at ho5
  have hi6 : nibble u (6 : Fin 8) = nibble v (6 : Fin 8) := by
    change BitVec.extractLsb' 24 4 u = BitVec.extractLsb' 24 4 v
    bv_decide
  have ho6 : nibble (Magma.t u) (6 : Fin 8) =
      nibble (Magma.t v) (6 : Fin 8) := by
    simpa only [t_substitutes_components] using
      congrArg (π (6 : Fin 8)) hi6
  change BitVec.extractLsb' 24 4 (Magma.t u) =
    BitVec.extractLsb' 24 4 (Magma.t v) at ho6
  bv_decide

/-- Guaranteed conservation of the 28-bit nibble prefix of g[k]. -/
private theorem g_low7_safe (k x s : Word)
    (hs : (s &&& low7) = 0#32) :
    (g k (x ^^^ s) &&& out7) = (g k x &&& out7) := by
  have ha : (((x ^^^ s) + k) &&& low7) =
      ((x + k) &&& low7) := by
    unfold low7 at *
    bv_decide
  have hb := substitution_low7 ((x ^^^ s) + k) (x + k) ha
  have hc :
      ((Magma.t ((x ^^^ s) + k)).rotateLeft 11 &&& out7) =
        ((Magma.t (x + k)).rotateLeft 11 &&& out7) := by
    unfold low7 out7 at *
    bv_decide
  simpa only [g_as_modShift, modShift_eq_add, rot11] using hc

/-- The extractor is sound for every 32-bit direction and every key. -/
theorem guaranteedMask_sound (k x s : Word) :
    (g k (x ^^^ s) &&& guaranteedMask s) =
      (g k x &&& guaranteedMask s) := by
  unfold guaranteedMask
  split_ifs with h0 h7 h6 h5 h4 h3 h2 h1
  · have hx : x ^^^ s = x := by bv_decide
    rw [hx]
  · exact g_low7_safe k x s h7
  · exact g_low6_safe k x s h6
  · exact g_low5_safe k x s h5
  · exact g_low4_safe k x s h4
  · exact g_low3_safe k x s h3
  · exact g_low2_safe k x s h2
  · exact g_low1_safe k x s h1
  · simp [out0]

/-- For 0x6000 the extractor returns the previously proved 12-bit mask. -/
theorem mask_6000_exact : guaranteedMask (0x00006000#32) =
    (0x007FF800#32) := by decide

/-- A bitwise fact: equal masked outputs give zero masked XOR difference. -/
private theorem masked_eq_xor_zero (u v m : Word)
    (h : (u &&& m) = (v &&& m)) :
    ((u ^^^ v) &&& m) = 0#32 := by bv_decide

/-- A bitwise fact: an invariant larger observation may be restricted to a
submask without losing invariance. -/
private theorem restrict_mask (u v mask small : Word)
    (h : (u &&& mask) = (v &&& mask))
    (hsub : (small &&& (~~~ mask)) = 0#32) :
    (u &&& small) = (v &&& small) := by bv_decide

/-- Counterexample certificate 1: concrete key and concrete base state. -/
private theorem witness0 :
    (g (0x00007000#32) ((0x7FFF8000#32) ^^^ (0x00006000#32)) ^^^
      g (0x00007000#32) (0x7FFF8000#32)) = 0xDF8003FA#32 := by decide

/-- Counterexample certificate 2: concrete key and concrete base state. -/
private theorem witness1 :
    (g (0x00001000#32) ((0x32EF9000#32) ^^^ (0x00006000#32)) ^^^
      g (0x00001000#32) (0x32EF9000#32)) = 0x5B000007#32 := by decide

/-- Counterexample certificate 3: concrete key and concrete base state. -/
private theorem witness2 :
    (g (0x00001000#32) ((0xDD0A9000#32) ^^^ (0x00006000#32)) ^^^
      g (0x00001000#32) (0xDD0A9000#32)) = 0x6B000000#32 := by decide

/-- Counterexample certificate 4: concrete key and concrete base state. -/
private theorem witness3 :
    (g (0xA4155000#32) ((0x4BEA8000#32) ^^^ (0x00006000#32)) ^^^
      g (0xA4155000#32) (0x4BEA8000#32)) = 0xDF8004FA#32 := by decide

/-- The four witnessed differences cover every bit outside the 12-bit
guaranteed mask. This certificate is only a 32-bit OR of four words. -/
private theorem witness_cover :
    ((0xDF8003FA#32) ||| (0x5B000007#32) ||| (0x6B000000#32) ||| (0xDF8004FA#32)) = (0xFF8007FF#32) := by decide

/-- No strictly larger output mask can be invariant under 0x6000 for
every master-independent round key and every base state. -/
theorem mask_6000_maximal (m : Word)
    (hm : ∀ k x : Word,
      (g k (x ^^^ (0x00006000#32)) &&& m) =
        (g k x &&& m)) :
    (m &&& (0xFF8007FF#32)) = 0#32 := by
  have h0 := masked_eq_xor_zero _ _ m (hm (0x00007000#32) (0x7FFF8000#32))
  rw [witness0] at h0
  have h1 := masked_eq_xor_zero _ _ m (hm (0x00001000#32) (0x32EF9000#32))
  rw [witness1] at h1
  have h2 := masked_eq_xor_zero _ _ m (hm (0x00001000#32) (0xDD0A9000#32))
  rw [witness2] at h2
  have h3 := masked_eq_xor_zero _ _ m (hm (0xA4155000#32) (0x4BEA8000#32))
  rw [witness3] at h3
  have hc := witness_cover
  -- Only Boolean algebra on four concrete 32-bit differences remains.
  bv_decide

/-- For the direction 0x6000, all universally invariant masks are
exactly the submasks of the automatically extracted mask. -/
theorem mask_6000_complete (m : Word) :
    (∀ k x : Word,
      (g k (x ^^^ (0x00006000#32)) &&& m) =
        (g k x &&& m)) ↔
      (m &&& (0xFF8007FF#32)) = 0#32 := by
  constructor
  · exact mask_6000_maximal m
  · intro hm k x
    have h := guaranteedMask_sound k x (0x00006000#32)
    rw [mask_6000_exact] at h
    have hsub : (m &&& (~~~ (0x007FF800#32))) = 0#32 := by
      bv_decide
    exact restrict_mask _ _ _ _ h hsub

end Magma.DifanAutomaticOutputMasks
