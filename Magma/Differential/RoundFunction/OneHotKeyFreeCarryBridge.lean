module

import all Init.Data.Range.Basic
public import Magma.Differential.FiveRounds.FiveRoundUniversalSupport
public import Magma.Differential.FiveRounds.FiveRoundDDTReverse

@[expose] public section

/-!
# An executable carry-support interface for impossible five-round differences

The one-round support can be relaxed by existentially quantifying the
eight key digits of Magma's already certified carry automaton.
A false result for the three intermediate local supports then
certifies a true five-round impossible differential for every key.

In particular, proving a finite key-free carry certificate for only
ordered one-hot pairs is sufficient: five-round Feistel reversal
transports the conclusion to all reverse-ordered pairs.
-/

namespace Magma.DiffanOneHotKeyFreeCarryBridge

open Magma
open Magma.CarryAutomaton
open Magma.MultiRoundDDT
open Magma.DiffanFiveRoundCoreDefect
open Magma.DiffanFiveRoundUniversalSupport
open Magma.DiffanFiveRoundDDTReverse

private abbrev Word :=
  V 32

/-- A key-free overapproximation of the real one-round support.
    It uses the certified four-state carry automaton, not an
    enumeration of complete base states. -/
def keyFreeCarrySupport (d out : Word) : Prop :=
  ∃ keyDigits : Fin 8 → Fin 16,
    carryHasPathBoolean keyDigits (wordDigits d)
      (wordDigits (out.rotateRight 11)) = true

/-- Every genuine Magma derivative yields a path in the certified
    carry automaton for the corresponding key digits. -/
theorem anyKeyGSupport_implies_keyFreeCarrySupport
    (d out : Word) (h : anyKeyGSupport d out) :
    keyFreeCarrySupport d out := by
  rcases h with ⟨k, x, hx⟩
  have hpos : 0 < xorDDT_g k d out := by
    unfold xorDDT_g
    apply Finset.card_pos.mpr
    refine ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    exact hx
  have hbool := (xorDiffPossibleBoolean_iff k d out).mpr hpos
  exact ⟨wordDigits k, hbool⟩

/-- All three inner supports are allowed independent keys, bases, and
    carry paths. Even then, their failure at every middle difference
    excludes every genuine five-round trajectory. -/
theorem fiveRound_zero_of_no_keyFreeCarry_joint
    (k₀ k₁ k₂ k₃ k₄ a s : Word)
    (hcert : ∀ c : Word,
      ¬ (keyFreeCarrySupport a c ∧
         keyFreeCarrySupport c (xor s a) ∧
         keyFreeCarrySupport s c)) :
    xorDDT_rounds 5 (fiveRoundKeys k₀ k₁ k₂ k₃ k₄)
      (a, 0#32) (0#32, s) = 0 := by
  apply fiveRound_zero_of_no_anyKey_joint_support
  intro c hc
  exact hcert c
    ⟨anyKeyGSupport_implies_keyFreeCarrySupport a c hc.1,
     anyKeyGSupport_implies_keyFreeCarrySupport c (xor s a) hc.2.1,
     anyKeyGSupport_implies_keyFreeCarrySupport s c hc.2.2⟩

/-- A certificate obligation for ordered one-hot bit pairs.
    This avoids checking the reversed 496 off-diagonal pairs twice. -/
def OrderedOneHotCarryCertificate : Prop :=
  ∀ i j : Fin 32, i.val ≤ j.val → ∀ c : Word,
    ¬ (keyFreeCarrySupport (oneHotDifference i) c ∧
       keyFreeCarrySupport c
         (xor (oneHotDifference j) (oneHotDifference i)) ∧
       keyFreeCarrySupport (oneHotDifference j) c)

/-- The exact one-hot five-round impossibility claim follows from
    a certificate over ordered bit-position pairs alone, by DDT reversal. -/
theorem universal_oneHot_zero_of_ordered_carry_certificate
    (hcert : OrderedOneHotCarryCertificate)
    (k₀ k₁ k₂ k₃ k₄ : Word) (i j : Fin 32) :
    xorDDT_rounds 5 (fiveRoundKeys k₀ k₁ k₂ k₃ k₄)
      (oneHotDifference i, 0#32) (0#32, oneHotDifference j) = 0 := by
  by_cases hij : i.val ≤ j.val
  · exact fiveRound_zero_of_no_keyFreeCarry_joint
      k₀ k₁ k₂ k₃ k₄ (oneHotDifference i) (oneHotDifference j)
      (hcert i j hij)
  · rw [outer_ddt_reverse]
    exact fiveRound_zero_of_no_keyFreeCarry_joint
      k₄ k₃ k₂ k₁ k₀ (oneHotDifference j) (oneHotDifference i)
      (hcert j i (by omega))

/-- A finite state-path formulation with independent choices of the
    four-bit key and input digit at each of the eight S-boxes. -/
def keyFreeLocalPath (d out : Word) : Prop :=
  ∃ states : Fin 9 → CarryState,
    states 0 = ((0, 0) : CarryState) ∧
    ∀ i : Fin 8, ∃ k x : Fin 16,
      sboxCarryStep i k (wordDigits d i) x (states i.castSucc) =
        (wordDigits (out.rotateRight 11) i, states i.succ)

/-- The certified eight-step automaton yields concrete local witnesses,
    forgetting the full key and base state only after their soundness
    has been established. -/
theorem keyFreeCarrySupport_implies_localPath
    (d out : Word) (h : keyFreeCarrySupport d out) :
    keyFreeLocalPath d out := by
  obtain ⟨digits, hp⟩ := h
  let k : Word := packDigits digits
  have hd : wordDigits k = digits := wordDigitsEquiv.right_inv digits
  have hp' : carryHasPathBoolean (wordDigits k) (wordDigits d)
        (wordDigits (out.rotateRight 11)) = true := by
    simpa only [hd] using hp
  obtain ⟨w⟩ := verifiedCarryPath_of_carryHasPathBoolean
    k d (out.rotateRight 11) hp'
  refine ⟨w.states, w.initial, ?_⟩
  intro i
  refine ⟨digits i, w.input i, ?_⟩
  simpa only [hd] using w.step i

/-- Local paths for the three inner functions, sharing only the
    intermediate difference. Their absence excludes all five-round
    witnesses regardless of the round keys. -/
def KeyFreeThreePath (a s : Word) : Prop :=
  ∃ c : Word,
    keyFreeLocalPath a c ∧
    keyFreeLocalPath c (xor s a) ∧
    keyFreeLocalPath s c

theorem fiveRound_zero_of_no_keyFree_threePath (k₀ k₁ k₂ k₃ k₄ a s : Word)
    (hno : ¬KeyFreeThreePath a s) :
    xorDDT_rounds 5 (fiveRoundKeys k₀ k₁ k₂ k₃ k₄) (a, 0#32) (0#32, s) = 0 := by
  apply fiveRound_zero_of_no_keyFreeCarry_joint
  intro c hc
  exact
    hno
      ⟨c, keyFreeCarrySupport_implies_localPath a c hc.1,
        keyFreeCarrySupport_implies_localPath c (xor s a) hc.2.1,
        keyFreeCarrySupport_implies_localPath s c hc.2.2⟩

end Magma.DiffanOneHotKeyFreeCarryBridge
