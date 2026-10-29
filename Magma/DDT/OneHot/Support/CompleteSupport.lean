module

public import Magma.Certificates.UInt8NoPath
import all Init.Data.Range.Basic

@[expose] public section

/-!
# Two-sided certificates for one-bit round-function support

A fast backward automaton proposes an input word. The original RFC round
function `g` independently checks the resulting XOR differential, giving a
positive-DDT witness. The no-path checker certifies zero DDT entries outside
a proposed support list. Successful checks of both inclusions establish the
exact support among the 32 one-bit input differences for a fixed key and
output difference.

The witness generator and fast carry arithmetic are not assumed correct.
Failure to find or check a witness does not prove impossibility.
-/

open Magma.Internal Magma.CarryAutomaton Magma.MultiRoundDDT
open Magma.UInt8NoPathCertificates Magma.FastSearch Magma.Certificates.Encoding

namespace Magma.OneHotCompleteSupport

/-- The one-bit difference at position `i`. -/
def oneHot (i : Fin 32) : V 32 :=
  BitVec.ofNat 32 (2 ^ i.val)

/-! ### A bounded backtracking generator, not part of the trusted proof -/

/-- Reconstruct one 32-bit input from the backward carry sets. The search
    considers at most 8 * 16 local x-nibbles (four carry states have already
    been compressed into a backward mask). `none` does NOT prove no path. -/
def proposeGInputWitness (k d b : V 32) : Option (V 32) := Id.run do
  let target := b.rotateRight 11
  let backwards := fastCarryBackward (proposeTargetCarryEdges k d b)
  if !carryStateMemFast (backwards.getD 0 0) 0 then
    return none
  let mut carry : Nat := 0
  let mut xWord : Nat := 0
  for i in (List.finRange 8) do
    let box := fastSboxTables.getD i.val #[]
    let kn := (wordDigits k i).val
    let dn := (wordDigits d i).val
    let bn := (wordDigits target i).val
    let mut found : Option (Nat × Nat) := none
    for xn in [:16] do
      if found.isNone then
        let (out, next) := fastSboxCarryStep box kn dn xn carry
        if out == bn &&
            carryStateMemFast (backwards.getD (i.val + 1) 0) next then
          found := some (xn, next)
    match found with
    | none => return none
    | some (xn, next) =>
        xWord := xWord + xn * (16 ^ i.val)
        carry := next
  return some (BitVec.ofNat 32 xWord)

/-- A proposed witness becomes trusted only after computing the original
    Magma round function `g` from the formal specification. -/
def checkedGInputWitness (k d b : V 32) : Option (V 32) := do
  let x ← proposeGInputWitness k d b
  if xor (g k (xor x d)) (g k x) = b then some x else none

theorem checkedGInputWitness_sound (k d b x : V 32) (h : checkedGInputWitness k d b = some x) :
    xor (g k (xor x d)) (g k x) = b := by
  cases hp : proposeGInputWitness k d b with
  | none => simp [checkedGInputWitness, hp] at h
  | some y =>
    by_cases hy : xor (g k (xor y d)) (g k y) = b
    · have heq : y = x := by simpa [checkedGInputWitness, hp, hy] using h
      subst x
      exact hy
    · simp [checkedGInputWitness, hp, hy] at h

/-! ### Positive DDT from a single explicitly checked input -/

/-- Polymorphic lemma prevents reduction of the 2^32-element `Finset.univ`. -/
private theorem filter_univ_card_pos_witness
    {α : Type} [Fintype α] (P : α → Prop) [DecidablePred P]
    (x : α) (hx : P x) :
    0 < ((Finset.univ : Finset α).filter P).card := by
  exact Finset.Nonempty.card_pos
    ⟨x, (Finset.mem_filter_univ x).2 hx⟩

theorem checkedGInputWitness_pos (k d b x : V 32) (h : checkedGInputWitness k d b = some x) :
    0 < xorDDT_g k d b := by
  change 0 < ((Finset.univ : Finset (V 32)).filter (fun z => xor (g k (xor z d)) (g k z) = b)).card
  exact
    filter_univ_card_pos_witness (fun z : V 32 => xor (g k (xor z d)) (g k z) = b) x
      (checkedGInputWitness_sound k d b x h)

theorem checkedGInputWitness_isSome_pos (k d b : V 32)
    (h : (checkedGInputWitness k d b).isSome = true) : 0 < xorDDT_g k d b := by
  cases hw : checkedGInputWitness k d b with
  | none => simp [hw] at h
  | some x => exact checkedGInputWitness_pos k d b x hw

/-! ### Both inclusions of a proposed one-bit support set -/

/-- Outside `mayBePossible`, an independently verified carry frontier
    must prove that no genuine input realizes the differential. -/
def verifyOneHotUpperBound
    (k aR : V 32) (mayBePossible : List (Fin 32)) : Bool :=
  (List.finRange 32).all fun i =>
    decide (i ∈ mayBePossible) || verifyUInt8NoPath k (oneHot i) aR

/-- For every listed index, require a verified positive witness. -/
def verifyOneHotLowerBound
    (k aR : V 32) (mayBePossible : List (Fin 32)) : Bool :=
  mayBePossible.all fun i =>
    (checkedGInputWitness k (oneHot i) aR).isSome

theorem verifyOneHotUpperBound_sound (k aR : V 32) (S : List (Fin 32))
    (h : verifyOneHotUpperBound k aR S = true) (i : Fin 32) (hi : i ∉ S) :
    xorDDT_g k (oneHot i) aR = 0 := by
  unfold verifyOneHotUpperBound at h
  have hcheck := (List.all_eq_true.mp h) i (List.mem_finRange i)
  have hzero : verifyUInt8NoPath k (oneHot i) aR = true := by simpa [hi] using hcheck
  exact verifyUInt8NoPath_sound k (oneHot i) aR hzero

theorem verifyOneHotLowerBound_sound (k aR : V 32) (S : List (Fin 32))
    (h : verifyOneHotLowerBound k aR S = true) (i : Fin 32) (hi : i ∈ S) :
    0 < xorDDT_g k (oneHot i) aR := by
  unfold verifyOneHotLowerBound at h
  have hp := (List.all_eq_true.mp h) i hi
  exact checkedGInputWitness_isSome_pos k (oneHot i) aR hp

/-- Exact one-bit support for an arbitrary fixed key and output difference.
    A support set is accepted only after checking both inclusions. -/
theorem oneHot_g_support_iff
    (k aR : V 32) (S : List (Fin 32))
    (hu : verifyOneHotUpperBound k aR S = true)
    (hl : verifyOneHotLowerBound k aR S = true)
    (i : Fin 32) :
    0 < xorDDT_g k (oneHot i) aR ↔ i ∈ S := by
  constructor
  · intro hp
    by_contra hn
    have hz := verifyOneHotUpperBound_sound k aR S hu i hn
    omega
  · intro hi
    exact verifyOneHotLowerBound_sound k aR S hl i hi

/-- This exact support set classifies entire 3-round columns because
    DDT3((aL,aR),(0,bR)) factors through DDT_g[k1](bR,aR). -/
theorem oneHot_threeRound_column_zero_iff
    (k₀ k₁ k₂ aR : V 32) (S : List (Fin 32))
    (hu : verifyOneHotUpperBound k₁ aR S = true)
    (hl : verifyOneHotLowerBound k₁ aR S = true)
    (i : Fin 32) :
    (∀ aL : V 32,
      xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
        (aL, aR) (0#32, oneHot i) = 0) ↔ i ∉ S := by
  rw [zeroLeft_column_empty_iff]
  constructor
  · intro hz hi
    have hp := (oneHot_g_support_iff k₁ aR S hu hl i).mpr hi
    omega
  · intro hnot
    by_contra hn
    have hp : 0 < xorDDT_g k₁ (oneHot i) aR := Nat.pos_of_ne_zero hn
    exact hnot ((oneHot_g_support_iff k₁ aR S hu hl i).mp hp)

end Magma.OneHotCompleteSupport
