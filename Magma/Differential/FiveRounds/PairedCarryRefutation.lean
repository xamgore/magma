module
import all Init.Data.Range.Basic
public import Magma.Differential.RoundFunction.KeyFreeCarryAutomaton

@[expose] public section

/-!
# Sound exhaustive search over paired carry frontiers

Eight output nibbles are explored simultaneously through two four-state
key-free carry automata. Dead frontiers prune entire subtrees.
At each surviving leaf, the middle differential is tested by the
already certified Boolean automaton. A successful refutation implies
an impossible five-round ordinary Feistel differential for all keys.
-/

namespace Magma.DifanPairedCarryRefutation

open Magma
open Magma.Internal
open Magma.CarryAutomaton
open Magma.MultiRoundDDT
open Magma.DifanFiveRoundCoreDefect
open Magma.DifanFiveRoundUniversalSupport
open Magma.DifanOneHotKeyFreeCarryBridge
open Magma.DifanKeyFreeCarryAutomaton

private abbrev Word :=
  V 32

private abbrev Digits :=
  Fin 8 → Fin 16

private abbrev Frontier :=
  Finset CarryState

def frontierStep (i : Fin 8) (input output : Fin 16) (prior : Frontier) : Frontier :=
  (Finset.univ : Finset CarryState).filter fun next =>
    ∃ prev ∈ prior, ∃ k x : Fin 16, sboxCarryStep i k input x prev = (output, next)

def initialFrontier : Frontier :=
  {((0, 0) : CarryState)}

/-- The Boolean checker is executable. Only 16 nibble values and
    4 two-carry states per side are considered at each level. -/
def pairedCheck (a s : Word) (n : Nat) (bits : Digits)
    (ra rs : Frontier) : Nat → Bool
  | 0 => !(keyFreePossible (rot11 (packDigits bits)) (xor s a))
  | fuel + 1 =>
    if hn : n < 8 then
      (List.finRange 16).all fun v =>
        let ra' := frontierStep ⟨n, hn⟩ (wordDigits a ⟨n, hn⟩) v ra
        let rs' := frontierStep ⟨n, hn⟩ (wordDigits s ⟨n, hn⟩) v rs
        if decide (ra'.Nonempty ∧ rs'.Nonempty) then
          pairedCheck a s (n + 1)
            (Function.update bits ⟨n, hn⟩ v) ra' rs' fuel
        else true
    else !(keyFreePossible (rot11 (packDigits bits)) (xor s a))

def refutesTriple (a s : Word) : Bool :=
  pairedCheck a s 0 (fun _ => 0) initialFrontier initialFrontier 8

private theorem frontierStep_contains (i : Fin 8) (input output : Fin 16) (prior : Frontier)
    (prev next : CarryState) (hprev : prev ∈ prior) (k x : Fin 16)
    (hstep : sboxCarryStep i k input x prev = (output, next)) :
    next ∈ frontierStep i input output prior := by
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨prev, hprev, k, x, hstep⟩⟩

private theorem updated_matches (n : Nat) (hn : n < 8) (bits target : Digits)
    (hp : ∀ i : Fin 8, i.val < n → bits i = target i) :
    ∀ i : Fin 8, i.val < n + 1 → Function.update bits ⟨n, hn⟩ (target ⟨n, hn⟩) i = target i := by
  intro i hi
  by_cases h : i = ⟨n, hn⟩
  · subst i
    simp
  · have hv : i.val < n := by
      have hne : i.val ≠ n := by
        intro he
        apply h
        exact Fin.ext he
      omega
    simpa [Function.update, h] using hp i hv

/-- A genuine central derivative makes the Boolean checker fail
    whenever both actual extreme carry traces are represented in its
    current frontiers. This is the global inductive invariant. -/
private theorem pairedCheck_rejects_genuine
    (a s c : Word) (statesA statesS : Fin 9 → CarryState)
    (hA : ∀ i : Fin 8, ∃ k x : Fin 16,
      sboxCarryStep i k (wordDigits a i) x (statesA i.castSucc) =
        (wordDigits (c.rotateRight 11) i, statesA i.succ))
    (hS : ∀ i : Fin 8, ∃ k x : Fin 16,
      sboxCarryStep i k (wordDigits s i) x (statesS i.castSucc) =
        (wordDigits (c.rotateRight 11) i, statesS i.succ))
    (hmiddle : keyFreePossible c (xor s a) = true) :
    ∀ fuel (index : Fin 9) (bits : Digits) (ra rs : Frontier),
      index.val + fuel = 8 →
      (∀ i : Fin 8, i.val < index.val →
        bits i = wordDigits (c.rotateRight 11) i) →
      statesA index ∈ ra →
      statesS index ∈ rs →
      pairedCheck a s index.val bits ra rs fuel = false := by
  intro fuel
  induction fuel with
  | zero =>
      intro index bits ra rs hn hp _ _
      have hn8 : index.val = 8 := by omega
      have hb : bits = wordDigits (c.rotateRight 11) := by
        funext i
        exact hp i (by omega)
      have hround : packDigits (wordDigits (c.rotateRight 11)) =
          c.rotateRight 11 := wordDigitsEquiv.left_inv _
      have hc : rot11 (packDigits bits) = c := by
        rw [hb, hround]
        exact rot11_rotateRight11 c
      simp [pairedCheck, hc, hmiddle]
  | succ fuel ih =>
      intro index bits ra rs hn hp hra hrs
      let n := index.val
      have hn8 : n < 8 := by omega
      let i : Fin 8 := ⟨n, hn8⟩
      let v := wordDigits (c.rotateRight 11) i
      let ra' := frontierStep i (wordDigits a i) v ra
      let rs' := frontierStep i (wordDigits s i) v rs
      let nextIndex : Fin 9 := ⟨n + 1, by omega⟩
      obtain ⟨ka, xa, ha⟩ := hA i
      obtain ⟨ks, xs, hs⟩ := hS i
      have hcastA : statesA i.castSucc = statesA index := by
        congr
      have hcastS : statesS i.castSucc = statesS index := by
        congr
      have hnextA : statesA nextIndex ∈ ra' := by
        exact frontierStep_contains i (wordDigits a i) v ra
          (statesA i.castSucc) (statesA i.succ)
          (by rw [hcastA]; exact hra) ka xa (by simpa only [Fin.succ] using ha)
      have hnextS : statesS nextIndex ∈ rs' := by
        exact frontierStep_contains i (wordDigits s i) v rs
          (statesS i.castSucc) (statesS i.succ)
          (by rw [hcastS]; exact hrs) ks xs (by simpa only [Fin.succ] using hs)
      have hkeep : decide (ra'.Nonempty ∧ rs'.Nonempty) = true :=
        (decide_eq_true_eq).mpr ⟨⟨_, hnextA⟩, ⟨_, hnextS⟩⟩
      have hpnext :
          ∀ j : Fin 8, j.val < nextIndex.val →
            Function.update bits i v j = wordDigits (c.rotateRight 11) j :=
        updated_matches n hn8 bits _ hp
      have hnext : pairedCheck a s nextIndex.val
          (Function.update bits i v) ra' rs' fuel = false :=
        ih nextIndex (Function.update bits i v) ra' rs'
          (by change n + 1 + fuel = 8; omega) hpnext hnextA hnextS
      change (if h : n < 8 then
        (List.finRange 16).all (fun v =>
          let ra' := frontierStep ⟨n, h⟩ (wordDigits a ⟨n, h⟩) v ra
          let rs' := frontierStep ⟨n, h⟩ (wordDigits s ⟨n, h⟩) v rs
          if decide (ra'.Nonempty ∧ rs'.Nonempty) then
            pairedCheck a s (n + 1)
              (Function.update bits ⟨n, h⟩ v) ra' rs' fuel
          else true)
        else !(keyFreePossible (rot11 (packDigits bits)) (xor s a))) = false
      rw [dite_eq_left hn8]
      have hmem : v ∈ List.finRange 16 := List.mem_finRange _
      have hfalse : ¬ (List.finRange 16).all
        (fun v =>
          let ra' := frontierStep i (wordDigits a i) v ra
          let rs' := frontierStep i (wordDigits s i) v rs
          if decide (ra'.Nonempty ∧ rs'.Nonempty) then
            pairedCheck a s (n + 1) (Function.update bits i v) ra' rs' fuel
          else true) = true := by
        intro hall
        have hv := (List.all_eq_true.mp hall) v hmem
        have hvfalse : (if decide (ra'.Nonempty ∧ rs'.Nonempty) then
             pairedCheck a s (n+1) (Function.update bits i v) ra' rs' fuel
           else true) = false := by
          simpa [hkeep, nextIndex] using hnext
        exact Bool.false_ne_true (hvfalse.symm.trans (by simpa only [i, ra', rs'] using hv))
      cases hres : (List.finRange 16).all
        (fun v =>
          let ra' := frontierStep i (wordDigits a i) v ra
          let rs' := frontierStep i (wordDigits s i) v rs
          if decide (ra'.Nonempty ∧ rs'.Nonempty) then
            pairedCheck a s (n+1) (Function.update bits i v) ra' rs' fuel
          else true) with
      | false => rfl
      | true => exact False.elim (hfalse hres)

/-- A kernel-checked positive result of the pruned paired-frontier
    checker gives a genuine five-round impossible differential for
    all five round keys, without SAT or an independence assumption. -/
theorem refutesTriple_sound
    (a s : Word) (h : refutesTriple a s = true)
    (k₀ k₁ k₂ k₃ k₄ : Word) :
    xorDDT_rounds 5 (fiveRoundKeys k₀ k₁ k₂ k₃ k₄)
      (a, 0#32) (0#32, s) = 0 := by
  apply fiveRound_zero_of_no_anyKey_joint_support
  intro c hc
  obtain ⟨⟨ka,xa,ha⟩, ⟨km,xm,hm⟩, ⟨ks,xs,hs⟩⟩ := hc
  have hpa := keyFreeCarrySupport_implies_localPath a c
    (anyKeyGSupport_implies_keyFreeCarrySupport a c ⟨ka,xa,ha⟩)
  have hps := keyFreeCarrySupport_implies_localPath s c
    (anyKeyGSupport_implies_keyFreeCarrySupport s c ⟨ks,xs,hs⟩)
  obtain ⟨statesA,hinitA,hA⟩ := hpa
  obtain ⟨statesS,hinitS,hS⟩ := hps
  have hmid := keyFreePossible_of_anyKeyGSupport c (xor s a) ⟨km,xm,hm⟩
  have hfalse := pairedCheck_rejects_genuine a s c statesA statesS
    hA hS hmid 8 0 (fun _ => 0) initialFrontier initialFrontier
    (by omega) (by simp)
    (by simp [initialFrontier, hinitA])
    (by simp [initialFrontier, hinitS])
  exact Bool.false_ne_true (hfalse.symm.trans h)

/-- One Boolean certificate for the complete upper-triangular one-hot
    family. Reversed bit-position pairs need not be checked twice. -/
def oneHotHalfCertificate : Bool :=
  (List.finRange 32).all fun i =>
    (List.finRange 32).all fun j =>
      if i.val ≤ j.val then
        refutesTriple (oneHotDifference i) (oneHotDifference j)
      else true

/-- A *single checked Boolean certificate* (528 cells) implies the
    complete universal one-hot five-round impossibility theorem.
    The certificate is not claimed to have been evaluated here. -/
theorem universal_oneHot_of_half_certificate
    (hcert : oneHotHalfCertificate = true)
    (k₀ k₁ k₂ k₃ k₄ : Word) (i j : Fin 32) :
    xorDDT_rounds 5 (fiveRoundKeys k₀ k₁ k₂ k₃ k₄)
      (oneHotDifference i, 0#32)
      (0#32, oneHotDifference j) = 0 := by
  have hrow : (List.finRange 32).all
      (fun j => if i.val ≤ j.val then
        refutesTriple (oneHotDifference i) (oneHotDifference j)
        else true) = true :=
    (List.all_eq_true.mp hcert) i (List.mem_finRange i)
  by_cases hij : i.val ≤ j.val
  · have hp := (List.all_eq_true.mp hrow) j (List.mem_finRange j)
    have href : refutesTriple (oneHotDifference i)
        (oneHotDifference j) = true := by
      simpa [hij] using hp
    exact refutesTriple_sound _ _ href k₀ k₁ k₂ k₃ k₄
  · have hrow' : (List.finRange 32).all
        (fun q => if j.val ≤ q.val then
          refutesTriple (oneHotDifference j) (oneHotDifference q)
          else true) = true :=
      (List.all_eq_true.mp hcert) j (List.mem_finRange j)
    have hp := (List.all_eq_true.mp hrow') i (List.mem_finRange i)
    have hji : j.val ≤ i.val := by omega
    have href : refutesTriple (oneHotDifference j)
        (oneHotDifference i) = true := by
      simpa [hji] using hp
    rw [Magma.DifanFiveRoundDDTReverse.outer_ddt_reverse]
    exact refutesTriple_sound _ _ href k₄ k₃ k₂ k₁ k₀

end Magma.DifanPairedCarryRefutation
