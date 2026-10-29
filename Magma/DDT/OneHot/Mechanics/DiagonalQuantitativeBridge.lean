module

public import Magma.DDT.OneHot.Mechanics.DiagonalQuantitativeFibers
import all Init.Data.Range.Basic
import Mathlib.Tactic.Ring
import Magma.DDT.OneHot.Mechanics.SilentNibbleStructure
import Magma.DDT.OneHot.Mechanics.ExactCarryRegimes

@[expose] public section

/-!
Exact quantitative fiber bridge for the 32×32 one-hot DDT matrix.

This file follows `Magma.OneHot.DiagonalQuantitativeFibers`. The
factorized fiber has already been proved to have cardinality
`diagonalWeight`. Here we prove the missing per-input acceptance
characterization and then transfer the cardinality using a radix-16
coordinate equivalence.

-/

namespace Magma.OneHotDiagonalQuantitativeBridge

open Magma
open Magma.CarryAutomaton
open Magma.OneHotDiagonalExactWeights
open Magma.OneHotDiagonalQuantitativeFibers
open Magma.OneHotExactCarryRegimes
open Magma.OneHotSilentNibbleStructure

private abbrev Word :=
  V 32

private abbrev Q :=
  Fin 16

private def src (i : Fin 8) (r : Fin 4) : Word :=
  BitVec.ofNat 32 (2 ^ (4 * i.val + r.val))

private def dst (i : Fin 8) (s : Fin 4) : Word :=
  BitVec.ofNat 32 (2 ^ (4 * i.val + s.val))

private theorem xorDigit_zero (x : Q) : xorDigit x 0 = x := by fin_cases x <;> decide

/-- For a one-hot word, every other digit is zero. -/
private theorem singleDigit (i u : Fin 8) (r : Fin 4) :
    wordDigits (src i r) u =
      if u = i then Fin.ofNat 16 (2 ^ r.val) else 0 := by
  fin_cases i <;> fin_cases u <;> fin_cases r <;> decide

private theorem singleDigit_target (i u : Fin 8) (s : Fin 4) :
    wordDigits (dst i s) u = if u = i then Fin.ofNat 16 (2 ^ s.val) else 0 := by
  fin_cases i <;> fin_cases u <;> fin_cases s <;> decide

/-- The two carry chains agree on arrival at the first active digit. -/
private theorem incoming_diagonal (k x : Word) (i : Fin 8) (r : Fin 4) :
    (wordCarryPair k (src i r) x i.val).1 =
      (wordCarryPair k (src i r) x i.val).2 := by
  have hprefix : ∀ n : Nat, n ≤ i.val →
      incomingCarry (wordDigitStream x) (wordDigitStream k) n =
      incomingCarry (wordDigitStream (xor x (src i r)))
        (wordDigitStream k) n := by
    intro n hn
    induction n with
    | zero => rfl
    | succ n ih =>
        have hi := ih (by omega)
        let u : Fin 8 := ⟨n, by omega⟩
        have hne : u ≠ i := by
          intro hh
          have hv := congrArg Fin.val hh
          dsimp [u] at hv
          omega
        have hz : wordDigits (src i r) u = 0 := by
          rw [singleDigit]; simp [hne]
        have heq : wordDigitStream (xor x (src i r)) n =
            wordDigitStream x n := by
          rw [wordDigitStream_at (xor x (src i r)) u,
            wordDigitStream_at x u, wordDigits_xor, hz, xorDigit_zero]
        change nextCarry (wordDigitStream x n) (wordDigitStream k n)
            (incomingCarry (wordDigitStream x) (wordDigitStream k) n) =
          nextCarry (wordDigitStream (xor x (src i r)) n)
            (wordDigitStream k n)
            (incomingCarry (wordDigitStream (xor x (src i r)))
              (wordDigitStream k) n)
        rw [heq, hi]
  exact hprefix i.val (le_refl _)

private theorem incoming_diagonal_state (k x : Word) (i : Fin 8) (r : Fin 4) :
    wordCarryPair k (src i r) x i.val =
      ((wordCarryPair k (src i r) x i.val).1, (wordCarryPair k (src i r) x i.val).1) := by
  apply Prod.ext
  · rfl
  · exact (incoming_diagonal k x i r).symm

/-- For an arbitrary full input, passing the eight S-box difference
    checks is EQUIVALENT to a single active digit test, plus convergence
    of its outgoing carries except at the last digit. -/
theorem accepted_iff_active
    (k x : Word) (i : Fin 8) (r s : Fin 4) :
    (carryTrace (wordDigits k) (wordDigits (src i r))
      (wordDigits (dst i s)) (wordDigits x)).2 = true ↔
      let c := (wordCarryPair k (src i r) x i.val).1
      let step := sboxCarryStep i (wordDigits k i)
        (Fin.ofNat 16 (2 ^ r.val)) (wordDigits x i) (c, c)
      step.1 = Fin.ofNat 16 (2 ^ s.val) ∧
        (i.val = 7 ∨ step.2.1 = step.2.2) := by
  let d := src i r
  let b := dst i s
  let c := (wordCarryPair k d x i.val).1
  let step := sboxCarryStep i (wordDigits k i)
    (Fin.ofNat 16 (2 ^ r.val)) (wordDigits x i) (c, c)
  have hstate : wordCarryPair k d x i.val = (c, c) :=
    incoming_diagonal_state k x i r
  have hd : wordDigits d i = Fin.ofNat 16 (2 ^ r.val) := by
    simp [d, singleDigit]
  have hb : wordDigits b i = Fin.ofNat 16 (2 ^ s.val) := by
    simp [b, singleDigit_target]
  have hstep : step =
      (localSBoxDifference k d x i,
        wordCarryPair k d x (i.val + 1)) := by
    simpa only [hd, hstate] using (sboxCarryStep_word_correct k d x i)
  have hlocal (u : Fin 8) :
      localSBoxDifference k d x u = wordDigits b u ↔
        xor (π u (Internal.nibble (Magma.GProperties.modShift k (xor x d)) u))
            (π u (Internal.nibble (Magma.GProperties.modShift k x) u)) =
          Internal.nibble b u := by
    exact localSBoxDifference_eq_iff k d b x u
  have haccept :
      (carryTrace (wordDigits k) (wordDigits d) (wordDigits b)
        (wordDigits x)).2 = true ↔
      ∀ u : Fin 8, localSBoxDifference k d x u = wordDigits b u := by
    rw [carryTrace_iff_nibbleDifferences]
    exact forall_congr' (fun u => (hlocal u).symm)
  constructor
  · intro h
    have hall := haccept.mp h
    have hfst := congrArg Prod.fst hstep
    have hout : step.1 = Fin.ofNat 16 (2 ^ s.val) := by
      rw [hfst, hall i, hb]
    refine ⟨hout, ?_⟩
    by_cases hlast : i.val = 7
    · exact Or.inl hlast
    · right
      let j : Fin 8 := ⟨i.val + 1, by omega⟩
      have hnot : j ≠ i := by
        intro hh
        have hv := congrArg Fin.val hh
        dsimp [j] at hv
        omega
      have hdz : wordDigits d j = 0 := by
        rw [singleDigit]; simp [hnot]
      have hbz : wordDigits b j = 0 := by
        rw [singleDigit_target]; simp [hnot]
      have hj := congrArg Prod.fst (sboxCarryStep_word_correct k d x j)
      rw [hdz] at hj
      have hz : (sboxCarryStep j (wordDigits k j) 0
            (wordDigits x j) (wordCarryPair k d x j.val)).1 = 0 := by
        rw [hj, hall j, hbz]
      have heq := silent_sbox_zero_forces_diagonal j
        (wordDigits k j) (wordDigits x j)
        (wordCarryPair k d x j.val).1
        (wordCarryPair k d x j.val).2 hz
      have hsnd := congrArg Prod.snd hstep
      rw [hsnd]
      exact heq
  · rintro ⟨hout, hcarry⟩
    apply haccept.mpr
    intro u
    by_cases hactive : u = i
    · subst u
      have hf := congrArg Prod.fst hstep
      exact (hf.symm.trans hout).trans hb.symm
    · have hdz : wordDigits d u = 0 := by
        rw [singleDigit]; simp [hactive]
      have hbz : wordDigits b u = 0 := by
        rw [singleDigit_target]; simp [hactive]
      have hdiag : ∀ n : Nat, i.val < n → n ≤ 7 →
          (wordCarryPair k d x n).1 = (wordCarryPair k d x n).2 := by
        intro n
        induction n with
        | zero => intro hh _; omega
        | succ n ih =>
            intro hi hn
            by_cases hbase : n = i.val
            · subst n
              have hcase : i.val ≠ 7 := by omega
              rcases hcarry with hc7 | hsync
              · exact False.elim (hcase hc7)
              · have hsnd := congrArg Prod.snd hstep
                rw [hsnd] at hsync
                exact hsync
            · have hprev := ih (by omega) (by omega)
              let v : Fin 8 := ⟨n, by omega⟩
              have hnot : v ≠ i := by
                intro hh
                have hv := congrArg Fin.val hh
                dsimp [v] at hv
                omega
              have hzero : wordDigits d v = 0 := by
                rw [singleDigit]; simp [hnot]
              have hxEq : wordDigitStream (xor x d) n =
                  wordDigitStream x n := by
                rw [wordDigitStream_at (xor x d) v,
                  wordDigitStream_at x v, wordDigits_xor,
                  hzero, xorDigit_zero]
              change nextCarry (wordDigitStream x n) (wordDigitStream k n)
                  (wordCarryPair k d x n).1 =
                nextCarry (wordDigitStream (xor x d) n)
                  (wordDigitStream k n) (wordCarryPair k d x n).2
              rw [hxEq, hprev]
      have hstateu : wordCarryPair k d x u.val =
          ((wordCarryPair k d x u.val).1,
           (wordCarryPair k d x u.val).1) := by
        apply Prod.ext
        · rfl
        · by_cases hbefore : u.val < i.val
          · have heq : (wordCarryPair k d x u.val).1 =
                (wordCarryPair k d x u.val).2 := by
              have hp : ∀ j : Nat, j ≤ u.val →
                  incomingCarry (wordDigitStream x) (wordDigitStream k) j =
                  incomingCarry (wordDigitStream (xor x d))
                    (wordDigitStream k) j := by
                intro j hj
                induction j with
                | zero => rfl
                | succ j ih =>
                    have hh := ih (by omega)
                    let v : Fin 8 := ⟨j, by omega⟩
                    have hv : v ≠ i := by
                      intro he
                      have hval := congrArg Fin.val he
                      dsimp [v] at hval
                      omega
                    have hdz' : wordDigits d v = 0 := by
                      rw [singleDigit]; simp [hv]
                    have hxu : wordDigitStream (xor x d) j =
                        wordDigitStream x j := by
                      rw [wordDigitStream_at (xor x d) v,
                        wordDigitStream_at x v, wordDigits_xor,
                        hdz', xorDigit_zero]
                    change nextCarry (wordDigitStream x j) (wordDigitStream k j)
                        (incomingCarry (wordDigitStream x) (wordDigitStream k) j) =
                      nextCarry (wordDigitStream (xor x d) j)
                        (wordDigitStream k j)
                        (incomingCarry (wordDigitStream (xor x d))
                          (wordDigitStream k) j)
                    rw [hxu, hh]
              exact hp u.val (le_refl _)
            exact heq.symm
          · exact (hdiag u.val (by omega) (by omega)).symm
      have hs := congrArg Prod.fst (sboxCarryStep_word_correct k d x u)
      rw [hdz, hstateu] at hs
      dsimp only at hs
      rw [hbz, ← hs]
      simp only [silent_sbox_step_diagonal]

/-! ### Numeric coordinates: high × (active × low). -/

private abbrev Coords (i : Fin 8) :=
  Fin (suffixFactor i) × (Fin 16 × Fin (lowBase i))

private theorem totalBase (i : Fin 8) : suffixFactor i * (16 * lowBase i) = 2 ^ 32 := by
  have hi : (7 - i.val) + (i.val + 1) = 8 := by omega
  change 16 ^ (7 - i.val) * (16 * 16 ^ i.val) = 2 ^ 32
  rw [show (16 : Nat) * 16 ^ i.val = 16 ^ (i.val + 1) by
      rw [pow_succ]; ring]
  rw [← pow_add, hi]
  norm_num

/-- An explicit product equivalence, compatible with the little-endian
    radix-16 numeric interpretation. -/
private def coordsEquiv (i : Fin 8) : Coords i ≃ Word := by
  let e : Coords i ≃ Fin (suffixFactor i * (16 * lowBase i)) :=
    (Equiv.prodCongr (Equiv.refl (Fin (suffixFactor i)))
      (finProdFinEquiv : Fin 16 × Fin (lowBase i) ≃
        Fin (16 * lowBase i))).trans
      (finProdFinEquiv : Fin (suffixFactor i) ×
        Fin (16 * lowBase i) ≃ Fin (suffixFactor i * (16 * lowBase i)))
  exact e.trans ((finCongr (totalBase i)).trans
    (BitVec.equivFin (m := 32)).toEquiv.symm)

private theorem coords_toNat (i : Fin 8) (p : Coords i) :
    (coordsEquiv i p).toNat = p.2.2.val + lowBase i * p.2.1.val + (16 * lowBase i) * p.1.val := by
  change (finProdFinEquiv (p.1, finProdFinEquiv p.2)).val = _
  simp only [finProdFinEquiv_apply_val]

private theorem coords_prefix (i : Fin 8) (p : Coords i) :
    (coordsEquiv i p).toNat % lowBase i = p.2.2.val := by
  have hval : (coordsEquiv i p).toNat = p.2.2.val + lowBase i * (p.2.1.val + 16 * p.1.val) := by
    rw [coords_toNat]
    ring
  rw [hval, Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt p.2.2.isLt

private theorem coords_active (i : Fin 8) (p : Coords i) :
    wordDigits (coordsEquiv i p) i = p.2.1 := by
  apply Fin.ext
  rw [wordDigits_val]
  change (coordsEquiv i p).toNat / lowBase i % 16 = p.2.1.val
  have hval : (coordsEquiv i p).toNat = p.2.2.val + lowBase i * (p.2.1.val + 16 * p.1.val) := by
    rw [coords_toNat]
    ring
  rw [hval, Nat.add_mul_div_left _ _ (by simp [lowBase])]
  rw [Nat.div_eq_of_lt p.2.2.isLt]
  simp only [Nat.zero_add]
  rw [Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt p.2.1.isLt

/-- This is the membership bridge. It is pointwise (each concrete full
    input), not merely an existence statement about the support. -/
theorem coords_accepted_iff_factorized
    (k : Word) (i : Fin 8) (r s : Fin 4) (p : Coords i) :
    (carryTrace (wordDigits k) (wordDigits (src i r))
      (wordDigits (dst i s)) (wordDigits (coordsEquiv i p))).2 = true ↔
      (p.2.2.val, (p.2.1, p.1)) ∈ factorizedInputFiber k i r s := by
  let x := coordsEquiv i p
  let c : Fin 2 := (wordCarryPair k (src i r) x i.val).1
  have hcarry : c.val =
      (p.2.2.val + keyPrefix k i) / lowBase i := by
    have hh := incomingCarry_prefix_formula k x i
    change c.val = _
    change c.val =
      (x.toNat % nibbleBase i + k.toNat % nibbleBase i) /
        nibbleBase i at hh
    simpa only [show nibbleBase i = lowBase i from rfl,
      x, coords_prefix, keyPrefix] using hh
  have ha : wordDigits x i = p.2.1 := coords_active i p
  rw [accepted_iff_active]
  simp only [factorizedInputFiber_mem_iff]
  have hlow : p.2.2.val < lowBase i := p.2.2.isLt
  have h0 : p.2.2.val ∈ lowerCarryFiber k i 0 ↔ c = 0 := by
    simp only [lowerCarryFiber, Finset.mem_filter, Finset.mem_range,
      hlow, true_and]
    constructor
    · intro hh
      apply Fin.ext
      rw [hcarry, hh]
    · intro hc
      rw [hc] at hcarry
      exact hcarry.symm
  have h1 : p.2.2.val ∈ lowerCarryFiber k i 1 ↔ c = 1 := by
    simp only [lowerCarryFiber, Finset.mem_filter, Finset.mem_range,
      hlow, true_and]
    constructor
    · intro hh
      apply Fin.ext
      rw [hcarry, hh]
    · intro hc
      rw [hc] at hcarry
      exact hcarry.symm
  have hlocal (c' : Fin 2) :
      p.2.1 ∈ activeDigitFiber k i r s c' ↔
        let step := sboxCarryStep i (wordDigits k i)
          (Fin.ofNat 16 (2 ^ r.val)) p.2.1 (c', c')
        step.1 = Fin.ofNat 16 (2 ^ s.val) ∧
          (i.val = 7 ∨ step.2.1 = step.2.2) := by
    simp only [activeDigitFiber, Finset.mem_filter,
      Finset.mem_univ, true_and]
  rw [h0, h1, hlocal, hlocal]
  rw [ha]
  let P (v : Fin 2) : Prop :=
    let step := sboxCarryStep i (wordDigits k i)
      (Fin.ofNat 16 (2 ^ r.val)) p.2.1 (v, v)
    step.1 = Fin.ofNat 16 (2 ^ s.val) ∧
      (i.val = 7 ∨ step.2.1 = step.2.2)
  change P c ↔ (c = 0 ∧ P 0) ∨ (c = 1 ∧ P 1)
  have alternatives (v : Fin 2) : v = 0 ∨ v = 1 := by
    fin_cases v <;> simp
  rcases alternatives c with hc | hc <;> simp [hc]

/-- The full semantic bridge for all eight active nibble positions. -/
theorem quantitativeFiberBridge_proved : quantitativeFiberBridge := by
  intro k i r s
  let C := Coords i
  let S : Finset C := (Finset.univ : Finset C).filter (fun p =>
    (carryTrace (wordDigits k) (wordDigits (src i r))
      (wordDigits (dst i s)) (wordDigits (coordsEquiv i p))).2 = true)
  have hwords :
      carryWordCount k (src i r) (dst i s) = S.card := by
    unfold carryWordCount
    exact (Finset.card_equiv (coordsEquiv i) (by
      intro p
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and])).symm
  change carryWordCount k (src i r) (dst i s) = _
  rw [hwords]
  apply Finset.card_bij
    (fun p _ => (p.2.2.val, (p.2.1, p.1)))
  · intro p hp
    exact (coords_accepted_iff_factorized k i r s p).mp
      ((Finset.mem_filter.mp hp).2)
  · intro p hp q hq heq
    rcases p with ⟨u, a, l⟩
    rcases q with ⟨v, b, m⟩
    simp only [Prod.mk.injEq] at heq
    rcases heq with ⟨hlow, ⟨hactive, hupper⟩⟩
    have hfin : l = m := Fin.ext hlow
    subst m
    subst b
    subst v
    rfl
  · intro z hz
    rcases z with ⟨low, a, upper⟩
    have hl : low < lowBase i := by
      rcases (factorizedInputFiber_mem_iff k i r s low a upper).mp hz with
          h | h
      · exact (Finset.mem_range.mp (Finset.mem_filter.mp h.1).1)
      · exact (Finset.mem_range.mp (Finset.mem_filter.mp h.1).1)
    let p : C := (upper, (a, ⟨low, hl⟩))
    refine ⟨p, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (coords_accepted_iff_factorized k i r s p).mpr hz⟩

/-- Numeric one-hot DDT formula, for every key and diagonal cell. -/
theorem diagonal_DDT_exact (k : Word) (i : Fin 8) (r s : Fin 4) :
    xorDDT_g k (src i r) (rot11 (dst i s)) = diagonalWeight k i r s :=
  real_DDT_eq_diagonalWeight_of_fiberCount
    quantitativeFiberBridge_proved k i r s

end Magma.OneHotDiagonalQuantitativeBridge
