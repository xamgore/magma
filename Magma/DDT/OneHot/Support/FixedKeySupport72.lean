module

public import Magma.DDT.OneHot.Support.FixedKeySupportAudit
import all Init.Data.Range.Basic

@[expose] public section

/-!
# Sharp fixed-key maximum of one-hot DDT support

Real RFC transitions yield local-potential witnesses with the actual key
nibble and feasible incoming carry. Counting these witnesses bounds the
one-hot support of every round key by the previously certified ceiling 72.
The key `0x06120010` attains the bound, giving an exact maximum for the
original 32-by-32 one-hot DDT support over all 32-bit round keys.

The argument uses symbolic carry and cardinality proofs rather than an
exhaustive key scan. The per-nibble witness scores are certified separately
in Evidence iteration 18.
-/

namespace Magma.OneHotFixedKeySupport72

open Magma
open Magma.GProperties
open Magma.CarryAutomaton
open Magma.OneHotDiagonalCarryMasks
open Magma.OneHotActiveNibbleNecessary
open Magma.OneHotFixedKeySupportAudit
open Magma.OneHotSilentNibbleStructure

private abbrev Word :=
  V 32

private abbrev Cell :=
  Fin 32 × Fin 32

private abbrev Local :=
  Fin 4 × Fin 4

private abbrev Triple :=
  Fin 8 × Local

/-- A carry into the next nibble is impossible if its key digit and
    incoming carry are both zero, regardless of input digit. -/
private theorem nextCarry_key_zero (x : Fin 16) :
    nextCarry x 0 0 = 0 := by
  fin_cases x <;> decide

private theorem prefixCarry_key_zero (xs ks : Nat → Fin 16) (n : Nat) (h : ∀ j, j < n → ks j = 0) :
    incomingCarry xs ks n = 0 := by
  induction n with
  | zero => rfl
  | succ n
    ih =>
    have hp : ∀ j, j < n → ks j = 0 := by
      intro j hj
      exact h j (by omega)
    have hn := h n (by omega)
    change nextCarry (xs n) (ks n) (incomingCarry xs ks n) = 0
    rw [hn, ih hp, nextCarry_key_zero]

/-- The only carry regimes that can matter for the sharp 72 bound.
    For nibble 0, carry-in is always zero. At nibble 1 or 2 it may
    equal one only if the corresponding lower key prefix is nonzero.
    For higher digits we safely allow both carry values. -/
def feasibleCarryFlag (k : Word) (i : Fin 8) : Bool :=
  if i.val = 0 then false
  else if i.val = 1 then decide (wordDigits k 0 ≠ 0)
  else if i.val = 2 then
    decide (wordDigits k 0 ≠ 0 ∨ wordDigits k 1 ≠ 0)
  else true

/-- Whenever the flag is false, the real first-branch incoming carry
    must be zero. This is the key-prefix consistency missing from a
    purely local 16×16×2 overapproximation. -/
private theorem carry_zero_if_flag_false
    (k d x : Word) (i : Fin 8)
    (hf : feasibleCarryFlag k i = false) :
    (wordCarryPair k d x i.val).1 = 0 := by
  change incomingCarry (wordDigitStream x) (wordDigitStream k) i.val = 0
  by_cases h0 : i.val = 0
  · have hi : i.val = 0 := h0
    rw [hi]
    rfl
  by_cases h1 : i.val = 1
  · have hq : wordDigits k (0 : Fin 8) = 0 := by
      simpa [feasibleCarryFlag, h0, h1] using hf
    rw [h1]
    apply prefixCarry_key_zero
    intro j hj
    have hj0 : j = 0 := by omega
    subst j
    exact (wordDigitStream_at k (0 : Fin 8)).trans hq
  by_cases h2 : i.val = 2
  · have hq : wordDigits k (0 : Fin 8) = 0 ∧
        wordDigits k (1 : Fin 8) = 0 := by
      simpa [feasibleCarryFlag, h0, h1, h2] using hf
    rw [h2]
    apply prefixCarry_key_zero
    intro j hj
    have hc : j = 0 ∨ j = 1 := by omega
    rcases hc with hc | hc
    · subst j
      exact (wordDigitStream_at k (0 : Fin 8)).trans hq.1
    · subst j
      exact (wordDigitStream_at k (1 : Fin 8)).trans hq.2
  · have ht : feasibleCarryFlag k i = true := by
      simp [feasibleCarryFlag, h0, h1, h2]
    rw [ht] at hf
    cases hf

/-- For any actual input x, the incoming carry at the active nibble
    is one of the states enumerated in `localPotential`. -/
private theorem actual_carry_is_permitted
    (k d x : Word) (i : Fin 8) :
    let c := (wordCarryPair k d x i.val).1
    c = 0 ∨ (feasibleCarryFlag k i = true ∧ c = 1) := by
  dsimp
  let c := (wordCarryPair k d x i.val).1
  by_cases hc0 : c = 0
  · exact Or.inl hc0
  · have hc1 : c = 1 := by
      have hlt := c.isLt
      have hn : c.val ≠ 0 := by
        intro h
        exact hc0 (Fin.ext h)
      apply Fin.ext
      change c.val = 1
      omega
    have hf : feasibleCarryFlag k i = true := by
      cases h : feasibleCarryFlag k i with
      | true => rfl
      | false =>
          have hz := carry_zero_if_flag_false k d x i h
          exact False.elim (hc0 hz)
    exact Or.inr ⟨hf, hc1⟩

/-- Equal lower input nibbles imply equal incoming carries. -/
private theorem incomingCarry_congr_prefix
    (xs ys ks : Nat → Fin 16) (n : Nat)
    (h : ∀ j, j < n → xs j = ys j) :
    incomingCarry xs ks n = incomingCarry ys ks n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hp := ih (by
        intro j hj
        exact h j (by omega))
      change nextCarry (xs n) (ks n) (incomingCarry xs ks n) =
        nextCarry (ys n) (ks n) (incomingCarry ys ks n)
      rw [h n (by omega), hp]

private theorem xorDigit_zero_right (v : Fin 16) : xorDigit v 0 = v := by fin_cases v <;> decide

private theorem oneHot_other_nibble_zero (j : Fin 32) (i : Fin 8) (h : i.val ≠ j.val / 4) :
    wordDigits (BitVec.ofNat 32 (2 ^ j.val)) i = 0 := by
  revert h
  fin_cases j <;> fin_cases i <;> decide

private theorem oneHot_own_nibble (j : Fin 32) :
    wordDigits (BitVec.ofNat 32 (2 ^ j.val)) (⟨j.val / 4, by omega⟩ : Fin 8) =
      Fin.ofNat 16 (2 ^ (j.val % 4)) := by
  fin_cases j <;> decide

private theorem pairCarry_diagonal_of_lower_zero (k d x : Word) (i : Fin 8)
    (hlow : ∀ u : Fin 8, u.val < i.val → wordDigits d u = 0) :
    (wordCarryPair k d x i.val).1 = (wordCarryPair k d x i.val).2 := by
  change
    incomingCarry (wordDigitStream x) (wordDigitStream k) i.val =
      incomingCarry (wordDigitStream (xor x d)) (wordDigitStream k) i.val
  apply incomingCarry_congr_prefix
  intro n hn
  have hn8 : n < 8 := by omega
  let u : Fin 8 := ⟨n, hn8⟩
  have hd : wordDigits d u = 0 := hlow u (by simpa [u] using hn)
  have hxor : wordDigits (xor x d) u = wordDigits x u := by
    rw [wordDigits_xor, hd, xorDigit_zero_right]
  calc
    wordDigitStream x n = wordDigits x u := wordDigitStream_at x u
    _ = wordDigits (xor x d) u := hxor.symm
    _ = wordDigitStream (xor x d) n := (wordDigitStream_at (xor x d) u).symm

/-- Strengthen the prior `real_transition_implies_local` by retaining
    the ACTUAL key digit and the ACTUAL incoming carry. The earlier
    theorem existentially quantified them and hence lost key-specific
    information needed for the 72 bound. -/
private theorem actual_transition_has_fixed_local_witness
    (k x : Word) (j s : Fin 32)
    (hsame : j.val / 4 = s.val / 4)
    (haccept : ∀ t : Fin 8,
      xor (π t (Internal.nibble (modShift k
        (xor x (BitVec.ofNat 32 (2 ^ j.val)))) t))
        (π t (Internal.nibble (modShift k x) t)) =
          Internal.nibble (BitVec.ofNat 32 (2 ^ s.val)) t) :
    ∃ (a : Fin 16) (c : Fin 2),
      let i : Fin 8 := ⟨j.val / 4, by omega⟩
      let r : Fin 4 := ⟨j.val % 4, by omega⟩
      let z : Fin 4 := ⟨s.val % 4, by omega⟩
      let step := sboxCarryStep i (wordDigits k i)
        (Fin.ofNat 16 (2 ^ r.val)) a (c,c)
      (c = 0 ∨ (feasibleCarryFlag k i = true ∧ c = 1)) ∧
      step.1 = Fin.ofNat 16 (2 ^ z.val) ∧
        (i.val = 7 ∨ step.2.1 = step.2.2) := by
  let d : Word := BitVec.ofNat 32 (2 ^ j.val)
  let b : Word := BitVec.ofNat 32 (2 ^ s.val)
  let i : Fin 8 := ⟨j.val / 4, by omega⟩
  let r : Fin 4 := ⟨j.val % 4, by omega⟩
  let z : Fin 4 := ⟨s.val % 4, by omega⟩
  have hlow : ∀ u : Fin 8, u.val < i.val → wordDigits d u = 0 := by
    intro u hu
    exact oneHot_other_nibble_zero j u (by dsimp [i] at hu; omega)
  have hc := pairCarry_diagonal_of_lower_zero k d x i hlow
  let c : Fin 2 := (wordCarryPair k d x i.val).1
  have hstate : wordCarryPair k d x i.val = (c,c) := by
    apply Prod.ext <;> simp [c, hc]
  have hdigit : wordDigits d i = Fin.ofNat 16 (2 ^ r.val) := by
    simpa only [d, i, r] using oneHot_own_nibble j
  have htarget : wordDigits b i = Fin.ofNat 16 (2 ^ z.val) := by
    have hii : i = (⟨s.val / 4, by omega⟩ : Fin 8) :=
      Fin.ext (by dsimp [i]; omega)
    rw [hii]
    simpa only [b, z] using oneHot_own_nibble s
  have hgood (u : Fin 8) :
      localSBoxDifference k d x u = wordDigits b u :=
    (localSBoxDifference_eq_iff k d b x u).mpr (haccept u)
  let st := sboxCarryStep i (wordDigits k i)
    (Fin.ofNat 16 (2 ^ r.val)) (wordDigits x i) (c,c)
  have hstep : st =
      (localSBoxDifference k d x i, wordCarryPair k d x (i.val+1)) := by
    simpa only [st, hdigit, hstate] using
      (sboxCarryStep_word_correct k d x i)
  have ho : st.1 = Fin.ofNat 16 (2 ^ z.val) := by
    rw [hstep, hgood i, htarget]
  have hcarry : i.val = 7 ∨ st.2.1 = st.2.2 := by
    by_cases hlast : i.val = 7
    · exact Or.inl hlast
    · have hnext : i.val < 7 := by omega
      let next : Fin 8 := ⟨i.val+1, by omega⟩
      have hdnext : wordDigits d next = 0 :=
        oneHot_other_nibble_zero j next (by dsimp [next,i]; omega)
      have hbnext : wordDigits b next = 0 :=
        oneHot_other_nibble_zero s next (by dsimp [next,i]; omega)
      have hnextstep := congrArg Prod.fst
        (sboxCarryStep_word_correct k d x next)
      have hzero :
          (sboxCarryStep next (wordDigits k next) 0
            (wordDigits x next) (wordCarryPair k d x next.val)).1 = 0 := by
        rw [hdnext] at hnextstep
        rw [hgood next, hbnext] at hnextstep
        exact hnextstep
      have hcnext :
          (wordCarryPair k d x next.val).1 =
            (wordCarryPair k d x next.val).2 :=
        silent_sbox_zero_forces_diagonal next (wordDigits k next)
          (wordDigits x next) _ _ hzero
      right
      rw [hstep]
      exact hcnext
  refine ⟨wordDigits x i, c, ?_, ho, hcarry⟩
  exact actual_carry_is_permitted k d x i

/-- All the steps above are now used in ONE reusable soundness bridge. -/
theorem real_positive_implies_localPotential
    (k : Word) (j s : Fin 32)
    (hsame : j.val / 4 = s.val / 4)
    (hp : 0 < xorDDT_g k (BitVec.ofNat 32 (2 ^ j.val))
      (rot11 (BitVec.ofNat 32 (2 ^ s.val)))) :
    let i : Fin 8 := ⟨j.val / 4, by omega⟩
    let r : Fin 4 := ⟨j.val % 4, by omega⟩
    let z : Fin 4 := ⟨s.val % 4, by omega⟩
    localPotential i (wordDigits k i) (feasibleCarryFlag k i) r z = true := by
  rw [xorDDT_g_eq_nibbles] at hp
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hp
  have haccept := (Finset.mem_filter.mp hx).2
  obtain ⟨a, c, hc, ho, hout⟩ :=
    actual_transition_has_fixed_local_witness k x j s hsame haccept
  unfold localPotential
  apply List.any_eq_true.mpr
  refine ⟨a, by simp, ?_⟩
  apply List.any_eq_true.mpr
  refine ⟨c, by simp, ?_⟩
  simp only [ite_eq_left hc, decide_eq_true_eq]
  exact ⟨ho, hout⟩

private def srcBit (i : Fin 8) (r : Fin 4) : Fin 32 :=
  ⟨4 * i.val + r.val, by omega⟩

private def dstBit (i : Fin 8) (s : Fin 4) : Fin 32 :=
  ⟨(4 * i.val + s.val + 11) % 32, by omega⟩

private theorem dst_unrotate (i : Fin 8) (s : Fin 4) :
    ((dstBit i s).val + 21) % 32 = 4 * i.val + s.val := by
  dsimp [dstBit]
  omega

private theorem src_div (i : Fin 8) (r : Fin 4) : (srcBit i r).val / 4 = i.val := by
  dsimp [srcBit]
  omega

private theorem src_rem (i : Fin 8) (r : Fin 4) : (srcBit i r).val % 4 = r.val := by
  dsimp [srcBit]
  omega

private theorem dst_injective (i : Fin 8) : Function.Injective (dstBit i) := by
  intro s t h
  apply Fin.ext
  have heq := congrArg (fun z : Fin 32 => (z.val + 21) % 32) h
  rw [dst_unrotate, dst_unrotate] at heq
  omega

private theorem src_injective (i : Fin 8) : Function.Injective (srcBit i) := by
  intro s t h
  apply Fin.ext
  have hh := congrArg Fin.val h
  dsimp [srcBit] at hh
  omega

/-- A tuple (i,r,s) has an exact 32-bit entry in the original matrix. -/
private def tripleActual (k : Word) : Finset Triple :=
  Finset.univ.filter (fun p : Triple =>
    0 < fastOneHotDDT k (srcBit p.1 p.2.1) (dstBit p.1 p.2.2))

/-- All locally permitted triples for this particular key. -/
private def triplePotential (k : Word) : Finset Triple :=
  Finset.univ.filter (fun p : Triple =>
    localPotential p.1 (wordDigits k p.1) (feasibleCarryFlag k p.1)
      p.2.1 p.2.2 = true)

private theorem tripleActual_subset_triplePotential (k : Word) :
    tripleActual k ⊆ triplePotential k := by
  intro ⟨i, r, s⟩ hp
  simp only [tripleActual, triplePotential, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
  have hpos :
    0 <
      xorDDT_g k (BitVec.ofNat 32 (2 ^ (srcBit i r).val))
        (BitVec.ofNat 32 (2 ^ (dstBit i s).val)) := by
    rw [← fastOneHotDDT_correct]
    exact hp
  have hrot :
    rot11 (BitVec.ofNat 32 (2 ^ (4 * i.val + s.val))) = BitVec.ofNat 32 (2 ^ (dstBit i s).val) := by
    fin_cases i <;> fin_cases s <;> decide
  have hpos' :
    0 <
      xorDDT_g k (BitVec.ofNat 32 (2 ^ (srcBit i r).val))
        (rot11 (BitVec.ofNat 32 (2 ^ (4 * i.val + s.val)))) := by
    rw [hrot]
    exact hpos
  let j : Fin 32 := srcBit i r
  let z : Fin 32 := ⟨4 * i.val + s.val, by omega⟩
  have hsame : j.val / 4 = z.val / 4 := by
    simp only [j, z, src_div]
    omega
  have hs := real_positive_implies_localPotential k j z hsame hpos'
  simpa [j, z, src_div, src_rem, Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt s.isLt] using hs

/-- Triples parameterize exactly the diagonal 4×4 input/output cells.
    Since all off-diagonal transitions are zero, they parameterize the
    positive support for every key. -/
private theorem real_support_card_eq_triple (k : Word) :
    (fastPositiveCells k).card = (tripleActual k).card := by
  classical
  symm
  apply Finset.card_bij (fun p _ =>
    (srcBit p.1 p.2.1, dstBit p.1 p.2.2))
  · intro ⟨i,r,s⟩ hp
    simpa only [tripleActual, fastPositiveCells, Finset.mem_filter,
      Finset.mem_univ, true_and] using hp
  · intro ⟨i,r,s⟩ _ ⟨i',r',s'⟩ _ heq
    have hs := congrArg Prod.fst heq
    have hd := congrArg Prod.snd heq
    have hi : i=i' := by
      apply Fin.ext
      have hh := congrArg (fun v : Fin 32 => v.val/4) hs
      simpa only [src_div] using hh
    subst i'
    have hr : r=r' := src_injective i hs
    have ht : s=s' := dst_injective i hd
    subst r'
    subst s'
    rfl
  · intro ⟨j,ell⟩ hp
    have hr : 0 < xorDDT_g k (BitVec.ofNat 32 (2^j.val))
        (BitVec.ofNat 32 (2^ell.val)) := by
      rw [← fastOneHotDDT_correct]
      exact (Finset.mem_filter.mp hp).2
    have hsame := oneHot_positive_implies_same_nibble k j ell hr
    let i : Fin 8 := ⟨j.val/4, by omega⟩
    let r : Fin 4 := ⟨j.val%4, by omega⟩
    let s : Fin 4 := ⟨((ell.val+21)%32)%4, by omega⟩
    have hj : srcBit i r = j := by
      apply Fin.ext
      dsimp [srcBit,i,r]
      omega
    have he : dstBit i s = ell := by
      apply Fin.ext
      dsimp [dstBit,i,s] at *
      omega
    refine ⟨(i,(r,s)), ?_, ?_⟩
    · simp only [tripleActual, Finset.mem_filter,
        Finset.mem_univ, true_and]
      rw [hj, he]
      exact (Finset.mem_filter.mp hp).2
    · exact Prod.ext hj he

/-- The local-potential grid is the disjoint union of eight nibble
    fibers, and its size is the sum of their 16-entry local counts. -/
private theorem triplePotential_card (k : Word) :
    (triplePotential k).card =
      ∑ i : Fin 8,
        localPotentialCount i (wordDigits k i) (feasibleCarryFlag k i) := by
  let block (i : Fin 8) : Finset Local :=
    Finset.univ.filter (fun rs : Local =>
      localPotential i (wordDigits k i) (feasibleCarryFlag k i)
        rs.1 rs.2 = true)
  have hset : triplePotential k =
      (Finset.univ : Finset (Fin 8)).biUnion
        (fun i => ({i} : Finset (Fin 8)) ×ˢ block i) := by
    ext ⟨i,rs⟩
    simp [triplePotential, block]
  rw [hset, Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro i _
    simp [block, localPotentialCount]
  · intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro ⟨u,rs⟩ hu hv
    have hui : u=i := by
      exact Finset.mem_singleton.mp (Finset.mem_product.mp hu).1
    have huj : u=j := by
      exact Finset.mem_singleton.mp (Finset.mem_product.mp hv).1
    exact hij (hui.symm.trans huj)

/-- Sound local bound: no independence assumptions, no
    enumeration of the full key space, and no heuristic pruning. -/
theorem fixedKey_realSupport_le_localCeiling (k : Word) :
    (fastPositiveCells k).card ≤
      ∑ i : Fin 8,
        localPotentialCount i (wordDigits k i) (feasibleCarryFlag k i) := by
  rw [real_support_card_eq_triple]
  calc
    (tripleActual k).card ≤ (triplePotential k).card :=
      Finset.card_le_card (tripleActual_subset_triplePotential k)
    _ = _ := triplePotential_card k

/-- The previously verified arithmetic ceiling now applies to the
    ACTUAL one-hot DDT for EVERY 32-bit key. -/
theorem every_key_at_most_72 (k : Word) :
    (fastPositiveCells k).card ≤ 72 := by
  have hsound := fixedKey_realSupport_le_localCeiling k
  have hnum := consistent_local_ceiling_72
    (wordDigits k 0) (wordDigits k 1) (wordDigits k 2)
    (wordDigits k 3) (wordDigits k 4) (wordDigits k 5)
    (wordDigits k 6) (wordDigits k 7)
  have hsum :
      (∑ i : Fin 8,
        localPotentialCount i (wordDigits k i) (feasibleCarryFlag k i)) ≤ 72 := by
    rw [Fin.sum_univ_eight]
    simpa [feasibleCarryFlag] using hnum
  omega

/-- SHARP fixed-key maximum of the real 32×32 one-hot DDT support.
    Existence is witnessed by the previous certified candidate72Key. -/
theorem exact_maximum_real_oneHot_support :
    (∀ k : Word, (fastPositiveCells k).card ≤ 72) ∧
    (∃ k : Word, (fastPositiveCells k).card = 72) := by
  exact ⟨every_key_at_most_72,
    ⟨candidate72Key, candidate72Key_has_72_cells⟩⟩

/-- A fully semantic version, phrased only with the original DDT. -/
theorem exact_maximum_real_ddt_support :
    (∀ k : Word,
      ((Finset.univ : Finset Cell).filter (fun p : Cell =>
        0 < xorDDT_g k
          (BitVec.ofNat 32 (2 ^ p.1.val))
          (BitVec.ofNat 32 (2 ^ p.2.val)))).card ≤ 72) ∧
    (∃ k : Word,
      ((Finset.univ : Finset Cell).filter (fun p : Cell =>
        0 < xorDDT_g k
          (BitVec.ofNat 32 (2 ^ p.1.val))
          (BitVec.ofNat 32 (2 ^ p.2.val)))).card = 72) := by
  constructor
  · intro k
    rw [← fastPositiveCells_eq_real]
    exact every_key_at_most_72 k
  · refine ⟨candidate72Key, ?_⟩
    exact real_candidate72Key_has_72_cells

/-- Value tests are propositions, not printed experimental messages. -/
example : (fastPositiveCells candidate72Key).card = 72 :=
  candidate72Key_has_72_cells

end Magma.OneHotFixedKeySupport72
