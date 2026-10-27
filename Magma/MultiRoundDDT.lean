module

public import Magma.CarryAutomaton
import all Init.Data.Range.Basic

@[expose] public section

/-!
# Exact differential models of Feistel rounds

One-, two- and three-round formulas, intersection and convolution bounds,
and joint carry/rotation constraints for impossible differentials.
-/

namespace Magma.FeistelDDT
end Magma.FeistelDDT

open Magma.Internal Magma.GProperties Magma.CarryAutomaton Magma.FeistelDDT

namespace Magma.FeistelDDT

/-- XOR difference of a single 64-bit Feistel round, represented by a
    pair of 32-bit words as in the RFC formalization. -/
def feistelXorDiff (k dL dR L R : V 32) : V 32 × V 32 :=
  let p := G k (xor L dL, xor R dR)
  let q := G k (L, R)
  (xor p.1 q.1, xor p.2 q.2)

/-- XOR cancellation for the right half of the Feistel round. -/
private theorem xor_feistel_rearrange (u v L a : V 32) :
    (u ^^^ (L ^^^ a)) ^^^ (v ^^^ L) =
      (u ^^^ v) ^^^ a := by
  calc
    (u ^^^ (L ^^^ a)) ^^^ (v ^^^ L) =
        (u ^^^ v) ^^^ (L ^^^ (L ^^^ a)) := by ac_rfl
    _ = (u ^^^ v) ^^^ a := by
      rw [← BitVec.xor_assoc L L a,
          BitVec.xor_self, BitVec.zero_xor]

/-- The output difference of a Feistel round has a fixed first half.
    The second half is the difference of `g` XORed with `dL`. -/
theorem feistelXorDiff_eq (k dL dR L R : V 32) :
    feistelXorDiff k dL dR L R =
      (dR, xor (xor (g k (xor R dR)) (g k R)) dL) := by
  apply Prod.ext
  · change (R ^^^ dR) ^^^ R = dR
    calc
      (R ^^^ dR) ^^^ R = (R ^^^ R) ^^^ dR := by ac_rfl
      _ = dR := by simp only [BitVec.xor_self, BitVec.zero_xor]
  · change
      (g k (R ^^^ dR) ^^^ (L ^^^ dL)) ^^^ (g k R ^^^ L) =
        (g k (R ^^^ dR) ^^^ g k R) ^^^ dL
    exact xor_feistel_rearrange _ _ L dL

/-- XORing twice with the same word cancels. -/
private theorem xor_twice_right (u a : V 32) :
    xor (xor u a) a = u := by
  change (u ^^^ a) ^^^ a = u
  rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

/-- XORing a fixed word is an involution, expressed as an equivalence
    between two possible difference equations. -/
private theorem xor_right_eq_iff (u a b : V 32) :
    xor u a = b ↔ u = xor b a := by
  constructor
  · intro h
    have hh :=
      congrArg (fun w : V 32 => xor w a) h
    simpa only [xor_twice_right] using hh
  · intro h
    rw [h]
    exact xor_twice_right b a

/-- The Feistel output difference equation depends only on the right
    input word, provided the output left difference equals `dR`. -/
private theorem feistelXorDiff_condition
    (k dL dR eR L R : V 32) :
    (feistelXorDiff k dL dR L R = (dR, eR)) ↔
      xor (g k (xor R dR)) (g k R) = xor eR dL := by
  constructor
  · intro h
    have hs :
        xor (xor (g k (xor R dR)) (g k R)) dL = eR := by
      simpa only [feistelXorDiff_eq, Prod.snd] using
        congrArg Prod.snd h
    exact (xor_right_eq_iff _ _ _).mp hs
  · intro h
    rw [feistelXorDiff_eq]
    apply Prod.ext
    · rfl
    · exact (xor_right_eq_iff _ _ _).mpr h

/-- Standard XOR-input/XOR-output DDT of one 64-bit Feistel round.
    An input is a pair `(L, R)`, not a concatenated bitvector. -/
def xorDDT_G (k : V 32) (inputDiff outputDiff : V 32 × V 32) : Nat :=
  ((Finset.univ : Finset (V 32 × V 32)).filter (fun p =>
    feistelXorDiff k inputDiff.1 inputDiff.2 p.1 p.2 = outputDiff)).card

/-- Exactly `2^32` choices of the left input word are possible for
    every right-input solution of the differential equation. -/
theorem xorDDT_G_of_left_eq (k dL dR eR : V 32) :
    xorDDT_G k (dL, dR) (dR, eR) =
      Fintype.card (V 32) * xorDDT_g k dR (xor eR dL) := by
  have hfilter :
      ((Finset.univ : Finset (V 32 × V 32)).filter (fun p =>
        feistelXorDiff k dL dR p.1 p.2 = (dR, eR))) =
      (Finset.univ : Finset (V 32)) ×ˢ
        ((Finset.univ : Finset (V 32)).filter (fun R =>
          xor (g k (xor R dR)) (g k R) = xor eR dL)) := by
    ext p
    rcases p with ⟨L, R⟩
    simp only [Finset.mem_filter, Finset.mem_univ,
      Finset.mem_product, true_and]
    exact feistelXorDiff_condition k dL dR eR L R
  unfold xorDDT_G xorDDT_g
  rw [hfilter, Finset.card_product, Finset.card_univ]

/-- A one-round XOR differential is impossible if the output left
    difference does not equal the input right difference. -/
theorem xorDDT_G_of_left_ne
    (k dL dR eL eR : V 32) (h : eL ≠ dR) :
    xorDDT_G k (dL, dR) (eL, eR) = 0 := by
  unfold xorDDT_G
  have hempty :
      ((Finset.univ : Finset (V 32 × V 32)).filter (fun p =>
        feistelXorDiff k dL dR p.1 p.2 = (eL, eR))) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro p _ hp
    rcases p with ⟨L, R⟩
    have hfirst : dR = eL := by
      simpa only [feistelXorDiff_eq, Prod.fst] using
        congrArg Prod.fst hp
    exact h hfirst.symm
  rw [hempty]
  rfl

/-- The cardinality of 32-bit words, without enumerating them. -/
private theorem card_V32 : Fintype.card (V 32) = 2 ^ 32 := by
  change Fintype.card (BitVec 32) = 2 ^ 32
  rw [← FinEnum.card_eq_fintypeCard]
  exact FinEnum.card_bitVec 32

/-- Exact ordinary XOR-DDT of one Magma Feistel round.
    The first output difference is forced to equal `dR`. -/
theorem xorDDT_G_formula (k dL dR eL eR : V 32) :
    xorDDT_G k (dL, dR) (eL, eR) =
      if eL = dR then
        2 ^ 32 * xorDDT_g k dR (xor eR dL)
      else 0 := by
  by_cases h : eL = dR
  · subst eL
    rw [ite_eq_left (rfl : dR = dR), xorDDT_G_of_left_eq, card_V32]
  · rw [ite_eq_right h, xorDDT_G_of_left_ne k dL dR eL eR h]

/-- The verified four-state carry-matrix expression computes the
    DDT of a complete 64-bit Feistel round, up to a factor of 2^32.
    This is the form best suited for subsequent round-level analysis. -/
theorem xorDDT_G_eq_carryMatrixCount
    (k dL dR out : V 32) :
    xorDDT_G k (dL, dR)
      (dR, xor (rot11 out) dL) =
      2 ^ 32 *
        carryMatrixCount
          (wordDigits k)
          (wordDigits dR)
          (wordDigits out) := by
  calc
    xorDDT_G k (dL, dR)
        (dR, xor (rot11 out) dL) =
        Fintype.card (V 32) *
          xorDDT_g k dR
            (xor (xor (rot11 out) dL) dL) :=
      xorDDT_G_of_left_eq k dL dR
        (xor (rot11 out) dL)

    _ = 2 ^ 32 *
          xorDDT_g k dR (rot11 out) := by
      rw [card_V32, xor_twice_right]

    _ = 2 ^ 32 *
          carryMatrixCount
            (wordDigits k)
            (wordDigits dR)
            (wordDigits out) :=
      congrArg (fun n : Nat => 2 ^ 32 * n)
        (xorDDT_g_eq_carryMatrixCount k dR out)

end Magma.FeistelDDT

namespace Magma.MultiRoundDDT

/-- A Feistel state consists of the left and right 32-bit words. -/
abbrev FeistelState := V 32 × V 32

/-- Componentwise XOR of two Feistel states. -/
def stateXor (p q : FeistelState) : FeistelState :=
  (xor p.1 q.1, xor p.2 q.2)

/-- Recover the other state from a state and their XOR difference. -/
private theorem stateXor_recover (p q : FeistelState) :
    stateXor p (stateXor q p) = q := by
  rcases p with ⟨pL, pR⟩
  rcases q with ⟨qL, qR⟩
  apply Prod.ext
  · change pL ^^^ (qL ^^^ pL) = qL
    calc
      pL ^^^ (qL ^^^ pL) = (pL ^^^ pL) ^^^ qL := by ac_rfl
      _ = qL := by simp only [BitVec.xor_self, BitVec.zero_xor]
  · change pR ^^^ (qR ^^^ pR) = qR
    calc
      pR ^^^ (qR ^^^ pR) = (pR ^^^ pR) ^^^ qR := by ac_rfl
      _ = qR := by simp only [BitVec.xor_self, BitVec.zero_xor]

/-- XOR with the original state cancels an input difference. -/
private theorem stateXor_cancel_right (p q : FeistelState) :
    stateXor (stateXor p q) p = q := by
  rcases p with ⟨pL, pR⟩
  rcases q with ⟨qL, qR⟩
  apply Prod.ext
  · change (pL ^^^ qL) ^^^ pL = qL
    calc
      (pL ^^^ qL) ^^^ pL = (pL ^^^ pL) ^^^ qL := by ac_rfl
      _ = qL := by simp only [BitVec.xor_self, BitVec.zero_xor]
  · change (pR ^^^ qR) ^^^ pR = qR
    calc
      (pR ^^^ qR) ^^^ pR = (pR ^^^ pR) ^^^ qR := by ac_rfl
      _ = qR := by simp only [BitVec.xor_self, BitVec.zero_xor]

/-- Exact one-round difference, retaining the actual base state `p`.
    This is a deterministic identity, not a Markov assumption. -/
theorem stateXor_G_eq_feistel (k : V 32) (p q : FeistelState) :
    stateXor (G k q) (G k p) =
      feistelXorDiff k (stateXor q p).1 (stateXor q p).2 p.1 p.2 := by
  calc
    stateXor (G k q) (G k p) =
        stateXor (G k (stateXor p (stateXor q p))) (G k p) := by
      rw [stateXor_recover]
    _ = feistelXorDiff k (stateXor q p).1 (stateXor q p).2 p.1 p.2 := by
      rfl

/-- The result of applying `n` Feistel rounds with the given keys,
    in order of their `Fin n` indices. -/
def iterateG (n : Nat) (keys : Fin n → V 32)
    (p : FeistelState) : FeistelState :=
  Fin.foldl n (fun state i => G (keys i) state) p

/-- The empty round sequence is the identity. -/
theorem iterateG_zero (keys : Fin 0 → V 32) (p : FeistelState) :
    iterateG 0 keys p = p := by
  simp only [iterateG, Fin.foldl_zero]

/-- Split off the last round, keeping the order of the key schedule. -/
theorem iterateG_succ (n : Nat) (keys : Fin (n + 1) → V 32)
    (p : FeistelState) :
    iterateG (n + 1) keys p =
      G (keys (Fin.last n))
        (iterateG n (fun i => keys i.castSucc) p) := by
  unfold iterateG
  rw [Fin.foldl_succ_last]

/-- Actual fixed-key XOR difference after `n` Feistel rounds.
    The two executions share the same round keys and have related inputs. -/
def multiRoundDelta (n : Nat) (keys : Fin n → V 32)
    (start inputDiff : FeistelState) : FeistelState :=
  stateXor (iterateG n keys (stateXor start inputDiff))
    (iterateG n keys start)

/-- With zero rounds, the output difference equals the input difference. -/
theorem multiRoundDelta_zero (keys : Fin 0 → V 32)
    (start inputDiff : FeistelState) :
    multiRoundDelta 0 keys start inputDiff = inputDiff := by
  simp only [multiRoundDelta, iterateG_zero]
  exact stateXor_cancel_right start inputDiff

/-- Exact recursive propagation of an XOR difference.
    Crucially, the final Feistel transition depends on the *base state*
    after the first `n` rounds, not merely on the previous difference. -/
theorem multiRoundDelta_succ (n : Nat) (keys : Fin (n + 1) → V 32)
    (start inputDiff : FeistelState) :
    multiRoundDelta (n + 1) keys start inputDiff =
      feistelXorDiff (keys (Fin.last n))
        (multiRoundDelta n (fun i => keys i.castSucc) start inputDiff).1
        (multiRoundDelta n (fun i => keys i.castSucc) start inputDiff).2
        (iterateG n (fun i => keys i.castSucc) start).1
        (iterateG n (fun i => keys i.castSucc) start).2 := by
  let pre : Fin n → V 32 := fun i => keys i.castSucc
  let p : FeistelState := iterateG n pre start
  let q : FeistelState := iterateG n pre (stateXor start inputDiff)
  calc
    multiRoundDelta (n + 1) keys start inputDiff =
        stateXor (G (keys (Fin.last n)) q)
          (G (keys (Fin.last n)) p) := by
      simp only [multiRoundDelta, iterateG_succ]
      rfl
    _ = feistelXorDiff (keys (Fin.last n))
          (stateXor q p).1 (stateXor q p).2 p.1 p.2 :=
      stateXor_G_eq_feistel _ _ _
    _ = feistelXorDiff (keys (Fin.last n))
          (multiRoundDelta n pre start inputDiff).1
          (multiRoundDelta n pre start inputDiff).2 p.1 p.2 := by
      rfl

/-- A forced relation between successive 64-bit XOR differences:
    the left half of the new difference equals the preceding right half. -/
theorem multiRoundDelta_succ_left (n : Nat)
    (keys : Fin (n + 1) → V 32) (start inputDiff : FeistelState) :
    (multiRoundDelta (n + 1) keys start inputDiff).1 =
      (multiRoundDelta n (fun i => keys i.castSucc) start inputDiff).2 := by
  rw [multiRoundDelta_succ, feistelXorDiff_eq]

/-- A single round of `multiRoundDelta` is precisely `feistelXorDiff`. -/
theorem multiRoundDelta_one (k : V 32)
    (start inputDiff : FeistelState) :
    multiRoundDelta 1 (fun _ : Fin 1 => k) start inputDiff =
      feistelXorDiff k inputDiff.1 inputDiff.2 start.1 start.2 := by
  have h := multiRoundDelta_succ 0
    (fun _ : Fin 1 => k) start inputDiff
  simpa only [multiRoundDelta_zero, iterateG_zero] using h

/-- Exact XOR-DDT of the composed *fixed-key* `n`-round permutation.
    Do not compute this definition by `decide` for a 64-bit state. -/
def xorDDT_rounds (n : Nat) (keys : Fin n → V 32)
    (inputDiff outputDiff : FeistelState) : Nat :=
  ((Finset.univ : Finset FeistelState).filter (fun start =>
    multiRoundDelta n keys start inputDiff = outputDiff)).card

/-- The new definition agrees with the already proved one-round DDT. -/
theorem xorDDT_rounds_one (k : V 32)
    (inputDiff outputDiff : FeistelState) :
    xorDDT_rounds 1 (fun _ : Fin 1 => k) inputDiff outputDiff =
      xorDDT_G k inputDiff outputDiff := by
  have hset :
      ((Finset.univ : Finset FeistelState).filter (fun start =>
        multiRoundDelta 1 (fun _ : Fin 1 => k) start inputDiff = outputDiff)) =
      ((Finset.univ : Finset FeistelState).filter (fun start =>
        feistelXorDiff k inputDiff.1 inputDiff.2 start.1 start.2 = outputDiff)) := by
    ext start
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [multiRoundDelta_one]
  unfold xorDDT_rounds xorDDT_G
  exact congrArg Finset.card hset

/-- The 32-round iteration agrees with the round sequence appearing in
    the RFC encryption specification, before the final swap/packing.
    This theorem reuses the existing `E_as_fold` proof. -/
theorem encrypt_as_iterG (K : V 256) (a : V 64) :
    encrypt K a =
      pack (Prod.swap
        (iterateG 32 (roundKey K) (split 32 32 a))) := by
  simpa only [encrypt, iterateG] using
    (E_as_fold (roundKey K) a)

-- two rounds

/-- The fixed keys of two consecutive Feistel rounds, in forward order. -/
def twoRoundKeys (k₀ k₁ : V 32) : Fin 2 → V 32 :=
  ![k₀, k₁]

/-- Ordinary XOR difference of the 32-bit round function at a base word. -/
private def gDifference (k x d : V 32) : V 32 :=
  xor (g k (xor x d)) (g k x)

/-- Cancelling two XOR operations by the same right operand. -/
private theorem xor_right_right (u a : V 32) :
    xor (xor u a) a = u := by
  change (u ^^^ a) ^^^ a = u
  rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

/-- An equation with a fixed XOR operand can be rearranged. -/
private theorem xor_right_iff (u a b : V 32) :
    xor u a = b ↔ u = xor b a := by
  constructor
  · intro h
    have hh := congrArg (fun w : V 32 => xor w a) h
    simpa only [xor_right_right] using hh
  · intro h
    rw [h]
    exact xor_right_right b a

/-- The difference after exactly two rounds, calculated symbolically. -/
private theorem twoRoundDelta_formula (k₀ k₁ aL aR L R : V 32) :
    multiRoundDelta 2 (twoRoundKeys k₀ k₁) (L, R) (aL, aR) =
      (xor (gDifference k₀ R aR) aL,
       xor (gDifference k₁ (xor (g k₀ R) L)
         (xor (gDifference k₀ R aR) aL)) aR) := by
  let pre : Fin 1 → V 32 :=
    fun i => twoRoundKeys k₀ k₁ i.castSucc
  have hpre : pre = (fun _ : Fin 1 => k₀) := by
    funext i
    fin_cases i ; rfl
  have hdelta :
      multiRoundDelta 1 pre (L, R) (aL, aR) =
        (aR, xor (gDifference k₀ R aR) aL) := by
    rw [hpre, multiRoundDelta_one, feistelXorDiff_eq]
    rfl
  have hstate :
      iterateG 1 pre (L, R) = (R, xor (g k₀ R) L) := by
    rw [hpre]
    rw [iterateG_succ, iterateG_zero]
    rfl
  rw [multiRoundDelta_succ]
  rw [hdelta, hstate, feistelXorDiff_eq]
  rfl

/-- Change coordinates from `(L,R)` to `(R, g[k₀](R) XOR L)`.
    The transformation is a bijection for every fixed first-round key. -/
private def twoRoundCoordinates (k₀ : V 32) :
    FeistelState ≃ FeistelState where
  toFun := fun p => (p.2, xor (g k₀ p.2) p.1)
  invFun := fun q => (xor (g k₀ q.1) q.2, q.1)
  left_inv := by
    intro p
    rcases p with ⟨L, R⟩
    apply Prod.ext
    · change xor (g k₀ R) (xor (g k₀ R) L) = L
      change (g k₀ R) ^^^ ((g k₀ R) ^^^ L) = L
      rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
    · rfl
  right_inv := by
    intro q
    rcases q with ⟨R, Z⟩
    apply Prod.ext
    · rfl
    · change xor (g k₀ R) (xor (g k₀ R) Z) = Z
      change (g k₀ R) ^^^ ((g k₀ R) ^^^ Z) = Z
      rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

/-- The exact two-round differential condition splits across the
    bijective coordinates `(R, g[k₀](R) XOR L)`. -/
private theorem twoRoundCondition
    (k₀ k₁ aL aR bL bR L R : V 32) :
    (multiRoundDelta 2 (twoRoundKeys k₀ k₁) (L, R) (aL, aR) =
       (bL, bR)) ↔
      (gDifference k₀ R aR = xor bL aL ∧
       gDifference k₁ (xor (g k₀ R) L) bL = xor bR aR) := by
  rw [twoRoundDelta_formula]
  constructor
  · intro h
    have hL := congrArg Prod.fst h
    have hR := congrArg Prod.snd h
    change xor (gDifference k₀ R aR) aL = bL at hL
    change xor (gDifference k₁ (xor (g k₀ R) L)
      (xor (gDifference k₀ R aR) aL)) aR = bR at hR
    have h₀ := (xor_right_iff _ _ _).mp hL
    rw [hL] at hR
    exact ⟨h₀, (xor_right_iff _ _ _).mp hR⟩
  · rintro ⟨h₀, h₁⟩
    have hL : xor (gDifference k₀ R aR) aL = bL :=
      (xor_right_iff _ _ _).mpr h₀
    have hR : xor (gDifference k₁ (xor (g k₀ R) L) bL) aR = bR :=
      (xor_right_iff _ _ _).mpr h₁
    apply Prod.ext
    · exact hL
    · simpa only [hL] using hR

/-- Exact fixed-key XOR-DDT of a two-round Feistel network.

    Unlike generic multi-round Markov approximations, this factorization
    is an *identity*. The left initial half freely parametrizes the
    second round's base input after the first round. -/
theorem xorDDT_rounds_two (k₀ k₁ aL aR bL bR : V 32) :
    xorDDT_rounds 2 (twoRoundKeys k₀ k₁) (aL, aR) (bL, bR) =
      xorDDT_g k₀ aR (xor bL aL) *
        xorDDT_g k₁ bL (xor bR aR) := by
  let p₀ : V 32 → Prop :=
    fun R => gDifference k₀ R aR = xor bL aL
  let p₁ : V 32 → Prop :=
    fun Z => gDifference k₁ Z bL = xor bR aR
  let s₀ : Finset (V 32) := (Finset.univ : Finset (V 32)).filter p₀
  let s₁ : Finset (V 32) := (Finset.univ : Finset (V 32)).filter p₁
  have hcoordinate :
      xorDDT_rounds 2 (twoRoundKeys k₀ k₁) (aL, aR) (bL, bR) =
        ((Finset.univ : Finset FeistelState).filter
          (fun q => p₀ q.1 ∧ p₁ q.2)).card := by
    unfold xorDDT_rounds
    refine Finset.card_equiv (twoRoundCoordinates k₀) ?_
    intro x
    rcases x with ⟨L, R⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change
      (multiRoundDelta 2 (twoRoundKeys k₀ k₁) (L, R) (aL, aR) =
        (bL, bR)) ↔
      (gDifference k₀ R aR = xor bL aL ∧
       gDifference k₁ (xor (g k₀ R) L) bL = xor bR aR)
    exact twoRoundCondition k₀ k₁ aL aR bL bR L R
  have hproduct :
      ((Finset.univ : Finset FeistelState).filter
        (fun q => p₀ q.1 ∧ p₁ q.2)) = s₀ ×ˢ s₁ := by
    ext q
    rcases q with ⟨R, Z⟩
    simp only [Finset.mem_filter, Finset.mem_univ,
      Finset.mem_product, true_and]
    simp only [s₀, s₁, Finset.mem_filter,
      Finset.mem_univ, true_and]
  have hs₀ : s₀.card = xorDDT_g k₀ aR (xor bL aL) := by
    rfl
  have hs₁ : s₁.card = xorDDT_g k₁ bL (xor bR aR) := by
    rfl
  calc
    xorDDT_rounds 2 (twoRoundKeys k₀ k₁) (aL, aR) (bL, bR) =
        ((Finset.univ : Finset FeistelState).filter
          (fun q => p₀ q.1 ∧ p₁ q.2)).card := hcoordinate
    _ = (s₀ ×ˢ s₁).card := congrArg Finset.card hproduct
    _ = s₀.card * s₁.card := Finset.card_product s₀ s₁
    _ = xorDDT_g k₀ aR (xor bL aL) *
          xorDDT_g k₁ bL (xor bR aR) := by
      rw [hs₀, hs₁]

/-- Replace the two round-function DDT factors by verified carry-matrix
    counts. These output differences are rotated back to align with `g`. -/
theorem xorDDT_rounds_two_matrix (k₀ k₁ aL aR u v : V 32) :
    xorDDT_rounds 2 (twoRoundKeys k₀ k₁) (aL, aR)
      (xor (rot11 u) aL, xor (rot11 v) aR) =
      carryMatrixCount (wordDigits k₀) (wordDigits aR) (wordDigits u) *
        carryMatrixCount (wordDigits k₁)
          (wordDigits (xor (rot11 u) aL)) (wordDigits v) := by
  rw [xorDDT_rounds_two]
  rw [xor_right_right, xor_right_right]
  rw [xorDDT_g_eq_carryMatrixCount, xorDDT_g_eq_carryMatrixCount]

-- three rounds

/-- The first three round keys in encryption order. -/
def threeRoundKeys (k₀ k₁ k₂ : V 32) : Fin 3 → V 32 :=
  ![k₀, k₁, k₂]

/-! ### Zero-left output: exact reduction to two rounds

A last-round output difference `(0, bR)` forces the preceding difference
`(bR, 0)`. Both executions then evaluate the last round function on the same
right word, so its contribution cancels regardless of the third key.

The three- and two-round predicates therefore agree on every starting state.
Their exact DDT counts coincide, and the two-round formula factors this slice
into `xorDDT_g k₀ aR (xor bR aL) * xorDDT_g k₁ bR aR`.
This uses no independence or Markov assumption and enumerates no states.
-/

/-- A last Feistel round can output `(0,bR)` exactly when its input
    XOR difference was `(bR,0)`; the last key plays no role. -/
private theorem feistelXorDiff_zero_left_iff
    (k dL dR L R bR : V 32) :
    feistelXorDiff k dL dR L R = (0#32, bR) ↔
      (dL, dR) = (bR, 0#32) := by
  rw [feistelXorDiff_eq]
  constructor
  · intro h
    have hr : dR = (0#32) := congrArg Prod.fst h
    have hl : xor (xor (g k (xor R dR)) (g k R)) dL = bR :=
      congrArg Prod.snd h
    rw [hr] at hl
    change ((g k (R ^^^ (0#32))) ^^^ (g k R)) ^^^ dL = bR at hl
    simp only [BitVec.xor_zero, BitVec.xor_self, BitVec.zero_xor] at hl
    exact Prod.ext hl hr
  · intro h
    have hl : dL = bR := congrArg Prod.fst h
    have hr : dR = (0#32) := congrArg Prod.snd h
    rw [hl, hr]
    change (0#32, ((g k (R ^^^ (0#32))) ^^^ (g k R)) ^^^ bR) = (0#32, bR)
    simp only [BitVec.xor_zero, BitVec.xor_self, BitVec.zero_xor]

/-- Pointwise predicate equivalence. In particular, the third key is
    irrelevant whenever the LEFT output difference is zero. -/
theorem threeRound_zero_left_iff_twoRound
    (k₀ k₁ k₂ aL aR bR : V 32) (start : FeistelState) :
    multiRoundDelta 3 (threeRoundKeys k₀ k₁ k₂) start (aL, aR) =
        (0#32, bR) ↔
      multiRoundDelta 2 (twoRoundKeys k₀ k₁) start (aL, aR) =
        (bR, 0#32) := by
  have hprefix :
      (fun i : Fin 2 => (threeRoundKeys k₀ k₁ k₂) i.castSucc) =
        twoRoundKeys k₀ k₁ := by
    funext i
    fin_cases i <;> rfl
  have hlast :
      threeRoundKeys k₀ k₁ k₂ (Fin.last 2) = k₂ := by
    rfl
  rw [multiRoundDelta_succ 2 (threeRoundKeys k₀ k₁ k₂) start (aL, aR)]
  rw [hprefix, hlast]
  exact feistelXorDiff_zero_left_iff k₂ _ _ _ _ bR

/-- Exact equality of DDT COUNTS, not just equivalence of positivity.
    The proof only compares predicates, never constructs `Finset.univ`. -/
theorem xorDDT_rounds_three_zero_left_eq_two
    (k₀ k₁ k₂ aL aR bR : V 32) :
    xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
        (aL, aR) (0#32, bR) =
      xorDDT_rounds 2 (twoRoundKeys k₀ k₁)
        (aL, aR) (bR, 0#32) := by
  have hsets :
      ((Finset.univ : Finset FeistelState).filter
        (fun start =>
          multiRoundDelta 3 (threeRoundKeys k₀ k₁ k₂)
            start (aL, aR) = (0#32, bR))) =
      ((Finset.univ : Finset FeistelState).filter
        (fun start =>
          multiRoundDelta 2 (twoRoundKeys k₀ k₁)
            start (aL, aR) = (bR, 0#32))) := by
    ext start
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact threeRound_zero_left_iff_twoRound
      k₀ k₁ k₂ aL aR bR start
  unfold xorDDT_rounds
  exact congrArg Finset.card hsets

/-- The structural factorization: three-round DDT with zero LEFT
    output is the PRODUCT of two exact 32-bit round-function DDTs.
    No condition or hypothesis about the third-round key. -/
theorem xorDDT_rounds_three_zero_left_factorization
    (k₀ k₁ k₂ aL aR bR : V 32) :
    xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
        (aL, aR) (0#32, bR) =
      xorDDT_g k₀ aR (xor bR aL) *
        xorDDT_g k₁ bR aR := by
  have hzero : xor (0#32) aR = aR := by
    change (0#32) ^^^ aR = aR
    exact BitVec.zero_xor
  rw [xorDDT_rounds_three_zero_left_eq_two, xorDDT_rounds_two, hzero]

/-! ### Zero-left row mass for arbitrary round keys -/

private theorem zeroLeft_word_card : Fintype.card (V 32) = 2 ^ 32 := by
  rw [← FinEnum.card_eq_fintypeCard]
  exact FinEnum.card_bitVec 32

/-- Summing over `aL` gives the second-round DDT count times `2^32`.
    The result is independent of the first and third keys. -/
theorem zeroLeft_row_mass (k₀ k₁ k₂ aR bR : V 32) :
    (∑ aL : V 32,
      xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
        (aL, aR) (0#32, bR)) =
      Fintype.card (V 32) * xorDDT_g k₁ bR aR := by
  classical
  calc
    (∑ aL : V 32,
      xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
        (aL, aR) (0#32, bR)) =
        ∑ aL : V 32,
          xorDDT_g k₀ aR (xor bR aL) * xorDDT_g k₁ bR aR := by
      apply Finset.sum_congr rfl
      intro aL _
      exact xorDDT_rounds_three_zero_left_factorization k₀ k₁ k₂ aL aR bR
    _ = (∑ aL : V 32, xorDDT_g k₀ aR (xor bR aL)) *
          xorDDT_g k₁ bR aR := (Finset.sum_mul _ _ _).symm
    _ = Fintype.card (V 32) * xorDDT_g k₁ bR aR := by
      rw [xorDDT_g_sum_output_xor]

/-- A fixed `bR` column vanishes exactly when the second-round
    differential is impossible, for arbitrary round keys. -/
theorem zeroLeft_column_empty_iff (k₀ k₁ k₂ aR bR : V 32) :
    (∀ aL : V 32,
      xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
        (aL, aR) (0#32, bR) = 0) ↔
      xorDDT_g k₁ bR aR = 0 := by
  constructor
  · intro hall
    have hsum :
        (∑ aL : V 32,
          xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
            (aL, aR) (0#32, bR)) = 0 := by
      simp only [hall, Finset.sum_const_zero]
    rw [zeroLeft_row_mass] at hsum
    rcases mul_eq_zero.mp hsum with hc | hb
    · rw [zeroLeft_word_card] at hc
      norm_num at hc
    · exact hb
  · intro hb aL
    rw [xorDDT_rounds_three_zero_left_factorization, hb, mul_zero]

/-- One Boolean carry test excludes every `aL` in a fixed `bR` column. -/
theorem zeroLeft_column_empty_iff_boolean (k₀ k₁ k₂ aR bR : V 32) :
    (∀ aL : V 32,
      xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
        (aL, aR) (0#32, bR) = 0) ↔
      xorDiffPossibleBooleanFast k₁ bR aR = false := by
  rw [zeroLeft_column_empty_iff, xorDiffPossibleBooleanFast_eq]
  exact (xorDiffPossibleBoolean_false_iff k₁ bR aR).symm

/-- The zero-left slice has total DDT mass `2^64` for arbitrary round keys
    and right input difference. All sums are symbolic. -/
theorem zeroLeft_total_mass_all_keys (k₀ k₁ k₂ aR : V 32) :
    (∑ p : V 32 × V 32,
      xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
        (p.1, aR) (0#32, p.2)) = 2 ^ 64 := by
  classical
  calc
    (∑ p : V 32 × V 32,
      xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
        (p.1, aR) (0#32, p.2)) =
        ∑ bR : V 32, ∑ aL : V 32,
          xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
            (aL, aR) (0#32, bR) := by
      rw [Fintype.sum_prod_type_right]
    _ = ∑ bR : V 32, Fintype.card (V 32) * xorDDT_g k₁ bR aR := by
      apply Finset.sum_congr rfl
      intro bR _
      exact zeroLeft_row_mass k₀ k₁ k₂ aR bR
    _ = Fintype.card (V 32) * ∑ bR : V 32, xorDDT_g k₁ bR aR :=
      (Finset.mul_sum _ _ _).symm
    _ = Fintype.card (V 32) * Fintype.card (V 32) := by
      rw [xorDDT_g_sum_input]
    _ = 2 ^ 64 := by rw [zeroLeft_word_card]; norm_num

/-- Universal exact formula for the zero-left output slice with the
    first two keys zero. No heuristic independence assumption appears. -/
theorem zeroLeft_three_round_exact_sbox_product
    (k₂ aL aR bR : V 32) :
    xorDDT_rounds 3 (threeRoundKeys (0#32) (0#32) k₂)
      (aL, aR) (0#32, bR) =
    (∏ i : Fin 8,
       SBoxProperties.ddt i (wordDigits aR i)
         (wordDigits ((xor bR aL).rotateRight 11) i)) *
    (∏ i : Fin 8,
       SBoxProperties.ddt i (wordDigits bR i)
         (wordDigits (aR.rotateRight 11) i)) := by
  calc
    xorDDT_rounds 3 (threeRoundKeys (0#32) (0#32) k₂)
        (aL, aR) (0#32, bR) =
        xorDDT_g (0#32) aR (xor bR aL) *
          xorDDT_g (0#32) bR aR :=
      xorDDT_rounds_three_zero_left_factorization
        (0#32) (0#32) k₂ aL aR bR
    _ = xorDDT_g (0#32) aR
            (rot11 ((xor bR aL).rotateRight 11)) *
          xorDDT_g (0#32) bR (rot11 (aR.rotateRight 11)) := by
      simp only [rot11_rotateRight11]
    _ = _ := by
      simp only [xorDDT_g_zero_key_factor]

/-- Independence from the third key, for the restricted bL = 0 slice.
    This is an equality of exact differential counts. -/
theorem xorDDT_rounds_three_zero_left_independent_of_k₂
    (k₀ k₁ k₂ k₂' aL aR bR : V 32) :
    xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
        (aL, aR) (0#32, bR) =
      xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂')
        (aL, aR) (0#32, bR) := by
  rw [xorDDT_rounds_three_zero_left_factorization,
      xorDDT_rounds_three_zero_left_factorization]

/-- Structural zero condition: it suffices that ONE of the two
    independent 32-bit g-DDT factors is zero. -/
theorem xorDDT_rounds_three_zero_left_of_first_zero
    (k₀ k₁ k₂ aL aR bR : V 32)
    (h : xorDDT_g k₀ aR (xor bR aL) = 0) :
    xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
      (aL, aR) (0#32, bR) = 0 := by
  rw [xorDDT_rounds_three_zero_left_factorization, h]
  simp

theorem xorDDT_rounds_three_zero_left_of_second_zero (k₀ k₁ k₂ aL aR bR : V 32)
    (h : xorDDT_g k₁ bR aR = 0) :
    xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂) (aL, aR) (0#32, bR) = 0 := by
  rw [xorDDT_rounds_three_zero_left_factorization, h]
  simp

/-- Fast, EXACT support test for three Feistel rounds with left output
    difference 0. Both factors are checked by the proven carry automaton. -/
def zeroLeftPossibleByTwoG
    (k₀ k₁ aL aR bR : V 32) : Bool :=
  xorDiffPossible k₀ aR (xor bR aL) &&
    xorDiffPossible k₁ bR aR

/-- The proposed two-factor Boolean test is sound AND complete for
    strictly positive three-round DDT, for every third-round key. -/
theorem zeroLeftPossibleByTwoG_iff
    (k₀ k₁ k₂ aL aR bR : V 32) :
    zeroLeftPossibleByTwoG k₀ k₁ aL aR bR = true ↔
      0 < xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
        (aL, aR) (0#32, bR) := by
  rw [xorDDT_rounds_three_zero_left_factorization]
  unfold zeroLeftPossibleByTwoG
  constructor
  · intro h
    obtain ⟨h₀, h₁⟩ := Bool.and_eq_true_iff.mp h
    exact Nat.mul_pos
      ((xorDiffPossible_iff k₀ aR (xor bR aL)).mp h₀)
      ((xorDiffPossible_iff k₁ bR aR).mp h₁)
  · intro h
    apply Bool.and_eq_true_iff.mpr
    constructor
    · exact (xorDiffPossible_iff k₀ aR (xor bR aL)).mpr
        (Nat.pos_of_mul_pos_right h)
    · exact (xorDiffPossible_iff k₁ bR aR).mpr
        (Nat.pos_of_mul_pos_left h)

/-- Equivalent criterion for a zero entry, with no enumeration of
    `Finset.univ : Finset FeistelState`. -/
theorem zeroLeftPossibleByTwoG_false_iff
    (k₀ k₁ k₂ aL aR bR : V 32) :
    zeroLeftPossibleByTwoG k₀ k₁ aL aR bR = false ↔
      xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
        (aL, aR) (0#32, bR) = 0 := by
  constructor
  · intro hf
    by_contra hn
    have hp : 0 < xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
        (aL, aR) (0#32, bR) := by omega
    have ht := (zeroLeftPossibleByTwoG_iff k₀ k₁ k₂ aL aR bR).mpr hp
    rw [hf] at ht
    cases ht
  · intro hz
    cases ht : zeroLeftPossibleByTwoG k₀ k₁ aL aR bR with
    | false => rfl
    | true =>
      have hp := (zeroLeftPossibleByTwoG_iff k₀ k₁ k₂ aL aR bR).mp ht
      rw [hz] at hp
      cases hp

/-- A positive DDT remains positive after changing the THIRD key,
    as long as the left output difference is zero. -/
theorem zeroLeft_pos_for_every_third_key
    (k₀ k₁ k₂ k₂' aL aR bR : V 32)
    (h : 0 < xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂')
      (aL, aR) (0#32, bR)) :
    0 < xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
      (aL, aR) (0#32, bR) := by
  rw [xorDDT_rounds_three_zero_left_independent_of_k₂
    k₀ k₁ k₂ k₂' aL aR bR]
  exact h

/-- The base state after two Feistel rounds. -/
private theorem iterateG_two_formula
    (k₀ k₁ L R : V 32) :
    iterateG 2 (twoRoundKeys k₀ k₁) (L, R) =
      (xor (g k₀ R) L,
       xor (g k₁ (xor (g k₀ R) L)) R) := by
  rw [iterateG_succ]
  have hpre :
      (fun i : Fin 1 => (twoRoundKeys k₀ k₁) i.castSucc) =
        (fun _ : Fin 1 => k₀) := by
    funext i
    fin_cases i ; rfl
  rw [hpre, iterateG_succ, iterateG_zero]
  rfl

/-- The three-round XOR difference, keeping the base input explicitly.

    Z is the right word after the first round, C its XOR difference;
    D is the difference of the right word after the second round. -/
private theorem threeRoundDelta_formula
    (k₀ k₁ k₂ aL aR L R : V 32) :
    let Z := xor (g k₀ R) L
    let C := xor (gDifference k₀ R aR) aL
    let D := xor (gDifference k₁ Z C) aR
    multiRoundDelta 3 (threeRoundKeys k₀ k₁ k₂) (L, R) (aL, aR) =
      (D, xor (gDifference k₂ (xor (g k₁ Z) R) D) C) := by
  have hpre :
      (fun i : Fin 2 => (threeRoundKeys k₀ k₁ k₂) i.castSucc) =
        twoRoundKeys k₀ k₁ := by
    funext i
    fin_cases i <;> rfl
  rw [multiRoundDelta_succ]
  rw [hpre, twoRoundDelta_formula, iterateG_two_formula,
      feistelXorDiff_eq]
  rfl

/-- Coupled constraints for an exact three-round differential.

    R and Z are independent *coordinates*, but the final-round
    condition depends on both. This is not a product of DDT entries. -/
def threeRoundCoupled
    (k₀ k₁ k₂ aL aR bL bR R Z : V 32) : Prop :=
  let C := xor (gDifference k₀ R aR) aL
  let D := xor (gDifference k₁ Z C) aR
  D = bL ∧
    gDifference k₂ (xor (g k₁ Z) R) bL = xor bR C

/-- The three-round difference condition expressed in the first two
    rounds' bijective coordinates. -/
private theorem threeRoundCondition
    (k₀ k₁ k₂ aL aR bL bR L R : V 32) :
    multiRoundDelta 3 (threeRoundKeys k₀ k₁ k₂) (L, R) (aL, aR) =
        (bL, bR) ↔
      threeRoundCoupled k₀ k₁ k₂ aL aR bL bR
        R (xor (g k₀ R) L) := by
  rw [threeRoundDelta_formula]
  let Z : V 32 := xor (g k₀ R) L
  let C : V 32 := xor (gDifference k₀ R aR) aL
  let D : V 32 := xor (gDifference k₁ Z C) aR
  change
    (D, xor (gDifference k₂ (xor (g k₁ Z) R) D) C) =
      (bL, bR) ↔
    (D = bL ∧
      gDifference k₂ (xor (g k₁ Z) R) bL = xor bR C)
  constructor
  · intro h
    have hL : D = bL := congrArg Prod.fst h
    have hR :
        xor (gDifference k₂ (xor (g k₁ Z) R) D) C = bR :=
      congrArg Prod.snd h
    rw [hL] at hR
    exact ⟨hL, (xor_right_iff _ _ _).mp hR⟩
  · rintro ⟨hL, hR⟩
    apply Prod.ext
    · exact hL
    · rw [hL]
      exact (xor_right_iff _ _ _).mpr hR

/-- Exact number of coupled three-round differential solutions.
    This is a mathematical count; do not evaluate it by `decide`. -/
noncomputable def threeRoundCoupledCount
    (k₀ k₁ k₂ aL aR bL bR : V 32) : Nat := by
  classical
  exact ((Finset.univ : Finset FeistelState).filter (fun q =>
    threeRoundCoupled k₀ k₁ k₂ aL aR bL bR q.1 q.2)).card

/-- Exact fixed-key three-round XOR-DDT, without a Markov assumption.
    It counts correlated conditions in the independent coordinates (R,Z). -/
theorem xorDDT_rounds_three
    (k₀ k₁ k₂ aL aR bL bR : V 32) :
    xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂) (aL, aR) (bL, bR) =
      threeRoundCoupledCount k₀ k₁ k₂ aL aR bL bR := by
  classical
  unfold xorDDT_rounds threeRoundCoupledCount
  refine Finset.card_equiv (twoRoundCoordinates k₀) ?_
  intro p
  rcases p with ⟨L, R⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  change
    (multiRoundDelta 3 (threeRoundKeys k₀ k₁ k₂)
        (L, R) (aL, aR) = (bL, bR)) ↔
      threeRoundCoupled k₀ k₁ k₂ aL aR bL bR
        R (xor (g k₀ R) L)
  exact threeRoundCondition k₀ k₁ k₂ aL aR bL bR L R

open Classical in
/--
  The exact fixed-key three-round XOR-DDT expressed as
  a double sum of indicator functions over the
  intermediate coordinates R and Z.

  The coupled differential conditions are preserved
  without assuming independence between rounds.

  The proof is structural and does not enumerate
  the 2^64 possible input states.
-/
theorem xorDDT_rounds_three_sum
    (k₀ k₁ k₂ aL aR bL bR : V 32) :
    xorDDT_rounds 3
        (threeRoundKeys k₀ k₁ k₂)
        (aL, aR) (bL, bR) =
      ∑ R : V 32, ∑ Z : V 32,
        if threeRoundCoupled
            k₀ k₁ k₂ aL aR bL bR R Z
        then (1 : Nat) else 0 := by
  classical
  rw [xorDDT_rounds_three]
  unfold threeRoundCoupledCount
  rw [Finset.card_filter, Fintype.sum_prod_type]

-- 3 round intersection bounds

/-- The right-half XOR difference after the first Feistel round. -/
private def firstRoundRightDiff (k₀ aL aR R : V 32) : V 32 :=
  xor (gDifference k₀ R aR) aL

/-- Values of Z satisfying the second-round difference condition. -/
private def secondRoundCandidates
    (k₀ k₁ aL aR bL R : V 32) : Finset (V 32) :=
  (Finset.univ : Finset (V 32)).filter (fun Z =>
    xor (gDifference k₁ Z (firstRoundRightDiff k₀ aL aR R)) aR = bL)

/-- Values of Z satisfying the third-round difference condition. -/
private def thirdRoundCandidates
    (k₀ k₁ k₂ aL aR bL bR R : V 32) : Finset (V 32) :=
  (Finset.univ : Finset (V 32)).filter (fun Z =>
    gDifference k₂ (xor (g k₁ Z) R) bL =
      xor bR (firstRoundRightDiff k₀ aL aR R))

/-- For fixed R the exact three-round condition is the intersection
    of its second- and third-round constraints on Z. -/
private theorem threeRoundCoupled_iff_inter
    (k₀ k₁ k₂ aL aR bL bR R Z : V 32) :
    threeRoundCoupled k₀ k₁ k₂ aL aR bL bR R Z ↔
      Z ∈ secondRoundCandidates k₀ k₁ aL aR bL R ∩
        thirdRoundCandidates k₀ k₁ k₂ aL aR bL bR R := by
  classical
  simp only [Finset.mem_inter, secondRoundCandidates,
    thirdRoundCandidates, Finset.mem_filter,
    Finset.mem_univ, true_and]
  change
    (xor (gDifference k₁ Z (firstRoundRightDiff k₀ aL aR R)) aR = bL ∧
     gDifference k₂ (xor (g k₁ Z) R) bL =
       xor bR (firstRoundRightDiff k₀ aL aR R)) ↔
    (xor (gDifference k₁ Z (firstRoundRightDiff k₀ aL aR R)) aR = bL ∧
     gDifference k₂ (xor (g k₁ Z) R) bL =
       xor bR (firstRoundRightDiff k₀ aL aR R))
  rfl

/-- Exact three-round fixed-key XOR-DDT, expressed as a sum of
    intersection cardinalities. There is no independence assumption. -/
theorem xorDDT_rounds_three_intersections
    (k₀ k₁ k₂ aL aR bL bR : V 32) :
    xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂) (aL, aR) (bL, bR) =
      ∑ R : V 32,
        (secondRoundCandidates k₀ k₁ aL aR bL R ∩
         thirdRoundCandidates k₀ k₁ k₂ aL aR bL bR R).card := by
  classical
  rw [xorDDT_rounds_three_sum]
  apply Finset.sum_congr rfl
  intro R _
  calc
    (∑ Z : V 32,
        if threeRoundCoupled k₀ k₁ k₂ aL aR bL bR R Z
        then (1 : Nat) else 0) =
      ((Finset.univ : Finset (V 32)).filter
        (fun Z => threeRoundCoupled k₀ k₁ k₂ aL aR bL bR R Z)).card := by
          rw [Finset.card_filter]
    _ = (secondRoundCandidates k₀ k₁ aL aR bL R ∩
         thirdRoundCandidates k₀ k₁ k₂ aL aR bL bR R).card := by
          apply congrArg Finset.card
          ext Z
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact threeRoundCoupled_iff_inter k₀ k₁ k₂ aL aR bL bR R Z

/-- The second-round candidate count equals the actual XOR-DDT of g[k₁]. -/
private theorem secondRoundCandidates_card
    (k₀ k₁ aL aR bL R : V 32) :
    (secondRoundCandidates k₀ k₁ aL aR bL R).card =
      Magma.CarryAutomaton.xorDDT_g k₁
        (firstRoundRightDiff k₀ aL aR R) (xor bL aR) := by
  unfold secondRoundCandidates Magma.CarryAutomaton.xorDDT_g
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro Z _
  exact xor_right_iff
    (gDifference k₁ Z (firstRoundRightDiff k₀ aL aR R)) aR bL

/-- A rigorous upper bound for the fixed-key three-round DDT.
    It deliberately does NOT multiply probabilities of rounds. -/
theorem xorDDT_rounds_three_le_second
    (k₀ k₁ k₂ aL aR bL bR : V 32) :
    xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂) (aL, aR) (bL, bR) ≤
      ∑ R : V 32,
        Magma.CarryAutomaton.xorDDT_g k₁
          (firstRoundRightDiff k₀ aL aR R) (xor bL aR) := by
  rw [xorDDT_rounds_three_intersections]
  apply Finset.sum_le_sum
  intro R _
  rw [← secondRoundCandidates_card]
  exact Finset.card_le_card Finset.inter_subset_left

/-- If the necessary middle-round differential has no solutions for
    every base word R, the entire three-round differential is impossible. -/
theorem xorDDT_rounds_three_eq_zero_of_middle_impossible
    (k₀ k₁ k₂ aL aR bL bR : V 32)
    (h : ∀ R : V 32,
      Magma.CarryAutomaton.xorDDT_g k₁
        (firstRoundRightDiff k₀ aL aR R) (xor bL aR) = 0) :
    xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂) (aL, aR) (bL, bR) = 0 := by
  have hupper := xorDDT_rounds_three_le_second
    k₀ k₁ k₂ aL aR bL bR
  have hsum :
      (∑ R : V 32,
        Magma.CarryAutomaton.xorDDT_g k₁
          (firstRoundRightDiff k₀ aL aR R) (xor bL aR)) = 0 := by
    apply Finset.sum_eq_zero
    intro R _
    exact h R
  rw [hsum] at hupper
  exact Nat.eq_zero_of_le_zero hupper

-- 3 rounds without independence

/-- The input base words producing a prescribed right-half difference
    after the first Feistel round. -/
private def firstRoundFiber (k₀ aL aR c : V 32) : Finset (V 32) :=
  (Finset.univ : Finset (V 32)).filter (fun R =>
    firstRoundRightDiff k₀ aL aR R = c)

/-- The number of first-round base words in a difference fiber is
    exactly an entry of the XOR-DDT of the round function `g`. -/
private theorem firstRoundFiber_card
    (k₀ aL aR c : V 32) :
    (firstRoundFiber k₀ aL aR c).card =
      xorDDT_g k₀ aR (xor c aL) := by
  unfold firstRoundFiber firstRoundRightDiff xorDDT_g
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro R _
  exact xor_right_iff (gDifference k₀ R aR) aL c

/-- Regroup a sum by fibers of a map over arbitrary finite types. -/
private theorem sum_by_fibers_card
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (φ : α → β) (F : β → Nat) :
    (∑ x : α, F (φ x)) =
      ∑ y : β,
        ((Finset.univ : Finset α).filter
          (fun x => φ x = y)).card * F y := by
  calc
    (∑ x : α, F (φ x)) =
        ∑ y : β,
          ∑ x ∈ (Finset.univ : Finset α) with φ x = y, F y :=
      (Finset.sum_fiberwise'
        (Finset.univ : Finset α) φ F).symm
    _ = ∑ y : β,
          ((Finset.univ : Finset α).filter
            (fun x => φ x = y)).card * F y := by
      apply Finset.sum_congr rfl
      intro y _
      simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_id]

/-- Regroup a fixed-key sum over base words `R` by their intermediate
    difference `c`. This is an equality, not a Markov approximation. -/
theorem threeRound_middle_sum_eq_convolution
    (k₀ k₁ aL aR bL : V 32) :
    (∑ R : V 32,
      xorDDT_g k₁ (firstRoundRightDiff k₀ aL aR R)
        (xor bL aR)) =
      ∑ c : V 32,
        xorDDT_g k₀ aR (xor c aL) *
          xorDDT_g k₁ c (xor bL aR) := by
  calc
    (∑ R : V 32,
        xorDDT_g k₁ (firstRoundRightDiff k₀ aL aR R)
          (xor bL aR)) =
      ∑ c : V 32,
        ((Finset.univ : Finset (V 32)).filter
          (fun R => firstRoundRightDiff k₀ aL aR R = c)).card *
            xorDDT_g k₁ c (xor bL aR) :=
      sum_by_fibers_card
        (fun R : V 32 => firstRoundRightDiff k₀ aL aR R)
        (fun c : V 32 => xorDDT_g k₁ c (xor bL aR))
    _ = ∑ c : V 32,
          xorDDT_g k₀ aR (xor c aL) *
            xorDDT_g k₁ c (xor bL aR) := by
      apply Finset.sum_congr rfl
      intro c _
      have hcard :
          ((Finset.univ : Finset (V 32)).filter
            (fun R => firstRoundRightDiff k₀ aL aR R = c)).card =
            xorDDT_g k₀ aR (xor c aL) := by
        simpa only [firstRoundFiber] using
          (firstRoundFiber_card k₀ aL aR c)
      exact congrArg
        (fun n : Nat => n * xorDDT_g k₁ c (xor bL aR)) hcard

/-- A rigorous fixed-key upper bound on the exact three-round XOR-DDT,
    expressed only with the XOR-DDTs of the first two round functions.

    This does not claim that individual round transitions are independent.
-/
theorem xorDDT_rounds_three_le_convolution
    (k₀ k₁ k₂ aL aR bL bR : V 32) :
    xorDDT_rounds 3
      (threeRoundKeys k₀ k₁ k₂)
      (aL, aR) (bL, bR) ≤
    ∑ c : V 32,
      xorDDT_g k₀ aR (xor c aL) *
        xorDDT_g k₁ c (xor bL aR) :=
  LE.le.trans_eq
    (xorDDT_rounds_three_le_second
      k₀ k₁ k₂ aL aR bL bR)
    (threeRound_middle_sum_eq_convolution
      k₀ k₁ aL aR bL)

/-- A necessary two-round support condition for a three-round XOR
    differential: every possible intermediate difference must be
    excluded by at least one of the two round-function DDTs. -/
theorem xorDDT_rounds_three_eq_zero_of_disjoint_support
    (k₀ k₁ k₂ aL aR bL bR : V 32)
    (h : ∀ c : V 32,
      xorDDT_g k₀ aR (xor c aL) = 0 ∨
      xorDDT_g k₁ c (xor bL aR) = 0) :
    xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
      (aL, aR) (bL, bR) = 0 := by
  have hbound := xorDDT_rounds_three_le_convolution
    k₀ k₁ k₂ aL aR bL bR
  have hsum :
      (∑ c : V 32,
        xorDDT_g k₀ aR (xor c aL) *
          xorDDT_g k₁ c (xor bL aR)) = 0 := by
    apply Finset.sum_eq_zero
    intro c _
    rcases h c with h₀ | h₁
    · rw [h₀, zero_mul]
    · rw [h₁, mul_zero]
  rw [hsum] at hbound
  exact Nat.eq_zero_of_le_zero hbound

/-- The exact fixed-key XOR-DDT of two Feistel rounds can be expressed
    with carry-matrix counts for arbitrary input and output differences. -/
theorem xorDDT_rounds_two_eq_matrixDDT
    (k₀ k₁ aL aR bL bR : V 32) :
    xorDDT_rounds 2 (twoRoundKeys k₀ k₁) (aL, aR) (bL, bR) =
      matrixDDT_g k₀ aR (xor bL aL) *
        matrixDDT_g k₁ bL (xor bR aR) := by
  calc
    xorDDT_rounds 2 (twoRoundKeys k₀ k₁) (aL, aR) (bL, bR) =
        xorDDT_g k₀ aR (xor bL aL) *
          xorDDT_g k₁ bL (xor bR aR) :=
      xorDDT_rounds_two k₀ k₁ aL aR bL bR
    _ = matrixDDT_g k₀ aR (xor bL aL) *
          matrixDDT_g k₁ bL (xor bR aR) := by
      simp only [xorDDT_g_eq_matrixDDT]

/-- The exact fixed-key three-round XOR-DDT is bounded by a convolution
    of verified carry-matrix counts for the first two round functions.

    No assumption of independent round transitions is made.
-/
theorem xorDDT_rounds_three_le_matrix_convolution
    (k₀ k₁ k₂ aL aR bL bR : V 32) :
    xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
        (aL, aR) (bL, bR) ≤
      ∑ c : V 32,
        matrixDDT_g k₀ aR (xor c aL) *
          matrixDDT_g k₁ c (xor bL aR) := by
  calc
    xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂) (aL, aR) (bL, bR) ≤
        ∑ c : V 32,
          xorDDT_g k₀ aR (xor c aL) *
            xorDDT_g k₁ c (xor bL aR) :=
      xorDDT_rounds_three_le_convolution k₀ k₁ k₂ aL aR bL bR
    _ = ∑ c : V 32,
          matrixDDT_g k₀ aR (xor c aL) *
            matrixDDT_g k₁ c (xor bL aR) := by
      apply Finset.sum_congr rfl
      intro c _
      simp only [xorDDT_g_eq_matrixDDT]

/-- A certified impossible three-round differential criterion expressed
    solely using zero entries of the four-state carry-matrix model. -/
theorem xorDDT_rounds_three_zero_of_matrix_support
    (k₀ k₁ k₂ aL aR bL bR : V 32)
    (h : ∀ c : V 32,
      matrixDDT_g k₀ aR (xor c aL) = 0 ∨
      matrixDDT_g k₁ c (xor bL aR) = 0) :
    xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
      (aL, aR) (bL, bR) = 0 := by
  apply xorDDT_rounds_three_eq_zero_of_disjoint_support
  intro c
  simpa only [xorDDT_g_eq_matrixDDT] using h c

/-- One absent factor makes the exact two-round Feistel differential impossible. -/
theorem xorDDT_rounds_two_zero_of_no_first_path
    (k₀ k₁ aL aR bL bR : V 32)
    (h : xorDiffPossible k₀ aR (xor bL aL) = false) :
    xorDDT_rounds 2 (twoRoundKeys k₀ k₁)
      (aL, aR) (bL, bR) = 0 := by
  rw [xorDDT_rounds_two]
  have hz := (xorDiffPossible_false_iff k₀ aR (xor bL aL)).mp h
  rw [hz, Nat.zero_mul]

/-- If every intermediate difference has an absent first or second
    transition, the exact fixed-key three-round differential is impossible.
    The universal premise is a mathematical certificate; it does not
    by itself provide an efficient search over all 2^32 differences. -/
theorem xorDDT_rounds_three_zero_of_no_common_path
    (k₀ k₁ k₂ aL aR bL bR : V 32)
    (h : ∀ c : V 32,
      xorDiffPossible k₀ aR (xor c aL) = false ∨
      xorDiffPossible k₁ c (xor bL aR) = false) :
    xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
      (aL, aR) (bL, bR) = 0 := by
  apply xorDDT_rounds_three_eq_zero_of_disjoint_support
  intro c
  rcases h c with h₀ | h₁
  · left
    exact (xorDiffPossible_false_iff k₀ aR (xor c aL)).mp h₀
  · right
    exact (xorDiffPossible_false_iff k₁ c (xor bL aR)).mp h₁

/-- A sufficient condition for an impossible three-round differential,
    expressed entirely through Boolean local-support tests.

    The universal premise still quantifies over intermediate differences;
    this theorem does not claim an efficient 2^32-element search. -/
theorem xorDDT_rounds_three_zero_of_boolean_support
    (k₀ k₁ k₂ aL aR bL bR : V 32)
    (h : ∀ c : V 32,
      xorDiffPossibleBoolean k₀ aR (xor c aL) = false ∨
      xorDiffPossibleBoolean k₁ c (xor bL aR) = false) :
    xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
      (aL, aR) (bL, bR) = 0 := by
  apply xorDDT_rounds_three_zero_of_no_common_path
  intro c
  rcases h c with h₀ | h₁
  · left
    have hz := (xorDiffPossibleBoolean_false_iff
      k₀ aR (xor c aL)).mp h₀
    exact (xorDiffPossible_false_iff
      k₀ aR (xor c aL)).mpr hz
  · right
    have hz := (xorDiffPossibleBoolean_false_iff
      k₁ c (xor bL aR)).mp h₁
    exact (xorDiffPossible_false_iff
      k₁ c (xor bL aR)).mpr hz

/-- The pre-rotation output digits `y` of the first carry automaton
    encode the desired first-round output difference `c XOR aL`.

    Stating the relation as a separate wire constraint is useful for
    constructing a symbolic solver: the two carry automata remain local
    to each nibble, and the 11-bit rotation is handled as bit wiring. -/
def jointRotationWiring (aL : V 32)
    (c y : Fin 8 → Fin 16) : Prop :=
  rot11 (packDigits y) = xor (packDigits c) aL

/-- The rotation wire is equivalent to 32 independent Boolean equations.
    They permute bit positions and XOR fixed bits of `aL`.
    No 32-bit enumeration or bit-vector SAT oracle is needed. -/
theorem jointRotationWiring_iff_bits
    (aL : V 32) (c y : Fin 8 → Fin 16) :
    jointRotationWiring aL c y ↔
      ∀ i : Fin 32,
        component (packDigits y) i =
          Bool.xor (component (packDigits c) (i + 11))
            (component aL (i + 11)) := by
  constructor
  · intro hw i
    calc
      component (packDigits y) i =
          component (rot11 (packDigits y)) (i + 11) :=
        (rot11_moves_components_up (packDigits y) i).symm
      _ = component (xor (packDigits c) aL) (i + 11) := by
        rw [hw]
      _ = Bool.xor (component (packDigits c) (i + 11))
            (component aL (i + 11)) :=
        xor_components (packDigits c) aL (i + 11)
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let i : Fin 32 := (⟨j, hj⟩ : Fin 32) - 11
    have hi : i + 11 = (⟨j, hj⟩ : Fin 32) := by
      dsimp [i]
      simp
    change
      component (rot11 (packDigits y)) (⟨j, hj⟩ : Fin 32) =
        component (xor (packDigits c) aL) (⟨j, hj⟩ : Fin 32)
    rw [← hi]
    calc
      component (rot11 (packDigits y)) (i + 11) =
          component (packDigits y) i :=
        rot11_moves_components_up (packDigits y) i
      _ = Bool.xor (component (packDigits c) (i + 11))
            (component aL (i + 11)) := h i
      _ = component (xor (packDigits c) aL) (i + 11) :=
        (xor_components (packDigits c) aL (i + 11)).symm

/-- A coupled support constraint for two successive round functions.

    * `c`: eight nibbles of the intermediate XOR difference;
    * `y`: eight nibbles of the first round's PRE-rotation output difference;
    * each carry automaton has only four internal carry states;
    * the first and second automata are coupled solely through `c`, `y`,
      and the fixed rotation/XOR wiring relation.

    The final carry states may be arbitrary because addition is modulo 2^32. -/
def jointCarryConstraint
    (k₀ k₁ aL aR bL : V 32)
    (c y : Fin 8 → Fin 16) : Prop :=
  jointRotationWiring aL c y ∧
  carryHasPathBoolean (wordDigits k₀) (wordDigits aR) y = true ∧
  carryHasPathBoolean (wordDigits k₁) c
    (wordDigits ((xor bL aR).rotateRight 11)) = true

/-- The symbolic two-automaton constraint is satisfiable exactly when
    there exists an intermediate 32-bit difference supporting both
    necessary one-round transitions.

    No independence of round transitions is assumed. -/
theorem jointCarryConstraint_iff_common_difference
    (k₀ k₁ aL aR bL : V 32) :
    (∃ c y : Fin 8 → Fin 16,
      jointCarryConstraint k₀ k₁ aL aR bL c y) ↔
    (∃ mid : V 32,
      xorDiffPossibleBoolean k₀ aR (xor mid aL) = true ∧
      xorDiffPossibleBoolean k₁ mid (xor bL aR) = true) := by
  constructor
  · rintro ⟨c, y, hw, hfirst, hsecond⟩
    let mid : V 32 := packDigits c
    have hy : packDigits y = (xor mid aL).rotateRight 11 := by
      apply rot11_is_bijective.injective
      calc
        rot11 (packDigits y) = xor mid aL := hw
        _ = rot11 ((xor mid aL).rotateRight 11) :=
          (rot11_rotateRight11 (xor mid aL)).symm
    have hyDigits :
        y = wordDigits ((xor mid aL).rotateRight 11) := by
      calc
        y = wordDigits (packDigits y) :=
          (wordDigitsEquiv.right_inv y).symm
        _ = wordDigits ((xor mid aL).rotateRight 11) :=
          congrArg wordDigits hy
    have hcDigits : wordDigits mid = c := wordDigitsEquiv.right_inv c
    refine ⟨mid, ?_, ?_⟩
    · change carryHasPathBoolean (wordDigits k₀) (wordDigits aR)
        (wordDigits ((xor mid aL).rotateRight 11)) = true
      rw [← hyDigits]
      exact hfirst
    · change carryHasPathBoolean (wordDigits k₁) (wordDigits mid)
        (wordDigits ((xor bL aR).rotateRight 11)) = true
      rw [hcDigits]
      exact hsecond
  · rintro ⟨mid, hfirst, hsecond⟩
    refine ⟨wordDigits mid,
      wordDigits ((xor mid aL).rotateRight 11), ?_⟩
    constructor
    · have hy :
          packDigits (wordDigits ((xor mid aL).rotateRight 11)) =
            (xor mid aL).rotateRight 11 :=
        wordDigitsEquiv.left_inv _

      have hc :
          packDigits (wordDigits mid) = mid :=
        wordDigitsEquiv.left_inv _

      change
        rot11 (packDigits (wordDigits ((xor mid aL).rotateRight 11))) =
          xor (packDigits (wordDigits mid)) aL

      rw [hy, hc]
      exact rot11_rotateRight11 (xor mid aL)
    constructor
    · exact hfirst
    · exact hsecond

/-- Absence of a solution to the coupled two-automaton constraint
    certifies an impossible three-round differential.

    This is a sufficient condition, not a characterization of all
    impossible three-round differentials: the third round can introduce
    additional restrictions not reflected in the two-automaton constraint. -/
theorem xorDDT_rounds_three_zero_of_no_joint_constraint
    (k₀ k₁ k₂ aL aR bL bR : V 32)
    (hno : ¬ ∃ c y : Fin 8 → Fin 16,
      jointCarryConstraint k₀ k₁ aL aR bL c y) :
    xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
      (aL, aR) (bL, bR) = 0 := by
  apply xorDDT_rounds_three_zero_of_boolean_support
  intro mid
  cases hfirst :
      xorDiffPossibleBoolean k₀ aR (xor mid aL) with
  | false =>
      exact Or.inl rfl
  | true =>
      cases hsecond :
          xorDiffPossibleBoolean k₁ mid (xor bL aR) with
      | false =>
          exact Or.inr rfl
      | true =>
          exfalso
          apply hno
          exact
            (jointCarryConstraint_iff_common_difference
              k₀ k₁ aL aR bL).mpr
              ⟨mid, hfirst, hsecond⟩

/-! ## Concrete path witnesses for the exact three-round constraint -/

/-- The two Boolean path constraints in `jointCarryConstraint` have
    concrete `VerifiedCarryPath` witnesses, not just abstract DP flags. -/
theorem verifiedCarryPaths_of_jointCarryConstraint
    (k₀ k₁ aL aR bL : V 32)
    (c y : Fin 8 → Fin 16)
    (hjoint : jointCarryConstraint k₀ k₁ aL aR bL c y) :
    Nonempty (VerifiedCarryPath
      (wordDigits k₀) (wordDigits aR) y) ∧
    Nonempty (VerifiedCarryPath
      (wordDigits k₁) c
      (wordDigits ((xor bL aR).rotateRight 11))) := by
  rcases hjoint with ⟨_, hfirst, hsecond⟩
  constructor
  · let out := packDigits y
    have hout : wordDigits out = y :=
      wordDigitsEquiv.right_inv y
    have hh : carryHasPathBoolean (wordDigits k₀)
        (wordDigits aR) (wordDigits out) = true := by
      simpa only [hout] using hfirst
    simpa only [hout] using
      (verifiedCarryPath_of_carryHasPathBoolean k₀ aR out hh)
  · let diff := packDigits c
    let out := (xor bL aR).rotateRight 11
    have hdiff : wordDigits diff = c :=
      wordDigitsEquiv.right_inv c
    have hh : carryHasPathBoolean (wordDigits k₁)
        (wordDigits diff) (wordDigits out) = true := by
      simpa only [hdiff] using hsecond
    simpa only [hdiff] using
      (verifiedCarryPath_of_carryHasPathBoolean k₁ diff out hh)

end Magma.MultiRoundDDT

/-! ## Exact support of the zero-key zero-left slice

The following results underlie research iterations 08, 10, and 11:
two local S-box tables predict 64 pairs, each has count `2^58`, and
together they exhaust the total slice mass `2^64`.
-/

open Magma.Internal Magma.CarryAutomaton Magma.MultiRoundDDT

namespace Magma.ZeroLeftSupport

/-- XOR on 4-bit S-box inputs, represented by `Fin 16`. -/
private def xor4 (x d : Fin 16) : Fin 16 :=
  ((BitVec.ofNat 4 x.val) ^^^ (BitVec.ofNat 4 d.val)).toFin

/-- The ordinary 4-bit XOR-DDT of RFC S-box number `i`. -/
def nibbleDDT (i : Fin 8) (d out : Fin 16) : Nat :=
  ((Finset.univ : Finset (Fin 16)).filter fun x =>
    Nat.xor (π'arrays i (xor4 x d)).val (π'arrays i x).val = out.val).card

/-- For S-box 0, input difference 1 gives exactly eight outputs,
    each with DDT count 2 (all other entries zero). -/
theorem pi0_one_exact (out : Fin 16) :
    nibbleDDT 0 1 out =
      if out.val ∈ ([2, 3, 4, 6, 8, 10, 14, 15] : List Nat)
      then 2 else 0 := by
  fin_cases out <;> decide

/-- For S-box 5, output difference 2 is possible for exactly eight
    input differences, each with DDT count 2. -/
theorem pi5_two_exact (d : Fin 16) :
    nibbleDDT 5 d 2 =
      if d.val ∈ ([3, 6, 8, 9, 10, 12, 13, 15] : List Nat)
      then 2 else 0 := by
  fin_cases d <;> decide

/-- Output differences before rotation of the S-box 0 transition. -/
def U : List Nat := [2, 3, 4, 6, 8, 10, 14, 15]

/-- Input differences of S-box 5 producing output difference 2. -/
def W : List Nat := [3, 6, 8, 9, 10, 12, 13, 15]

/-- Predicted `(aL, bR)` pairs from the two independent 4-bit tables.
    They have the form `(w*2^20 XOR u*2^11, w*2^20)`. Since the bit
    ranges are disjoint, `+` equals XOR in this particular expression. -/
def predictedPairs : List (V 32 × V 32) :=
  W.flatMap fun w =>
    U.map fun u =>
      (BitVec.ofNat 32 (w * 2^20 + u * 2^11),
       BitVec.ofNat 32 (w * 2^20))

theorem predictedPairs_length : predictedPairs.length = 64 := by decide

/-- Which single-bit input differences belong to the predicted support? -/
def predictedOneBitPositions : List Nat :=
  (List.range 32).filter fun i =>
    predictedPairs.any fun p => p.1 == BitVec.ofNat 32 (2^i)

/-- Which two-bit input differences belong to the predicted support? -/
def predictedTwoBitPairs : List (Nat × Nat) := Id.run do
  let mut result := []
  for i in [:32] do
    for j in [i+1:32] do
      let aL := BitVec.ofNat 32 (2^i + 2^j)
      if predictedPairs.any (fun p => p.1 == aL) then
        result := (i, j) :: result
  return result.reverse

/-- No one-bit input difference occurs in the predicted list. -/
theorem predictedOneBitPositions_eq_nil : predictedOneBitPositions = [] := by
  decide +kernel

/-- The predicted two-bit masks are exactly the three earlier search exceptions. -/
theorem predictedTwoBitPairs_eq :
    predictedTwoBitPairs = [(12, 23), (13, 23), (14, 23)] := by
  decide +kernel

end Magma.ZeroLeftSupport

open Magma.ZeroLeftSupport

namespace Magma.ZeroLeft64Exact

/-- All eight-by-eight parameter choices have exact count `2^58`.
    Importantly, each goal below is a *small*, fixed product of eight
    4-bit S-box DDT entries; no `Finset FeistelState` is evaluated. -/
theorem exact_count_for_UW
    (k₂ : V 32) (w u : Nat)
    (hw : w ∈ W) (hu : u ∈ U) :
    xorDDT_rounds 3 (threeRoundKeys (0#32) (0#32) k₂)
      (BitVec.ofNat 32 (w * 2^20 + u * 2^11), 1#32)
      (0#32, BitVec.ofNat 32 (w * 2^20)) = 2^58 := by
  have hw' :
      w = 3 ∨ w = 6 ∨ w = 8 ∨ w = 9 ∨
      w = 10 ∨ w = 12 ∨ w = 13 ∨ w = 15 := by
    simpa [W] using hw
  have hu' :
      u = 2 ∨ u = 3 ∨ u = 4 ∨ u = 6 ∨
      u = 8 ∨ u = 10 ∨ u = 14 ∨ u = 15 := by
    simpa [U] using hu
  rcases hw' with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    rcases hu' with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    rw [zeroLeft_three_round_exact_sbox_product] <;>
    decide +kernel

/-- Every element of the original enumerated list has DDT exactly `2^58`.
    This converts a 64-case computation into one reusable theorem. -/
theorem predictedPairs_exact_count
    (k₂ aL bR : V 32)
    (hp : (aL, bR) ∈ predictedPairs) :
    xorDDT_rounds 3 (threeRoundKeys (0#32) (0#32) k₂)
      (aL, 1#32) (0#32, bR) = 2^58 := by
  unfold predictedPairs at hp
  rcases List.mem_flatMap.mp hp with ⟨w, hw, hwu⟩
  rcases List.mem_map.mp hwu with ⟨u, hu, hpair⟩
  have hc := exact_count_for_UW k₂ w u hw hu
  have ha : BitVec.ofNat 32 (w * 2^20 + u * 2^11) = aL :=
    (Prod.mk.inj hpair).1
  have hb : BitVec.ofNat 32 (w * 2^20) = bR :=
    (Prod.mk.inj hpair).2
  rw [ha, hb] at hc
  exact hc

/-- In particular all enumerated pairs have strictly positive DDT. -/
theorem predictedPairs_possible
    (k₂ aL bR : V 32)
    (hp : (aL, bR) ∈ predictedPairs) :
    0 < xorDDT_rounds 3 (threeRoundKeys (0#32) (0#32) k₂)
      (aL, 1#32) (0#32, bR) := by
  rw [predictedPairs_exact_count k₂ aL bR hp]
  norm_num

/-- The parametrization has no duplicate pairs: all 64 entries
    correspond to different input/output difference pairs. -/
theorem predictedPairs_nodup : predictedPairs.Nodup := by
  decide +kernel

/-- A compact public statement: there are 64 distinct *certified*
    pairs, and every one has the same exact count. Note that this is
    an inclusion, not yet the converse (all other pairs impossible). -/
theorem sixty_four_certified_pairs (k₂ : V 32) :
    predictedPairs.length = 64 ∧
    predictedPairs.Nodup ∧
    (∀ aL bR : V 32, (aL, bR) ∈ predictedPairs →
      xorDDT_rounds 3 (threeRoundKeys (0#32) (0#32) k₂)
        (aL, 1#32) (0#32, bR) = 2^58) := by
  refine ⟨predictedPairs_length, predictedPairs_nodup, ?_⟩
  intro aL bR hp
  exact predictedPairs_exact_count k₂ aL bR hp

end Magma.ZeroLeft64Exact

open Magma.ZeroLeftSupport Magma.ZeroLeft64Exact

namespace Magma.ZeroLeft64Completeness

/-! ### The total weight of the zero-left DDT slice -/

def zeroLeftSlice (k₂ : V 32) (p : FeistelState) : Nat :=
  xorDDT_rounds 3 (threeRoundKeys (0#32) (0#32) k₂) (p.1, 1#32) (0#32, p.2)

/-- Constant row sums factor out of a sum weighted by the second coordinate. -/
private theorem sum_pair_weights
    {α β : Type*} [Fintype α] [Fintype β]
    (f : β → α → Nat) (g : β → Nat) (row total : Nat)
    (hrow : ∀ b, (∑ a : α, f b a) = row)
    (hcol : (∑ b : β, g b) = total) :
    (∑ p : α × β, f p.2 p.1 * g p.2) = row * total := by
  classical
  rw [Fintype.sum_prod_type_right]
  have hinner (b : β) : (∑ a : α, f b a * g b) = row * g b := by
    rw [← Finset.sum_mul, hrow]
  simp_rw [hinner]
  rw [← Finset.mul_sum, hcol]

/-- The zero-left slice has total DDT mass `2^64` for every third key. -/
theorem zeroLeftSlice_total_mass (k₂ : V 32) :
    (∑ p : FeistelState, zeroLeftSlice k₂ p) = 2^64 := by
  classical
  have hcount : Fintype.card (V 32) = 2^32 := by
    rw [← FinEnum.card_eq_fintypeCard]
    exact FinEnum.card_bitVec 32
  have hsum :
      (∑ p : FeistelState,
        xorDDT_g (0#32) (1#32) (xor p.2 p.1) *
          xorDDT_g (0#32) p.2 (1#32)) = (2^32 : Nat) * 2^32 :=
    sum_pair_weights
      (fun bR aL : V 32 => xorDDT_g (0#32) (1#32) (xor bR aL))
      (fun bR : V 32 => xorDDT_g (0#32) bR (1#32)) (2^32) (2^32)
      (fun bR => (xorDDT_g_sum_output_xor (0#32) (1#32) bR).trans hcount)
      ((xorDDT_g_sum_input (0#32) (1#32)).trans hcount)
  calc
    (∑ p : FeistelState, zeroLeftSlice k₂ p) =
        ∑ p : FeistelState,
          xorDDT_g (0#32) (1#32) (xor p.2 p.1) *
            xorDDT_g (0#32) p.2 (1#32) := by
      apply Finset.sum_congr rfl
      intro p _
      exact xorDDT_rounds_three_zero_left_factorization
        (0#32) (0#32) k₂ p.1 (1#32) p.2
    _ = (2^32 : Nat) * 2^32 := hsum
    _ = 2^64 := by norm_num

/-! ### Saturation: finite mass already exhausted by a known subset -/

/-- If a finite set carries the entire mass of a natural-valued function,
    every point outside it has weight zero. -/
theorem zero_off_saturated_subset
    {α : Type*} [Fintype α] [DecidableEq α]
    (S : Finset α) (weight : α → Nat) (mass : Nat)
    (htotal : (∑ x : α, weight x) = mass)
    (hknown : (∑ x ∈ S, weight x) = mass)
    (x : α) (hx : x ∉ S) : weight x = 0 := by
  have hcompl : (∑ x ∈ Sᶜ, weight x) = 0 := by
    have hsplit := Finset.sum_add_sum_compl S weight
    rw [hknown, htotal] at hsplit
    omega
  exact (Finset.sum_eq_zero_iff.mp hcompl) x (Finset.mem_compl.mpr hx)

private def all64 : Finset FeistelState :=
  predictedPairs.toFinset

/-- The 64 certified entries already consume the entire 2^64 mass. -/
theorem known64_total_mass (k₂ : V 32) :
    (∑ p ∈ all64, zeroLeftSlice k₂ p) = 2^64 := by
  have hcard : all64.card = 64 := by
    change predictedPairs.toFinset.card = 64
    rw [List.toFinset_card_of_nodup predictedPairs_nodup]
    exact predictedPairs_length
  calc
    (∑ p ∈ all64, zeroLeftSlice k₂ p) =
        ∑ _p ∈ all64, (2^58 : Nat) := by
      apply Finset.sum_congr rfl
      intro p hp
      exact predictedPairs_exact_count k₂ p.1 p.2
        (by simpa only [all64, List.mem_toFinset] using hp)
    _ = all64.card * 2^58 := by simp
    _ = 2^64 := by rw [hcard]; norm_num

/-- Exact classification of the zero-left slice for every third round key. -/
theorem zeroLeftSlice_exact_iff_listed (k₂ aL bR : V 32) :
    xorDDT_rounds 3 (threeRoundKeys (0#32) (0#32) k₂)
      (aL, 1#32) (0#32, bR) =
      if (aL, bR) ∈ predictedPairs then 2^58 else 0 := by
  classical
  by_cases hmem : (aL, bR) ∈ predictedPairs
  · rewrite [ite_eq_left hmem]
    exact predictedPairs_exact_count k₂ aL bR hmem
  · rewrite [ite_eq_right hmem]
    change zeroLeftSlice k₂ (aL, bR) = 0
    apply zero_off_saturated_subset
      (S := all64) (weight := zeroLeftSlice k₂)
      (mass := 2^64)
      (zeroLeftSlice_total_mass k₂) (known64_total_mass k₂)
      (aL, bR)
    simpa only [all64, List.mem_toFinset] using hmem

/-- Positive DDT support is exactly the list of 64 certified pairs. -/
theorem zeroLeftSlice_possible_iff_listed (k₂ aL bR : V 32) :
    0 < xorDDT_rounds 3 (threeRoundKeys (0#32) (0#32) k₂)
      (aL, 1#32) (0#32, bR) ↔
      (aL, bR) ∈ predictedPairs := by
  rw [zeroLeftSlice_exact_iff_listed]
  by_cases h : (aL, bR) ∈ predictedPairs <;> norm_num [h]

end Magma.ZeroLeft64Completeness
