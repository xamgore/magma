module

public import Magma.OneHot.ExactLocalSupportCompleteness
import all Init.Data.Range.Basic

@[expose] public section

/-!
Quantitative one-hot diagonal DDT: closed local multiplicities and
prefix-carry weights, for all eight Magma nibbles.

This module defines the proposed closed EXACT NUMBER of DDT solutions:

  16^(7-i) * ((16^i-K)*L(i,q,0,r,s) + K*L(i,q,1,r,s)),
  K = k.toNat % 16^i, q = wordDigits k i.

The file proves that this expression is positive EXACTLY for the
already kernel-verified real DDT support, for every key and bit pair.
In particular, it gives an unconditional certified zero test.

IMPORTANT: Equality of the positive NUMERIC VALUES with xorDDT_g is a
separate quantitative factorization obligation, NOT asserted here.
The next proof needs to count prefix, active digit and suffix fibers,
not just construct one full-word witness.
-/

namespace Magma.OneHotDiagonalExactWeights

open Magma
open Magma.CarryAutomaton
open Magma.OneHotFixedKeySupportAudit
open Magma.OneHotExactCarryRegimes
open Magma.OneHotExactLocalSupportCompleteness

private abbrev Word :=
  V 32

/-- Count 4-bit inputs with the requested active S-box difference.
    For i<7 the two outgoing carries must agree. For i=7 they are
    discarded by 32-bit modular addition. -/
def localMultiplicity (i : Fin 8) (q : Fin 16)
    (c : Fin 2) (r s : Fin 4) : Nat :=
  ((Finset.univ : Finset (Fin 16)).filter (fun x =>
    let step := sboxCarryStep i q (Fin.ofNat 16 (2 ^ r.val)) x (c,c)
    step.1 = Fin.ofNat 16 (2 ^ s.val) ∧
      (i.val = 7 ∨ step.2.1 = step.2.2))).card

/-- The low key prefix and radix at the active nibble. -/
def lowBase (i : Fin 8) : Nat := 16 ^ i.val

def keyPrefix (k : Word) (i : Fin 8) : Nat :=
  k.toNat % lowBase i

/-- Exactly 16^(7-i) upper digit assignments are unconstrained by an
    isolated output difference when the active carry pair converges. -/
def suffixFactor (i : Fin 8) : Nat := 16 ^ (7 - i.val)

/-- Closed-form candidate for the TRUE DDT coefficient, expressed
    using only the low key prefix and TWO local 16-element counts.
    The quantitative equality with `xorDDT_g` is intentionally left
    to the next counting/factorization theorem. -/
def diagonalWeight (k : Word) (i : Fin 8) (r s : Fin 4) : Nat :=
  let K := keyPrefix k i
  let B := lowBase i
  let q := wordDigits k i
  suffixFactor i *
    ((B-K) * localMultiplicity i q 0 r s +
       K  * localMultiplicity i q 1 r s)

private theorem lowBase_pos (i : Fin 8) : 0 < lowBase i := by simp [lowBase]

private theorem suffixFactor_pos (i : Fin 8) : 0 < suffixFactor i := by simp [suffixFactor]

private theorem prefix_lt_base (k : Word) (i : Fin 8) : keyPrefix k i < lowBase i := by
  unfold keyPrefix
  exact Nat.mod_lt _ (lowBase_pos i)

/-! ## Exact arithmetic counts of lower carry prefixes. -/

/-- Exactly B-K lower prefixes give incoming carry zero. -/
theorem count_zero_prefixes (k : Word) (i : Fin 8) :
    ((Finset.range (lowBase i)).filter (fun x =>
      (x + keyPrefix k i) / lowBase i = 0)).card =
      lowBase i - keyPrefix k i := by
  let B := lowBase i
  let K := keyPrefix k i
  have hB : 0 < B := lowBase_pos i
  have hK : K < B := prefix_lt_base k i
  have heq :
      (Finset.range B).filter (fun x => (x+K)/B=0) =
        Finset.Ico 0 (B-K) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    constructor
    · rintro ⟨hx,hc⟩
      constructor
      · omega
      · have hs : x+K < B := (Nat.div_eq_zero_iff.mp hc).resolve_left (by omega)
        omega
    · rintro ⟨_,hx⟩
      have hxB : x < B := by omega
      refine ⟨hxB, ?_⟩
      apply Nat.div_eq_of_lt
      omega
  change ((Finset.range B).filter (fun x => (x+K)/B=0)).card = B-K
  rw [heq]
  simp only [Nat.card_Ico]
  omega

/-- Exactly K lower prefixes give incoming carry one. -/
theorem count_one_prefixes (k : Word) (i : Fin 8) :
    ((Finset.range (lowBase i)).filter (fun x =>
      (x + keyPrefix k i) / lowBase i = 1)).card =
      keyPrefix k i := by
  let B := lowBase i
  let K := keyPrefix k i
  have hB : 0 < B := lowBase_pos i
  have hK : K < B := prefix_lt_base k i
  have heq :
      (Finset.range B).filter (fun x => (x+K)/B=1) =
        Finset.Ico (B-K) B := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    constructor
    · rintro ⟨hx,hc⟩
      have hsum : x+K < 2*B := by omega
      have hlow : B ≤ x+K :=
        (Nat.div_pos_iff.mp (by omega : 0 < (x+K)/B)).2
      exact ⟨by omega, hx⟩
    · rintro ⟨hlo,hx⟩
      refine ⟨hx, ?_⟩
      have hlower : B ≤ x+K := by omega
      have hupper : x+K < 2*B := by omega
      exact Nat.div_eq_of_lt_le (by simpa using hlower) hupper
  change ((Finset.range B).filter (fun x => (x+K)/B=1)).card = K
  rw [heq]
  simp only [Nat.card_Ico]
  omega

/-- The prefix fiber weights are already a CLOSED affine function of
    the key prefix; no enumeration of 16^i possible prefixes needed. -/
def weightedLocalPrefix (k : Word) (i : Fin 8) (r s : Fin 4) : Nat :=
  ∑ x ∈ Finset.range (lowBase i),
    if (x + keyPrefix k i) / lowBase i = 0 then
      localMultiplicity i (wordDigits k i) 0 r s
    else localMultiplicity i (wordDigits k i) 1 r s

/-- The arithmetic heart of the quantitative formula, independent of
    the remaining trace-factorization proof. -/
theorem weightedLocalPrefix_closed (k : Word) (i : Fin 8) (r s : Fin 4) :
    weightedLocalPrefix k i r s =
      (lowBase i-keyPrefix k i) *
        localMultiplicity i (wordDigits k i) 0 r s +
      keyPrefix k i *
        localMultiplicity i (wordDigits k i) 1 r s := by
  unfold weightedLocalPrefix
  rw [Finset.sum_ite]
  simp only [Finset.sum_const, smul_eq_mul]
  rw [count_zero_prefixes]
  have hnot :
      ((Finset.range (lowBase i)).filter (fun x =>
        ¬((x + keyPrefix k i) / lowBase i = 0))).card =
        keyPrefix k i := by
    let B := lowBase i
    let K := keyPrefix k i
    have hB : 0 < B := lowBase_pos i
    have hK : K < B := prefix_lt_base k i
    have heq :
        (Finset.range B).filter (fun x => (x+K)/B ≠ 0) =
          (Finset.range B).filter (fun x => (x+K)/B=1) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨hx,hn⟩
        have hsum : x+K < 2*B := by omega
        have hlower : B ≤ x+K :=
          (Nat.div_pos_iff.mp (Nat.pos_of_ne_zero hn)).2
        have hone : (x+K)/B=1 :=
          Nat.div_eq_of_lt_le (by simpa using hlower) hsum
        exact ⟨hx,hone⟩
      · rintro ⟨hx,hone⟩
        exact ⟨hx,by omega⟩
    change ((Finset.range B).filter (fun x => (x+K)/B ≠ 0)).card = K
    rw [heq]
    exact count_one_prefixes k i
  rw [hnot]

/-- The four-bit local count is positive precisely when a concrete
    nibble witness exists. -/
theorem localMultiplicity_pos_iff
    (i : Fin 8) (q : Fin 16) (c : Fin 2) (r s : Fin 4) :
    0 < localMultiplicity i q c r s ↔
      ∃ x : Fin 16,
        (sboxCarryStep i q (Fin.ofNat 16 (2 ^ r.val)) x (c,c)).1 =
          Fin.ofNat 16 (2 ^ s.val) ∧
        (i.val = 7 ∨
          (sboxCarryStep i q (Fin.ofNat 16 (2 ^ r.val)) x (c,c)).2.1 =
          (sboxCarryStep i q (Fin.ofNat 16 (2 ^ r.val)) x (c,c)).2.2) := by
  unfold localMultiplicity
  rw [Finset.card_pos, Finset.filter_nonempty_iff]
  simp only [Finset.mem_univ, true_and]

/-- A successful local witness uses either carry zero, or a reachable
    carry one; the finite count detects exactly these alternatives. -/
theorem localPotential_iff_multiplicity
    (k : Word) (i : Fin 8) (r s : Fin 4) :
    localPotential i (wordDigits k i) (exactCarryFlag k i) r s = true ↔
      0 < localMultiplicity i (wordDigits k i) 0 r s ∨
        (exactCarryFlag k i = true ∧
          0 < localMultiplicity i (wordDigits k i) 1 r s) := by
  rw [exact_localPotential_iff_witness]
  constructor
  · rintro ⟨x,c,hc,ho,hout⟩
    fin_cases c
    · left
      exact (localMultiplicity_pos_iff i (wordDigits k i) 0 r s).mpr
        ⟨x,ho,hout⟩
    · right
      have hf : exactCarryFlag k i = true := by
        rcases hc with h | ⟨hf,_⟩
        · cases h
        · exact hf
      exact ⟨hf,
        (localMultiplicity_pos_iff i (wordDigits k i) 1 r s).mpr
          ⟨x,ho,hout⟩⟩
  · intro h
    rcases h with h0 | ⟨hf,h1⟩
    · obtain ⟨x,ho,hout⟩ :=
        (localMultiplicity_pos_iff i (wordDigits k i) 0 r s).mp h0
      exact ⟨x,0,Or.inl rfl,ho,hout⟩
    · obtain ⟨x,ho,hout⟩ :=
        (localMultiplicity_pos_iff i (wordDigits k i) 1 r s).mp h1
      exact ⟨x,1,Or.inr ⟨hf,rfl⟩,ho,hout⟩

/-- Algebraic content of the closed prefix-weight expression:
    the zero-carry coefficient is always strictly positive, whereas
    the one-carry coefficient is positive precisely when the key's
    low prefix is nonzero. -/
theorem diagonalWeight_pos_iff_local
    (k : Word) (i : Fin 8) (r s : Fin 4) :
    0 < diagonalWeight k i r s ↔
      localPotential i (wordDigits k i) (exactCarryFlag k i) r s = true := by
  let B := lowBase i
  let K := keyPrefix k i
  let A := localMultiplicity i (wordDigits k i) 0 r s
  let C := localMultiplicity i (wordDigits k i) 1 r s
  have hK : K < B := prefix_lt_base k i
  have hB : 0 < B := lowBase_pos i
  have hBZ : 0 < B-K := by omega
  have hS : 0 < suffixFactor i := suffixFactor_pos i
  have hflag : (0 < K ↔ exactCarryFlag k i = true) := by
    change 0 < k.toNat % (16 ^ i.val) ↔
      decide (k.toNat % (16 ^ i.val) ≠ 0) = true
    simp only [decide_eq_true_eq]
    omega
  have hA : 0 < (B-K)*A ↔ 0 < A :=
    Nat.mul_pos_iff_of_pos_left hBZ
  have hC : 0 < K*C ↔ 0 < K ∧ 0 < C := by
    constructor
    · intro h
      exact ⟨Nat.pos_of_mul_pos_right h,
        Nat.pos_of_mul_pos_left h⟩
    · rintro ⟨h₁,h₂⟩
      exact Nat.mul_pos h₁ h₂
  change (0 < suffixFactor i * ((B-K)*A + K*C)) ↔ _
  rw [Nat.mul_pos_iff_of_pos_left hS]
  have hsum : (0 < (B-K)*A + K*C) ↔
      0 < (B-K)*A ∨ 0 < K*C := by omega
  rw [hsum, hA, hC, hflag]
  exact (localPotential_iff_multiplicity k i r s).symm

/-- THE key correctness certificate available already, without the
    quantitative factorization: our closed formula predicts precisely
    the actual positive DDT positions at any fixed key. -/
theorem diagonalWeight_pos_iff_DDT
    (k : Word) (i : Fin 8) (r s : Fin 4) :
    0 < diagonalWeight k i r s ↔
      0 < fastOneHotDDT k
        (⟨4*i.val+r.val, by omega⟩ : Fin 32)
        (⟨(4*i.val+s.val+11)%32, by omega⟩ : Fin 32) := by
  rw [diagonalWeight_pos_iff_local]
  exact localPotential_exact_iff_real k i r s

/-- The same zero/positive criterion expressed using the original
    mathematical XOR-DDT, rather than the fast DP implementation. -/
theorem diagonalWeight_pos_iff_real
    (k : Word) (i : Fin 8) (r s : Fin 4) :
    0 < diagonalWeight k i r s ↔
      0 < xorDDT_g k
        (BitVec.ofNat 32 (2 ^ (4*i.val+r.val)))
        (rot11 (BitVec.ofNat 32 (2 ^ (4*i.val+s.val)))) := by
  have hrotate :
      rot11 (BitVec.ofNat 32 (2 ^ (4*i.val+s.val))) =
        BitVec.ofNat 32 (2 ^ ((4*i.val+s.val+11)%32)) := by
    fin_cases i <;> fin_cases s <;> decide
  simpa only [hrotate, fastOneHotDDT_correct] using
    (diagonalWeight_pos_iff_DDT k i r s)

/-- Both interpretations of a diagonal cell have EXACTLY the same
    zero cases. In particular this remains valid for the final nibble,
    whose outgoing carry is deliberately discarded. -/
theorem diagonalWeight_zero_iff_real_zero
    (k : Word) (i : Fin 8) (r s : Fin 4) :
    diagonalWeight k i r s = 0 ↔
      xorDDT_g k
        (BitVec.ofNat 32 (2 ^ (4*i.val+r.val)))
        (rot11 (BitVec.ofNat 32 (2 ^ (4*i.val+s.val)))) = 0 := by
  have hpos := diagonalWeight_pos_iff_real k i r s
  omega

end Magma.OneHotDiagonalExactWeights
