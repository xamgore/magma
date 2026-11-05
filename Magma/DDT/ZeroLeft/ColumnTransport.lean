module

public import Magma.Differential.Core.MultiRoundDDT
import all Init.Data.Range.Basic

@[expose] public section

/-!
# Exact transport of zero-left three-round DDT columns

For arbitrary round keys, each coefficient factors as
`DDT_g[k₀](aR, bR XOR aL) * DDT_g[k₁](bR, aR)`.
Reindexing by `aL = bR XOR d` isolates the same first-round coefficient
in every column with fixed `(k₀, aR)`.

A positive second factor makes the column support an XOR translation
of the first-round support and preserves its cardinality. A zero second
factor makes the column empty. Cross-column proportionality holds even
when either factor vanishes. All support arguments are symbolic.
-/

namespace Magma.ZeroLeftColumnTransport

open Magma.Internal Magma.CarryAutomaton Magma.MultiRoundDDT

/-- The first-round output differences attainable with input difference `aR`. -/
def firstRoundSupport (k₀ aR : (V 32)) : Finset (V 32) :=
  Finset.univ.filter (fun d => 0 < xorDDT_g k₀ aR d)

/-- The positive entries of one zero-left three-round column,
    indexed by its LEFT input difference `aL`. -/
def leftColumnSupport
    (k₀ k₁ k₂ aR bR : (V 32)) : Finset (V 32) :=
  Finset.univ.filter (fun aL =>
    0 < xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
      (aL, aR) (0#32, bR))

/-- XOR-translation is involutive. -/
private theorem xor_left_twice (z x : (V 32)) :
    xor z (xor z x) = x := by
  change z ^^^ (z ^^^ x) = x
  rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

/-- XOR-translation is injective, and hence preserves finite support size. -/
private theorem xor_left_injective (z : (V 32)) :
    Function.Injective (fun x : (V 32) => xor z x) := by
  intro x y h
  have hh := congrArg (fun t : (V 32) => xor z t) h
  rw [xor_left_twice, xor_left_twice] at hh
  exact hh

/-- Main coefficient formula, reindexed by the *first-round* DDT output.
    This is exact for arbitrary keys, with no assumption of positivity. -/
theorem reindexed_entry (k₀ k₁ k₂ aR bR d : (V 32)) :
    xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
        (xor bR d, aR) (0#32, bR) =
      xorDDT_g k₀ aR d * xorDDT_g k₁ bR aR := by
  rw [xorDDT_rounds_three_zero_left_factorization]
  rw [xor_left_twice]

/-- Each individual coefficient is positive iff BOTH 32-bit g-transitions
    are possible. Thus there is no probabilistic independence assumption. -/
theorem reindexed_entry_pos_iff (k₀ k₁ k₂ aR bR d : (V 32)) :
    0 < xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
      (xor bR d, aR) (0#32, bR) ↔
      0 < xorDDT_g k₀ aR d ∧ 0 < xorDDT_g k₁ bR aR := by
  rw [reindexed_entry]
  constructor
  · intro hp
    exact ⟨Nat.pos_of_mul_pos_right hp,
      Nat.pos_of_mul_pos_left hp⟩
  · rintro ⟨h0, h1⟩
    exact Nat.mul_pos h0 h1

/-- If the second-round factor is positive, the entire exact support of
    a three-round column is a shifted copy of the first-round support. -/
theorem leftColumnSupport_eq_image_of_pos
    (k₀ k₁ k₂ aR bR : (V 32))
    (hC : 0 < xorDDT_g k₁ bR aR) :
    leftColumnSupport k₀ k₁ k₂ aR bR =
      (firstRoundSupport k₀ aR).image (fun d => xor bR d) := by
  classical
  ext aL
  simp only [leftColumnSupport, firstRoundSupport,
    Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · intro hp
    have hF : 0 < xorDDT_g k₀ aR (xor bR aL) := by
      rw [xorDDT_rounds_three_zero_left_factorization] at hp
      exact Nat.pos_of_mul_pos_right hp
    exact ⟨xor bR aL, hF, xor_left_twice bR aL⟩
  · rintro ⟨d, hd, hda⟩
    rw [← hda, reindexed_entry]
    exact Nat.mul_pos hd hC

/-- The number of positive coefficients in any nonempty column depends
    only on the FIRST round key and on the right input difference. -/
theorem leftColumnSupport_card_of_pos
    (k₀ k₁ k₂ aR bR : (V 32))
    (hC : 0 < xorDDT_g k₁ bR aR) :
    (leftColumnSupport k₀ k₁ k₂ aR bR).card =
      (firstRoundSupport k₀ aR).card := by
  rw [leftColumnSupport_eq_image_of_pos k₀ k₁ k₂ aR bR hC]
  exact Finset.card_image_of_injective _ (xor_left_injective bR)

/-- If the second-round factor is zero, every entry is zero. -/
theorem leftColumnSupport_empty_of_second_zero
    (k₀ k₁ k₂ aR bR : (V 32))
    (hC : xorDDT_g k₁ bR aR = 0) :
    leftColumnSupport k₀ k₁ k₂ aR bR = ∅ := by
  classical
  ext aL
  simp [leftColumnSupport,
    xorDDT_rounds_three_zero_left_factorization, hC]

/-- A positive second factor always gives at least one positive entry.
    The existence follows from the already proved exact column-zero
    criterion (which itself uses conservation of DDT mass). -/
theorem leftColumnSupport_nonempty_of_second_pos
    (k₀ k₁ k₂ aR bR : (V 32))
    (hC : 0 < xorDDT_g k₁ bR aR) :
    (leftColumnSupport k₀ k₁ k₂ aR bR).Nonempty := by
  classical
  by_contra hn
  have hAll : ∀ aL : (V 32),
      xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
        (aL, aR) (0#32, bR) = 0 := by
    intro aL
    apply Nat.eq_zero_of_not_pos
    intro hp
    apply hn
    exact ⟨aL, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩⟩
  have hz := (zeroLeft_column_empty_iff k₀ k₁ k₂ aR bR).mp hAll
  omega

/-- The exact test for an empty column support, with no Boolean verifier. -/
theorem leftColumnSupport_empty_iff_second_zero
    (k₀ k₁ k₂ aR bR : (V 32)) :
    leftColumnSupport k₀ k₁ k₂ aR bR = ∅ ↔
      xorDDT_g k₁ bR aR = 0 := by
  constructor
  · intro he
    by_contra hc
    have hpos : 0 < xorDDT_g k₁ bR aR := by omega
    have hnonempty :=
      leftColumnSupport_nonempty_of_second_pos k₀ k₁ k₂ aR bR hpos
    rcases hnonempty with ⟨x, hx⟩
    rw [he] at hx
    simp only [Finset.notMem_empty] at hx
  · exact leftColumnSupport_empty_of_second_zero k₀ k₁ k₂ aR bR

/-- All nonempty zero-left columns for a fixed `(k0,aR)` have the same
    support CARDINALITY, even with completely different second and third
    keys, and completely different right output differences. -/
theorem two_nonempty_columns_same_support_card
    (k₀ k₁ k₂ k₁' k₂' aR bR bR' : (V 32))
    (hC : 0 < xorDDT_g k₁ bR aR)
    (hC' : 0 < xorDDT_g k₁' bR' aR) :
    (leftColumnSupport k₀ k₁ k₂ aR bR).card =
      (leftColumnSupport k₀ k₁' k₂' aR bR').card := by
  rw [leftColumnSupport_card_of_pos k₀ k₁ k₂ aR bR hC,
      leftColumnSupport_card_of_pos k₀ k₁' k₂' aR bR' hC']

/-- Cross-column PROPORTIONALITY of the complete DDT, valid even if
    one (or both) second-round multipliers vanishes.

    We match entries by their first-round argument `d = bR XOR aL`.
    This is the algebraic basis for transporting concrete certificates
    from one nonzero column to any other. -/
theorem cross_column_proportionality
    (k₀ k₁ k₂ k₁' k₂' aR bR bR' aL : (V 32)) :
    xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
        (aL, aR) (0#32, bR) * xorDDT_g k₁' bR' aR =
      xorDDT_rounds 3 (threeRoundKeys k₀ k₁' k₂')
        (xor bR' (xor bR aL), aR) (0#32, bR') *
          xorDDT_g k₁ bR aR := by
  rw [xorDDT_rounds_three_zero_left_factorization,
      reindexed_entry]
  exact Nat.mul_right_comm _ _ _

end Magma.ZeroLeftColumnTransport
