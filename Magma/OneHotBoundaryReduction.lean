module

public import Magma.OneHotCarryPrefix
public import Magma.OneHotSilentNibbleStructure
import all Init.Data.Range.Basic

@[expose] public section

/-!
# Reduction of the active nibble boundary to the local key-class table

A nonempty silent suffix accepts precisely equal incoming carry bits.
Consequently, an active nibble-five transition followed by such a suffix
is possible exactly when the original local S-box predicate holds.
Combining this with arithmetic prefix-carry reachability gives an exact
boundary condition for every key and invariance under its representative.

These are unconditional boundary statements. Connecting the full eight-digit
`carryTrace` existential to this prefix/active/suffix description remains
necessary for the full `xorDDT_g` key-class classification.
-/

open Magma.CarryAutomaton Magma.OneHotKeyClasses Magma.OneHotCarryPrefix
open Magma.OneHotSilentNibbleStructure Magma.OneHotClassCertificates

namespace Magma.OneHotBoundaryReduction

/-! ### 1. A nonempty silent suffix detects carry equality -/

/-- If even the FIRST zero-input-difference S-box in a suffix is required
    to have zero output difference, the input carries must coincide.
    Conversely, diagonal carries pass EVERY silent suffix. -/
theorem nonempty_silent_suffix_iff_diagonal
    (i : Fin 8) (k x : Fin 16)
    (rest : List (Fin 8 × Fin 16 × Fin 16))
    (s : CarryState) :
    (silentRun ((i, k, x) :: rest) s).2 = true ↔ s.1 = s.2 := by
  constructor
  · intro h
    have hfirst :
        decide ((sboxCarryStep i k 0 x s).1 = 0) = true := by
      change (decide ((sboxCarryStep i k 0 x s).1 = 0) &&
        (silentRun rest (sboxCarryStep i k 0 x s).2).2) = true at h
      exact (Bool.and_eq_true_iff.mp h).1
    have hzero : (sboxCarryStep i k 0 x s).1 = 0 := by
      simpa only [decide_eq_true_eq] using hfirst
    rcases s with ⟨c₀, c₁⟩
    exact silent_sbox_zero_forces_diagonal i k x c₀ c₁ hzero
  · intro hdiag
    rcases s with ⟨c₀, c₁⟩
    change c₀ = c₁ at hdiag
    subst c₁
    obtain ⟨c', hc'⟩ := silentRun_diagonal rest (nextCarry x k c₀)
    simp [silentRun, silent_sbox_step_diagonal, hc']

/-! ### 2. The active step followed by a real silent suffix -/

/-- A local active pi_5 transition that must produce output nibble 2,
    followed by a nonempty silent suffix. The suffix may have arbitrarily
    many further nibbles, and their inputs/keys need not be known. -/
def activeWithSilentSuffix
    (q : Fin 16) (c : Fin 2) (r : Fin 4)
    (i : Fin 8) (upperKey upperInput : Fin 16)
    (rest : List (Fin 8 × Fin 16 × Fin 16)) : Prop :=
  ∃ x : Fin 16,
    (sboxCarryStep 5 q (Fin.ofNat 16 (2 ^ r.val)) x (c, c)).1 = 2 ∧
    (silentRun ((i, upperKey, upperInput) :: rest)
      (sboxCarryStep 5 q (Fin.ofNat 16 (2 ^ r.val)) x (c, c)).2).2 = true

/-- Passing the complete silent suffix imposes EXACTLY the local
    equality-of-outgoing-carries condition; no other restriction. -/
theorem activeWithSilentSuffix_iff_local
    (q : Fin 16) (c : Fin 2) (r : Fin 4)
    (i : Fin 8) (upperKey upperInput : Fin 16)
    (rest : List (Fin 8 × Fin 16 × Fin 16)) :
    activeWithSilentSuffix q c r i upperKey upperInput rest ↔
      localOneHotStepPossible q c r = true := by
  constructor
  · rintro ⟨x, hout, hsuffix⟩
    let step := sboxCarryStep 5 q (Fin.ofNat 16 (2 ^ r.val)) x (c, c)
    have hdiag : step.2.1 = step.2.2 :=
      (nonempty_silent_suffix_iff_diagonal i upperKey upperInput rest
        step.2).mp hsuffix
    have hpair : step.2 = (step.2.1, step.2.1) := by
      apply Prod.ext
      · rfl
      · exact hdiag.symm
    apply (localOneHotStepPossible_iff_original_step q c r).mpr
    refine ⟨x, step.2.1, ?_⟩
    exact Prod.ext hout hpair
  · intro hlocal
    obtain ⟨x, t, hx⟩ :=
      (localOneHotStepPossible_iff_original_step q c r).mp hlocal
    refine ⟨x, ?_, ?_⟩
    · exact congrArg Prod.fst hx
    · rw [hx]
      exact (nonempty_silent_suffix_iff_diagonal
        i upperKey upperInput rest (t, t)).mpr rfl

/-! ### 3. An arbitrary silent prefix followed by the active boundary -/

/-- This is the *concrete* prefix/active/suffix problem for a fixed
    list of lower input nibbles, with the pair initially at carry (0,0).
    Because the whole prefix is silent, its final state is diagonal. -/
def fixedPrefixBoundaryPath
    (prefixSteps : List (Fin 8 × Fin 16 × Fin 16))
    (q : Fin 16) (r : Fin 4)
    (i : Fin 8) (upperKey upperInput : Fin 16)
    (rest : List (Fin 8 × Fin 16 × Fin 16)) : Prop :=
  ∃ x : Fin 16,
    (sboxCarryStep 5 q (Fin.ofNat 16 (2 ^ r.val)) x
      (silentRun prefixSteps (0, 0)).1).1 = 2 ∧
    (silentRun ((i, upperKey, upperInput) :: rest)
      (sboxCarryStep 5 q (Fin.ofNat 16 (2 ^ r.val)) x
        (silentRun prefixSteps (0, 0)).1).2).2 = true

/-- Once the lower input digits are fixed, ONLY their final equal carry
    matters. The upper suffix imposes no further restriction beyond
    equal outgoing carries from the active S-box. -/
theorem fixedPrefixBoundaryPath_iff_local
    (prefixSteps : List (Fin 8 × Fin 16 × Fin 16))
    (q : Fin 16) (r : Fin 4)
    (i : Fin 8) (upperKey upperInput : Fin 16)
    (rest : List (Fin 8 × Fin 16 × Fin 16)) :
    fixedPrefixBoundaryPath prefixSteps q r i upperKey upperInput rest ↔
      localOneHotStepPossible q
        (silentRun prefixSteps (0, 0)).1.1 r = true := by
  obtain ⟨c, hc⟩ := silentRun_diagonal prefixSteps (0 : Fin 2)
  simp only [fixedPrefixBoundaryPath, hc]
  exact activeWithSilentSuffix_iff_local
    q c r i upperKey upperInput rest

/-! ### 4. Exact key-dependent boundary condition -/

/-- Arithmetic reachability of the input carry, AND acceptance of the
    original (not accelerated) active S-box transition.

    The 32-bit key is arbitrary: this predicate does not enumerate keys. -/
def keyBoundaryPossible (k : V 32) (r : Fin 4) : Prop :=
  ∃ c : Fin 2,
    WordPrefixCarryPossible k c ∧
      localOneHotStepPossible (keyNibble5 k) c r = true

/-- The previously proved prefix theorem, expressed using the Boolean
    carry-regime flag employed by the local S-box classification. -/
theorem wordPrefixCarry_iff_regime (k : V 32) (c : Fin 2) :
    WordPrefixCarryPossible k c ↔
      c = 0 ∨ (c = 1 ∧ canCarryIntoNibble5 k = true) := by
  have h := prefix_carry_possible_iff
    (keyLow20 k) (keyLow20_lt k) c
  change WordPrefixCarryPossible k c ↔
    c = 0 ∨ (c = 1 ∧ keyLow20 k ≠ 0) at h
  constructor
  · intro hc
    rcases h.mp hc with hz | ⟨ho, hn⟩
    · exact Or.inl hz
    · exact Or.inr ⟨ho, (canCarryIntoNibble5_iff k).mpr hn⟩
  · intro hc
    apply h.mpr
    rcases hc with hz | ⟨ho, hn⟩
    · exact Or.inl hz
    · exact Or.inr ⟨ho, (canCarryIntoNibble5_iff k).mp hn⟩

/-- MAIN BOUNDARY THEOREM: for every key, a feasible incoming carry
    and a valid pi_5 transition exist EXACTLY for the entries of the
    previously kernel-checked 32-class local support table. -/
theorem keyBoundaryPossible_iff_localTable (k : V 32) (r : Fin 4) :
    keyBoundaryPossible k r ↔
      r ∈ localOneHotSupportedBits
        (keyNibble5 k) (canCarryIntoNibble5 k) := by
  have hmem :
      r ∈ localOneHotSupportedBits (keyNibble5 k) (canCarryIntoNibble5 k) ↔
        localOneHotStepPossible (keyNibble5 k) 0 r = true ∨
        (canCarryIntoNibble5 k = true ∧
          localOneHotStepPossible (keyNibble5 k) 1 r = true) := by
    simp only [localOneHotSupportedBits, List.mem_filter,
      List.mem_finRange, true_and, Bool.or_eq_true,
      Bool.and_eq_true]
  rw [hmem]
  constructor
  · rintro ⟨c, hc, hlocal⟩
    rcases (wordPrefixCarry_iff_regime k c).mp hc with hz | ⟨ho, hflag⟩
    · subst c
      exact Or.inl hlocal
    · subst c
      exact Or.inr ⟨hflag, hlocal⟩
  · intro h
    rcases h with hz | ⟨hflag, hlocal⟩
    · exact ⟨0, (wordPrefixCarry_iff_regime k 0).mpr (Or.inl rfl), hz⟩
    · exact ⟨1, (wordPrefixCarry_iff_regime k 1).mpr
        (Or.inr ⟨rfl, hflag⟩), hlocal⟩

/-- The complete boundary condition is exactly invariant across any
    two keys with the same sixth nibble and same carry-regime flag. -/
theorem keyBoundaryPossible_same_class
    (k k' : V 32)
    (hq : keyNibble5 k = keyNibble5 k')
    (hc : canCarryIntoNibble5 k = canCarryIntoNibble5 k')
    (r : Fin 4) :
    keyBoundaryPossible k r ↔ keyBoundaryPossible k' r := by
  rw [keyBoundaryPossible_iff_localTable,
      keyBoundaryPossible_iff_localTable, hq, hc]

/-- Every 32-bit key has the same boundary support as its 32-class
    representative. This is unconditional, not a Boolean certificate. -/
theorem keyBoundaryPossible_representative (k : V 32) (r : Fin 4) :
    keyBoundaryPossible k r ↔
      keyBoundaryPossible
        (representativeKey (keyNibble5 k) (canCarryIntoNibble5 k)) r := by
  apply keyBoundaryPossible_same_class
  · exact (representativeKey_has_class
      (keyNibble5 k) (canCarryIntoNibble5 k)).1.symm
  · exact (representativeKey_has_class
      (keyNibble5 k) (canCarryIntoNibble5 k)).2.symm

/-- A whole CLASS of keys (not one representative): if sixth key
    digit is 8 and the lower 20 key bits vanish, no one-hot active
    boundary transition can produce output difference 2. -/
theorem nibble8_no_lower_carry_boundary_empty
    (k : V 32)
    (hq : keyNibble5 k = (8 : Fin 16))
    (hc : canCarryIntoNibble5 k = false)
    (r : Fin 4) :
    ¬ keyBoundaryPossible k r := by
  rw [keyBoundaryPossible_iff_localTable, hq, hc]
  fin_cases r <;> decide

/-- With the same sixth key digit, but NONZERO lower 20 key bits,
    the exact boundary support instead consists of local bit positions
    r=0 and r=2 (absolute bit positions 20 and 22). -/
theorem nibble8_with_lower_carry_boundary_support
    (k : V 32)
    (hq : keyNibble5 k = (8 : Fin 16))
    (hc : canCarryIntoNibble5 k = true)
    (r : Fin 4) :
    keyBoundaryPossible k r ↔ r = 0 ∨ r = 2 := by
  rw [keyBoundaryPossible_iff_localTable, hq, hc]
  fin_cases r <;> decide

/-- A new structural impossibility valid for the class of key 0x00800000.
    This uses the tiny original S-box table, NOT the huge 32-bit DDT. -/
theorem key_00800000_boundary_empty (r : Fin 4) :
    ¬ keyBoundaryPossible (0x00800000#32) r := by
  rw [keyBoundaryPossible_iff_localTable]
  have h : localOneHotSupportedBits
      (keyNibble5 (0x00800000#32))
      (canCarryIntoNibble5 (0x00800000#32)) = [] := by
    decide
  simp [h]

end Magma.OneHotBoundaryReduction
