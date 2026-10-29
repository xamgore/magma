module

public import Magma.RFC8891
import all Init.Data.Range.Basic

@[expose] public section

/-!
# Cryptographic properties of the Magma components

S-box DDT/LAT bounds, substitution-layer Walsh spectra and nonlinearity,
and modular/XOR differential properties of the keyed round function.
-/

open Magma.Internal

namespace Magma.SBoxProperties

/-- Four-bit input/output masks, represented as numbers from 0 to 15. -/
abbrev Mask := Fin 16

/-- Interpret a mask as a 4-bit vector. -/
private def bits (x : Mask) : V 4 := BitVec.ofNat 4 x.val

/-- DDT_i(a,b) = # {x | π_i(x ⊕ a) ⊕ π_i(x) = b}. -/
def ddt (i : Fin 8) (a b : Mask) : Nat :=
  ((Finset.univ : Finset Mask).filter (fun x =>
    (π i (xor (bits x) (bits a)) ^^^ π i (bits x)) = bits b)).card

/-- Maximum nontrivial entry of the DDT, excluding zero input differences. -/
def differentialUniformity (i : Fin 8) : Nat :=
  ((Finset.univ : Finset Mask).filter (fun a => a ≠ 0)).sup
    (fun a => (Finset.univ : Finset Mask).sup (fun b => ddt i a b))

/-- Parity of the GF(2) dot product, i.e. the low bit of the popcount. -/
private def dotParity (u v : V 4) : Bool :=
  ((u &&& v).cpop).getLsbD 0

/-- Number of inputs for which the linear input/output approximations agree. -/
def latAgreements (i : Fin 8) (a b : Mask) : Nat :=
  ((Finset.univ : Finset Mask).filter (fun x =>
    dotParity (bits a) (bits x) = dotParity (bits b) (π i (bits x)))).card

/-- Signed Walsh/LAT coefficient: (#agreements) - (#disagreements). -/
def lat (i : Fin 8) (a b : Mask) : Int :=
  2 * (latAgreements i a b : Int) - 16

/-- Max absolute Walsh/LAT coefficient for one nonzero output mask. -/
def maxAbsLat (i : Fin 8) (b : Mask) : Nat :=
  (Finset.univ : Finset Mask).sup (fun a => (lat i a b).natAbs)

/-- Component nonlinearity, i.e. minimum Hamming distance from affine functions. -/
def componentNonlinearity (i : Fin 8) (b : Mask) : Nat :=
  8 - maxAbsLat i b / 2

/-- Every S-box is differentially 4-uniform. -/
theorem differentialUniformity_eq_four (i : Fin 8) :
    differentialUniformity i = 4 := by
  fin_cases i <;> decide

/-- Every nonzero component mask has maximum absolute Walsh coefficient 8. -/
theorem maxAbsLat_eq_eight (i : Fin 8) (b : Mask) (hb : b ≠ 0) :
    maxAbsLat i b = 8 := by
  have h : ∀ i : Fin 8, ∀ b : Mask,
      b = 0 ∨ maxAbsLat i b = 8 := by
    decide
  exact (h i b).resolve_left hb

/-- Every nonzero component of all eight S-boxes has nonlinearity 4. -/
theorem componentNonlinearity_eq_four
    (i : Fin 8) (b : Mask) (hb : b ≠ 0) :
    componentNonlinearity i b = 4 := by
  simp [componentNonlinearity, maxAbsLat_eq_eight i b hb]

/-- Individual DDT entries are bounded by the differential uniformity 4. -/
theorem ddt_le_four (i : Fin 8) (a b : Mask) (ha : a ≠ 0) :
    ddt i a b ≤ 4 := by
  have h : ∀ i : Fin 8, ∀ a b : Mask,
      a = 0 ∨ ddt i a b ≤ 4 := by
    decide
  exact (h i a b).resolve_left ha

/-- All nontrivial LAT entries have magnitude at most 8. -/
theorem lat_natAbs_le_eight (i : Fin 8) (a b : Mask) (hb : b ≠ 0) :
    (lat i a b).natAbs ≤ 8 := by
  have h : ∀ i : Fin 8, ∀ a b : Mask,
      b = 0 ∨ (lat i a b).natAbs ≤ 8 := by
    decide
  exact (h i a b).resolve_left hb

-- Checks for the first S-box and the trivial entries.
example : ddt 0 0 0 = 16 := by decide

example : ddt 0 2 15 = 4 := by decide

example : lat 0 0 0 = 16 := by decide

example : lat 0 1 8 = -8 := by decide

end Magma.SBoxProperties

namespace Magma.TProperties

open Magma.SBoxProperties

/-- Reassemble eight little-endian-indexed nibbles into a 32-bit word. -/
private def packNibbles (f : Fin 8 → V 4) : V 32 :=
  f 7 ++ f 6 ++ f 5 ++ f 4 ++ f 3 ++ f 2 ++ f 1 ++ f 0

private theorem nibble_packNibbles (f : Fin 8 → V 4) (i : Fin 8) :
    nibble (packNibbles f) i = f i := by
  unfold packNibbles
  rw [nibble_concat]
  fin_cases i <;> rfl

private theorem packNibbles_nibble (x : V 32) : packNibbles (fun i => nibble x i) = x := by
  apply nibble_ext
  intro i
  exact nibble_packNibbles (fun j => nibble x j) i

/-- A 32-bit word is precisely a tuple of eight independent 4-bit words. -/
private def nibbleEquiv : V 32 ≃ (Fin 8 → V 4) where
  toFun := fun x i => nibble x i
  invFun := packNibbles
  left_inv := packNibbles_nibble
  right_inv := by
    intro f
    funext i
    exact nibble_packNibbles f i

private theorem nibble_xor (x y : V 32) (i : Fin 8) :
    nibble (xor x y) i = xor (nibble x i) (nibble y i) := by
  change
    BitVec.extractLsb' (4 * i.val) 4 (x ^^^ y) =
      BitVec.extractLsb' (4 * i.val) 4 x ^^^ BitVec.extractLsb' (4 * i.val) 4 y
  exact BitVec.extractLsb'_xor

/-- The global difference equation holds iff it holds in all eight nibbles. -/
private theorem difference_iff_nibbles (a b x : V 32) :
    xor (t (xor x a)) (t x) = b ↔
      ∀ i : Fin 8,
        xor (π i (xor (nibble x i) (nibble a i)))
            (π i (nibble x i)) = nibble b i := by
  constructor
  · intro h i
    have hi := congrArg (fun z : V 32 => nibble z i) h
    simpa only [nibble_xor, t_substitutes_components] using hi
  · intro h
    apply nibble_ext
    intro i
    simpa only [nibble_xor, t_substitutes_components] using h i

/-- 4-bit DDT using BitVec rather than `Fin 16`. -/
private def ddt4 (i : Fin 8) (a b : V 4) : Nat :=
  ((Finset.univ : Finset (V 4)).filter (fun x =>
    xor (π i (xor x a)) (π i x) = b)).card

private theorem bits_toFin (x : V 4) : bits x.toFin = x := by
  change BitVec.ofNat 4 x.toNat = x
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- The local DDT is exactly the already formalized SBoxProperties.ddt. -/

private theorem ddt4_eq_ddt (i : Fin 8) (a b : V 4) :
    ddt4 i a b = ddt i a.toFin b.toFin := by
  unfold ddt4 ddt
  refine Finset.card_equiv (BitVec.equivFin (m := 4)).toEquiv ?_
  intro x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

  have hx :
      bits ((BitVec.equivFin (m := 4)).toEquiv x) = x := by
    change bits x.toFin = x
    exact bits_toFin x

  rw [hx, bits_toFin a, bits_toFin b]
  rfl

/-- The mathematical DDT of the complete 32-bit substitution `t`. -/
def ddtT (a b : V 32) : Nat :=
  ((Finset.univ : Finset (V 32)).filter (fun x =>
    xor (t (xor x a)) (t x) = b)).card

/-- Structural factorization: no enumeration of the 2^32 input words. -/
theorem ddtT_factor (a b : V 32) :
    ddtT a b =
      ∏ i : Fin 8, ddt i (nibble a i).toFin (nibble b i).toFin := by
  let choices : Fin 8 → Finset (V 4) := fun i =>
    (Finset.univ : Finset (V 4)).filter (fun x =>
      xor (π i (xor x (nibble a i))) (π i x) = nibble b i)

  have hcount : ddtT a b = (Fintype.piFinset choices).card := by
    unfold ddtT
    refine Finset.card_equiv nibbleEquiv ?_
    intro x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Fintype.mem_piFinset]

    constructor
    · intro hx i
      change nibble x i ∈ choices i
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _,
          (difference_iff_nibbles a b x).mp hx i⟩

    · intro hx
      apply (difference_iff_nibbles a b x).mpr
      intro i
      have hi : nibble x i ∈ choices i := hx i
      exact (Finset.mem_filter.mp hi).2

  calc
    ddtT a b = (Fintype.piFinset choices).card := hcount
    _ = ∏ i : Fin 8, (choices i).card := Fintype.card_piFinset choices
    _ = ∏ i : Fin 8, ddt i (nibble a i).toFin (nibble b i).toFin := by
      apply Finset.prod_congr rfl
      intro i _
      exact ddt4_eq_ddt i (nibble a i) (nibble b i)

/-- Each inactive nibble contributes at most 16 matches; each active one at most 4. -/
theorem ddtT_le_active_bound (a b : V 32) :
    ddtT a b ≤
      ∏ i : Fin 8, (if nibble a i = (0 : V 4) then 16 else 4) := by
  rw [ddtT_factor]
  apply Finset.prod_le_prod
  intro i _
  by_cases h : nibble a i = (0 : V 4)
  · rw [ite_eq_left h]
    have hsubset :
        ((Finset.univ : Finset Mask).filter (fun x =>
          (π i (xor (bits x) (bits (nibble a i).toFin)) ^^^ π i (bits x)) =
            bits (nibble b i).toFin)) ⊆ Finset.univ :=
      Finset.filter_subset _ _
    have hle := Finset.card_le_card hsubset
    have hc : (Finset.univ : Finset Mask).card = 16 := by decide
    simpa only [ddt, hc] using hle
  · rw [ite_eq_right h]
    apply ddt_le_four
    intro hz
    apply h
    calc
      nibble a i = bits (nibble a i).toFin := (bits_toFin _).symm
      _ = bits (0 : Mask) := congrArg bits hz
      _ = (0 : V 4) := rfl

/-- The signed character of one four-bit input/output mask pair.
    This is `(-1)^(a·x + b·πᵢ(x))`, with products/sums in GF(2). -/
private def sign4 (i : Fin 8) (a b x : V 4) : Int :=
  if dotParity a x = dotParity b (π i x) then 1 else -1

/-- Walsh coefficient of the SPECIFIED 32-bit transformation `t`.
    The parity signs are grouped by nibble. Their product equals
    `(-1)^(a·x + b·t(x))` by additivity of the GF(2) inner product.
    This definition refers directly to `t`, not an alternative S-box
    implementation. The definition is a sum, not a product of LATs. -/
def walshT (a b : V 32) : Int :=
  ∑ x : V 32, ∏ i : Fin 8,
    if dotParity (nibble a i) (nibble x i) =
         dotParity (nibble b i) (nibble (t x) i)
    then (1 : Int) else -1

/-- Re-express the signed sum over Fin 16 as the existing `lat`. -/
private theorem sum_sign_mask_eq_lat (i : Fin 8) (a b : Mask) :
    (∑ x : Mask,
      if dotParity (bits a) (bits x) = dotParity (bits b) (π i (bits x))
      then (1 : Int) else -1) = lat i a b := by
  let P : Mask → Prop := fun x =>
    dotParity (bits a) (bits x) = dotParity (bits b) (π i (bits x))
  have hterm (x : Mask) :
      (if P x then (1 : Int) else -1) =
        2 * (if P x then (1 : Int) else 0) - 1 := by
    by_cases h : P x <;> simp [h]
  calc
    (∑ x : Mask, if P x then (1 : Int) else -1) =
        ∑ x : Mask, (2 * (if P x then (1 : Int) else 0) - 1) := by
      apply Finset.sum_congr rfl
      intro x _
      exact hterm x
    _ = 2 * (∑ x : Mask, if P x then (1 : Int) else 0) - 16 := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      simp
    _ = 2 * (latAgreements i a b : Int) - 16 := by
      rw [Finset.sum_boole]
      rfl
    _ = lat i a b := rfl

/-- Connect the sum of local signed characters to the existing LAT. -/
private theorem sum_sign4_eq_lat (i : Fin 8) (a b : V 4) :
    (∑ x : V 4, sign4 i a b x) = lat i a.toFin b.toFin := by
  calc
    (∑ x : V 4, sign4 i a b x) =
        ∑ x : Mask,
          (if dotParity (bits a.toFin) (bits x) =
                dotParity (bits b.toFin) (π i (bits x))
           then (1 : Int) else -1) := by
      apply Fintype.sum_equiv (BitVec.equivFin (m := 4)).toEquiv
      intro x
      change (if dotParity a x = dotParity b (π i x)
              then (1 : Int) else -1) = _
      have hx : bits ((BitVec.equivFin (m := 4)).toEquiv x) = x := by
        change bits x.toFin = x
        exact bits_toFin x
      rw [hx, bits_toFin a, bits_toFin b]
    _ = lat i a.toFin b.toFin := sum_sign_mask_eq_lat i a.toFin b.toFin

/--
  **Walsh transform factorization** for the parallel
  32-bit substitution `t`.

  Each Walsh coefficient of `t` equals the product of
  the corresponding Walsh coefficients of its eight
  four-bit S-boxes.

  It is the Fourier analogue of `ddtT_factor`.

  The proof follows from the independence of the eight
  nibble substitutions and avoids exhaustive evaluation
  over the 32-bit input space.
-/
theorem walshT_factor (a b : V 32) :
    walshT a b =
      ∏ i : Fin 8, lat i (nibble a i).toFin (nibble b i).toFin := by
  let F : Fin 8 → V 4 → Int := fun i x =>
    sign4 i (nibble a i) (nibble b i) x
  calc
    walshT a b = ∑ x : V 32, ∏ i : Fin 8, F i (nibble x i) := by
      simp only [walshT, t_substitutes_components, F, sign4]
    _ = ∑ f : Fin 8 → V 4, ∏ i : Fin 8, F i (f i) := by
      apply Fintype.sum_equiv nibbleEquiv
      intro x
      rfl
    _ = ∏ i : Fin 8, ∑ x : V 4, F i x := by
      simpa only [Fintype.piFinset_univ] using
        (Finset.sum_prod_piFinset (Finset.univ : Finset (V 4)) F)
    _ = ∏ i : Fin 8, lat i (nibble a i).toFin (nibble b i).toFin := by
      apply Finset.prod_congr rfl
      intro i _
      exact sum_sign4_eq_lat i (nibble a i) (nibble b i)

/-- For an inactive output nibble every local Walsh coefficient has
    magnitude ≤ 16; for an active nibble the previously proven bound is 8. -/
private theorem local_lat_bound (i : Fin 8) (a b : V 4) :
    (lat i a.toFin b.toFin).natAbs ≤
      if b = (0 : V 4) then 16 else 8 := by
  by_cases hb : b = 0
  · subst b
    have h : ∀ j : Fin 8, ∀ m : Mask,
        (lat j m 0).natAbs ≤ 16 := by decide
    simpa using h i a.toFin
  · have hbfin : b.toFin ≠ (0 : Mask) := by
      intro hz
      apply hb
      calc
        b = bits b.toFin := (bits_toFin b).symm
        _ = bits (0 : Mask) := congrArg bits hz
        _ = (0 : V 4) := rfl
    simp only [hb, ite_false]
    exact lat_natAbs_le_eight i a.toFin b.toFin hbfin

/-- Structural upper bound on the absolute 32-bit Walsh coefficient. -/
theorem walshT_natAbs_le (a b : V 32) :
    (walshT a b).natAbs ≤
      ∏ i : Fin 8, (if nibble b i = (0 : V 4) then 16 else 8) := by
  calc
    (walshT a b).natAbs =
        (∏ i : Fin 8, lat i (nibble a i).toFin (nibble b i).toFin).natAbs :=
          congrArg Int.natAbs (walshT_factor a b)
    _ = ∏ i : Fin 8, (lat i (nibble a i).toFin (nibble b i).toFin).natAbs := by
      simpa only [Int.natAbsHom_apply] using
        (map_prod Int.natAbsHom
          (fun i : Fin 8 => lat i (nibble a i).toFin (nibble b i).toFin)
          Finset.univ)
    _ ≤ ∏ i : Fin 8, (if nibble b i = (0 : V 4) then 16 else 8) := by
      apply Finset.prod_le_prod
      intro i _
      exact local_lat_bound i (nibble a i) (nibble b i)

/-- Each local upper bound is actually attained by some input mask.
    This is a small computation over the 8 × 16 × 16 local cases. -/
private theorem exists_local_max (i : Fin 8) (b : V 4) :
    ∃ a : V 4, (lat i a.toFin b.toFin).natAbs =
      if b = (0 : V 4) then 16 else 8 := by
  have h : ∀ j : Fin 8, ∀ v : V 4,
      ∃ u : V 4, (lat j u.toFin v.toFin).natAbs =
        if v = (0 : V 4) then 16 else 8 := by decide
  exact h i b

/-- Maximum (over input masks) of the absolute Walsh coefficient. -/
def maxAbsWalshT (b : V 32) : Nat :=
  (Finset.univ : Finset (V 32)).sup (fun a => (walshT a b).natAbs)

private theorem finset_sup_eq_of_bound_attained {α : Type*} (s : Finset α) (f : α → Nat) (c : Nat)
    (hupper : ∀ x ∈ s, f x ≤ c) (x : α) (hx : x ∈ s) (heq : f x = c) : s.sup f = c := by
  apply le_antisymm
  · exact Finset.sup_le hupper
  · calc
      c = f x := heq.symm
      _ ≤ s.sup f := Finset.le_sup hx

/--
  Exact maximum absolute Walsh coefficient of `t`
  for a fixed 32-bit output mask.

  Each zero output nibble contributes a factor of 16,
  while each nonzero output nibble contributes a factor
  of 8.

  Consequently, an output mask containing k active
  nibbles has maximum absolute Walsh coefficient 2^(32-k).
  The product upper bound is SHARP for every output mask.

  The bound is attained because each local S-box admits
  an input mask achieving its corresponding maximum.
-/
theorem maxAbsWalshT_eq (b : V 32) :
    maxAbsWalshT b =
      ∏ i : Fin 8, (if nibble b i = (0 : V 4) then 16 else 8) := by
  let a : V 32 := packNibbles (fun i =>
    Classical.choose (exists_local_max i (nibble b i)))
  have hexact : (walshT a b).natAbs =
      ∏ i : Fin 8, (if nibble b i = (0 : V 4) then 16 else 8) := by
    calc
      (walshT a b).natAbs =
          (∏ i : Fin 8, lat i (nibble a i).toFin (nibble b i).toFin).natAbs :=
            congrArg Int.natAbs (walshT_factor a b)
      _ = ∏ i : Fin 8, (lat i (nibble a i).toFin (nibble b i).toFin).natAbs := by
        simpa only [Int.natAbsHom_apply] using
          (map_prod Int.natAbsHom
            (fun i : Fin 8 => lat i (nibble a i).toFin (nibble b i).toFin)
            Finset.univ)
      _ = ∏ i : Fin 8, (if nibble b i = (0 : V 4) then 16 else 8) := by
        apply Finset.prod_congr rfl
        intro i _
        simpa only [a, nibble_packNibbles] using
          (Classical.choose_spec (exists_local_max i (nibble b i)))
  unfold maxAbsWalshT
  exact finset_sup_eq_of_bound_attained
    (s := (Finset.univ : Finset (V 32)))
    (f := fun x : V 32 => (walshT x b).natAbs)
    (c := ∏ i : Fin 8,
      (if nibble b i = (0 : V 4) then 16 else 8))
    (by
      intro x _
      exact walshT_natAbs_le x b)
    a
    (Finset.mem_univ a)
    hexact

/-- Hamming distance of the b-component of t to affine Boolean functions. -/
def componentNonlinearityT (b : V 32) : Nat :=
  2 ^ 31 - maxAbsWalshT b / 2

/-- Exact nonlinearity of EVERY output component, expressed as an
    explicit product of 8 small, already certified local bounds. -/
theorem componentNonlinearityT_eq (b : V 32) :
    componentNonlinearityT b =
      2 ^ 31 -
        (∏ i : Fin 8,
          (if nibble b i = (0 : V 4) then 16 else 8)) / 2 := by
  rw [componentNonlinearityT, maxAbsWalshT_eq]

/-- A zero 32-bit word has eight zero nibbles. -/
private theorem nibble_zero (i : Fin 8) :
    nibble (0 : V 32) i = 0 := by
  fin_cases i <;> decide

/-- For every NONZERO output mask, at least one nibble is active.
    The largest absolute nontrivial Walsh coefficient is therefore ≤ 2^31. -/
theorem maxAbsWalshT_le_half (b : V 32) (hb : b ≠ 0) :
    maxAbsWalshT b ≤ 2 ^ 31 := by
  obtain ⟨i, hi⟩ : ∃ i : Fin 8, nibble b i ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hb
    apply nibble_ext
    intro j
    simpa only [nibble_zero] using hn j
  rw [maxAbsWalshT_eq]
  have hle :
      (∏ j : Fin 8,
        (if nibble b j = (0 : V 4) then 16 else 8)) ≤
      ∏ j : Fin 8,
        (if j = i then 8 else 16) := by
    apply Finset.prod_le_prod
    intro j _
    by_cases hij : j = i
    · subst j
      rw [ite_eq_right hi,
          ite_eq_left (rfl : i = i)]
    · rw [ite_eq_right hij]
      split_ifs <;> omega
  have hconst : (∏ j : Fin 8, (if j = i then 8 else 16)) =
      2 ^ 31 := by
    fin_cases i <;> decide
  simpa only [hconst] using hle

/-- All nonzero 32-bit output components have nonlinearity ≥ 2^30. -/
theorem componentNonlinearityT_ge (b : V 32) (hb : b ≠ 0) :
    2 ^ 30 ≤ componentNonlinearityT b := by
  have h := maxAbsWalshT_le_half b hb
  unfold componentNonlinearityT
  omega

/-- One active output nibble ATTAINS the global Walsh maximum. -/
theorem maxAbsWalshT_one :
    maxAbsWalshT (1#32) = 2 ^ 31 := by
  rw [maxAbsWalshT_eq]
  decide

/-- Hence one output component has nonlinearity exactly 2^30. -/
theorem componentNonlinearityT_one :
    componentNonlinearityT (1#32) = 2 ^ 30 := by
  rw [componentNonlinearityT_eq]
  decide

/--
  The maximum absolute Walsh coefficient of the 32-bit
  substitution `t`, taken over all nonzero output masks,
  is exactly 2^31.

  The upper bound follows from `maxAbsWalshT_le_half`.
  It is attained by the output mask `1#32`, as shown by
  `maxAbsWalshT_one`.

  The proof uses structural properties of the eight
  S-boxes rather than exhaustive enumeration of 2^32 masks.
-/
private theorem globalMaxWalsh_eq :
    ((Finset.univ : Finset (V 32)).filter
      (fun b => b ≠ 0)).sup maxAbsWalshT = 2 ^ 31 := by
  apply le_antisymm
  · apply Finset.sup_le
    intro b hb
    exact maxAbsWalshT_le_half b
      (Finset.mem_filter.mp hb).2
  · calc
      2 ^ 31 = maxAbsWalshT (1#32) :=
        maxAbsWalshT_one.symm
      _ ≤ ((Finset.univ : Finset (V 32)).filter
          (fun b => b ≠ 0)).sup maxAbsWalshT := by
        apply Finset.le_sup
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, by decide⟩

/--
  Elementary arithmetic identity used to calculate
  the vectorial nonlinearity from the maximum absolute
  Walsh coefficient.

  For a 32-bit vectorial Boolean function, the
  nonlinearity is 2^31 minus half the maximum
  absolute nontrivial Walsh coefficient.
-/
private theorem nl_arithmetic :
    (2 ^ 31 : Nat) - (2 ^ 31) / 2 = 2 ^ 30 := by
  norm_num

/--
  The vectorial nonlinearity of the RFC 8891
  32-bit parallel substitution `t` is exactly 2^30.

  This theorem uses the original mathematical definition:
  the maximum absolute Walsh coefficient over all
  nonzero output masks.

  It is the principal numerical nonlinearity result,
  independent of any alternative computational
  representation of `vectorNonlinearityT`.
-/
private theorem vectorNL_raw_eq :
    (2 ^ 31 : Nat) -
      (((Finset.univ : Finset (V 32)).filter
        (fun b => b ≠ 0)).sup maxAbsWalshT) / 2 =
      2 ^ 30 := by
  exact
    (congrArg
      (fun n : Nat => (2 ^ 31 : Nat) - n / 2)
      globalMaxWalsh_eq).trans nl_arithmetic

/--
  Computationally simplified representation of the
  vectorial nonlinearity of `t`.

  The expensive maximum over 32-bit output masks is
  replaced by its formally established value, 2^31.

  Equivalence with the original Walsh-based definition
  is established by `vectorNonlinearityT_spec`.
-/
def vectorNonlinearityT : Nat :=
  (2 ^ 31 : Nat) - (2 ^ 31) / 2

/--
  The simplified definition `vectorNonlinearityT` agrees
  with the original Walsh-based mathematical definition
  of vectorial nonlinearity.

  The latter is 2^31 minus half the maximum absolute
  Walsh coefficient over all nonzero output masks.

  This theorem justifies replacing the expensive finite
  supremum with the certified numerical result.
-/
theorem vectorNonlinearityT_spec :
    vectorNonlinearityT =
      (2 ^ 31 : Nat) -
        (((Finset.univ : Finset (V 32)).filter
          (fun b => b ≠ 0)).sup maxAbsWalshT) / 2 := by
  exact
    (congrArg
      (fun n : Nat => (2 ^ 31 : Nat) - n / 2)
      globalMaxWalsh_eq).symm

/--
  The simplified vectorial nonlinearity of the 32-bit
  substitution `t` evaluates to 2^30.

  Together with `vectorNonlinearityT_spec`, this gives
  the formally established vectorial nonlinearity
  of the original RFC 8891 substitution.
-/
theorem vector2NonlinearityT_eq :
    vectorNonlinearityT = 2 ^ 30 := by
  exact nl_arithmetic

end Magma.TProperties

namespace Magma.GProperties

/-- Modular addition on RFC's `V 32` representation. -/
def modShift (d x : V 32) : V 32 :=
  Vec_s 32 (add₃₂ (Int_s 32 x) (Int_s 32 d))

/-- Addition of the zero key does not change the 32-bit input. -/
theorem modShift_zero_key (x : V 32) :
    modShift (0#32) x = x := by
  change Vec_s 32 (add₃₂ (Int_s 32 x) (Int_s 32 (0#32))) = x
  have hz : Int_s 32 (0#32) = 0 := by decide
  rw [hz]
  change Vec_s 32 (Int_s 32 x + 0) = x
  simp only [add_zero]
  exact (vecEquiv 32).apply_symm_apply x

/-- Adding a fixed residue modulo 2^32 is a permutation. -/
private def zAddEquiv (c : Z2 32) : Z2 32 ≃ Z2 32 where
  toFun := fun z => z + c
  invFun := fun z => z - c
  left_inv := by
    intro z
    simp
  right_inv := by
    intro z
    simp

/-- The modular translation in bitvector representation is a permutation. -/
private def modShiftEquiv (d : V 32) : V 32 ≃ V 32 :=
  ((vecEquiv 32).symm.trans (zAddEquiv (Int_s 32 d))).trans (vecEquiv 32)

private theorem modShiftEquiv_apply (d x : V 32) : modShiftEquiv d x = modShift d x := by rfl

/-- Modular translations commute, because Z/(2^32) is additive abelian. -/
private theorem modShift_comm (d k x : V 32) :
    modShift k (modShift d x) = modShift d (modShift k x) := by
  unfold modShift add₃₂
  simp only [Int_s_Vec_s]
  congr 1
  ac_rfl

/-- Rotation preserves XOR differences exactly. -/
theorem rot11_xor (u v : V 32) :
    xor (rot11 u) (rot11 v) = rot11 (xor u v) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let i : Fin 32 := (⟨j, hj⟩ : Fin 32) - 11
  have hi : i + 11 = (⟨j, hj⟩ : Fin 32) := by
    dsimp [i]
    simp
  change
    component (xor (rot11 u) (rot11 v)) (⟨j, hj⟩ : Fin 32) =
      component (rot11 (xor u v)) (⟨j, hj⟩ : Fin 32)
  calc
    component (xor (rot11 u) (rot11 v)) (⟨j, hj⟩ : Fin 32) =
        component (xor (rot11 u) (rot11 v)) (i + 11) := by rw [hi]
    _ = Bool.xor (component u i) (component v i) := by
      rw [xor_components, rot11_moves_components_up,
          rot11_moves_components_up]
    _ = component (xor u v) i := (xor_components u v i).symm
    _ = component (rot11 (xor u v)) (i + 11) :=
      (rot11_moves_components_up (xor u v) i).symm
    _ = component (rot11 (xor u v)) (⟨j, hj⟩ : Fin 32) := by rw [hi]

/-- The existing `g` is precisely `rot11 ∘ t ∘ modShift k`. -/
theorem g_as_modShift (k x : V 32) :
    g k x = rot11 (t (modShift k x)) := by
  rfl

/-- Exact pointwise formula for a modular input difference of `g`. -/
theorem g_mod_difference (k d x : V 32) :
    xor (g k (modShift d x)) (g k x) =
      rot11 (xor (t (modShift d (modShift k x)))
                 (t (modShift k x))) := by
  change xor (rot11 (t (modShift k (modShift d x))))
             (rot11 (t (modShift k x))) = _
  rw [modShift_comm d k x]
  exact rot11_xor _ _

/-- Number of modular-input / XOR-output differential solutions.
    **This is NOT the usual XOR/XOR DDT.** -/
def addXorDDT (f : V 32 → V 32) (d b : V 32) : Nat :=
  ((Finset.univ : Finset (V 32)).filter (fun x =>
    xor (f (modShift d x)) (f x) = b)).card

/-- The output difference equation is equivalent to the one for `t`
    after a key-dependent bijective reindexing of the input. -/
private theorem g_mod_difference_iff (k d b x : V 32) :
    (xor (g k (modShift d x)) (g k x) = rot11 b) ↔
    (xor (t (modShift d (modShift k x))) (t (modShift k x)) = b) := by
  rw [g_mod_difference]
  constructor
  · intro h
    exact rot11_is_bijective.injective h
  · intro h
    exact congrArg rot11 h

/-- Main result: the *modular-input / XOR-output* DDT of `g[k]`
    is independent of k (up to rotating the output difference).
    This is a structural counting proof; it never enumerates 2^32 words. -/
theorem addXorDDT_g (k d b : V 32) :
    addXorDDT (g k) d (rot11 b) = addXorDDT t d b := by
  unfold addXorDDT
  refine Finset.card_equiv (modShiftEquiv k) ?_
  intro x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [modShiftEquiv_apply]
  exact g_mod_difference_iff k d b x

/-- As a corollary, every pair of round keys gives the same
    modular-input / XOR-output DDT. -/
theorem addXorDDT_key_independent (k₁ k₂ d b : V 32) :
    addXorDDT (g k₁) d (rot11 b) =
      addXorDDT (g k₂) d (rot11 b) := by
  rw [addXorDDT_g, addXorDDT_g]

/-- Key independence in the most useful form: no restriction on the output mask. -/
theorem addXorDDT_key_independent_all (k₁ k₂ d b : V 32) :
    addXorDDT (g k₁) d b = addXorDDT (g k₂) d b := by
  obtain ⟨c, hc⟩ := rot11_is_bijective.surjective b
  rw [← hc]
  exact addXorDDT_key_independent k₁ k₂ d c

/-- For a standard XOR input difference, the difference *after*
    key addition depends on x (because of carry propagation). -/
def carriedXorDifference (k d x : V 32) : V 32 :=
  xor (modShift k (xor x d)) (modShift k x)

/-- This is the exact XOR propagation equation for `g`.
    Unlike the modular-input case, it has an x-dependent inner delta. -/
theorem g_xor_difference (k d x : V 32) :
    xor (g k (xor x d)) (g k x) =
      rot11 (xor (t (xor (modShift k x) (carriedXorDifference k d x)))
                 (t (modShift k x))) := by
  have hcancel :
      xor (modShift k x) (carriedXorDifference k d x) =
        modShift k (xor x d) := by
    unfold carriedXorDifference
    change (modShift k x) ^^^
        ((modShift k (xor x d)) ^^^ (modShift k x)) =
      modShift k (xor x d)
    rw [BitVec.xor_comm (modShift k (xor x d)) (modShift k x)]
    exact xor_cancel_twice _ _
  change xor (rot11 (t (modShift k (xor x d))))
             (rot11 (t (modShift k x))) = _
  rw [rot11_xor, hcancel]

end Magma.GProperties
