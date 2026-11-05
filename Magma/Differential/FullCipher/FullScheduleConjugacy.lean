module
public import Magma.Differential.NinePlus.NineReflection
public import Diffan.Symmetry.ReflectedMacroSchedule
import all Init.Data.Range.Basic

set_option maxRecDepth 2048
set_option maxHeartbeats 1000000

@[expose] public section

/-!
# The *entire* RFC 32-round schedule, not only the nine-round reflection.

An 8-round fixed-key forward block H, repeated three times and followed
by its reverse-key Feistel block R, yields the native 32 ordinary rounds
R ∘ H^3. The final RFC round GStar is the half-swap J of the final
ordinary Feistel G round, so the RFC ciphertext (in pair coordinates)
is C = J ∘ R ∘ H^3.

For EVERY eight independent 32-bit key words:
  R = J ∘ H^{-1} ∘ J,
  C = H^{-1} ∘ J ∘ H^3,
  H ∘ C ∘ H^{-1} = J ∘ H^2.

The last equation is a PERMUTATION CONJUGACY, not an XOR-DDT equality
in the original plaintext coordinates.

In the pulled-back difference geometry delta_H(x,x') =
H(x) XOR H(x'), the 32-round DDT equals the *ordinary XOR*
DDT of the 16-round map J ∘ H^2, with exact integer counts.
No 2^64 enumeration and no cryptanalytic independence assumption.
-/

namespace Magma.DiffanFullScheduleConjugacy

open Magma Magma.Internal Magma.MultiRoundDDT
abbrev W := V 32
abbrev S := FeistelState

def J (p : S) : S := Prod.swap p

/-- The forward 8-round block indexed 0..7. -/
def H (k : Fin 8 → W) (p : S) : S :=
  G (k 7) (G (k 6) (G (k 5) (G (k 4)
    (G (k 3) (G (k 2) (G (k 1) (G (k 0) p)))))))

/-- Reversed chronological KEY ORDER: 7,..,0. -/
def R (k : Fin 8 → W) (p : S) : S :=
  G (k 0) (G (k 1) (G (k 2) (G (k 3)
    (G (k 4) (G (k 5) (G (k 6) (G (k 7) p)))))))

def HE (k : Fin 8 → W) : S ≃ S :=
  ((((((((GEquiv (k 0)).trans (GEquiv (k 1))).trans
    (GEquiv (k 2))).trans (GEquiv (k 3))).trans
    (GEquiv (k 4))).trans (GEquiv (k 5))).trans
    (GEquiv (k 6))).trans (GEquiv (k 7)))

theorem HE_apply (k : Fin 8 → W) (p : S) : HE k p = H k p := rfl

private theorem F_J_F (key : W) (p : S) :
    G key (J (G key p)) = J p := by
  rcases p with ⟨l,r⟩
  change (r, (g key r ^^^ (g key r ^^^ l))) = (r,l)
  rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

theorem R_J_H (k : Fin 8 → W) (p : S) :
    R k (J (H k p)) = J p := by
  unfold R H
  rw [F_J_F (k 7), F_J_F (k 6), F_J_F (k 5),
      F_J_F (k 4), F_J_F (k 3), F_J_F (k 2),
      F_J_F (k 1), F_J_F (k 0)]

theorem H_J_R (k : Fin 8 → W) (p : S) :
    H k (J (R k p)) = J p := by
  unfold R H
  rw [F_J_F (k 0), F_J_F (k 1), F_J_F (k 2),
      F_J_F (k 3), F_J_F (k 4), F_J_F (k 5),
      F_J_F (k 6), F_J_F (k 7)]

def E16 (k : Fin 8 → W) (p : S) : S := R k (H k p)
def Q16 (k : Fin 8 → W) (p : S) : S := J (E16 k p)

/-- The second 16-round palindrome Q16 is an involution. -/
theorem H_Q16 (k : Fin 8 → W) (p : S) :
    H k (Q16 k p) = J (H k p) := by
  exact H_J_R k (H k p)

theorem Q16_involutive (k : Fin 8 → W) (p : S) :
    Q16 k (Q16 k p) = p := by
  change J (R k (H k (Q16 k p))) = p
  rw [H_Q16, R_J_H]
  exact Prod.swap_swap p

/-- Sixteen palindromic rounds (with one final swap)
are conjugate to the elementary half-swap. -/
theorem Q16_eq_conjugated_swap (k : Fin 8 → W) :
    Q16 k = ((HE k).symm ∘ J ∘ HE k) := by
  funext p
  apply (HE k).injective
  calc
    HE k (Q16 k p) = J (H k p) := by
      rw [HE_apply]
      exact H_Q16 k p
    _ = J (HE k p) := by rw [HE_apply]
    _ = HE k (((HE k).symm ∘ J ∘ HE k) p) := by
      simp only [Function.comp_apply, (HE k).apply_symm_apply]

def E32ord (k : Fin 8 → W) (p : S) : S :=
  R k (H k (H k (H k p)))

/-- Ciphertext PAIR with the RFC final no-swap round included.
It is J ∘ 32 ordinary Feistel rounds, not E32ord alone. -/
def C (k : Fin 8 → W) (p : S) : S :=
  J (E32ord k p)

/-- RFC full encryption is a 16-round reflected macro
after two repeated 8-round blocks, without any independent
DDT multiplication. -/
theorem C_eq_Q16_after_H_squared (k : Fin 8 → W) (p : S) :
    C k p = Q16 k (H k (H k p)) := by
  rfl

/-- Stronger than a 16-round reflection: the entire RFC 32-round
permutation is H-conjugate to J ∘ H^2. -/
theorem H_C (k : Fin 8 → W) (p : S) :
    H k (C k p) = J (H k (H k (H k p))) := by
  exact H_J_R k (H k (H k (H k p)))

/-- Exact ciphertext formula using ONE H inverse, ONE swap and H^3. -/
theorem C_eq_H_inverse_J_H_cubed (k : Fin 8 → W) (p : S) :
    C k p =
      (HE k).symm (J (H k (H k (H k p)))) := by
  apply (HE k).injective
  rw [HE_apply]
  exact (H_C k p).trans (by
    simp only [(HE k).apply_symm_apply])

/-- MAIN MACRO STRUCTURE: conjugating the full cipher with the
8-round H reduces it to 16 ordinary forward rounds followed
by a half-swap J. Permutation cycle structure is preserved. -/
theorem conjugate_full32_eq_swap_two_H (k : Fin 8 → W) (u : S) :
    HE k (C k ((HE k).symm u)) = J (H k (H k u)) := by
  rw [HE_apply, H_C]
  simp only [← HE_apply, (HE k).apply_symm_apply]

/-- The forward 8-block agrees with native ordinary Feistel iterate. -/
theorem iterate8_eq_H (k : Fin 8 → W) (p : S) :
    iterateG 8 k p = H k p := by
  rfl

/-- RFC master key words are inserted in their EXACT native order. -/
def master8 (K : V 256) : Fin 8 → W := baseRoundKey K

private theorem iterateG_split (n m : Nat)
    (keys : Fin (n + m) → W) (p : S) :
    iterateG (n+m) keys p =
      iterateG m (fun i => keys (i.natAdd n))
        (iterateG n (fun i => keys (i.castLE (Nat.le_add_right n m))) p) := by
  unfold iterateG
  exact Fin.foldl_add (fun s i => G (keys i) s) p

/-- The actual standard round sequence agrees with
3 repeated forward eight-round blocks and one reverse block.
This includes both first and last key and has 32 rounds. -/
theorem native_iterate32_eq_E32ord (K : V 256) (p : S) :
    iterateG 32 (roundKey K) p = E32ord (master8 K) p := by
  change iterateG (24+8) (roundKey K) p = E32ord (master8 K) p
  rw [iterateG_split 24 8]
  rw [iterateG_split 16 8]
  rw [iterateG_split 8 8]
  simp only [iterate8_eq_H]
  change
    H (fun i : Fin 8 => roundKey K ⟨24+i.val, by omega⟩)
      (H (fun i : Fin 8 => roundKey K ⟨16+i.val, by omega⟩)
        (H (fun i : Fin 8 => roundKey K ⟨8+i.val, by omega⟩)
          (H (fun i : Fin 8 => roundKey K ⟨i.val, by omega⟩) p))) =
    E32ord (master8 K) p
  have h0 : (fun i : Fin 8 => roundKey K ⟨i.val, by omega⟩) = master8 K := by
    funext i
    fin_cases i <;> rfl
  have h1 : (fun i : Fin 8 => roundKey K ⟨8+i.val, by omega⟩) = master8 K := by
    funext i
    fin_cases i <;> rfl
  have h2 : (fun i : Fin 8 => roundKey K ⟨16+i.val, by omega⟩) = master8 K := by
    funext i
    fin_cases i <;> rfl
  have h3 : (fun i : Fin 8 => roundKey K ⟨24+i.val, by omega⟩) =
      (fun i : Fin 8 => baseRoundKey K ⟨7-i.val, by omega⟩) := by
    funext i
    fin_cases i <;> rfl
  rw [h0, h1, h2, h3]
  change H (fun i : Fin 8 => (master8 K) ⟨7-i.val, by omega⟩)
      (H (master8 K) (H (master8 K) (H (master8 K) p))) =
    E32ord (master8 K) p
  have hrev : ∀ q : S,
      H (fun i : Fin 8 => (master8 K) ⟨7-i.val, by omega⟩) q =
        R (master8 K) q := by
    intro q
    rfl
  unfold E32ord
  exact hrev _

/-- Native RFC cipher output is the master-key macro C. The
last GStar is the swap of the full 32-round ordinary sequence. -/
theorem rfc_encrypt_pair_eq_C (K : V 256) (p : S) :
    split 32 32 (encrypt K (pack p)) = C (master8 K) p := by
  have hpack : split 32 32 (pack p) = p := by
    rcases p with ⟨l,r⟩
    exact concat_split ⟨32,l⟩ ⟨32,r⟩
  have henc := Magma.MultiRoundDDT.encrypt_as_iterG K (pack p)
  have hresult := congrArg (split 32 32) henc
  have hfinal : ∀ q : S, split 32 32 (pack q) = q := by
    intro q
    rcases q with ⟨l,r⟩
    exact concat_split ⟨32,l⟩ ⟨32,r⟩
  calc
    split 32 32 (encrypt K (pack p)) =
        split 32 32
          (pack (Prod.swap (iterateG 32 (roundKey K)
            (split 32 32 (pack p))))) := hresult
    _ = C (master8 K) p := by
      rw [hfinal, hpack, native_iterate32_eq_E32ord]
      rfl

/-- The eight-round key block HE conjugates the full RFC
cipher (including the last no-swap round) to exactly
T = J o H o H. The key schedule is the SAME across
all three occurrences of H in the 32-round expression. -/
theorem C_eq_conjugated_sixteen (k : Fin 8 → W) :
    C k = ((HE k).symm ∘
      (fun u : S => J (H k (H k u))) ∘ HE k) := by
  funext p
  calc
    C k p = (HE k).symm (J (H k (H k (H k p)))) :=
      C_eq_H_inverse_J_H_cubed k p
    _ = ((HE k).symm ∘
          (fun u : S => J (H k (H k u))) ∘ HE k) p := by
      simp only [Function.comp_apply, HE_apply]

/-- The actual RFC macro is the n=2 instance of the
cipher-independent reflected/repeated schedule law. -/
theorem C_eq_generic_schedule (k : Fin 8 → W) :
    C k = Diffan.ReflectedMacroSchedule.fullSchedule (HE k) J 2 := by
  funext p
  calc
    C k p = (HE k).symm (J (H k (H k (H k p)))) :=
      C_eq_H_inverse_J_H_cubed k p
    _ = Diffan.ReflectedMacroSchedule.shortConjugated (HE k) J 2 p := by
      change (HE k).symm (J (H k (H k (H k p)))) =
        (HE k).symm (J ((HE k) ((HE k) ((HE k) p))))
      simp only [HE_apply]
    _ = Diffan.ReflectedMacroSchedule.fullSchedule (HE k) J 2 p :=
      (Diffan.ReflectedMacroSchedule.fullSchedule_eq_short
        (HE k) J (by intro q; exact Prod.swap_swap q) 2 p).symm

def pairXor : Diffan.DifferenceSpace S S :=
  Diffan.DifferenceSpace.prod
    Magma.DiffanBridge.xor32 Magma.DiffanBridge.xor32

/-- Key-dependent nonlinear state difference:
d_H(x,y) := H(y) XOR H(x). This is NOT ordinary XOR on
the original plaintext/ciphertext halves. -/
def adaptedXor (k : Fin 8 → W) : Diffan.DifferenceSpace S S :=
  Diffan.ConjugatedDifferenceSpace.pullback (HE k) pairXor

/-- The entire reflected 16-round second half has a trivial
DDT only in the NONLINEAR KEY-DEPENDENT H geometry, not
in ordinary plaintext XOR differences. -/
theorem reflected16_ddt_in_H_geometry_is_half_swap
    (k : Fin 8 → W) (a b : S) :
    Diffan.ddt (adaptedXor k) (adaptedXor k) (Q16 k) a b =
      if J a = b then Fintype.card S else 0 := by
  rw [Q16_eq_conjugated_swap]
  calc
    Diffan.ddt (adaptedXor k) (adaptedXor k)
        ((HE k).symm ∘ J ∘ HE k) a b =
        Diffan.ddt pairXor pairXor J a b :=
      Diffan.ConjugatedDifferenceSpace.ddt_conjugate
        (HE k) pairXor J a b
    _ = if J a = b then Fintype.card S else 0 :=
      Magma.DiffanNineReflection.J_ddt_trivial a b

/-- Exact integer DDT REDUCTION: after an 8-round
KEY-DEPENDENT change in the DIFFERENCE CONVENTION, the
full 32-round cipher has the DDT of a 16-round H²
followed by the half-swap J. This is NOT an ordinary
XOR-DDT 32-to-16 shortcut. -/
theorem full32_ddt_in_adapted_geometry_eq_sixteen
    (k : Fin 8 → W) (a b : S) :
    Diffan.ddt (adaptedXor k) (adaptedXor k) (C k) a b =
      Diffan.ddt pairXor pairXor
        (fun u : S => J (H k (H k u))) a b := by
  rw [C_eq_conjugated_sixteen]
  exact Diffan.ConjugatedDifferenceSpace.ddt_conjugate
    (HE k) pairXor (fun u : S => J (H k (H k u))) a b

/-- The same result expressed directly using the actual RFC
encrypt API and the RFC master-key schedule, on pair states. -/
theorem rfc_full32_ddt_in_adapted_geometry_eq_sixteen
    (K : V 256) (a b : S) :
    Diffan.ddt (adaptedXor (master8 K))
        (adaptedXor (master8 K))
        (fun p : S => split 32 32 (encrypt K (pack p))) a b =
      Diffan.ddt pairXor pairXor
        (fun u : S => J (H (master8 K) (H (master8 K) u)))
        a b := by
  have h : (fun p : S => split 32 32 (encrypt K (pack p))) =
      C (master8 K) := by
    funext p
    exact rfc_encrypt_pair_eq_C K p
  rw [h]
  exact full32_ddt_in_adapted_geometry_eq_sixteen (master8 K) a b

/-- As a permutation invariant (not an XOR-DDT invariant),
C has the same fixed-point count as J o H², for ALL
eight 32-bit key words. -/
def full32_fixed_points_equiv (k : Fin 8 → W) :
    {p : S // C k p = p} ≃
    {u : S // J (H k (H k u)) = u} where
  toFun := fun p =>
    ⟨HE k p.1, by
      have h := congrArg (HE k) p.2
      change HE k (C k p.1) = HE k p.1 at h
      have hc := conjugate_full32_eq_swap_two_H k (HE k p.1)
      rw [(HE k).symm_apply_apply] at hc
      exact hc.symm.trans h⟩
  invFun := fun u =>
    ⟨(HE k).symm u.1, by
      apply (HE k).injective
      rw [HE_apply, H_C]
      have hc := u.2
      change J (H k (H k u.1)) = u.1 at hc
      simp only [← HE_apply, (HE k).apply_symm_apply]
      exact hc⟩
  left_inv := by
    intro p
    apply Subtype.ext
    exact (HE k).symm_apply_apply p.1
  right_inv := by
    intro u
    apply Subtype.ext
    exact (HE k).apply_symm_apply u.1

end Magma.DiffanFullScheduleConjugacy
