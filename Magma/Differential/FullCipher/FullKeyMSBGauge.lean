module
public import Magma.Differential.FullCipher.FullScheduleConjugacy
import all Init.Data.Range.Basic

@[expose] public section

/-!
# Top-bit gauge of the actual 32-round RFC Magma permutation

Let h=0x80000000. For 32-bit modular addition,
  x XOR h = x + h,
and 2h=0 mod 2^32.

T(L,R)=(L XOR h,R XOR h) is a *global XOR translation*
of the 64-bit Feistel state. Toggle h in every one of
the 8 real round-key words, with ALL repeated/reversed
uses of the SAME key word toggled consistently.

The genuine round function obeys g(k XOR h,x XOR h)=g(k,x).
Thus every ordinary Feistel G, the complete RFC
32-round cipher and its final no-swap GStar are equivariant:

  C_flip(T(x)) = T(C(x)),

or C_flip=T o C o T. Unlike the nonlinear H-conjugacy,
T preserves UNMODIFIED XOR DIFFERENCES. Therefore the
full 32-round ordinary XOR-DDT is EXACTLY key-invariant
under the eight-word simultaneous flip.

This is an equality between TWO master-key classes, not
a new impossible differential or a computational attack.
-/

namespace Magma.DiffanFullKeyMSBGauge

open Magma Magma.Internal Magma.GProperties
open Magma.MultiRoundDDT Magma.DiffanFullScheduleConjugacy

abbrev W := V 32
abbrev S := FeistelState

def hi : W := 0x80000000#32
def T (p : S) : S :=
  (p.1 ^^^ hi,p.2 ^^^ hi)

def keyFlip (keys : Fin 8 → W) : Fin 8 → W :=
  fun i => (keys i) ^^^ hi

private theorem xor_hi_eq_add_hi (x : W) :
    x ^^^ hi = x + hi := by
  unfold hi
  bv_decide

private theorem hi_double_zero : (hi + hi : W) = 0#32 := by
  decide

/-- Exact classification of ALL constant 32-bit masks e for
which x XOR e = x+e (mod 2^32) for EVERY base word x.

Only e=0 and e=0x80000000 work. The forward direction
uses the very short test x=e, forcing 2e=0 mod 2^32.
This classifies the ENTIRE natural XOR/add common-translation
subgroup; it is NOT a claim that no different S-box-specific
cross-key symmetries could exist. -/
theorem xor_translation_equals_add_for_all_iff (e : W) :
    (∀ x : W, x ^^^ e = x + e) ↔
      e = 0#32 ∨ e = hi := by
  constructor
  · intro he
    have hzero : e + e = 0#32 := by
      have h := he e
      simpa only [BitVec.xor_self] using h.symm
    have hnat : (e.toNat + e.toNat) % (2^32) = 0 := by
      have hz := congrArg BitVec.toNat hzero
      simpa [BitVec.toNat_add] using hz
    have hbound : e.toNat < (2^32) := e.toFin.isLt
    have hp : (2:Nat)^32 = 4294967296 := by decide
    rw [hp] at hnat hbound
    have hcases : e.toNat = 0 ∨ e.toNat = 2147483648 := by
      omega
    rcases hcases with h0 | hhi
    · left
      apply BitVec.eq_of_toNat_eq
      exact h0
    · right
      apply BitVec.eq_of_toNat_eq
      change e.toNat = 2147483648
      exact hhi
  · rintro (rfl | rfl) x
    · simp only [BitVec.xor_zero, BitVec.add_zero]
    · exact xor_hi_eq_add_hi x

/-- XOR and modular addition by the top bit are identical.
Two simultaneous shifts cancel in the round-function input. -/
theorem double_hi_add_cancel (k x : W) :
    (k ^^^ hi) + (x ^^^ hi) = k + x := by
  rw [xor_hi_eq_add_hi, xor_hi_eq_add_hi]
  calc
    (k+hi)+(x+hi) = (k+x)+(hi+hi) := by ac_rfl
    _ = k+x := by rw [hi_double_zero, BitVec.add_zero]

private theorem modShift_eq_add (k x : W) :
    modShift k x = x + k := by
  apply BitVec.eq_of_toNat_eq
  rw [Magma.CarryAutomaton.modShift_toNat_bridge, BitVec.toNat_add]
  congr 1

/-- The actual RFC modular-add/S-box/ROL11 g function,
at a fully symbolic 32-bit base and key. No toy model. -/
theorem g_hi_key_base_invariant (k x : W) :
    g (k ^^^ hi) (x ^^^ hi) = g k x := by
  simp only [g_as_modShift, modShift_eq_add]
  rw [BitVec.add_comm (x ^^^ hi) (k ^^^ hi),
      double_hi_add_cancel, BitVec.add_comm k x]

theorem T_involutive (p : S) : T (T p) = p := by
  rcases p with ⟨l,r⟩
  apply Prod.ext
  · change (l ^^^ hi) ^^^ hi = l
    rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
  · change (r ^^^ hi) ^^^ hi = r
    rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

theorem T_J_commute (p : S) :
    T (J p) = J (T p) := by
  rfl

/-- The SAME top-bit offset is applied to the left and right
base words and to the real 32-bit key, preserving g exactly. -/
theorem G_gauge (k : W) (p : S) :
    G (k ^^^ hi) (T p) = T (G k p) := by
  rcases p with ⟨l,r⟩
  apply Prod.ext
  · rfl
  · change g (k ^^^ hi) (r ^^^ hi) ^^^ (l ^^^ hi) =
      (g k r ^^^ l) ^^^ hi
    rw [g_hi_key_base_invariant]
    rw [BitVec.xor_assoc]

/-- A real eight-round H block is equivariant with a
single consistent flip of all eight key words. -/
theorem H_gauge (keys : Fin 8 → W) (p : S) :
    H (keyFlip keys) (T p) = T (H keys p) := by
  unfold H keyFlip
  rw [G_gauge (keys 0) p,
      G_gauge (keys 1) (G (keys 0) p),
      G_gauge (keys 2) (G (keys 1) (G (keys 0) p)),
      G_gauge (keys 3) (G (keys 2) (G (keys 1) (G (keys 0) p))),
      G_gauge (keys 4) (G (keys 3) (G (keys 2) (G (keys 1) (G (keys 0) p)))),
      G_gauge (keys 5) (G (keys 4) (G (keys 3) (G (keys 2) (G (keys 1) (G (keys 0) p))))),
      G_gauge (keys 6) (G (keys 5) (G (keys 4) (G (keys 3) (G (keys 2) (G (keys 1) (G (keys 0) p)))))),
      G_gauge (keys 7) (G (keys 6) (G (keys 5) (G (keys 4) (G (keys 3) (G (keys 2) (G (keys 1) (G (keys 0) p)))))))]

/-- Also the reversed-key H block, needed by the RFC final eight rounds. -/
theorem R_gauge (keys : Fin 8 → W) (p : S) :
    R (keyFlip keys) (T p) = T (R keys p) := by
  unfold R keyFlip
  rw [G_gauge (keys 7) p,
      G_gauge (keys 6) (G (keys 7) p),
      G_gauge (keys 5) (G (keys 6) (G (keys 7) p)),
      G_gauge (keys 4) (G (keys 5) (G (keys 6) (G (keys 7) p))),
      G_gauge (keys 3) (G (keys 4) (G (keys 5) (G (keys 6) (G (keys 7) p)))),
      G_gauge (keys 2) (G (keys 3) (G (keys 4) (G (keys 5) (G (keys 6) (G (keys 7) p))))),
      G_gauge (keys 1) (G (keys 2) (G (keys 3) (G (keys 4) (G (keys 5) (G (keys 6) (G (keys 7) p)))))),
      G_gauge (keys 0) (G (keys 1) (G (keys 2) (G (keys 3) (G (keys 4) (G (keys 5) (G (keys 6) (G (keys 7) p)))))))]

/-- Actual full 32 rounds, with RFC's last no-swap round. -/
theorem C_gauge (keys : Fin 8 → W) (p : S) :
    C (keyFlip keys) (T p) = T (C keys p) := by
  unfold C E32ord
  rw [H_gauge keys p,
      H_gauge keys (H keys p),
      H_gauge keys (H keys (H keys p)),
      R_gauge keys (H keys (H keys (H keys p)))]
  exact (T_J_commute _).symm

/-- The same input/output XOR-mask can be applied before
or after the uniform state-translation T. -/
theorem T_shift (p a : S) :
    pairXor.shift (T p) a = T (pairXor.shift p a) := by
  rcases p with ⟨l,r⟩
  rcases a with ⟨al,ar⟩
  apply Prod.ext
  · change (l ^^^ hi) ^^^ al = (l ^^^ al) ^^^ hi
    ac_rfl
  · change (r ^^^ hi) ^^^ ar = (r ^^^ ar) ^^^ hi
    ac_rfl

/-- A common XOR-translation of both inputs leaves their
XOR difference EXACTLY unchanged. -/
theorem T_diff (p q : S) :
    pairXor.diff (T p) (T q) = pairXor.diff p q := by
  rcases p with ⟨l,r⟩
  rcases q with ⟨m,s⟩
  apply Prod.ext
  · change (l ^^^ hi) ^^^ (m ^^^ hi) = l ^^^ m
    calc
      (l ^^^ hi) ^^^ (m ^^^ hi) = (l ^^^ m) ^^^ (hi ^^^ hi) := by ac_rfl
      _ = l ^^^ m := by rw [BitVec.xor_self, BitVec.xor_zero]
  · change (r ^^^ hi) ^^^ (s ^^^ hi) = r ^^^ s
    calc
      (r ^^^ hi) ^^^ (s ^^^ hi) = (r ^^^ s) ^^^ (hi ^^^ hi) := by ac_rfl
      _ = r ^^^ s := by rw [BitVec.xor_self, BitVec.xor_zero]

def TEquiv : S ≃ S where
  toFun := T
  invFun := T
  left_inv := T_involutive
  right_inv := T_involutive

/-- A complete 32-round key-flip change of variables
preserves the actual XOR derivative POINTWISE, if we
translate the input base with T. No DDT averaging here. -/
theorem C_derivative_keyFlip (keys : Fin 8 → W)
    (a p : S) :
    Diffan.derivative pairXor pairXor
      (C (keyFlip keys)) a (T p) =
    Diffan.derivative pairXor pairXor (C keys) a p := by
  unfold Diffan.derivative
  rw [T_shift, C_gauge keys (pairXor.shift p a), C_gauge keys p]
  exact T_diff _ _

/-- MAIN standard XOR full-32 DDT key-equivalence theorem:

Toggle the MOST SIGNIFICANT bit of each of the 8 different
actual RFC 32-bit subkeys. The original 64-bit XOR-DDT
is then EXACTLY unchanged at ALL input and output differences,
for ALL key words. Neither endpoint difference is transformed.

The proof is an exact bijection of base-state fibers,
NOT a scalar DDT approximation or an exhaustive count. -/
theorem C_xorDDT_invariant_under_all_key_msb_flip
    (keys : Fin 8 → W) (a b : S) :
    Diffan.ddt pairXor pairXor (C (keyFlip keys)) a b =
      Diffan.ddt pairXor pairXor (C keys) a b := by
  classical
  unfold Diffan.ddt
  apply Finset.card_equiv TEquiv
  intro p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have h := C_derivative_keyFlip keys a (T p)
  rw [T_involutive] at h
  rw [h]
  rfl

/-- Toggle the most significant bit in EACH of the eight
RFC 32-bit key words, in the genuine packed 256-bit master key. -/
def masterHiMask : V 256 :=
  0x8000000080000000800000008000000080000000800000008000000080000000#256

def masterFlip (K : V 256) : V 256 :=
  K ^^^ masterHiMask

/-- This is exactly the same key transformation as keyFlip
on the eight real RFC baseRoundKey words. The 256-bit
substring/XOR identity is proved SYMBOLICALLY, not sampled. -/
theorem master8_flip (K : V 256) :
    master8 (masterFlip K) = keyFlip (master8 K) := by
  funext i
  change (K ^^^ masterHiMask).extractLsb' (32*(7-i.val)) 32 =
    K.extractLsb' (32*(7-i.val)) 32 ^^^ hi
  rw [BitVec.extractLsb'_xor]
  have hm : masterHiMask.extractLsb' (32*(7-i.val)) 32 = hi := by
    fin_cases i <;> decide
  rw [hm]

/-- The 256-bit key transformation is an involution. -/
theorem masterFlip_involutive (K : V 256) :
    masterFlip (masterFlip K) = K := by
  unfold masterFlip
  rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

/-- Its orbits contain TWO distinct genuine master keys,
not just two different representations of the same 256-bit
word. No claim about OTHER possible key equivalences. -/
theorem masterFlip_not_self (K : V 256) :
    masterFlip K ≠ K := by
  intro he
  have hz : masterHiMask = 0#256 :=
    (BitVec.xor_right_inj K).mp (by
      simpa only [masterFlip, BitVec.xor_zero] using he)
  exact (by decide : masterHiMask ≠ 0#256) hz

/-- ACTUAL RFC encrypt API (not just a reconstructed
Feistel block). The resulting ciphertext is translated by
the same known XOR constant T after the master-key flip
and the matching input plaintext translation. -/
theorem rfc_encrypt_pair_msb_gauge (K : V 256) (p : S) :
    split 32 32 (encrypt (masterFlip K) (pack (T p))) =
      T (split 32 32 (encrypt K (pack p))) := by
  rw [rfc_encrypt_pair_eq_C, rfc_encrypt_pair_eq_C, master8_flip]
  exact C_gauge (master8 K) p

/-- Exact ordinary XOR-DDT key equivalence for the NATIVE
RFC 256-bit encrypt function, at ALL 64-bit differences.
No key-dependent geometry and no full-base enumeration. -/
theorem rfc_full32_xorDDT_master_msb_invariant
    (K : V 256) (a b : S) :
    Diffan.ddt pairXor pairXor
      (fun p : S => split 32 32 (encrypt (masterFlip K) (pack p)))
        a b =
    Diffan.ddt pairXor pairXor
      (fun p : S => split 32 32 (encrypt K (pack p)))
        a b := by
  have h1 :
      (fun p : S => split 32 32 (encrypt (masterFlip K) (pack p))) =
        C (master8 (masterFlip K)) := by
    funext p
    exact rfc_encrypt_pair_eq_C (masterFlip K) p
  have h2 :
      (fun p : S => split 32 32 (encrypt K (pack p))) =
        C (master8 K) := by
    funext p
    exact rfc_encrypt_pair_eq_C K p
  rw [h1,h2,master8_flip]
  exact C_xorDDT_invariant_under_all_key_msb_flip (master8 K) a b

/-- Exact Int-weighted correlation transport between TWO
true 32-round key settings, for ANY fixed observables.
LAT sign rules arise by specializing to Walsh characters;
nothing assumes any S-box independence. -/
theorem C_observable_correlation_key_flip (keys : Fin 8 → W)
    (phi psi : S → Int) :
    (∑ p : S, phi p * psi (C (keyFlip keys) p)) =
      ∑ p : S, phi (T p) * psi (T (C keys p)) := by
  classical
  calc
    (∑ p : S, phi p * psi (C (keyFlip keys) p)) =
        ∑ p : S, phi (T p) * psi (C (keyFlip keys) (T p)) := by
      exact (Equiv.sum_comp TEquiv
        (fun p : S => phi p * psi (C (keyFlip keys) p))).symm
    _ = ∑ p : S, phi (T p) * psi (T (C keys p)) := by
      simp only [C_gauge]

/-- Generic exact LAT/sign-transport schema: if two Int
observables are eigenfunctions of the uniform XOR
translation T, their full-cipher correlation changes by
the PRODUCT of their translation eigenvalues.

For ordinary Walsh characters, eigenvalues are (-1)
raised to the dot product of each linear mask with
t=0x8000000080000000. Thus the full standard LAT
can change in SIGN, but not ABSOLUTE VALUE, across
the two master-key settings. -/
theorem C_observable_eigen_sign_rule (keys : Fin 8 → W)
    (phi psi : S → Int) (σ τ : Int)
    (hphi : ∀ p, phi (T p) = σ * phi p)
    (hpsi : ∀ p, psi (T p) = τ * psi p) :
    (∑ p : S, phi p * psi (C (keyFlip keys) p)) =
      (σ*τ) * (∑ p : S, phi p * psi (C keys p)) := by
  rw [C_observable_correlation_key_flip]
  calc
    (∑ p : S, phi (T p) * psi (T (C keys p))) =
        ∑ p : S, (σ*phi p) * (τ*psi (C keys p)) := by
      simp only [hphi, hpsi]
    _ = (σ*τ) * ∑ p : S, phi p * psi (C keys p) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      ring

end Magma.DiffanFullKeyMSBGauge
