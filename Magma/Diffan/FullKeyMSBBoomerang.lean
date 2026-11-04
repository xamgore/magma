module
public import Magma.Diffan.FullKeyMSBGauge
public import Magma.Diffan.FullScheduleXorSymmetries
public import Diffan.BoomerangGauge
import all Init.Data.Range.Basic

@[expose] public section

/-!
# Exact ordinary-XOR BCT key equivalence of real RFC 8891 Magma

Every full 32-round Magma cipher with 256-bit master key K
has the EXACT SAME inverse-sensitive BCT as the distinct
master key K xor 0x80000000 in every one of its eight words.

This is proved without evaluating ANY 2^64 base table.
It uses true bijective RFC encrypt, a full symbolic
key-flip isometry, and generic BCT transport.
-/

namespace Magma.DiffanFullKeyMSBBoomerang

open Magma Magma.Internal Magma.MultiRoundDDT Magma.DiffanFullScheduleConjugacy
open Magma.DiffanFullScheduleXorSymmetries
open Magma.DiffanFullKeyMSBGauge

abbrev W := V 32
abbrev S := FeistelState

/-- A bijective genuine 32-round cipher from already certified
H/H/reflect geometry. The final RFC no-swap is included. -/
def CEquiv (keys : Fin 8 → W) : S ≃ S :=
  ((HE keys).trans (HE keys)).trans (Q16Equiv keys)

theorem CEquiv_apply (keys : Fin 8 → W) (p : S) :
    CEquiv keys p = C keys p := by
  rfl

/-- Inverse-sensitive BCT equality of whole Magma
for ALL 64-bit differences and all eight actual
32-bit key words. Not merely truncated DDT support. -/
theorem C_bct_master_key_gauge (keys : Fin 8 → W)
    (a b : S) :
    Diffan.BoomerangGauge.bct pairXor
      (CEquiv (keyFlip keys)) a b =
    Diffan.BoomerangGauge.bct pairXor
      (CEquiv keys) a b := by
  apply Diffan.BoomerangGauge.bct_intertwiner
    pairXor (CEquiv keys) (CEquiv (keyFlip keys)) TEquiv
  · intro p
    change C (keyFlip keys) (T p) = T (C keys p)
    exact C_gauge keys p
  · intro p c
    exact T_shift p c
  · intro p q
    exact T_diff p q

/-- Connect that BCT directly to the FULL RFC 256-bit
master-key packing and actual encrypt() API,
not a toy or a synthetic subkey family. -/
def nativeCEquiv (K : V 256) : S ≃ S :=
  CEquiv (master8 K)

theorem nativeCEquiv_encrypt (K : V 256) (p : S) :
    nativeCEquiv K p = split 32 32 (encrypt K (pack p)) := by
  change CEquiv (master8 K) p = split 32 32 (encrypt K (pack p))
  rw [CEquiv_apply]
  exact (rfc_encrypt_pair_eq_C K p).symm

theorem rfc_full32_bct_master_msb_invariant
    (K : V 256) (a b : S) :
    Diffan.BoomerangGauge.bct pairXor
      (nativeCEquiv (masterFlip K)) a b =
    Diffan.BoomerangGauge.bct pairXor
      (nativeCEquiv K) a b := by
  unfold nativeCEquiv
  rw [master8_flip]
  exact C_bct_master_key_gauge (master8 K) a b

end Magma.DiffanFullKeyMSBBoomerang
