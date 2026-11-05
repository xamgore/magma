module
public import Magma.Differential.FullCipher.FullKeyMSBGauge
public import Magma.Differential.FullCipher.PalindromicOracle
public import Diffan.Observables.OracleObservableBarrier
import all Init.Data.Range.Basic

@[expose] public section

/-!
# A REAL, strictly related-key two-query full-32 distinguisher

Threat model: an adversary obtains two encryption oracles
at UNKNOWN but RELATED master keys K and K' = K xor
0x80000000 in EVERY one of the eight 32-bit key words.
The adversary chooses ONE plaintext x for the K oracle
and ONE plaintext T(x) for the K' oracle.

For actual RFC Magma the publicly checkable condition

    E_K'(T x) = T(E_K(x))

holds for EVERY K,x.

For TWO independent ideal 64-bit random permutations
associated with unrelated ideal keys, conditional on
the first output, the second output is uniform among
2^64 states: exactly ONE passes. Hence the false-positive
probability is 2^-64 with only TWO chosen-input calls.

This is a related-key DISTINGUISHER, not a single-key
distinguisher, not a key-recovery attack and not
a break of standard chosen-plaintext Magma encryption.
-/

namespace Magma.DiffanRelatedKeyOracle
open Magma Magma.Internal Magma.MultiRoundDDT
open Magma.DiffanFullKeyMSBGauge

private abbrev S := FeistelState

/-- A PUBLICLY verifiable relation on TWO outputs,
without any access to internal states or to the secret key. -/
def passesTwoQueries (f g : S → S) (x : S) : Prop :=
  g (T x) = T (f x)

/-- ALL actual RFC master keys satisfy this relation for
the two related encryption oracles. This is NOT a
claim about the single unknown-key oracle alone. -/
theorem full_rfc_related_key_two_query_distinguisher
    (K : V 256) (x : S) :
    passesTwoQueries
      (fun p => split 32 32 (encrypt K (pack p)))
      (fun p => split 32 32 (encrypt (masterFlip K) (pack p)))
      x := by
  exact rfc_encrypt_pair_msb_gauge K x

/-- For a FIXED first output y, exactly ONE possible
second output among the entire 64-bit alphabet makes
the publicly checked relation pass. -/
theorem ideal_independent_second_output_one_matching_value
    (y : S) :
    ((Finset.univ : Finset S).filter
      (fun z => z = T y)).card = 1 := by
  classical
  have hs : (Finset.univ : Finset S).filter
      (fun z => z = T y) = {T y} := by
    ext z
    simp
  rw [hs, Finset.card_singleton]

/-- The second ideal permutation's output alphabet has
2^64 elements. For independent uniformly random keyed
ideal permutations, the one-query conditional pass
probability is thus precisely 2^-64. -/
theorem ideal_output_alphabet_card :
    Fintype.card S = 2 ^ 64 :=
  Magma.DiffanPalindromicOracle.all_64bit_states_count

end Magma.DiffanRelatedKeyOracle
