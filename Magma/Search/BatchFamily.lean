module

public import Magma.Search.BatchSearch
import all Init.Data.Range.Basic

@[expose] public section

/-!
# Certificates for families of three-round impossible XOR differentials

`BatchCertificate` shares one independently checked initial/carry base across
its target differences. Every target's grouped witness is checked separately.
Acceptance establishes zero three-round DDT for every member, for arbitrary
third keys and right output differences.

The two-bit candidate generator and fast prefilter do not assert impossibility.
`independentlyVerifiedHits` checks each retained grouped witness; its soundness
theorem additionally requires acceptance of the shared base.
Concrete one-bit family proofs and exploratory two-bit runs are recorded in
`Magma/Evidence/05_BatchFamilyCertificates.lean`.
-/

open Magma.Internal Magma.MultiRoundDDT Magma.BatchSearch

namespace Magma.BatchFamily

/-! ### 1. One checked base, multiple checked grouped witnesses -/

/-- Check grouped wiring and emptiness independently for EVERY target
    in a list. This does not repeat the shared carry-base verification. -/
def verifyBatchGroupedOnly
    (p : SearchBaseProposal) (targets : List (V 32)) : Bool :=
  targets.all fun aL =>
    verifySearchWiring aL p (proposeWiring aL p)

/-- Self-contained batch certificate. The same shared proposal is reused
    for each requested `aL`; each proposed grouped result is rechecked. -/
structure BatchCertificate where
  base : SearchBase
  proposal : SearchBaseProposal
  targets : List (V 32)

/-- Independent checker for an entire batch: one initial/carry check,
    followed by individual grouped/empty-domain checks. -/
def verifyBatchCertificate (cert : BatchCertificate) : Bool :=
  verifySearchBase cert.base cert.proposal &&
    verifyBatchGroupedOnly cert.proposal cert.targets

/-- Every member of a checked batch has zero three-round XOR-DDT,
    independently of the third round key and right output difference. -/
theorem xorDDT_rounds_three_zero_of_verifiedBatchCertificate
    (cert : BatchCertificate) (aL k₂ bR : V 32)
    (hverified : verifyBatchCertificate cert = true)
    (hmember : aL ∈ cert.targets) :
    xorDDT_rounds 3
      (threeRoundKeys cert.base.k₀ cert.base.k₁ k₂)
      (aL, cert.base.aR) (cert.base.bL, bR) = 0 := by
  unfold verifyBatchCertificate at hverified
  obtain ⟨hbase, hgroup⟩ := Bool.and_eq_true_iff.mp hverified
  unfold verifyBatchGroupedOnly at hgroup
  have hwiring :
      verifySearchWiring aL cert.proposal
        (proposeWiring aL cert.proposal) = true :=
    (List.all_eq_true.mp hgroup) aL hmember
  exact xorDDT_rounds_three_zero_of_verifiedBatchHit
    cert.base cert.proposal aL k₂ bR
    (proposeWiring aL cert.proposal) hbase hwiring

/-! ### 3. Larger exploratory search: the 496 two-bit differences -/

/-- All distinct two-bit masks, indexed by `0 ≤ i < j < 32`.
    This is an UNTRUSTED candidate list, not a cryptographic assertion. -/
def twoBitDifferences32 : List (V 32) :=
  (List.range 32).flatMap fun i =>
    ((List.range 32).filter (fun j => decide (i < j))).map fun j =>
      BitVec.ofNat 32 (2 ^ i + 2 ^ j)

/-- 32 one-bit candidates plus 496 two-bit candidates. -/
def atMostTwoBitDifferences32 : List (V 32) :=
  oneBitDifferences32 ++ twoBitDifferences32

/-- Keep only hits that satisfy BOTH the fast prefilter and the
    independent grouped verifier. The shared base is checked separately. -/
def independentlyVerifiedHits
    (p : SearchBaseProposal) (candidates : List (V 32)) :
    List (V 32) :=
  (scanAL p candidates).filter fun aL =>
    verifySearchWiring aL p (proposeWiring aL p)

private theorem independentlyVerifiedHits_sound (p : SearchBaseProposal) (candidates : List (V 32))
    (aL : V 32) (h : aL ∈ independentlyVerifiedHits p candidates) :
    verifySearchWiring aL p (proposeWiring aL p) = true := by
  unfold independentlyVerifiedHits at h
  exact (List.mem_filter.mp h).2

/-- A verified hit from a large scan is a genuine three-round impossible
    differential, provided the SHARED carry base passed its verifier. -/
theorem xorDDT_rounds_three_zero_of_independentlyVerifiedHit
    (b : SearchBase) (p : SearchBaseProposal)
    (candidates : List (V 32))
    (aL k₂ bR : V 32)
    (hbase : verifySearchBase b p = true)
    (hmem : aL ∈ independentlyVerifiedHits p candidates) :
    xorDDT_rounds 3 (threeRoundKeys b.k₀ b.k₁ k₂)
      (aL, b.aR) (b.bL, bR) = 0 := by
  exact xorDDT_rounds_three_zero_of_verifiedBatchHit
    b p aL k₂ bR (proposeWiring aL p) hbase
    (independentlyVerifiedHits_sound p candidates aL hmem)

end Magma.BatchFamily
