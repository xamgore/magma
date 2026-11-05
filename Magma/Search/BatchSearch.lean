module

public import Magma.Search.FastSearch
import all Init.Data.Range.Basic

@[expose] public section

/-!
# Batch search for three-round impossible XOR differentials

For fixed `(k₀, k₁, aR, bL)`, initial domains and carry propagation are shared
across candidate left input differences `aL`. Search proposals and the fast
grouped prefilter are untrusted. An accepted shared base and an independently
accepted grouped witness imply zero three-round DDT for arbitrary `k₂` and `bR`.

`firstVerifiedAL` checks grouped witnesses only. Full cryptographic soundness
also requires `verifySearchBase`; the zero-DDT theorems require both checks.
Experiment inputs, measurements, and recorded outcomes are in
`Magma/DDT/Experiments/04_BatchCarryGroupedSearch.lean`.
-/

open Magma.Internal Magma.MultiRoundDDT Magma.Certificates
open Magma.Certificates.Encoding Magma.Certificates.BackwardMask
open Magma.Certificates.FastInitialCheck Magma.FastSearch

namespace Magma.BatchSearch

/-! ## Fixed base: expensive computations can be shared over many aL -/

structure SearchBase where
  k₀ : V 32
  k₁ : V 32
  aR : V 32
  bL : V 32

structure SearchBaseProposal where
  initial : UInt16BitDomains
  carry : CarryReductionCertificate

/-- Proposal only; all fields are subject to independent checking. -/
def proposeSearchBase (b : SearchBase) : SearchBaseProposal :=
  let D := fastInitialBitDomains b.k₀ b.k₁ b.aR b.bL
  { initial := D
    carry := proposeCarryReduction b.k₀ b.k₁ b.aR b.bL D }

/-- Expensive verification ONCE per base, not once per candidate aL. -/
def verifySearchBase (b : SearchBase) (p : SearchBaseProposal) : Bool :=
  verifyInitialCoverBySteps b.k₀ b.k₁ b.aR b.bL p.initial &&
    verifyCarryReduction b.k₀ b.k₁ b.aR b.bL p.initial p.carry

/-! ## Cheap grouped search, and separate verifier for each hit -/

/-- The fast proposal for the grouped output masks at aL. -/
def proposeWiring (aL : V 32) (p : SearchBaseProposal) : UInt16BitDomains :=
  fastGroupedUInt16 aL p.carry.next

/-- Cheap prefilter. It is intentionally NOT the trusted verifier. -/
def quickWiringContradiction (aL : V 32) (p : SearchBaseProposal) : Bool :=
  emptyUInt16BitDomain (proposeWiring aL p)

/-- Reuse the SAME carry proposal for a whole list of aL candidates. -/
def scanAL (p : SearchBaseProposal) (aLs : List (V 32)) : List (V 32) :=
  aLs.filter (fun aL => quickWiringContradiction aL p)

/-- For an individual candidate: verify grouped support and final emptiness
    against the original mathematical relations. -/
def verifySearchWiring
    (aL : V 32) (p : SearchBaseProposal) (next : UInt16BitDomains) : Bool :=
  verifyGroupedMaskCover aL p.carry.next next &&
    verifyEmptyMaskedDomain next

/-- Reusable correctness theorem: proof of the fixed base can be shared
    across arbitrarily many choices of aL. This makes NO assumption that the
    fast proposal is sound. -/
theorem xorDDT_rounds_three_zero_of_verifiedBatchHit
    (b : SearchBase) (p : SearchBaseProposal)
    (aL k₂ bR : V 32) (next : UInt16BitDomains)
    (hbase : verifySearchBase b p = true)
    (hwiring : verifySearchWiring aL p next = true) :
    xorDDT_rounds 3 (threeRoundKeys b.k₀ b.k₁ k₂)
      (aL, b.aR) (b.bL, bR) = 0 := by
  unfold verifySearchBase at hbase
  unfold verifySearchWiring at hwiring
  obtain ⟨hinit, hcarry⟩ := Bool.and_eq_true_iff.mp hbase
  obtain ⟨hgroup, hempty⟩ := Bool.and_eq_true_iff.mp hwiring
  have hchecked :
      verifyOneCarryThenGrouped
        b.k₀ b.k₁ aL b.aR b.bL p.initial p.carry next = true := by
    unfold verifyOneCarryThenGrouped
    exact Bool.and_eq_true_iff.mpr
      ⟨Bool.and_eq_true_iff.mpr ⟨hcarry, hgroup⟩, hempty⟩
  exact xorDDT_rounds_three_zero_of_checkedCarryGrouped_fastInit
    b.k₀ b.k₁ k₂ aL b.aR b.bL bR
    p.initial p.carry next hinit hchecked

/-! ## Optional selection of one independently verified hit -/

/-- Restrict this to the hits from `scanAL`, otherwise each unsuccessful
    candidate unnecessarily invokes the more expensive trusted verifier. -/
def firstVerifiedAL
    (p : SearchBaseProposal) (aLs : List (V 32)) : Option (V 32) :=
  aLs.find? (fun aL => verifySearchWiring aL p (proposeWiring aL p))

/-- A result from the verified selection is backed by the grouped checker.
    Full crypto soundness additionally needs the shared base check. -/
theorem firstVerifiedAL_sound
    (p : SearchBaseProposal) (aLs : List (V 32)) (aL : V 32)
    (h : firstVerifiedAL p aLs = some aL) :
    verifySearchWiring aL p (proposeWiring aL p) = true := by
  unfold firstVerifiedAL at h
  exact (List.find?_eq_some_iff_append.mp h).1

/-- Fully checked result, quantifying over arbitrary k2 and bR. -/
theorem xorDDT_rounds_three_zero_of_firstVerifiedAL
    (b : SearchBase) (p : SearchBaseProposal)
    (aLs : List (V 32)) (aL k₂ bR : V 32)
    (hbase : verifySearchBase b p = true)
    (hfound : firstVerifiedAL p aLs = some aL) :
    xorDDT_rounds 3 (threeRoundKeys b.k₀ b.k₁ k₂)
      (aL, b.aR) (b.bL, bR) = 0 := by
  exact xorDDT_rounds_three_zero_of_verifiedBatchHit
    b p aL k₂ bR (proposeWiring aL p) hbase
    (firstVerifiedAL_sound p aLs aL hfound)

/-- 32 independent one-bit differences; contains `1#32` as first member. -/
def oneBitDifferences32 : List (V 32) :=
  (List.range 32).map (fun i => BitVec.ofNat 32 (2 ^ i))

end Magma.BatchSearch
