module

public import Magma.Certificates
import all Init.Data.Range.Basic

@[expose] public section

/-!
# Certificate search and fast domain propagation

Candidate generation and UInt16/UInt8 implementations. Search proposes witnesses;
the imported certificate checkers validate accepted results. Research comparisons,
measurements, and experimental runs are recorded in `Magma.Evidence`.
-/

open Magma.Internal Magma.CarryAutomaton Magma.MultiRoundDDT Magma.Pruning Magma.Certificates
open Magma.Certificates.Encoding Magma.Certificates.BackwardMask

namespace Magma.FastSearch

-- certificate generator of impossible 3round differentials

/-- Enumerate all possible single-value deletions and all four candidate
    bit witnesses, in a deterministic order. There are 2*8*16*4 = 1024
    entries; a candidate is only a PROPOSAL until it passes the verifier. -/
def allBitDeletionProposals : List BitDeletion :=
  (List.finRange 8).flatMap (fun digit =>
    (List.finRange 16).flatMap (fun value =>
      (List.finRange 4).flatMap (fun bit =>
        [ { side := .output, digit := digit, value := value, bit := bit },
          { side := .intermediate, digit := digit, value := value, bit := bit } ])))

/-- Find the first locally justified deletion from a list of proposals.
    This is an ordinary executable search, not a proof by itself. -/
def firstVerifiedBitDeletion (aL : V 32) (D : BitPruningDomains) :
    List BitDeletion → Option BitDeletion
  | [] => none
  | d :: rest =>
      if verifyBitDeletion aL D d = true then some d
      else firstVerifiedBitDeletion aL D rest

/-- Propose the next single-value deletion, using exactly the existing
    certified local-support condition (the full set of 1024 proposals). -/
def nextVerifiedBitDeletion (aL : V 32)
    (D : BitPruningDomains) : Option BitDeletion :=
  firstVerifiedBitDeletion aL D allBitDeletionProposals

/-- Build a compact deletion log. `fuel` bounds the number of deletions.
    Each proposed deletion is checked against the *updated* domains.
    A stopped or exhausted search need not have found a contradiction. -/
def buildBitDeletionLog (aL : V 32) (D : BitPruningDomains) :
    Nat → List BitDeletion
  | 0 => []
  | fuel + 1 =>
      if verifyEmptyBitPruningDomain D = true then []
      else
        match nextVerifiedBitDeletion aL D with
        | none => []
        | some d =>
            d :: buildBitDeletionLog aL (applyBitDeletion D d) fuel

/-- Turn a computed log into a *proposed* certificate.
    The initial domains are calculated from the actual parameters. -/
def proposeBitDeletionCertificate
    (k₀ k₁ aL aR bL : V 32) (fuel : Nat := 256) :
    BitDeletionCertificate :=
  { deletions := buildBitDeletionLog aL
      (initialBitDomains k₀ k₁ aR bL) fuel }

/-- Accept a proposal only if the existing, proved checker returns true.
    This is the small trust boundary between search and verification. -/
def checkProposedBitDeletionCertificate
    (k₀ k₁ aL aR bL : V 32)
    (candidate : BitDeletionCertificate) :
    Option BitDeletionCertificate :=
  if verifyBitDeletionCertificate k₀ k₁ aL aR bL candidate = true
  then some candidate
  else none

/-- The checker cannot return a certificate without verifying it.
    Crucially, the proof never unfolds the expensive bit-domain computation. -/
theorem checkProposedBitDeletionCertificate_verified
    (k₀ k₁ aL aR bL : V 32)
    (candidate result : BitDeletionCertificate)
    (h : checkProposedBitDeletionCertificate
      k₀ k₁ aL aR bL candidate = some result) :
    verifyBitDeletionCertificate k₀ k₁ aL aR bL result = true := by
  by_cases hc :
      verifyBitDeletionCertificate k₀ k₁ aL aR bL candidate = true
  · have heq : some candidate = some result := by
      simpa only [checkProposedBitDeletionCertificate, ite_eq_left hc] using h
    have hres : candidate = result := Option.some.inj heq
    subst result
    exact hc
  · have hcontra : (none : Option BitDeletionCertificate) = some result := by
      simpa only [checkProposedBitDeletionCertificate, ite_eq_right hc] using h
    cases hcontra

/-- Generate a compact certificate only when there is an actual checked
    contradiction. `none` means ONLY that this relaxation/search failed,
    never that the differential is possible. -/
def generateBitDeletionCertificate
    (k₀ k₁ aL aR bL : V 32) (fuel : Nat := 256) :
    Option BitDeletionCertificate :=
  checkProposedBitDeletionCertificate k₀ k₁ aL aR bL
    (proposeBitDeletionCertificate k₀ k₁ aL aR bL fuel)

/-- Generated certificates inherit the soundness of the checker,
    independently of the generator's heuristic or the fuel parameter. -/
theorem generatedBitDeletionCertificate_verified
    (k₀ k₁ aL aR bL : V 32) (fuel : Nat)
    (cert : BitDeletionCertificate)
    (hgen : generateBitDeletionCertificate
      k₀ k₁ aL aR bL fuel = some cert) :
    verifyBitDeletionCertificate k₀ k₁ aL aR bL cert = true := by
  exact checkProposedBitDeletionCertificate_verified
    k₀ k₁ aL aR bL
    (proposeBitDeletionCertificate k₀ k₁ aL aR bL fuel)
    cert hgen

/-- End-to-end certified result. Neither `k₂` nor `bR` participates in
    this sufficient impossibility condition, exactly as in the existing
    three-round DDT theorem. -/
theorem xorDDT_rounds_three_zero_of_generatedBitDeletionCertificate
    (k₀ k₁ k₂ aL aR bL bR : V 32)
    (fuel : Nat) (cert : BitDeletionCertificate)
    (hgen : generateBitDeletionCertificate
      k₀ k₁ aL aR bL fuel = some cert) :
    xorDDT_rounds 3
      (threeRoundKeys k₀ k₁ k₂)
      (aL, aR) (bL, bR) = 0 := by
  exact xorDDT_rounds_three_zero_of_verifiedBitDeletionCertificate
    k₀ k₁ k₂ aL aR bL bR cert
    (generatedBitDeletionCertificate_verified
      k₀ k₁ aL aR bL fuel cert hgen)

/-- Scan a user-provided list of candidate triples `(aL,aR,bL)`.
    Search is kept outside the trusted proof. It returns the first
    pair `(candidate, certificate)` accepted by the checker. -/
def scanThreeRoundBitDeletionCandidates
    (k₀ k₁ : V 32) (fuel : Nat) :
    List (V 32 × V 32 × V 32) →
    Option ((V 32 × V 32 × V 32) × BitDeletionCertificate)
  | [] => none
  | (aL, aR, bL) :: rest =>
      match generateBitDeletionCertificate k₀ k₁ aL aR bL fuel with
      | some cert => some ((aL, aR, bL), cert)
      | none => scanThreeRoundBitDeletionCandidates k₀ k₁ fuel rest

/-- A successful scan also provides a certificate validated by the checker.
    The proof does not depend on which input candidate the scan selected. -/
theorem scannedThreeRoundBitDeletionCandidates_verified
    (k₀ k₁ : V 32) (fuel : Nat) :
    ∀ (candidates : List (V 32 × V 32 × V 32))
      (result : (V 32 × V 32 × V 32) × BitDeletionCertificate),
      scanThreeRoundBitDeletionCandidates k₀ k₁ fuel candidates =
        some result →
      verifyBitDeletionCertificate k₀ k₁
        result.1.1 result.1.2.1 result.1.2.2 result.2 = true := by
  intro candidates
  induction candidates with
  | nil =>
      intro result h
      cases h
  | cons triple rest ih =>
      rcases triple with ⟨cl, cr, cb⟩
      intro result h
      cases hgen : generateBitDeletionCertificate k₀ k₁ cl cr cb fuel with
      | none =>
          apply ih result
          simpa only [scanThreeRoundBitDeletionCandidates, hgen] using h
      | some foundCert =>
          have heq : some ((cl, cr, cb), foundCert) = some result := by
            simpa only [scanThreeRoundBitDeletionCandidates, hgen] using h
          have hr : result = ((cl, cr, cb), foundCert) :=
            (Option.some.inj heq).symm
          subst result
          exact generatedBitDeletionCertificate_verified
            k₀ k₁ cl cr cb fuel foundCert hgen

/-- An externally chosen candidate list can be scanned without trusting
    the search result: its checked certificate proves a three-round zero. -/
theorem xorDDT_rounds_three_zero_of_scannedBitDeletionCandidates
    (k₀ k₁ k₂ aL aR bL bR : V 32) (fuel : Nat)
    (candidates : List (V 32 × V 32 × V 32))
    (cert : BitDeletionCertificate)
    (hscan : scanThreeRoundBitDeletionCandidates k₀ k₁ fuel candidates =
      some ((aL, aR, bL), cert)) :
    xorDDT_rounds 3
      (threeRoundKeys k₀ k₁ k₂)
      (aL, aR) (bL, bR) = 0 := by
  exact xorDDT_rounds_three_zero_of_verifiedBitDeletionCertificate
    k₀ k₁ k₂ aL aR bL bR cert
    (scannedThreeRoundBitDeletionCandidates_verified
      k₀ k₁ fuel candidates ((aL, aR, bL), cert) hscan)

/-! ## 1. Batched deletion search (same trusted checker) -/

/-- Collect all deletions already valid in the SAME current domain state.
    Only one full 1024-proposal scan is performed per propagation wave. -/
def availableBitDeletionBatch (aL : V 32) (D : BitPruningDomains) :
    List BitDeletion :=
  allBitDeletionProposals.filter (fun d => verifyBitDeletion aL D d)

/-- Replay a batch incrementally, dropping claims that for any reason fail
    against the current (already shrunk) domains. The output is in forward
    chronological order. No soundness assumption about this search code. -/
def applyVerifiedBitDeletionBatch (aL : V 32) (D : BitPruningDomains)
    (batch : List BitDeletion) : BitPruningDomains × List BitDeletion := Id.run do
  let mut state := D
  let mut accepted : List BitDeletion := []
  for d in batch do
    if verifyBitDeletion aL state d then
      state := applyBitDeletion state d
      accepted := d :: accepted
  return (state, accepted.reverse)

/-- Work in propagation waves, not one complete proposal scan per deletion.
    `waves` bounds full scans (not the number of individual deletions). -/
def buildBatchedBitDeletionLog (aL : V 32) (D : BitPruningDomains) :
    Nat → List BitDeletion
  | 0 => []
  | waves + 1 =>
      if verifyEmptyBitPruningDomain D then []
      else
        let batch := availableBitDeletionBatch aL D
        let result := applyVerifiedBitDeletionBatch aL D batch
        if result.2.isEmpty then []
        else result.2 ++ buildBatchedBitDeletionLog aL result.1 waves

/-- Proposal stage is intentionally untrusted. -/
def proposeBatchedBitDeletionCertificate
    (k₀ k₁ aL aR bL : V 32) (waves : Nat := 16) :
    BitDeletionCertificate :=
  { deletions := buildBatchedBitDeletionLog aL
      (initialBitDomains k₀ k₁ aR bL) waves }

/-- Only results accepted by the original, already-proved checker escape. -/
def generateBatchedBitDeletionCertificate
    (k₀ k₁ aL aR bL : V 32) (waves : Nat := 16) :
    Option BitDeletionCertificate :=
  checkProposedBitDeletionCertificate k₀ k₁ aL aR bL
    (proposeBatchedBitDeletionCertificate k₀ k₁ aL aR bL waves)

/-- A successful batched generator run produces a genuine certificate. -/
theorem generatedBatchedBitDeletionCertificate_verified
    (k₀ k₁ aL aR bL : V 32) (waves : Nat)
    (cert : BitDeletionCertificate)
    (h : generateBatchedBitDeletionCertificate k₀ k₁ aL aR bL waves =
      some cert) :
    verifyBitDeletionCertificate k₀ k₁ aL aR bL cert = true := by
  exact checkProposedBitDeletionCertificate_verified
    k₀ k₁ aL aR bL
    (proposeBatchedBitDeletionCertificate k₀ k₁ aL aR bL waves)
    cert h

/-- Existing certificate soundness is reused without modification. -/
theorem xorDDT_rounds_three_zero_of_generatedBatchedBitDeletionCertificate
    (k₀ k₁ k₂ aL aR bL bR : V 32) (waves : Nat)
    (cert : BitDeletionCertificate)
    (h : generateBatchedBitDeletionCertificate k₀ k₁ aL aR bL waves =
      some cert) :
    xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
      (aL, aR) (bL, bR) = 0 := by
  exact xorDDT_rounds_three_zero_of_verifiedBitDeletionCertificate
    k₀ k₁ k₂ aL aR bL bR cert
    (generatedBatchedBitDeletionCertificate_verified
      k₀ k₁ aL aR bL waves cert h)

/-
  Fast, UNTRUSTED certificate search using UInt16 domain masks.
  The previously proved verifyBitDeletionCertificate is unchanged.

  Main goals:
  * executable UInt16 nibble-bit test with a small verified bridge;
  * single-operation tests of local support using 16-bit masks;
  * generation of ordinary BitDeletionCertificate entries;
  * mandatory checking with the original certified verifier.

  Uses BitDeletionCertificate and its checker from Magma.Certificates.
-/
/-! ### Verified bridge: nibble bit and local compatibility -/

/-- Native 16-bit test of bit `r` in the value of a 4-bit nibble.
    The fixed width makes the representation executable without Finset search. -/
def nibbleBitUInt16 (x : Fin 16) (r : Fin 4) : Bool :=
  ((UInt16.ofNat x.val &&&
      ((1 : UInt16) <<< UInt16.ofNat r.val)) != 0)

/-- Small finite proof (4 * 16 cases), performed once at elaboration time.
    No native_decide, sorry, or new axioms. -/
theorem nibbleBitUInt16_correct (x : Fin 16) (r : Fin 4) :
    nibbleBitUInt16 x r = component (BitVec.ofFin x) r := by
  fin_cases r <;> fin_cases x <;>
    decide

/-- Executable version of the original local rotation/XOR compatibility. -/
def compatibleBitUInt16 (aL : V 32)
    (src dst : Fin 32) (yd cd : Fin 16) : Bool :=
  nibbleBitUInt16 yd (offsetAt src) ==
    Bool.xor (nibbleBitUInt16 cd (offsetAt dst)) (component aL dst)

/-- Bridge requested for replacing expensive decidable Prop checks with Bool. -/
theorem compatibleBit_decide_eq
    (aL : V 32) (src dst : Fin 32) (yd cd : Fin 16) :
    compatibleBit aL src dst yd cd ↔
      compatibleBitUInt16 aL src dst yd cd = true := by
  unfold compatibleBit compatibleBitUInt16
  rw [nibbleBitUInt16_correct, nibbleBitUInt16_correct]
  cases hy : component (BitVec.ofFin yd) (offsetAt src) <;>
    cases hc : component (BitVec.ofFin cd) (offsetAt dst) <;>
    cases ha : component aL dst <;> decide

/-- Among all 16 possible nibble *values*, those with the selected bit = 1.
    Index 0..3 maps to AAAA, CCCC, F0F0, FF00, respectively. -/
def nibbleOneSupportMask (r : Fin 4) : UInt16 :=
  match r.val with
  | 0 => 0xAAAA
  | 1 => 0xCCCC
  | 2 => 0xF0F0
  | _ => 0xFF00

/-- Is there a supported nibble value in the domain with the requested bit? -/
def uint16DomainHasBit
    (domain : UInt16) (r : Fin 4) (wanted : Bool) : Bool :=
  (domain &&&
      (if wanted then nibbleOneSupportMask r
       else ~~~(nibbleOneSupportMask r))) != 0

/-- Constant-time (relative to domain size) candidate rejection.
    This is SEARCH ONLY; validity of the deletion is independently checked
    by `verifyBitDeletionCertificate` when a certificate is returned. -/
def fastBitDeletionCandidate
    (aL : V 32) (D : UInt16BitDomains) (d : BitDeletion) : Bool :=
  match d.side with
  | .output =>
      let src := bitPos d.digit d.bit
      let dst := src + 11
      let requiredC :=
        Bool.xor (nibbleBitUInt16 d.value (offsetAt src))
          (component aL dst)
      uint16DomainHas (D.1.getD d.digit.val 0) d.value &&
        !(uint16DomainHasBit
          (D.2.getD (digitAt dst).val 0) (offsetAt dst) requiredC)
  | .intermediate =>
      let dst := bitPos d.digit d.bit
      let src := dst - 11
      let requiredY :=
        Bool.xor (nibbleBitUInt16 d.value (offsetAt dst))
          (component aL dst)
      uint16DomainHas (D.2.getD d.digit.val 0) d.value &&
        !(uint16DomainHasBit
          (D.1.getD (digitAt src).val 0) (offsetAt src) requiredY)

/-- Remove a nibble value by clearing one UInt16 bit. -/
def eraseUInt16DomainValue
    (D : UInt16BitDomains) (d : BitDeletion) : UInt16BitDomains :=
  let keep := ~~~(nibbleValueMask d.value)
  match d.side with
  | .output =>
      (D.1.set! d.digit.val ((D.1.getD d.digit.val 0) &&& keep), D.2)
  | .intermediate =>
      (D.1, D.2.set! d.digit.val ((D.2.getD d.digit.val 0) &&& keep))

/-- Is one of the 16 domain masks empty? -/
def emptyUInt16BitDomain (D : UInt16BitDomains) : Bool :=
  (List.finRange 8).any (fun i =>
    D.1.getD i.val 0 == (0 : UInt16) || D.2.getD i.val 0 == (0 : UInt16))

/-- Scan the 1024 possible witnesses with cheap UInt16 operations.
    After an accepted deletion, use the already updated masks. -/
def fastUInt16DeletionWave (aL : V 32)
    (D : UInt16BitDomains) :
    UInt16BitDomains × List BitDeletion := Id.run do
  let mut state := D
  let mut accepted : List BitDeletion := []
  for d in allBitDeletionProposals do
    if fastBitDeletionCandidate aL state d then
      state := eraseUInt16DomainValue state d
      accepted := d :: accepted
  return (state, accepted.reverse)

/-- An explicit bound on the number of full waves prevents runaway search.
    `none` at the eventual verified-generator level means "not certified". -/
def fastUInt16DeletionLog (aL : V 32)
    (D : UInt16BitDomains) : Nat → List BitDeletion
  | 0 => []
  | waves + 1 =>
      if emptyUInt16BitDomain D then []
      else
        let batch := fastUInt16DeletionWave aL D
        if batch.2.isEmpty then []
        else batch.2 ++ fastUInt16DeletionLog aL batch.1 waves

/-- Compact witness proposal, using only UInt16 for iterative domains. -/
def proposeUInt16DeletionCertificate
    (k₀ k₁ aL aR bL : V 32) (waves : Nat := 8) :
    BitDeletionCertificate :=
  { deletions :=
      fastUInt16DeletionLog aL
        (bitDomainsToUInt16 (initialBitDomains k₀ k₁ aR bL))
        waves }

/-- A result is returned only after REPLAY and validation by the existing
    proven Finset-based checker; no correctness of the heuristic is assumed. -/
def generateUInt16DeletionCertificate
    (k₀ k₁ aL aR bL : V 32) (waves : Nat := 8) :
    Option BitDeletionCertificate :=
  checkProposedBitDeletionCertificate k₀ k₁ aL aR bL
    (proposeUInt16DeletionCertificate k₀ k₁ aL aR bL waves)

theorem generatedUInt16DeletionCertificate_verified (k₀ k₁ aL aR bL : V 32) (waves : Nat)
    (cert : BitDeletionCertificate)
    (h : generateUInt16DeletionCertificate k₀ k₁ aL aR bL waves = some cert) :
    verifyBitDeletionCertificate k₀ k₁ aL aR bL cert = true := by
  exact
    checkProposedBitDeletionCertificate_verified k₀ k₁ aL aR bL
      (proposeUInt16DeletionCertificate k₀ k₁ aL aR bL waves) cert h

theorem xorDDT_rounds_three_zero_of_generatedUInt16DeletionCertificate (k₀ k₁ k₂ aL aR bL bR : V 32)
    (waves : Nat) (cert : BitDeletionCertificate)
    (h : generateUInt16DeletionCertificate k₀ k₁ aL aR bL waves = some cert) :
    xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂) (aL, aR) (bL, bR) = 0 := by
  exact
    xorDDT_rounds_three_zero_of_verifiedBitDeletionCertificate k₀ k₁ k₂ aL aR bL bR cert
      (generatedUInt16DeletionCertificate_verified k₀ k₁ aL aR bL waves cert h)

/-!
### Fast scan sanity check

With every nibble value allowed and a zero XOR offset, the scan finds no
unsupported value to delete.
-/

example :
    (fastUInt16DeletionWave (0#32)
          (Array.replicate 8 (0xFFFF : UInt16), Array.replicate 8 (0xFFFF : UInt16))).2.length =
      0 := by
  decide +kernel

/-
It does not change any of the existing certificate proofs or checker.
This module deliberately uses the already-proved checker ONLY when
the fast, untrusted search has actually found an empty nibble domain.

`none` means no certificate was found, not that the differential exists.
-/

/-- The final mask state obtained by replaying a proposed deletion log.
    This is only a fast search-side test, not part of the trusted checker. -/
def uint16DomainsAfterDeletions
    (D : UInt16BitDomains) (deletions : List BitDeletion) : UInt16BitDomains :=
  deletions.foldl eraseUInt16DomainValue D

/-- Unlike the previous generator, skip the expensive Finset verifier when
    the proposed log has NOT emptied a UInt16 domain. If an empty domain is
    found, replay the *entire* certificate using the old proved checker. -/
def generateUInt16CertificateEarlyReject
    (k₀ k₁ aL aR bL : V 32) (waves : Nat := 8) :
    Option BitDeletionCertificate :=
  let D := bitDomainsToUInt16 (initialBitDomains k₀ k₁ aR bL)
  let deletions := fastUInt16DeletionLog aL D waves
  if emptyUInt16BitDomain (uint16DomainsAfterDeletions D deletions) = true then
    checkProposedBitDeletionCertificate k₀ k₁ aL aR bL
      { deletions := deletions }
  else none

/-- The early-rejection optimization does not weaken certificate checking.
    No soundness lemma about UInt16 masks is needed: an incorrect mask may
    cause a missed candidate, but cannot create an accepted false certificate. -/
theorem generateUInt16CertificateEarlyReject_verified
    (k₀ k₁ aL aR bL : V 32) (waves : Nat)
    (cert : BitDeletionCertificate)
    (h : generateUInt16CertificateEarlyReject
      k₀ k₁ aL aR bL waves = some cert) :
    verifyBitDeletionCertificate k₀ k₁ aL aR bL cert = true := by
  unfold generateUInt16CertificateEarlyReject at h
  dsimp only at h
  split at h
  · exact checkProposedBitDeletionCertificate_verified
      k₀ k₁ aL aR bL _ cert h
  · cases h

/-- End-to-end theorem inherited entirely from the old trusted checker. -/
theorem xorDDT_rounds_three_zero_of_UInt16EarlyReject
    (k₀ k₁ k₂ aL aR bL bR : V 32)
    (waves : Nat) (cert : BitDeletionCertificate)
    (h : generateUInt16CertificateEarlyReject
      k₀ k₁ aL aR bL waves = some cert) :
    xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
      (aL, aR) (bL, bR) = 0 := by
  exact xorDDT_rounds_three_zero_of_verifiedBitDeletionCertificate
    k₀ k₁ k₂ aL aR bL bR cert
    (generateUInt16CertificateEarlyReject_verified
      k₀ k₁ aL aR bL waves cert h)

/-! ### Small native lookup table for the RFC 8891 S-boxes -/

/-- Build 8 x 16 substitution lookup entries from the original RFC table,
    rather than repeating ZMod/BitVec conversion inside the inner loops. -/
def fastSboxTables : Array (Array UInt8) :=
  ((List.finRange 8).map fun i =>
    ((List.finRange 16).map fun x =>
      UInt8.ofNat ((π'arrays i x).val)).toArray).toArray

/-- Differential output after addition and substitution, before rot11.
    Input carries are 0/1. Output carries are determined uniquely and
    therefore do not need to be enumerated for a LOCAL feasibility mask. -/
def fastLocalOutput (box : Array UInt8)
    (key diff : Fin 16) (x c₀ c₁ : Nat) : Nat :=
  let z₀ := (x + key.val + c₀) % 16
  let z₁ := ((x ^^^ diff.val) + key.val + c₁) % 16
  (box.getD z₀ 0).toNat ^^^ (box.getD z₁ 0).toNat

/-- A 16-bit mask for every feasible output difference of a single nibble.
    Complexity: 16 possible x values * 4 incoming carry pairs.
    No Finset, dependent finite quantifier, or output-carry search. -/
def fastLocalOutputMask (box : Array UInt8)
    (key diff : Fin 16) : UInt16 := Id.run do
  let mut mask : UInt16 := 0
  for x in [:16] do
    for c₀ in [:2] do
      for c₁ in [:2] do
        let v := fastLocalOutput box key diff x c₀ c₁
        mask := mask ||| ((1 : UInt16) <<< UInt16.ofNat v)
  return mask

/-- Invert local output feasibility for a prescribed target difference.
    Each candidate input difference is tested using a 16-bit output mask. -/
def fastLocalInputMask (box : Array UInt8)
    (key target : Fin 16) : UInt16 := Id.run do
  let mut mask : UInt16 := 0
  for diff in List.finRange 16 do
    let outs := fastLocalOutputMask box key diff
    if (outs &&& nibbleValueMask target) != 0 then
      mask := mask ||| nibbleValueMask diff
  return mask

/-- The pair of initial bit-pruning domain arrays constructed directly.
    Fast S-box output/rot11 carry search is only used to PROPOSE deletions;
    valid certificates are always checked against original initialBitDomains. -/
def fastInitialBitDomains
    (k₀ k₁ aR bL : V 32) : UInt16BitDomains :=
  let boxes := fastSboxTables
  let target := (xor bL aR).rotateRight 11
  let first := ((List.finRange 8).map fun i =>
    fastLocalOutputMask (boxes.getD i.val #[])
      (wordDigits k₀ i) (wordDigits aR i)).toArray
  let second := ((List.finRange 8).map fun i =>
    fastLocalInputMask (boxes.getD i.val #[])
      (wordDigits k₁ i) (wordDigits target i)).toArray
  (first, second)

/-- A fast generator with an early-reject filter.
    If no empty mask is found, do not run the slow checker at all.
    If one is found, CHECK the entire log with the existing verifier. -/
def generateFastInitialCertificate
    (k₀ k₁ aL aR bL : V 32) (waves : Nat := 8) :
    Option BitDeletionCertificate :=
  let D := fastInitialBitDomains k₀ k₁ aR bL
  let deletions := fastUInt16DeletionLog aL D waves
  if emptyUInt16BitDomain (uint16DomainsAfterDeletions D deletions) then
    checkProposedBitDeletionCertificate k₀ k₁ aL aR bL
      { deletions := deletions }
  else none

/-- Any `some cert` was checked using the original Finset semantics.
    Correctness of the fast initializer is deliberately NOT assumed. -/
theorem generateFastInitialCertificate_verified
    (k₀ k₁ aL aR bL : V 32) (waves : Nat)
    (cert : BitDeletionCertificate)
    (h : generateFastInitialCertificate
      k₀ k₁ aL aR bL waves = some cert) :
    verifyBitDeletionCertificate k₀ k₁ aL aR bL cert = true := by
  unfold generateFastInitialCertificate at h
  dsimp only at h
  split_ifs at h
  · exact checkProposedBitDeletionCertificate_verified
      k₀ k₁ aL aR bL _ cert h

/-- An ordinary certified 3-round impossibility theorem. -/
theorem xorDDT_rounds_three_zero_of_fastInitialCertificate
    (k₀ k₁ k₂ aL aR bL bR : V 32)
    (waves : Nat) (cert : BitDeletionCertificate)
    (h : generateFastInitialCertificate
      k₀ k₁ aL aR bL waves = some cert) :
    xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
      (aL, aR) (bL, bR) = 0 := by
  exact xorDDT_rounds_three_zero_of_verifiedBitDeletionCertificate
    k₀ k₁ k₂ aL aR bL bR cert
    (generateFastInitialCertificate_verified
      k₀ k₁ aL aR bL waves cert h)

/-
  Each addition has two carry chains (4 joint carry states). This module
  propagates the states across ALL eight nibbles, then filters the domain
  of every pre-rotation difference (round 1) and every input difference
  (round 2) using both forward and backward reachable carry states.
  The second stage also enforces grouped rot11/XOR nibble wiring.
-/
/-- `state = 2 * c0 + c1` with c0,c1 in {0,1}.
    The next state is computed, not searched for. -/
def fastSboxCarryStep (box : Array UInt8)
    (key diff x state : Nat) : Nat × Nat :=
  let x1 := x ^^^ diff
  let a0 := x + key + state / 2
  let a1 := x1 + key + state % 2
  let out := (box.getD (a0 % 16) 0).toNat ^^^
             (box.getD (a1 % 16) 0).toNat
  (out, 2 * (a0 / 16) + (a1 / 16))

/-! ### Transition edges for one nibble, as four UInt8 successor masks -/

/-- If first=true, the input difference is fixed and the output difference
    is selected from `allowed`. If first=false, the output difference is fixed
    and the input difference is selected from `allowed`.
    Result: edges[s] is the bit mask of possible next carry states. -/
def fastCarryEdgesAt (box : Array UInt8)
    (key fixed : Fin 16) (allowed : UInt16) (first : Bool) :
    Array UInt8 := Id.run do
  let mut edges := Array.replicate 4 (0 : UInt8)
  for s in [:4] do
    let mut successors : UInt8 := 0
    for d in [:16] do
      if (!first || d == fixed.val) &&
          (first || (allowed &&& ((1 : UInt16) <<< UInt16.ofNat d)) != 0) then
        for x in [:16] do
          let (out, next) := fastSboxCarryStep box key.val d x s
          if (if first then
                (allowed &&& ((1 : UInt16) <<< UInt16.ofNat out)) != 0
              else out == fixed.val) then
            successors := successors ||| carryStateBitFast next
    edges := edges.set! s successors
  return edges

/-- Forward image of one four-state set through the current edges. -/
def fastCarryNextStates (states : UInt8) (edges : Array UInt8) : UInt8 :=
  Id.run do
    let mut result : UInt8 := 0
    for s in [:4] do
      if carryStateMemFast states s then
        result := result ||| edges.getD s 0
    return result

/-- Backwards preimage of a set of allowed successor states. -/
def fastCarryPrevStates (successors : UInt8) (edges : Array UInt8) : UInt8 :=
  Id.run do
    let mut result : UInt8 := 0
    for s in [:4] do
      if ((edges.getD s 0) &&& successors) != 0 then
        result := result ||| carryStateBitFast s
    return result

/-- The array has 9 entries: before nibble 0, ..., after nibble 7. -/
def fastCarryForward (edges : Array (Array UInt8)) : Array UInt8 := Id.run do
  let mut F : Array UInt8 := #[1]
  for i in [:8] do
    F := F.push (fastCarryNextStates (F.getD i 0) (edges.getD i #[]))
  return F

/-- Final carries are unrestricted, so all four states are accepted at 8. -/
def fastCarryBackward (edges : Array (Array UInt8)) : Array UInt8 := Id.run do
  let mut B := (Array.replicate 9 (0 : UInt8)).set! 8 15
  for j in [:8] do
    let i := 7 - j
    B := B.set! i
      (fastCarryPrevStates (B.getD (i + 1) 0) (edges.getD i #[]))
  return B

/-- Return the 8 local matrices for either carry automaton.
    First: fixed aR input difference and Y output domain.
    Second: fixed pre-rotation output and C input domain. -/
def fastCarryBuildEdges
    (k₀ k₁ aR bL : V 32) (D : UInt16BitDomains)
    (first : Bool) : Array (Array UInt8) :=
  let boxes := fastSboxTables
  let target := (xor bL aR).rotateRight 11
  ((List.finRange 8).map fun i =>
    fastCarryEdgesAt (boxes.getD i.val #[])
      (if first then wordDigits k₀ i else wordDigits k₁ i)
      (if first then wordDigits aR i else wordDigits target i)
      (if first then D.1.getD i.val 0 else D.2.getD i.val 0)
      first).toArray

/-- All output-difference candidates supported by some FULL carry path.
    Here input difference is fixed. -/
def fastCarryOutputSupport
    (box : Array UInt8) (key diff : Fin 16)
    (domain : UInt16) (F B : UInt8) : UInt16 := Id.run do
  let mut supported : UInt16 := 0
  for s in [:4] do
    if carryStateMemFast F s then
      for x in [:16] do
        let (out, next) := fastSboxCarryStep box key.val diff.val x s
        let value := ((1 : UInt16) <<< UInt16.ofNat out)
        if carryStateMemFast B next && (domain &&& value) != 0 then
          supported := supported ||| value
  return supported

/-- All input-difference candidates supported by some FULL carry path.
    Here output difference is fixed. -/
def fastCarryInputSupport
    (box : Array UInt8) (key target : Fin 16)
    (domain : UInt16) (F B : UInt8) : UInt16 := Id.run do
  let mut supported : UInt16 := 0
  for d in [:16] do
    let value := ((1 : UInt16) <<< UInt16.ofNat d)
    if (domain &&& value) != 0 then
      for s in [:4] do
        if carryStateMemFast F s then
          for x in [:16] do
            let (out, next) := fastSboxCarryStep box key.val d x s
            if out == target.val && carryStateMemFast B next then
              supported := supported ||| value
  return supported

/-- One whole-automaton pruning pass on the two families of 8 masks.
    The two automata are computed using the SAME input state D. -/
def fastCarryPruneBoth
    (k₀ k₁ aR bL : V 32) (D : UInt16BitDomains) : UInt16BitDomains :=
  Id.run do
    let boxes := fastSboxTables
    let target := (xor bL aR).rotateRight 11
    let E0 := fastCarryBuildEdges k₀ k₁ aR bL D true
    let E1 := fastCarryBuildEdges k₀ k₁ aR bL D false
    let F0 := fastCarryForward E0
    let F1 := fastCarryForward E1
    let B0 := fastCarryBackward E0
    let B1 := fastCarryBackward E1
    let mut Y := Array.replicate 8 (0 : UInt16)
    let mut C := Array.replicate 8 (0 : UInt16)
    for i in List.finRange 8 do
      let box := boxes.getD i.val #[]
      Y := Y.set! i.val (fastCarryOutputSupport box
        (wordDigits k₀ i) (wordDigits aR i)
        (D.1.getD i.val 0) (F0.getD i.val 0) (B0.getD (i.val + 1) 0))
      C := C.set! i.val (fastCarryInputSupport box
        (wordDigits k₁ i) (wordDigits target i)
        (D.2.getD i.val 0) (F1.getD i.val 0) (B1.getD (i.val + 1) 0))
    return (Y, C)

/-! ### Nibble-grouped rot11/XOR consistency with UInt16 domains -/

/-- All bits of the source nibble that land in the same destination
    nibble must be explained by ONE destination value. -/
def fastGroupedYSupported (aL : V 32) (D : UInt16BitDomains)
    (i : Fin 8) (y : Fin 16) : Bool :=
  (List.finRange 4).all fun r =>
    let dst := bitPos i r + 11
    let j := digitAt dst
    (List.finRange 16).any fun c =>
      uint16DomainHas (D.2.getD j.val 0) c &&
        (List.finRange 4).all (fun q =>
          digitAt (bitPos i q + 11) != j ||
            compatibleBitUInt16 aL (bitPos i q) (bitPos i q + 11) y c)

/-- Symmetric grouped check for an intermediate-difference nibble. -/
def fastGroupedCSupported (aL : V 32) (D : UInt16BitDomains)
    (i : Fin 8) (c : Fin 16) : Bool :=
  (List.finRange 4).all fun r =>
    let src := bitPos i r - 11
    let j := digitAt src
    (List.finRange 16).any fun y =>
      uint16DomainHas (D.1.getD j.val 0) y &&
        (List.finRange 4).all (fun q =>
          digitAt (bitPos i q - 11) != j ||
            compatibleBitUInt16 aL (bitPos i q - 11) (bitPos i q) y c)

/-- The original grouped pruning semantics, now tested using bit masks. -/
def fastGroupedUInt16 (aL : V 32)
    (D : UInt16BitDomains) : UInt16BitDomains := Id.run do
  let mut Y := Array.replicate 8 (0 : UInt16)
  let mut C := Array.replicate 8 (0 : UInt16)
  for i in List.finRange 8 do
    let mut ym : UInt16 := 0
    let mut cm : UInt16 := 0
    for v in List.finRange 16 do
      if uint16DomainHas (D.1.getD i.val 0) v &&
          fastGroupedYSupported aL D i v then
        ym := ym ||| nibbleValueMask v
      if uint16DomainHas (D.2.getD i.val 0) v &&
          fastGroupedCSupported aL D i v then
        cm := cm ||| nibbleValueMask v
    Y := Y.set! i.val ym
    C := C.set! i.val cm
  return (Y, C)

/-- Compute separate carry-path and rotation-wiring reductions, until
    saturation or the requested number of passes. All domains shrink. -/
def fastCoupledCarryWiringPropagate
    (k₀ k₁ aL aR bL : V 32) (initial : UInt16BitDomains) :
    Nat → UInt16BitDomains
  | 0 => initial
  | steps + 1 =>
      let afterCarry := fastCarryPruneBoth k₀ k₁ aR bL initial
      let afterWiring := fastGroupedUInt16 aL afterCarry
      if afterWiring == initial || emptyUInt16BitDomain afterWiring then
        afterWiring
      else fastCoupledCarryWiringPropagate k₀ k₁ aL aR bL afterWiring steps

/-- Use the fast initializer; no old Finset init or verifier is called. -/
def fastCoupledCarryWiringFromInputs
    (k₀ k₁ aL aR bL : V 32) (passes : Nat := 16) :
    UInt16BitDomains :=
  fastCoupledCarryWiringPropagate k₀ k₁ aL aR bL
    (fastInitialBitDomains k₀ k₁ aR bL) passes

/-! ### Use fast search to propose, old semantics to verify. -/

/-- The two 8x4 transition tables and nine-state frontiers proposed by
    the existing efficient UInt8 carry implementation. -/
def proposeVerifiedCarryFrontiers
    (k₀ k₁ aR bL : V 32) (D : UInt16BitDomains) :
    (Array (Array UInt8) × Array UInt8) ×
    (Array (Array UInt8) × Array UInt8) :=
  let E₀ := fastCarryBuildEdges k₀ k₁ aR bL D true
  let E₁ := fastCarryBuildEdges k₀ k₁ aR bL D false
  ((E₀, fastCarryForward E₀), (E₁, fastCarryForward E₁))

/-- Four independent checks: original transitions and induction over
    the nine forward frontiers, for BOTH carry chains. -/
def verifyProposedCarryFrontiers
    (k₀ k₁ aR bL : V 32) (D : UInt16BitDomains) : Bool :=
  let proposal := proposeVerifiedCarryFrontiers k₀ k₁ aR bL D
  verifyFirstCarryEdges k₀ aR D proposal.1.1 &&
  verifySecondCarryEdges k₁ aR bL D proposal.2.1 &&
  verifyForwardCarryFrontiers proposal.1.1 proposal.1.2 &&
  verifyForwardCarryFrontiers proposal.2.1 proposal.2.2

/-- The search proposes the next masks; the checker validates ALL parts.
    No theorem in this file assumes correctness of fastCarryPruneBoth. -/
def proposeCarryReduction
    (k₀ k₁ aR bL : V 32) (D : UInt16BitDomains) :
    CarryReductionCertificate :=
  let E₀ := fastCarryBuildEdges k₀ k₁ aR bL D true
  let E₁ := fastCarryBuildEdges k₀ k₁ aR bL D false
  { edges₀ := E₀
    edges₁ := E₁
    forward₀ := fastCarryForward E₀
    forward₁ := fastCarryForward E₁
    backward₀ := fastCarryBackward E₀
    backward₁ := fastCarryBackward E₁
    next := fastCarryPruneBoth k₀ k₁ aR bL D }

end Magma.FastSearch
