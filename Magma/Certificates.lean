module

public import Magma.Pruning
import all Init.Data.Range.Basic

@[expose] public section

/-!
# Independently checked impossibility certificates

Certificate encodings, pruning/deletion traces, grouped masks and forward/
backward carry frontiers, with soundness proofs against the mathematical model.
`FastInitialCheck` verifies initial-mask coverage directly from `sboxCarryStep`
transitions. Its soundness theorem implies acceptance by the original Finset
checker without executing that checker or assuming equivalence of search code.
Search algorithms belong to `Magma.FastSearch`.
-/

namespace Magma.Certificates.Encoding
end Magma.Certificates.Encoding

open Magma.Internal Magma.CarryAutomaton Magma.MultiRoundDDT Magma.Pruning
  Magma.Certificates.Encoding

namespace Magma.Certificates.Encoding

/-! ### Fast search representation: a whole Finset (Fin 16) in 16 bits -/

/-- The i-th bit of the mask encodes membership of nibble value i. -/
def nibbleValueMask (v : Fin 16) : UInt16 :=
  (1 : UInt16) <<< UInt16.ofNat v.val

def uint16DomainHas (m : UInt16) (v : Fin 16) : Bool :=
  (m &&& nibbleValueMask v) != 0

def finsetToUInt16 (s : Finset (Fin 16)) : UInt16 :=
  (List.finRange 16).foldl (fun m v => if v ∈ s then m ||| nibbleValueMask v else m) (0 : UInt16)

/-- Two fixed-size arrays of 8 UInt16 masks. Unlike closures built by
    `(fun i => if i = ix then ... else ...)`, array updates do NOT accumulate
    a chain of tests as the deletion log grows. -/
abbrev UInt16BitDomains :=
  Array UInt16 × Array UInt16

def bitDomainsToUInt16 (D : BitPruningDomains) : UInt16BitDomains :=
  let indices := List.finRange 8
  ((indices.map (fun i => finsetToUInt16 (D.1 i))).toArray,
    (indices.map (fun i => finsetToUInt16 (D.2 i))).toArray)

/-
  Carry-state sets use the four low bits of UInt8. The encoding is shared
  by independently checked certificates and fast propagation algorithms.
-/
/-! ### Four carry states, encoded as four low bits of UInt8 -/

def carryStateBitFast (s : Nat) : UInt8 :=
  (1 : UInt8) <<< UInt8.ofNat s

def carryStateMemFast (states : UInt8) (s : Nat) : Bool :=
  (states &&& carryStateBitFast s) != 0

end Magma.Certificates.Encoding

namespace Magma.Certificates

/-- A claimed sequence of domain states, excluding the implicit initial one. -/
structure BitPruningCertificate where
  steps : List BitPruningDomains

/-- Verify that one claimed step is *exactly* the sound bit-pruning step.
    Pointwise equality avoids relying on decidable equality of functions. -/
def verifyBitPruningStep (aL : V 32)
    (before after : BitPruningDomains) : Bool :=
  decide (∀ i : Fin 8,
    after.1 i = pruneOutputBits aL before.1 before.2 i ∧
    after.2 i = pruneIntermediateBits aL before.1 before.2 i)

/-- Validate a complete pruning trace; the final domain must be empty.
    No search over full 32-bit intermediate differences is performed. -/
def verifyBitPruningTrace (aL : V 32) (D : BitPruningDomains) :
    List BitPruningDomains → Bool
  | [] => verifyEmptyBitPruningDomain D
  | next :: rest =>
      verifyBitPruningStep aL D next &&
        verifyBitPruningTrace aL next rest

/-- The initial domain pair is fixed by the cipher differences and keys;
    the certificate cannot substitute a different initial state. -/
def verifyBitPruningCertificate
    (k₀ k₁ aL aR bL : V 32)
    (cert : BitPruningCertificate) : Bool :=
  verifyBitPruningTrace aL
    (initialBitDomains k₀ k₁ aR bL) cert.steps

/-- A verified trace cannot eliminate any assignment satisfying the
    exact rotation wiring and the given initial domains. -/
private theorem verifiedBitPruningTrace_noSolution (aL : V 32) :
    ∀ (steps : List BitPruningDomains) (D : BitPruningDomains)
      (c y : Fin 8 → Fin 16),
      jointRotationWiring aL c y →
      (∀ i, y i ∈ D.1 i) →
      (∀ i, c i ∈ D.2 i) →
      verifyBitPruningTrace aL D steps = true → False := by
  intro steps
  induction steps with
  | nil =>
      intro D c y hw hy hc hchecked
      have hterminal : verifyEmptyBitPruningDomain D = true := hchecked
      have hconf :
          (∃ i : Fin 8, D.1 i = ∅) ∨
          (∃ i : Fin 8, D.2 i = ∅) :=
        (decide_eq_true_eq).mp hterminal
      rcases hconf with ⟨i, he⟩ | ⟨i, he⟩
      · have hm : y i ∈ (∅ : Finset (Fin 16)) := by
          rw [← he]
          exact hy i
        exact (Finset.notMem_empty (y i)) hm
      · have hm : c i ∈ (∅ : Finset (Fin 16)) := by
          rw [← he]
          exact hc i
        exact (Finset.notMem_empty (c i)) hm
  | cons next rest ih =>
      intro D c y hw hy hc hchecked
      have hparts :
          verifyBitPruningStep aL D next = true ∧
          verifyBitPruningTrace aL next rest = true :=
        Eq.mp (Bool.and_eq_true _ _) hchecked
      have hstep : ∀ i : Fin 8,
          next.1 i = pruneOutputBits aL D.1 D.2 i ∧
          next.2 i = pruneIntermediateBits aL D.1 D.2 i :=
        decide_eq_true_eq.mp hparts.1
      have hkeep := bitPruning_sound aL D.1 D.2 c y hw hy hc
      have hyNext : ∀ i, y i ∈ next.1 i := by
        intro i
        rw [(hstep i).1]
        exact hkeep.1 i
      have hcNext : ∀ i, c i ∈ next.2 i := by
        intro i
        rw [(hstep i).2]
        exact hkeep.2 i
      exact ih next c y hw hyNext hcNext hparts.2

/-- A checked finite certificate proves a three-round impossible
    fixed-key XOR differential. The third key and right output half
    are unrestricted because the original sufficient condition is. -/
theorem xorDDT_rounds_three_zero_of_verifiedBitPruningCertificate
    (k₀ k₁ k₂ aL aR bL bR : V 32)
    (cert : BitPruningCertificate)
    (hverified :
      verifyBitPruningCertificate
        k₀ k₁ aL aR bL cert = true) :
    xorDDT_rounds 3
      (threeRoundKeys k₀ k₁ k₂)
      (aL, aR) (bL, bR) = 0 := by
  apply xorDDT_rounds_three_zero_of_no_localDomains
    k₀ k₁ k₂ aL aR bL bR
  rintro ⟨c, y, hw, hy, hc⟩
  exact verifiedBitPruningTrace_noSolution aL cert.steps
    (initialBitDomains k₀ k₁ aR bL) c y hw hy hc hverified

-- A compact, proof-carrying alternative to complete pruning traces.
-- Each entry records just one domain value to delete and one bit witnessing
-- the lack of support. The checker reconstructs all intermediate domains.

/-- Which family of four-bit domains is being pruned. -/
inductive BitDeletionSide where
  | output
  | intermediate
  deriving DecidableEq, Repr

/-- Delete `value` from one digit domain. The `bit` field indicates a local
    bit position for which the opposite digit domain has no compatible value.
    This is a claim that the checker must verify, not a trusted assertion. -/
structure BitDeletion where
  side : BitDeletionSide
  digit : Fin 8
  value : Fin 16
  bit : Fin 4
  deriving Repr

/-- Apply one certified deletion to the current domain state, without
    storing another full state in the certificate. -/
def applyBitDeletion (D : BitPruningDomains)
    (d : BitDeletion) : BitPruningDomains :=
  match d.side with
  | .output =>
      (fun i => if i = d.digit then (D.1 i).erase d.value else D.1 i,
       D.2)
  | .intermediate =>
      (D.1,
       fun i => if i = d.digit then (D.2 i).erase d.value else D.2 i)

/-- Check that the value is currently present and cannot be supported
    at the nominated bit by ANY value of the opposite current domain.
    The checker examines at most 16 opposing digit values per deletion. -/
def verifyBitDeletion (aL : V 32) (D : BitPruningDomains)
    (d : BitDeletion) : Bool :=
  match d.side with
  | .output =>
      decide (d.value ∈ D.1 d.digit ∧
        ∀ cd ∈ D.2 (digitAt (bitPos d.digit d.bit + 11)),
          ¬ compatibleBit aL (bitPos d.digit d.bit)
              (bitPos d.digit d.bit + 11) d.value cd)
  | .intermediate =>
      decide (d.value ∈ D.2 d.digit ∧
        ∀ yd ∈ D.1 (digitAt (bitPos d.digit d.bit - 11)),
          ¬ compatibleBit aL (bitPos d.digit d.bit - 11)
              (bitPos d.digit d.bit) yd d.value)

/-- One accepted deletion keeps every full assignment that satisfies
    the exact rotation wiring and all current domains. The proof uses
    the existing `bitPruning_sound` invariant. -/
theorem verifiedBitDeletion_sound (aL : V 32)
    (D : BitPruningDomains) (d : BitDeletion)
    (c y : Fin 8 → Fin 16)
    (hw : jointRotationWiring aL c y)
    (hy : ∀ i, y i ∈ D.1 i)
    (hc : ∀ i, c i ∈ D.2 i)
    (hverified : verifyBitDeletion aL D d = true) :
    (∀ i, y i ∈ (applyBitDeletion D d).1 i) ∧
    (∀ i, c i ∈ (applyBitDeletion D d).2 i) := by
  obtain ⟨side, ix, val, bit⟩ := d
  cases side with
  | output =>
      -- Simplify the verifier syntactically; do not ask `change` to
      -- compare two independently elaborated Decidable (Fin 16) instances.
      simp only [verifyBitDeletion, decide_eq_true_eq] at hverified
      have hbad := hverified.2
      have hkeep := bitPruning_sound aL D.1 D.2 c y hw hy hc
      have hsupp :
          ∃ cd ∈ D.2 (digitAt (bitPos ix bit + 11)),
            compatibleBit aL (bitPos ix bit)
              (bitPos ix bit + 11) (y ix) cd :=
        (Finset.mem_filter.mp (hkeep.1 ix)).2 bit
      have hne : y ix ≠ val := by
        intro heq
        rcases hsupp with ⟨cd, hmem, hcompat⟩
        exact hbad cd hmem (heq ▸ hcompat)
      constructor
      · intro i
        change y i ∈ (if i = ix then (D.1 i).erase val else D.1 i)
        by_cases hi : i = ix
        · subst i
          simp only [ite_true]
          exact Finset.mem_erase.mpr ⟨hne, hy ix⟩
        · simp only [ite_eq_right hi]
          exact hy i
      · exact hc
  | intermediate =>
      -- The same avoidance of definitional-equality expansion for Fin 16.
      simp only [verifyBitDeletion, decide_eq_true_eq] at hverified
      have hbad := hverified.2
      have hkeep := bitPruning_sound aL D.1 D.2 c y hw hy hc
      have hsupp :
          ∃ yd ∈ D.1 (digitAt (bitPos ix bit - 11)),
            compatibleBit aL (bitPos ix bit - 11)
              (bitPos ix bit) yd (c ix) :=
        (Finset.mem_filter.mp (hkeep.2 ix)).2 bit
      have hne : c ix ≠ val := by
        intro heq
        rcases hsupp with ⟨yd, hmem, hcompat⟩
        exact hbad yd hmem (heq ▸ hcompat)
      constructor
      · exact hy
      · intro i
        change c i ∈ (if i = ix then (D.2 i).erase val else D.2 i)
        by_cases hi : i = ix
        · subst i
          simp only [ite_true]
          exact Finset.mem_erase.mpr ⟨hne, hc ix⟩
        · simp only [ite_eq_right hi]
          exact hc i

/-- A compact proof certificate consists only of individual deletions;
    no intermediate domain families are saved. -/
structure BitDeletionCertificate where
  deletions : List BitDeletion
  deriving Repr

/-- Replay the deletion log. If no valid deletion remains, a preexisting
    empty domain is also accepted as a zero-length certificate. -/
def verifyBitDeletionTrace (aL : V 32) (D : BitPruningDomains) :
    List BitDeletion → Bool
  | [] => verifyEmptyBitPruningDomain D
  | d :: rest =>
      verifyBitDeletion aL D d &&
        verifyBitDeletionTrace aL (applyBitDeletion D d) rest

/-- Verify the compact certificate against genuine initial nibble domains;
    the prover cannot forge the initial domains or any removal step. -/
def verifyBitDeletionCertificate
    (k₀ k₁ aL aR bL : V 32)
    (cert : BitDeletionCertificate) : Bool :=
  verifyBitDeletionTrace aL
    (initialBitDomains k₀ k₁ aR bL) cert.deletions

/-- A trace of accepted single-value deletions ending in an empty domain
    is incompatible with any solution of the wiring constraints. -/
private theorem verifiedBitDeletionTrace_noSolution (aL : V 32) :
    ∀ (deletions : List BitDeletion) (D : BitPruningDomains)
      (c y : Fin 8 → Fin 16),
      jointRotationWiring aL c y →
      (∀ i, y i ∈ D.1 i) →
      (∀ i, c i ∈ D.2 i) →
      verifyBitDeletionTrace aL D deletions = true → False := by
  intro deletions
  induction deletions with
  | nil =>
      intro D c y hw hy hc hchecked
      have hterminal : verifyEmptyBitPruningDomain D = true := hchecked
      have hconf :
          (∃ i : Fin 8, D.1 i = ∅) ∨
          (∃ i : Fin 8, D.2 i = ∅) :=
        (decide_eq_true_eq).mp hterminal
      rcases hconf with ⟨i, he⟩ | ⟨i, he⟩
      · have hm : y i ∈ (∅ : Finset (Fin 16)) := by
          rw [← he]
          exact hy i
        exact (Finset.notMem_empty (y i)) hm
      · have hm : c i ∈ (∅ : Finset (Fin 16)) := by
          rw [← he]
          exact hc i
        exact (Finset.notMem_empty (c i)) hm
  | cons d rest ih =>
      intro D c y hw hy hc hchecked
      have hparts :
          verifyBitDeletion aL D d = true ∧
          verifyBitDeletionTrace aL (applyBitDeletion D d) rest = true :=
        Eq.mp (Bool.and_eq_true _ _) hchecked
      have hkeep := verifiedBitDeletion_sound aL D d c y
        hw hy hc hparts.1
      exact ih (applyBitDeletion D d) c y hw hkeep.1 hkeep.2 hparts.2

/-- Compact, externally generated deletion logs suffice to formally
    certify impossible three-round XOR differentials of Magma. -/
theorem xorDDT_rounds_three_zero_of_verifiedBitDeletionCertificate
    (k₀ k₁ k₂ aL aR bL bR : V 32)
    (cert : BitDeletionCertificate)
    (hverified :
      verifyBitDeletionCertificate k₀ k₁ aL aR bL cert = true) :
    xorDDT_rounds 3
      (threeRoundKeys k₀ k₁ k₂)
      (aL, aR) (bL, bR) = 0 := by
  apply xorDDT_rounds_three_zero_of_no_localDomains
    k₀ k₁ k₂ aL aR bL bR
  rintro ⟨c, y, hw, hy, hc⟩
  exact verifiedBitDeletionTrace_noSolution aL cert.deletions
    (initialBitDomains k₀ k₁ aR bL) c y hw hy hc hverified

/-
  First proof-carrying layer for the fast global carry search.
  Four UInt8 edge masks per nibble, nine UInt8 frontier masks per chain.
  The verifier checks every permitted transition against ORIGINAL
  `sboxCarryStep`, then checks the frontier inductive invariant.
-/

/-- Integer encoding of two carry bits. -/
def checkedCarryIndex (s : CarryState) : Nat :=
  2 * s.1.val + s.2.val

/-- Edge masks proposed by the search engine. Each row contains four masks. -/
def checkedCarryEdge (E : Array (Array UInt8))
    (i : Fin 8) (s t : CarryState) : Bool :=
  carryStateMemFast ((E.getD i.val #[]).getD (checkedCarryIndex s) 0)
    (checkedCarryIndex t)

/-! ### Boolean checker utilities -/

/-- Extract one checked member without unfolding a decidable quantifier. -/
private theorem listAll_sound {α : Type} (p : α → Bool) :
    ∀ xs : List α, xs.all p = true → ∀ x ∈ xs, p x = true := by
  intro xs
  induction xs with
  | nil =>
      intro _ x hx
      cases hx
  | cons a tail ih =>
      intro h x hx
      change (p a && tail.all p) = true at h
      have ha : p a = true := (Bool.and_eq_true_iff.mp h).1
      have ht : tail.all p = true := (Bool.and_eq_true_iff.mp h).2
      rcases (List.mem_cons.mp hx) with hEq | hMem
      · subst x
        exact ha
      · exact ih ht x hMem

/-- Independent checker for the first carry chain. All four carry
    states and all sixteen concrete inputs are checked via Bool lists. -/
def verifyFirstCarryEdges
    (k₀ aR : V 32) (D : UInt16BitDomains)
    (E : Array (Array UInt8)) : Bool :=
  (List.finRange 8).all fun i =>
    (List.finRange 2).all fun c₀ =>
      (List.finRange 2).all fun c₁ =>
        (List.finRange 16).all fun x =>
          let s : CarryState := (c₀, c₁)
          let step := sboxCarryStep i (wordDigits k₀ i) (wordDigits aR i) x s
          !(uint16DomainHas (D.1.getD i.val 0) step.1) ||
            checkedCarryEdge E i s step.2

/-- Independent checker for the second carry chain. -/
def verifySecondCarryEdges
    (k₁ aR bL : V 32) (D : UInt16BitDomains)
    (E : Array (Array UInt8)) : Bool :=
  (List.finRange 8).all fun i =>
    (List.finRange 2).all fun c₀ =>
      (List.finRange 2).all fun c₁ =>
        (List.finRange 16).all fun c =>
          (List.finRange 16).all fun x =>
            let s : CarryState := (c₀, c₁)
            let step := sboxCarryStep i (wordDigits k₁ i) c x s
            !(uint16DomainHas (D.2.getD i.val 0) c) ||
              (!(decide (step.1 =
                wordDigits ((xor bL aR).rotateRight 11) i)) ||
                  checkedCarryEdge E i s step.2)

/-- Soundness of first-machine edge checks: every enabled source edge
    is covered by the supplied UInt8 edge mask. -/
private theorem verifyFirstCarryEdges_sound
    (k₀ aR : V 32) (D : UInt16BitDomains)
    (E : Array (Array UInt8))
    (he : verifyFirstCarryEdges k₀ aR D E = true)
    (i : Fin 8) (s : CarryState) (x : Fin 16)
    (hmem : uint16DomainHas (D.1.getD i.val 0)
      (sboxCarryStep i (wordDigits k₀ i) (wordDigits aR i) x s).1 = true) :
    checkedCarryEdge E i s
      (sboxCarryStep i (wordDigits k₀ i) (wordDigits aR i) x s).2 = true := by
  unfold verifyFirstCarryEdges at he
  have hi := listAll_sound _ _ he i (by simp)
  have h₀ := listAll_sound _ _ hi s.1 (by simp)
  have h₁ := listAll_sound _ _ h₀ s.2 (by simp)
  have hx := listAll_sound _ _ h₁ x (by simp)
  dsimp only at hx
  simp only [Bool.or_eq_true] at hx
  rcases hx with hbad | hedge
  · rw [hmem] at hbad
    cases hbad
  · exact hedge

/-- Soundness of second-machine edge checks. -/
private theorem verifySecondCarryEdges_sound
    (k₁ aR bL : V 32) (D : UInt16BitDomains)
    (E : Array (Array UInt8))
    (he : verifySecondCarryEdges k₁ aR bL D E = true)
    (i : Fin 8) (s : CarryState) (c x : Fin 16)
    (hmem : uint16DomainHas (D.2.getD i.val 0) c = true)
    (htarget : (sboxCarryStep i (wordDigits k₁ i) c x s).1 =
      wordDigits ((xor bL aR).rotateRight 11) i) :
    checkedCarryEdge E i s
      (sboxCarryStep i (wordDigits k₁ i) c x s).2 = true := by
  unfold verifySecondCarryEdges at he
  have hi := listAll_sound _ _ he i (by simp)
  have h₀ := listAll_sound _ _ hi s.1 (by simp)
  have h₁ := listAll_sound _ _ h₀ s.2 (by simp)
  have hc := listAll_sound _ _ h₁ c (by simp)
  have hx := listAll_sound _ _ hc x (by simp)
  dsimp only at hx
  simp only [Bool.or_eq_true] at hx
  rcases hx with hbad | hrest
  · rw [hmem] at hbad
    cases hbad
  · rcases hrest with hbad | hedge
    · simp [htarget] at hbad
    · exact hedge

/-- Check an OVER-approximation of the nine reachable frontiers.
    Any certified edge leaving the current frontier enters the next one.
    The initial frontier contains the real initial state (0,0). -/
def verifyForwardCarryFrontiers
    (E : Array (Array UInt8)) (F : Array UInt8) : Bool :=
  decide
    (carryStateMemFast (F.getD 0 0) 0 = true ∧
      ∀ i : Fin 8, ∀ s t : CarryState,
        carryStateMemFast (F.getD i.val 0) (checkedCarryIndex s) = true →
        checkedCarryEdge E i s t = true →
        carryStateMemFast (F.getD (i.val + 1) 0)
          (checkedCarryIndex t) = true)

/-- Generic soundness: no actual eight-step path following certified
    edges can ever leave a verified forward frontier. -/
theorem verifyForwardCarryFrontiers_sound
    (E : Array (Array UInt8)) (F : Array UInt8)
    (hverified : verifyForwardCarryFrontiers E F = true)
    (states : Fin 9 → CarryState)
    (hstart : states 0 = ((0, 0) : CarryState))
    (hsteps : ∀ i : Fin 8,
      checkedCarryEdge E i (states i.castSucc) (states i.succ) = true) :
    ∀ j : Fin 9,
      carryStateMemFast (F.getD j.val 0)
        (checkedCarryIndex (states j)) = true := by
  simp only [verifyForwardCarryFrontiers, decide_eq_true_eq] at hverified
  rcases hverified with ⟨hinit, hclosure⟩
  have aux : ∀ n : Nat, (hn : n < 9) →
      carryStateMemFast (F.getD n 0)
        (checkedCarryIndex (states ⟨n, hn⟩)) = true := by
    intro n
    induction n with
    | zero =>
        intro hn
        simpa [hstart, checkedCarryIndex] using hinit
    | succ n ih =>
        intro hn
        let i : Fin 8 := ⟨n, by omega⟩
        have hprev :
            carryStateMemFast (F.getD i.val 0)
              (checkedCarryIndex (states i.castSucc)) = true := by
          exact ih (by omega)
        exact hclosure i (states i.castSucc) (states i.succ)
          hprev (hsteps i)
  intro j
  exact aux j.val j.isLt

/-- End-to-end forward soundness for the first automaton, conditional
    on a full path through the ORIGINAL nibble transitions. -/
theorem verifiedFirstCarryForward_sound
    (k₀ aR : V 32) (D : UInt16BitDomains)
    (E : Array (Array UInt8)) (F : Array UInt8)
    (he : verifyFirstCarryEdges k₀ aR D E = true)
    (hf : verifyForwardCarryFrontiers E F = true)
    (y : Fin 8 → Fin 16)
    (w : VerifiedCarryPath (wordDigits k₀) (wordDigits aR) y)
    (hy : ∀ i, uint16DomainHas (D.1.getD i.val 0) (y i) = true) :
    ∀ j : Fin 9,
      carryStateMemFast (F.getD j.val 0)
        (checkedCarryIndex (w.states j)) = true := by
  apply verifyForwardCarryFrontiers_sound E F hf w.states w.initial
  intro i
  have hmem :
      uint16DomainHas (D.1.getD i.val 0)
        (sboxCarryStep i (wordDigits k₀ i) (wordDigits aR i)
          (w.input i) (w.states i.castSucc)).1 = true := by
    simpa only [w.step i] using hy i
  have hs := verifyFirstCarryEdges_sound k₀ aR D E he
    i (w.states i.castSucc) (w.input i) hmem
  simpa only [w.step i] using hs

/-- Symmetric forward soundness for the second carry chain. -/
theorem verifiedSecondCarryForward_sound
    (k₁ aR bL : V 32) (D : UInt16BitDomains)
    (E : Array (Array UInt8)) (F : Array UInt8)
    (he : verifySecondCarryEdges k₁ aR bL D E = true)
    (hf : verifyForwardCarryFrontiers E F = true)
    (c : Fin 8 → Fin 16)
    (w : VerifiedCarryPath (wordDigits k₁) c
      (wordDigits ((xor bL aR).rotateRight 11)))
    (hc : ∀ i, uint16DomainHas (D.2.getD i.val 0) (c i) = true) :
    ∀ j : Fin 9,
      carryStateMemFast (F.getD j.val 0)
        (checkedCarryIndex (w.states j)) = true := by
  apply verifyForwardCarryFrontiers_sound E F hf w.states w.initial
  intro i
  have htarget :
      (sboxCarryStep i (wordDigits k₁ i) (c i)
        (w.input i) (w.states i.castSucc)).1 =
        wordDigits ((xor bL aR).rotateRight 11) i := by
    simp only [w.step i]
  have hs := verifySecondCarryEdges_sound k₁ aR bL D E he
    i (w.states i.castSucc) (c i) (w.input i) (hc i) htarget
  simpa only [w.step i] using hs

/-
  Proof-carrying mask domains for grouped wiring.
  Fast UInt16 code proposes masks; the checker uses the proved
  Finset grouped-pruning semantics and proves soundness of a checked trace.
  This section checks grouped pruning. Independently checked carry reductions
  are established in the BackwardMask section below.

  No sorry, axioms, native_decide, or proof by kernel-unsafe evaluation.
-/

/-- Interpret one UInt16 mask by the OLD, trusted finite-set semantics. -/
def maskedDigitSet (A : Array UInt16) (i : Fin 8) : Finset (Fin 16) :=
  Finset.univ.filter (fun v =>
    uint16DomainHas (A.getD i.val 0) v = true)

theorem mem_maskedDigitSet_iff (A : Array UInt16) (i : Fin 8) (v : Fin 16) :
    v ∈ maskedDigitSet A i ↔ uint16DomainHas (A.getD i.val 0) v = true := by
  simp only [maskedDigitSet, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The actual Y/C nibble assignment is contained in both mask arrays. -/
def MaskCovers (D : UInt16BitDomains)
    (c y : Fin 8 → Fin 16) : Prop :=
  (∀ i, uint16DomainHas (D.1.getD i.val 0) (y i) = true) ∧
  (∀ i, uint16DomainHas (D.2.getD i.val 0) (c i) = true)

/-! ### Independent check of the initial masks -/

/-- The SEARCH-SIDE masks must cover ALL values in the proved initial
    nibble-local sets.  This checks every one of 8 × 16 possibilities;
    it does not trust `fastInitialBitDomains` as a proof. -/
def verifyInitialMaskCover (k₀ k₁ aR bL : V 32)
    (D : UInt16BitDomains) : Bool :=
  (List.finRange 8).all fun i =>
    (List.finRange 16).all fun v =>
      (!(decide (v ∈ outputDigitDomain i
          (wordDigits k₀ i) (wordDigits aR i))) ||
        uint16DomainHas (D.1.getD i.val 0) v) &&
      (!(decide (v ∈ inputDiffDigitDomain i
          (wordDigits k₁ i)
          (wordDigits ((xor bL aR).rotateRight 11) i))) ||
        uint16DomainHas (D.2.getD i.val 0) v)

/-- Initial-mask coverage proved without converting large bounded
    quantifiers into an elaborator-level `Decidable` tree. -/
theorem verifyInitialMaskCover_sound
    (k₀ k₁ aR bL : V 32) (D : UInt16BitDomains)
    (h : verifyInitialMaskCover k₀ k₁ aR bL D = true) :
    ∀ i : Fin 8,
      (∀ v ∈ outputDigitDomain i (wordDigits k₀ i) (wordDigits aR i),
        uint16DomainHas (D.1.getD i.val 0) v = true) ∧
      (∀ v ∈ inputDiffDigitDomain i (wordDigits k₁ i)
        (wordDigits ((xor bL aR).rotateRight 11) i),
        uint16DomainHas (D.2.getD i.val 0) v = true) := by
  intro i
  have hi := (List.all_eq_true.mp h) i (by simp)
  constructor
  · intro v hv
    have hb := (List.all_eq_true.mp hi) v (by simp)
    have hb' := (Bool.and_eq_true_iff.mp hb).1
    simpa [hv] using hb'
  · intro v hv
    have hb := (List.all_eq_true.mp hi) v (by simp)
    have hb' := (Bool.and_eq_true_iff.mp hb).2
    simpa [hv] using hb'

/-! ### One sound grouped-wiring mask reduction -/

/-- `next` must contain every value that the proved grouped Finset
    reduction keeps. It is allowed to contain EXTRA values: an
    over-approximation can never create a false contradiction. -/
def verifyGroupedMaskCover (aL : V 32)
    (D next : UInt16BitDomains) : Bool :=
  (List.finRange 8).all fun i =>
    (List.finRange 16).all fun v =>
      (!(decide (v ∈ pruneGroupedOutput aL
          (maskedDigitSet D.1) (maskedDigitSet D.2) i)) ||
        uint16DomainHas (next.1.getD i.val 0) v) &&
      (!(decide (v ∈ pruneGroupedIntermediate aL
          (maskedDigitSet D.1) (maskedDigitSet D.2) i)) ||
        uint16DomainHas (next.2.getD i.val 0) v)

/-- Extraction of one guaranteed-preserved Y/C value from the Boolean
    checker, without unfolding its `decide` instances in the proof. -/
theorem verifyGroupedMaskCover_sound
    (aL : V 32) (D next : UInt16BitDomains)
    (h : verifyGroupedMaskCover aL D next = true)
    (c y : Fin 8 → Fin 16)
    (hw : jointRotationWiring aL c y)
    (hD : MaskCovers D c y) : MaskCovers next c y := by
  have hy : ∀ i, y i ∈ maskedDigitSet D.1 i :=
    fun i => (mem_maskedDigitSet_iff D.1 i (y i)).mpr (hD.1 i)
  have hc : ∀ i, c i ∈ maskedDigitSet D.2 i :=
    fun i => (mem_maskedDigitSet_iff D.2 i (c i)).mpr (hD.2 i)
  have hp := groupedPruning_sound aL
    (maskedDigitSet D.1) (maskedDigitSet D.2)
    c y hw hy hc
  constructor
  · intro i
    have hi := (List.all_eq_true.mp h) i (by simp)
    have hb := (List.all_eq_true.mp hi) (y i) (by simp)
    have hb' := (Bool.and_eq_true_iff.mp hb).1
    simpa [hp.1 i] using hb'
  · intro i
    have hi := (List.all_eq_true.mp h) i (by simp)
    have hb := (List.all_eq_true.mp hi) (c i) (by simp)
    have hb' := (Bool.and_eq_true_iff.mp hb).2
    simpa [hp.2 i] using hb'

/-! ### A separate, Boolean empty-domain checker -/

/-- Directly check that some nibble contains no allowed value.
    Uses only 8 × 16 UInt16 membership tests. -/
def verifyEmptyMaskedDomain (D : UInt16BitDomains) : Bool :=
  (List.finRange 8).any fun i =>
    ((List.finRange 16).all fun v =>
      !(uint16DomainHas (D.1.getD i.val 0) v)) ||
    ((List.finRange 16).all fun v =>
      !(uint16DomainHas (D.2.getD i.val 0) v))

theorem verifyEmptyMaskedDomain_sound (D : UInt16BitDomains) (h : verifyEmptyMaskedDomain D = true)
    (c y : Fin 8 → Fin 16) : ¬MaskCovers D c y := by
  intro hD
  obtain ⟨i, _, hi⟩ := (List.any_eq_true.mp h)
  rcases Bool.or_eq_true_iff.mp hi with hy | hc
  · have hb := (List.all_eq_true.mp hy) (y i) (by simp)
    have hp := hD.1 i
    -- hb is (!X) = true. hp is X = true. We replace X with true:
    rw [hp] at hb
    -- hb is now (!true) = true, which reduces to false = true.
    contradiction
  · have hb := (List.all_eq_true.mp hc) (c i) (by simp)
    have hp := hD.2 i
    rw [hp] at hb
    contradiction

/-! ### Arbitrarily long checked grouped-mask traces -/

/-- Certificates list their successor states. The verifier starts
    from the supplied initial pair, checks EVERY grouped reduction,
    and then demands a genuine empty domain. -/
def verifyGroupedMaskTrace (aL : V 32) :
    UInt16BitDomains → List UInt16BitDomains → Bool
  | D, [] => verifyEmptyMaskedDomain D
  | D, next :: rest =>
      verifyGroupedMaskCover aL D next &&
        verifyGroupedMaskTrace aL next rest

theorem verifyGroupedMaskTrace_sound (aL : V 32) :
    ∀ (D : UInt16BitDomains) (steps : List UInt16BitDomains),
      verifyGroupedMaskTrace aL D steps = true →
        ∀ (c y : Fin 8 → Fin 16), jointRotationWiring aL c y → MaskCovers D c y → False := by
  intro D steps
  induction steps generalizing D with
  | nil =>
    intro h c y _ hD
    exact verifyEmptyMaskedDomain_sound D h c y hD
  | cons next rest ih =>
    intro h c y hw hD
    have h' := Bool.and_eq_true_iff.mp h
    have hnext := verifyGroupedMaskCover_sound aL D next h'.1 c y hw hD
    exact ih next h'.2 c y hw hnext

/-- A fully checked grouped-only certificate rules out the original
    three-round XOR differential. No new cryptographic assumptions. -/
theorem xorDDT_rounds_three_zero_of_maskedGroupedCertificate
    (k₀ k₁ k₂ aL aR bL bR : V 32)
    (D : UInt16BitDomains) (steps : List UInt16BitDomains)
    (hinit : verifyInitialMaskCover k₀ k₁ aR bL D = true)
    (htrace : verifyGroupedMaskTrace aL D steps = true) :
    xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
      (aL, aR) (bL, bR) = 0 := by
  apply xorDDT_rounds_three_zero_of_no_joint_constraint
  rintro ⟨c, y, hjoint⟩
  obtain ⟨hw, hy, hc⟩ :=
    jointCarryConstraint_implies_localDomains
      k₀ k₁ aL aR bL c y hjoint
  have hcover := verifyInitialMaskCover_sound k₀ k₁ aR bL D hinit
  apply verifyGroupedMaskTrace_sound aL D steps htrace c y hw
  exact ⟨(fun i => (hcover i).1 (y i) (hy i)),
         (fun i => (hcover i).2 (c i) (hc i))⟩

/-!
### Empty-mask sanity checks

The examples below prove the fixed results during module compilation. A mask trace
contains grouped steps; carry-value removal uses the separate BackwardMask
checkers. Concrete search-produced masks are exercised in
`Magma/Evidence/02_CarryGroupedPropagation.lean`.
-/

example :
    verifyEmptyMaskedDomain (Array.replicate 8 (0 : UInt16), Array.replicate 8 (0xFFFF : UInt16)) =
      true := by
  decide +kernel

example :
    verifyEmptyMaskedDomain
        (Array.replicate 8 (0xFFFF : UInt16), Array.replicate 8 (0xFFFF : UInt16)) =
      false := by
  decide +kernel

/-- From a genuine 3-round joint assignment, BOTH paths lie inside
    checked forward frontiers. These frontiers were independently
    verified against the original `sboxCarryStep`.

    This supplies the real path's local transitions to the certified
    per-nibble carry-mask reductions below. -/
theorem verifiedJointForwardFrontiers_sound
    (k₀ k₁ aL aR bL : V 32)
    (D : UInt16BitDomains)
    (E₀ E₁ : Array (Array UInt8))
    (F₀ F₁ : Array UInt8)
    (he₀ : verifyFirstCarryEdges k₀ aR D E₀ = true)
    (he₁ : verifySecondCarryEdges k₁ aR bL D E₁ = true)
    (hf₀ : verifyForwardCarryFrontiers E₀ F₀ = true)
    (hf₁ : verifyForwardCarryFrontiers E₁ F₁ = true)
    (c y : Fin 8 → Fin 16)
    (hjoint : jointCarryConstraint k₀ k₁ aL aR bL c y)
    (hcover : MaskCovers D c y) :
    (∃ w : VerifiedCarryPath (wordDigits k₀) (wordDigits aR) y,
      ∀ j : Fin 9,
        carryStateMemFast (F₀.getD j.val 0)
          (checkedCarryIndex (w.states j)) = true) ∧
    (∃ w : VerifiedCarryPath (wordDigits k₁) c
        (wordDigits ((xor bL aR).rotateRight 11)),
      ∀ j : Fin 9,
        carryStateMemFast (F₁.getD j.val 0)
          (checkedCarryIndex (w.states j)) = true) := by
  obtain ⟨⟨w₀⟩, ⟨w₁⟩⟩ :=
    verifiedCarryPaths_of_jointCarryConstraint k₀ k₁ aL aR bL c y hjoint
  constructor
  · exact ⟨w₀, verifiedFirstCarryForward_sound
      k₀ aR D E₀ F₀ he₀ hf₀ y w₀ hcover.1⟩
  · exact ⟨w₁, verifiedSecondCarryForward_sound
      k₁ aR bL D E₁ F₁ he₁ hf₁ c w₁ hcover.2⟩

end Magma.Certificates

namespace Magma.Certificates.BackwardMask

open Magma.Certificates

-- This one proves backward reachability and a checked carry-mask reduction.
-- Fast UInt8/UInt16 functions only PROPOSE witnesses; the checker
-- replays them against original sboxCarryStep through verified edge masks.

/-! ## 1. Independently checked backward frontier closure -/

/-- All four possible terminal carry states must be included, and
    each edge entering B[i+1] must start at a state in B[i]. -/
def verifyBackwardCarryFrontiers
    (E : Array (Array UInt8)) (B : Array UInt8) : Bool :=
  ((List.finRange 2).all fun c₀ =>
    (List.finRange 2).all fun c₁ =>
      carryStateMemFast (B.getD 8 0) (checkedCarryIndex (c₀, c₁))) &&
  ((List.finRange 8).all fun i =>
    (List.finRange 2).all fun a₀ =>
      (List.finRange 2).all fun a₁ =>
        (List.finRange 2).all fun b₀ =>
          (List.finRange 2).all fun b₁ =>
            let s : CarryState := (a₀, a₁)
            let t : CarryState := (b₀, b₁)
            (!checkedCarryEdge E i s t) ||
            (!carryStateMemFast (B.getD (i.val + 1) 0)
                (checkedCarryIndex t)) ||
            carryStateMemFast (B.getD i.val 0)
              (checkedCarryIndex s))

/-- A genuine complete eight-nibble path cannot leave a checked
    backward frontier. Final carries are unrestricted. -/
theorem verifyBackwardCarryFrontiers_sound
    (E : Array (Array UInt8)) (B : Array UInt8)
    (hverified : verifyBackwardCarryFrontiers E B = true)
    (states : Fin 9 → CarryState)
    (hsteps : ∀ i : Fin 8,
      checkedCarryEdge E i (states i.castSucc) (states i.succ) = true) :
    ∀ j : Fin 9,
      carryStateMemFast (B.getD j.val 0)
        (checkedCarryIndex (states j)) = true := by
  unfold verifyBackwardCarryFrontiers at hverified
  obtain ⟨hfinal, hclosed⟩ := Bool.and_eq_true_iff.mp hverified
  have hterminal (s : CarryState) :
      carryStateMemFast (B.getD 8 0) (checkedCarryIndex s) = true := by
    have h₀ := (List.all_eq_true.mp hfinal) s.1 (by simp)
    exact (List.all_eq_true.mp h₀) s.2 (by simp)
  have hback (i : Fin 8) (s t : CarryState)
      (hedge : checkedCarryEdge E i s t = true)
      (hnext : carryStateMemFast (B.getD (i.val + 1) 0)
        (checkedCarryIndex t) = true) :
      carryStateMemFast (B.getD i.val 0)
        (checkedCarryIndex s) = true := by
    have hi := (List.all_eq_true.mp hclosed) i (by simp)
    have h₀ := (List.all_eq_true.mp hi) s.1 (by simp)
    have h₁ := (List.all_eq_true.mp h₀) s.2 (by simp)
    have h₂ := (List.all_eq_true.mp h₁) t.1 (by simp)
    have h₃ := (List.all_eq_true.mp h₂) t.2 (by simp)
    dsimp only at h₃
    simp only [Bool.or_eq_true_iff] at h₃
    rcases h₃ with (hnoedge | hnonext) | hyes
    · rw [hedge] at hnoedge
      contradiction
    · rw [hnext] at hnonext
      contradiction
    · exact hyes
  have aux : ∀ n : Nat, (hn : n ≤ 8) →
      carryStateMemFast (B.getD (8 - n) 0)
        (checkedCarryIndex (states (⟨8 - n, by omega⟩ : Fin 9))) = true := by
    intro n
    induction n with
    | zero =>
        intro _
        simpa only [Nat.sub_zero] using
          (hterminal (states (⟨8, by omega⟩ : Fin 9)))
    | succ n ih =>
        intro hn
        let i : Fin 8 := ⟨7 - n, by omega⟩
        have hindexN : i.val + 1 = 8 - n := by
          dsimp [i]
          omega
        have hstateN : i.succ = (⟨8 - n, by omega⟩ : Fin 9) := by
          apply Fin.ext
          simpa only [Fin.val_succ] using hindexN
        have hnext :
            carryStateMemFast (B.getD (i.val + 1) 0)
              (checkedCarryIndex (states i.succ)) = true := by
          simpa only [hindexN, hstateN] using ih (by omega)
        have hprev := hback i (states i.castSucc) (states i.succ)
          (hsteps i) hnext
        have hindexP : i.val = 8 - (n + 1) := by
          dsimp [i]
          omega
        have hstateP :
            i.castSucc = (⟨8 - (n + 1), by omega⟩ : Fin 9) := by
          apply Fin.ext
          simpa only [Fin.val_castSucc] using hindexP
        simpa only [hindexP, hstateP] using hprev
  intro j
  have hj := aux (8 - j.val) (by omega)
  have hindex : 8 - (8 - j.val) = j.val := by omega
  have hstate :
      (⟨8 - (8 - j.val), by omega⟩ : Fin 9) = j := by
    apply Fin.ext
    exact hindex
  simpa only [hindex, hstate] using hj

/-! ## 2. Derive original edges locally (without using private
     declarations of the preceding module, so this file can later be imported). -/

private theorem firstEdge_of_check (k₀ aR : V 32) (D : UInt16BitDomains) (E : Array (Array UInt8))
    (he : verifyFirstCarryEdges k₀ aR D E = true) (i : Fin 8) (s : CarryState) (x : Fin 16)
    (hmem :
      uint16DomainHas (D.1.getD i.val 0)
          (sboxCarryStep i (wordDigits k₀ i) (wordDigits aR i) x s).1 =
        true) :
    checkedCarryEdge E i s (sboxCarryStep i (wordDigits k₀ i) (wordDigits aR i) x s).2 = true := by
  unfold verifyFirstCarryEdges at he
  have hi := (List.all_eq_true.mp he) i (by simp)
  have h₀ := (List.all_eq_true.mp hi) s.1 (by simp)
  have h₁ := (List.all_eq_true.mp h₀) s.2 (by simp)
  have hx := (List.all_eq_true.mp h₁) x (by simp)
  dsimp only at hx
  simp only [Bool.or_eq_true_iff] at hx
  rcases hx with hbad | hedge
  · rw [hmem] at hbad
    contradiction
  · exact hedge

private theorem secondEdge_of_check (k₁ aR bL : V 32) (D : UInt16BitDomains)
    (E : Array (Array UInt8)) (he : verifySecondCarryEdges k₁ aR bL D E = true) (i : Fin 8)
    (s : CarryState) (c x : Fin 16) (hmem : uint16DomainHas (D.2.getD i.val 0) c = true)
    (htarget :
      (sboxCarryStep i (wordDigits k₁ i) c x s).1 = wordDigits ((xor bL aR).rotateRight 11) i) :
    checkedCarryEdge E i s (sboxCarryStep i (wordDigits k₁ i) c x s).2 = true := by
  unfold verifySecondCarryEdges at he
  have hi := (List.all_eq_true.mp he) i (by simp)
  have h₀ := (List.all_eq_true.mp hi) s.1 (by simp)
  have h₁ := (List.all_eq_true.mp h₀) s.2 (by simp)
  have hc := (List.all_eq_true.mp h₁) c (by simp)
  have hx := (List.all_eq_true.mp hc) x (by simp)
  dsimp only at hx
  simp only [Bool.or_eq_true_iff] at hx
  rcases hx with hbad | hrest
  · rw [hmem] at hbad
    contradiction
  · rcases hrest with hbad | hedge
    · simp [htarget] at hbad
    · exact hedge

/-! ## 3. Both actual carry paths remain in checked backward frontiers -/

theorem verifiedFirstCarryBackward_sound (k₀ aR : V 32) (D : UInt16BitDomains)
    (E : Array (Array UInt8)) (B : Array UInt8) (he : verifyFirstCarryEdges k₀ aR D E = true)
    (hb : verifyBackwardCarryFrontiers E B = true) (y : Fin 8 → Fin 16)
    (w : VerifiedCarryPath (wordDigits k₀) (wordDigits aR) y)
    (hy : ∀ i, uint16DomainHas (D.1.getD i.val 0) (y i) = true) :
    ∀ j : Fin 9, carryStateMemFast (B.getD j.val 0) (checkedCarryIndex (w.states j)) = true := by
  apply verifyBackwardCarryFrontiers_sound E B hb w.states
  intro i
  have hmem :
    uint16DomainHas (D.1.getD i.val 0)
        (sboxCarryStep i (wordDigits k₀ i) (wordDigits aR i) (w.input i) (w.states i.castSucc)).1 =
      true := by
    simpa only [w.step i] using hy i
  have hs := firstEdge_of_check k₀ aR D E he i (w.states i.castSucc) (w.input i) hmem
  simpa only [w.step i] using hs

theorem verifiedSecondCarryBackward_sound (k₁ aR bL : V 32) (D : UInt16BitDomains)
    (E : Array (Array UInt8)) (B : Array UInt8) (he : verifySecondCarryEdges k₁ aR bL D E = true)
    (hb : verifyBackwardCarryFrontiers E B = true) (c : Fin 8 → Fin 16)
    (w : VerifiedCarryPath (wordDigits k₁) c (wordDigits ((xor bL aR).rotateRight 11)))
    (hc : ∀ i, uint16DomainHas (D.2.getD i.val 0) (c i) = true) :
    ∀ j : Fin 9, carryStateMemFast (B.getD j.val 0) (checkedCarryIndex (w.states j)) = true := by
  apply verifyBackwardCarryFrontiers_sound E B hb w.states
  intro i
  have htarget :
    (sboxCarryStep i (wordDigits k₁ i) (c i) (w.input i) (w.states i.castSucc)).1 =
      wordDigits ((xor bL aR).rotateRight 11) i := by
    simp only [w.step i]
  have hs :=
    secondEdge_of_check k₁ aR bL D E he i (w.states i.castSucc) (c i) (w.input i) (hc i) htarget
  simpa only [w.step i] using hs

/-! ## 3. Independent local checkers for reductions proposed by UInt16 DP -/

/-- First machine: if an old domain value lies on an F-to-B edge,
    it must still appear in the proposed next domain. -/
def verifyFirstCarryMaskCover (k₀ aR : V 32)
    (D next : UInt16BitDomains)
    (F B : Array UInt8) : Bool :=
  (List.finRange 8).all fun i =>
    (List.finRange 2).all fun c₀ =>
      (List.finRange 2).all fun c₁ =>
        (List.finRange 16).all fun x =>
          let s : CarryState := (c₀, c₁)
          let step := sboxCarryStep i
            (wordDigits k₀ i) (wordDigits aR i) x s
          (!carryStateMemFast (F.getD i.val 0) (checkedCarryIndex s)) ||
          (!carryStateMemFast (B.getD (i.val + 1) 0)
            (checkedCarryIndex step.2)) ||
          (!uint16DomainHas (D.1.getD i.val 0) step.1) ||
          uint16DomainHas (next.1.getD i.val 0) step.1

/-- Second machine: the input difference is variable while the output
    difference must equal the fixed round-2 target nibble. -/
def verifySecondCarryMaskCover (k₁ aR bL : V 32)
    (D next : UInt16BitDomains)
    (F B : Array UInt8) : Bool :=
  (List.finRange 8).all fun i =>
    (List.finRange 2).all fun c₀ =>
      (List.finRange 2).all fun c₁ =>
        (List.finRange 16).all fun d =>
          (List.finRange 16).all fun x =>
            let s : CarryState := (c₀, c₁)
            let step := sboxCarryStep i (wordDigits k₁ i) d x s
            (!carryStateMemFast (F.getD i.val 0) (checkedCarryIndex s)) ||
            (!carryStateMemFast (B.getD (i.val + 1) 0)
              (checkedCarryIndex step.2)) ||
            (!uint16DomainHas (D.2.getD i.val 0) d) ||
            (!(decide (step.1 =
              wordDigits ((xor bL aR).rotateRight 11) i))) ||
            uint16DomainHas (next.2.getD i.val 0) d

private theorem verifyFirstCarryMaskCover_sound (k₀ aR : V 32) (D next : UInt16BitDomains)
    (F B : Array UInt8) (h : verifyFirstCarryMaskCover k₀ aR D next F B = true) (i : Fin 8)
    (s : CarryState) (x : Fin 16)
    (hf : carryStateMemFast (F.getD i.val 0) (checkedCarryIndex s) = true)
    (hb :
      carryStateMemFast (B.getD (i.val + 1) 0)
          (checkedCarryIndex (sboxCarryStep i (wordDigits k₀ i) (wordDigits aR i) x s).2) =
        true)
    (hd :
      uint16DomainHas (D.1.getD i.val 0)
          (sboxCarryStep i (wordDigits k₀ i) (wordDigits aR i) x s).1 =
        true) :
    uint16DomainHas (next.1.getD i.val 0)
        (sboxCarryStep i (wordDigits k₀ i) (wordDigits aR i) x s).1 =
      true := by
  have hi := (List.all_eq_true.mp h) i (by simp)
  have h₀ := (List.all_eq_true.mp hi) s.1 (by simp)
  have h₁ := (List.all_eq_true.mp h₀) s.2 (by simp)
  have hx := (List.all_eq_true.mp h₁) x (by simp)
  dsimp only at hx
  simp only [Bool.or_eq_true_iff] at hx
  rcases hx with ((hnoF | hnoB) | hnoD) | hyes
  · rw [hf] at hnoF
    contradiction
  · rw [hb] at hnoB
    contradiction
  · rw [hd] at hnoD
    contradiction
  · exact hyes

private theorem verifySecondCarryMaskCover_sound (k₁ aR bL : V 32) (D next : UInt16BitDomains)
    (F B : Array UInt8) (h : verifySecondCarryMaskCover k₁ aR bL D next F B = true) (i : Fin 8)
    (s : CarryState) (d x : Fin 16)
    (hf : carryStateMemFast (F.getD i.val 0) (checkedCarryIndex s) = true)
    (hb :
      carryStateMemFast (B.getD (i.val + 1) 0)
          (checkedCarryIndex (sboxCarryStep i (wordDigits k₁ i) d x s).2) =
        true)
    (hd : uint16DomainHas (D.2.getD i.val 0) d = true)
    (ht : (sboxCarryStep i (wordDigits k₁ i) d x s).1 = wordDigits ((xor bL aR).rotateRight 11) i) :
    uint16DomainHas (next.2.getD i.val 0) d = true := by
  have hi := (List.all_eq_true.mp h) i (by simp)
  have h₀ := (List.all_eq_true.mp hi) s.1 (by simp)
  have h₁ := (List.all_eq_true.mp h₀) s.2 (by simp)
  have hd' := (List.all_eq_true.mp h₁) d (by simp)
  have hx := (List.all_eq_true.mp hd') x (by simp)
  dsimp only at hx
  simp only [Bool.or_eq_true_iff] at hx
  rcases hx with (((hnoF | hnoB) | hnoD) | hnoTarget) | hyes
  · rw [hf] at hnoF
    contradiction
  · rw [hb] at hnoB
    contradiction
  · rw [hd] at hnoD
    contradiction
  · simp [ht] at hnoTarget
  · exact hyes

/-! ## 4. One certified simultaneous reduction of both mask families -/

structure CarryReductionCertificate where
  edges₀ : Array (Array UInt8)
  edges₁ : Array (Array UInt8)
  forward₀ : Array UInt8
  forward₁ : Array UInt8
  backward₀ : Array UInt8
  backward₁ : Array UInt8
  next : UInt16BitDomains

def verifyCarryReduction (k₀ k₁ aR bL : V 32) (D : UInt16BitDomains)
    (cert : CarryReductionCertificate) : Bool :=
  verifyFirstCarryEdges k₀ aR D cert.edges₀ && verifySecondCarryEdges k₁ aR bL D cert.edges₁ &&
    verifyForwardCarryFrontiers cert.edges₀ cert.forward₀ &&
    verifyForwardCarryFrontiers cert.edges₁ cert.forward₁ &&
    verifyBackwardCarryFrontiers cert.edges₀ cert.backward₀ &&
    verifyBackwardCarryFrontiers cert.edges₁ cert.backward₁ &&
    verifyFirstCarryMaskCover k₀ aR D cert.next cert.forward₀ cert.backward₀ &&
    verifySecondCarryMaskCover k₁ aR bL D cert.next cert.forward₁ cert.backward₁

/-- The expensive semantic bridge: no actual jointCarryConstraint
    assignment covered by D is removed by an accepted carry reduction. -/
theorem verifyCarryReduction_sound
    (k₀ k₁ aL aR bL : V 32)
    (D : UInt16BitDomains) (cert : CarryReductionCertificate)
    (hverified : verifyCarryReduction k₀ k₁ aR bL D cert = true)
    (c y : Fin 8 → Fin 16)
    (hjoint : jointCarryConstraint k₀ k₁ aL aR bL c y)
    (hD : MaskCovers D c y) :
    MaskCovers cert.next c y := by
  simp only [verifyCarryReduction, Bool.and_eq_true_iff] at hverified
  rcases hverified with
    ⟨⟨⟨⟨⟨⟨⟨he₀, he₁⟩, hf₀⟩, hf₁⟩, hb₀⟩, hb₁⟩, hm₀⟩, hm₁⟩
  obtain ⟨⟨w₀, hwf₀⟩, ⟨w₁, hwf₁⟩⟩ :=
    verifiedJointForwardFrontiers_sound
      k₀ k₁ aL aR bL D
      cert.edges₀ cert.edges₁ cert.forward₀ cert.forward₁
      he₀ he₁ hf₀ hf₁ c y hjoint hD
  have hwb₀ := verifiedFirstCarryBackward_sound
    k₀ aR D cert.edges₀ cert.backward₀ he₀ hb₀ y w₀ hD.1
  have hwb₁ := verifiedSecondCarryBackward_sound
    k₁ aR bL D cert.edges₁ cert.backward₁ he₁ hb₁ c w₁ hD.2
  constructor
  · intro i
    have hold :
        uint16DomainHas (D.1.getD i.val 0)
          (sboxCarryStep i (wordDigits k₀ i) (wordDigits aR i)
            (w₀.input i) (w₀.states i.castSucc)).1 = true := by
      simpa only [w₀.step i] using hD.1 i
    have hnext := verifyFirstCarryMaskCover_sound
      k₀ aR D cert.next cert.forward₀ cert.backward₀ hm₀
      i (w₀.states i.castSucc) (w₀.input i)
      (hwf₀ i.castSucc) (by simpa only [Fin.val_succ, w₀.step i] using hwb₀ i.succ)
      hold
    simpa only [w₀.step i] using hnext
  · intro i
    have htarget :
        (sboxCarryStep i (wordDigits k₁ i) (c i)
          (w₁.input i) (w₁.states i.castSucc)).1 =
          wordDigits ((xor bL aR).rotateRight 11) i := by
      simp only [w₁.step i]
    have hnext := verifySecondCarryMaskCover_sound
      k₁ aR bL D cert.next cert.forward₁ cert.backward₁ hm₁
      i (w₁.states i.castSucc) (c i) (w₁.input i)
      (hwf₁ i.castSucc)
      (by simpa only [Fin.val_succ, w₁.step i] using hwb₁ i.succ)
      (hD.2 i) htarget
    exact hnext

/-! ## 5. Fast concrete proposal: first carry reduction plus grouped wiring -/

/-- Useful for checking the previously observed impossible candidate.
    A checked carry step is followed by the ALREADY VERIFIED grouped step. -/
def verifyOneCarryThenGrouped
    (k₀ k₁ aL aR bL : V 32)
    (D : UInt16BitDomains)
    (cert : CarryReductionCertificate)
    (next : UInt16BitDomains) : Bool :=
  verifyCarryReduction k₀ k₁ aR bL D cert &&
  verifyGroupedMaskCover aL cert.next next &&
  verifyEmptyMaskedDomain next

/-- If one checked carry reduction followed by one checked grouped
    reduction is contradictory, the corresponding three-round DDT is zero. -/
theorem xorDDT_rounds_three_zero_of_checkedCarryGrouped
    (k₀ k₁ k₂ aL aR bL bR : V 32)
    (D : UInt16BitDomains)
    (cert : CarryReductionCertificate)
    (next : UInt16BitDomains)
    (hinit : verifyInitialMaskCover k₀ k₁ aR bL D = true)
    (hchecked : verifyOneCarryThenGrouped
      k₀ k₁ aL aR bL D cert next = true) :
    xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
      (aL, aR) (bL, bR) = 0 := by
  apply xorDDT_rounds_three_zero_of_no_joint_constraint
  rintro ⟨c, y, hjoint⟩
  simp only [verifyOneCarryThenGrouped, Bool.and_eq_true_iff] at hchecked
  rcases hchecked with ⟨⟨hcarry, hgroup⟩, hempty⟩
  obtain ⟨hw, hy, hc⟩ :=
    jointCarryConstraint_implies_localDomains
      k₀ k₁ aL aR bL c y hjoint
  have hinit' := verifyInitialMaskCover_sound k₀ k₁ aR bL D hinit
  have hD : MaskCovers D c y :=
    ⟨(fun i => (hinit' i).1 (y i) (hy i)),
     (fun i => (hinit' i).2 (c i) (hc i))⟩
  have hC := verifyCarryReduction_sound
    k₀ k₁ aL aR bL D cert hcarry c y hjoint hD
  have hG := verifyGroupedMaskCover_sound
    aL cert.next next hgroup c y hw hC
  exact verifyEmptyMaskedDomain_sound next hempty c y hG

end Magma.Certificates.BackwardMask

namespace Magma.Certificates.FastInitialCheck

open Magma.Certificates.BackwardMask

/-!
## Transition-based verification of initial UInt16 masks

Enumerate the original `sboxCarryStep` transitions and check that the proposed
masks cover them. Acceptance implies the original `verifyInitialMaskCover`
condition for all inputs. This does not assert universal equality between
`fastInitialBitDomains` and the original finite-set domains. Carry and grouped
certificate formats, their checkers, and their soundness theorem are reused.
-/

/-! ## 1. Enumerate source transitions, not nested `Decidable` witnesses -/

/-- Every genuine first-machine local transition has its output value
    in the corresponding proposed UInt16 mask. -/
def verifyFirstInitialCoverBySteps
    (k₀ aR : V 32) (D : UInt16BitDomains) : Bool :=
  (List.finRange 8).all fun i =>
    (List.finRange 2).all fun c₀ =>
      (List.finRange 2).all fun c₁ =>
        (List.finRange 16).all fun x =>
          uint16DomainHas (D.1.getD i.val 0)
            (sboxCarryStep i (wordDigits k₀ i) (wordDigits aR i)
              x (c₀, c₁)).1

/-- For the second machine, only transitions producing the prescribed
    target difference impose a membership obligation on the input difference. -/
def verifySecondInitialCoverBySteps
    (k₁ aR bL : V 32) (D : UInt16BitDomains) : Bool :=
  let target := (xor bL aR).rotateRight 11
  (List.finRange 8).all fun i =>
    (List.finRange 16).all fun d =>
      (List.finRange 2).all fun c₀ =>
        (List.finRange 2).all fun c₁ =>
          (List.finRange 16).all fun x =>
            let step := sboxCarryStep i (wordDigits k₁ i) d x (c₀, c₁)
            (!(decide (step.1 = wordDigits target i))) ||
              uint16DomainHas (D.2.getD i.val 0) d

/-- A cheap source-semantics check for the two initial mask arrays. -/
def verifyInitialCoverBySteps
    (k₀ k₁ aR bL : V 32) (D : UInt16BitDomains) : Bool :=
  verifyFirstInitialCoverBySteps k₀ aR D &&
    verifySecondInitialCoverBySteps k₁ aR bL D

/-! ## 2. Boolean reflection without unfolding large Decidable instances -/

private theorem firstStep_mem (k₀ aR : V 32) (D : UInt16BitDomains)
    (h : verifyFirstInitialCoverBySteps k₀ aR D = true) (i : Fin 8) (s : CarryState) (x : Fin 16) :
    uint16DomainHas (D.1.getD i.val 0) (sboxCarryStep i (wordDigits k₀ i) (wordDigits aR i) x s).1 =
      true := by
  unfold verifyFirstInitialCoverBySteps at h
  have hi := (List.all_eq_true.mp h) i (by simp)
  have h₀ := (List.all_eq_true.mp hi) s.1 (by simp)
  have h₁ := (List.all_eq_true.mp h₀) s.2 (by simp)
  exact (List.all_eq_true.mp h₁) x (by simp)

private theorem secondStep_mem (k₁ aR bL : V 32) (D : UInt16BitDomains)
    (h : verifySecondInitialCoverBySteps k₁ aR bL D = true) (i : Fin 8) (s : CarryState)
    (d x : Fin 16)
    (htarget :
      (sboxCarryStep i (wordDigits k₁ i) d x s).1 = wordDigits ((xor bL aR).rotateRight 11) i) :
    uint16DomainHas (D.2.getD i.val 0) d = true := by
  unfold verifySecondInitialCoverBySteps at h
  dsimp only at h
  have hi := (List.all_eq_true.mp h) i (by simp)
  have hd := (List.all_eq_true.mp hi) d (by simp)
  have h₀ := (List.all_eq_true.mp hd) s.1 (by simp)
  have h₁ := (List.all_eq_true.mp h₀) s.2 (by simp)
  have hx := (List.all_eq_true.mp h₁) x (by simp)
  simp only [Bool.or_eq_true_iff] at hx
  rcases hx with hbad | hgood
  · simp [htarget] at hbad
  · exact hgood

/-! ## 3. Universal coverage of the *original* Finset local domains -/

private theorem firstCover_sound (k₀ aR : V 32) (D : UInt16BitDomains)
    (h : verifyFirstInitialCoverBySteps k₀ aR D = true) (i : Fin 8) (v : Fin 16)
    (hv : v ∈ outputDigitDomain i (wordDigits k₀ i) (wordDigits aR i)) :
    uint16DomainHas (D.1.getD i.val 0) v = true := by
  have hp := (Finset.mem_filter.mp hv).2
  obtain ⟨s, t, x, hstep⟩ := (decide_eq_true_eq).mp hp
  have hfound := firstStep_mem k₀ aR D h i s x
  have hout : (sboxCarryStep i (wordDigits k₀ i) (wordDigits aR i) x s).1 = v :=
    congrArg Prod.fst hstep
  simpa only [hout] using hfound

private theorem secondCover_sound (k₁ aR bL : V 32) (D : UInt16BitDomains)
    (h : verifySecondInitialCoverBySteps k₁ aR bL D = true) (i : Fin 8) (d : Fin 16)
    (hd :
      d ∈ inputDiffDigitDomain i (wordDigits k₁ i) (wordDigits ((xor bL aR).rotateRight 11) i)) :
    uint16DomainHas (D.2.getD i.val 0) d = true := by
  have hp := (Finset.mem_filter.mp hd).2
  obtain ⟨s, t, x, hstep⟩ := (decide_eq_true_eq).mp hp
  have htarget :
    (sboxCarryStep i (wordDigits k₁ i) d x s).1 = wordDigits ((xor bL aR).rotateRight 11) i :=
    congrArg Prod.fst hstep
  exact secondStep_mem k₁ aR bL D h i s d x htarget

/-- Universal semantic soundness: the fast checker covers EVERY member
    of both original Finset-domain families, for ALL 32-bit inputs. -/
theorem verifyInitialCoverBySteps_sound
    (k₀ k₁ aR bL : V 32) (D : UInt16BitDomains)
    (h : verifyInitialCoverBySteps k₀ k₁ aR bL D = true) :
    ∀ i : Fin 8,
      (∀ v ∈ outputDigitDomain i (wordDigits k₀ i) (wordDigits aR i),
        uint16DomainHas (D.1.getD i.val 0) v = true) ∧
      (∀ v ∈ inputDiffDigitDomain i (wordDigits k₁ i)
        (wordDigits ((xor bL aR).rotateRight 11) i),
        uint16DomainHas (D.2.getD i.val 0) v = true) := by
  obtain ⟨hfirst, hsecond⟩ := Bool.and_eq_true_iff.mp h
  intro i
  exact ⟨fun v hv => firstCover_sound k₀ aR D hfirst i v hv,
    fun d hd => secondCover_sound k₁ aR bL D hsecond i d hd⟩

/-- IMPORTANT: an accepted fast transition checker logically implies
    acceptance by the PREVIOUS, expensive initial Finset checker.
    This theorem does NOT execute the old checker. -/
theorem verifyInitialMaskCover_of_steps
    (k₀ k₁ aR bL : V 32) (D : UInt16BitDomains)
    (h : verifyInitialCoverBySteps k₀ k₁ aR bL D = true) :
    verifyInitialMaskCover k₀ k₁ aR bL D = true := by
  have hc := verifyInitialCoverBySteps_sound k₀ k₁ aR bL D h
  unfold verifyInitialMaskCover
  apply List.all_eq_true.mpr
  intro i _
  apply List.all_eq_true.mpr
  intro v _
  apply Bool.and_eq_true_iff.mpr
  constructor
  · by_cases hp : v ∈ outputDigitDomain i (wordDigits k₀ i) (wordDigits aR i)
    · have hm := (hc i).1 v hp
      simpa only [hp, decide_true, Bool.not_true, Bool.false_or] using hm
    · simp [hp]
  · by_cases hp : v ∈ inputDiffDigitDomain i (wordDigits k₁ i)
        (wordDigits ((xor bL aR).rotateRight 11) i)
    · have hm := (hc i).2 v hp
      simpa only [hp, decide_true, Bool.not_true, Bool.false_or] using hm
    · simp [hp]

/-! ## 4. Reuse the existing trusted carry + grouped theorem unchanged -/

/-- Final zero-DDT result with a fast initial-mask checker.
    The previous carry and grouped certificate checking stays unchanged. -/
theorem xorDDT_rounds_three_zero_of_checkedCarryGrouped_fastInit
    (k₀ k₁ k₂ aL aR bL bR : V 32)
    (D : UInt16BitDomains)
    (cert : CarryReductionCertificate)
    (next : UInt16BitDomains)
    (hinit : verifyInitialCoverBySteps k₀ k₁ aR bL D = true)
    (hchecked : verifyOneCarryThenGrouped
      k₀ k₁ aL aR bL D cert next = true) :
    xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
      (aL, aR) (bL, bR) = 0 := by
  exact xorDDT_rounds_three_zero_of_checkedCarryGrouped
    k₀ k₁ k₂ aL aR bL bR D cert next
    (verifyInitialMaskCover_of_steps k₀ k₁ aR bL D hinit) hchecked

end Magma.Certificates.FastInitialCheck
