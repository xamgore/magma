module
import all Init.Data.Range.Basic
public import Magma.Differential.FiveRounds.PairedCarryRefutation

@[expose] public section

/-!
# Eagerly cached local S-box/carry transition tables

Precompute eight nibble positions × sixteen output digits × four
incoming pair-carry states, once for each boundary difference.
The cached refuter is proven pointwise equal to the earlier certified
paired-frontier refuter.
-/

namespace Magma.DiffanCachedPairedCarry

open Magma
open Magma.CarryAutomaton
open Magma.DiffanPairedCarryRefutation
open Magma.DiffanKeyFreeCarryAutomaton
open Magma.DiffanFiveRoundCoreDefect
open Magma.MultiRoundDDT

private abbrev Word :=
  V 32

private abbrev Digits :=
  Fin 8 → Fin 16

private abbrev Frontier :=
  Finset CarryState

private abbrev Table :=
  Vector (Vector (Vector Frontier 4) 16) 8

def decode (q : Fin 4) : CarryState :=
  (⟨q.val % 2, by omega⟩, ⟨q.val / 2, by omega⟩)

def encode (s : CarryState) : Fin 4 :=
  ⟨s.1.val + 2 * s.2.val, by omega⟩

theorem decode_encode (s : CarryState) : decode (encode s) = s := by
  rcases s with ⟨a, b⟩
  fin_cases a <;> fin_cases b <;> decide

def buildTable (d : Word) : Table :=
  Vector.ofFn fun i =>
    Vector.ofFn fun v =>
      Vector.ofFn fun q =>
        (Finset.univ : Finset CarryState).filter fun t =>
          ∃ k x : Fin 16, sboxCarryStep i k (wordDigits d i) x (decode q) = (v, t)

def fastFrontierStep (tab : Table) (i : Fin 8) (v : Fin 16) (prior : Frontier) : Frontier :=
  prior.biUnion fun s => ((tab.get i).get v).get (encode s)

/-- Cached lookup is definitionally equivalent to the verified
    existential search over local key and base nibbles. -/
theorem cachedStep_eq_frontierStep (d : Word) (i : Fin 8)
    (v : Fin 16) (prior : Frontier) :
    fastFrontierStep (buildTable d) i v prior =
      frontierStep i (wordDigits d i) v prior := by
  ext t
  simp only [fastFrontierStep, Finset.mem_biUnion, frontierStep,
    Finset.mem_filter, Finset.mem_univ, true_and]
  simp only [buildTable, Vector.get_ofFn, decode_encode,
    Finset.mem_filter, Finset.mem_univ, true_and]

def cachedCheck (a s : Word) (ta ts : Table) (n : Nat) (bits : Digits) (ra rs : Frontier) :
    Nat → Bool
  | 0 => !(keyFreePossible (rot11 (packDigits bits)) (xor s a))
  | fuel + 1 =>
    if hn : n < 8 then
      (List.finRange 16).all fun v =>
        let ra' := fastFrontierStep ta ⟨n, hn⟩ v ra
        let rs' := fastFrontierStep ts ⟨n, hn⟩ v rs
        if decide (ra'.Nonempty ∧ rs'.Nonempty) then
          cachedCheck a s ta ts (n + 1) (Function.update bits ⟨n, hn⟩ v) ra' rs' fuel
        else true
    else !(keyFreePossible (rot11 (packDigits bits)) (xor s a))

def cachedRefutes (a s : Word) : Bool :=
  let ta := buildTable a
  let ts := buildTable s
  cachedCheck a s ta ts 0 (fun _ => 0) initialFrontier initialFrontier 8

theorem cachedCheck_eq (a s : Word) (n : Nat) (bits : Digits) (ra rs : Frontier) (fuel : Nat) :
    cachedCheck a s (buildTable a) (buildTable s) n bits ra rs fuel =
      pairedCheck a s n bits ra rs fuel := by
  induction fuel generalizing n bits ra rs with
  | zero => rfl
  | succ fuel ih =>
    unfold cachedCheck pairedCheck
    by_cases hn : n < 8
    · simp only [dite_eq_left hn]
      simp only [cachedStep_eq_frontierStep, ih]
    · simp only [dite_eq_right hn]

theorem cachedRefutes_eq (a s : Word) : cachedRefutes a s = refutesTriple a s := by
  exact cachedCheck_eq a s 0 (fun _ => 0) initialFrontier initialFrontier 8

/-- A cached refutation has the same proved five-round semantic
    interpretation as the uncached reference algorithm. -/
theorem cachedRefutes_sound
    (a s : Word) (h : cachedRefutes a s = true)
    (k₀ k₁ k₂ k₃ k₄ : Word) :
    xorDDT_rounds 5 (fiveRoundKeys k₀ k₁ k₂ k₃ k₄)
      (a, 0#32) (0#32, s) = 0 :=
  refutesTriple_sound a s ((cachedRefutes_eq a s).symm ▸ h)
    k₀ k₁ k₂ k₃ k₄

/-- The same one-hot upper-triangular certificate, with each cell
    computed using shared eager local transition tables. -/
def cachedOneHotHalfCertificate : Bool :=
  (List.finRange 32).all fun i =>
    (List.finRange 32).all fun j =>
      if i.val ≤ j.val then
        cachedRefutes
          (Magma.DiffanFiveRoundUniversalSupport.oneHotDifference i)
          (Magma.DiffanFiveRoundUniversalSupport.oneHotDifference j)
      else true

theorem cachedOneHotHalfCertificate_eq :
    cachedOneHotHalfCertificate = Magma.DiffanPairedCarryRefutation.oneHotHalfCertificate := by
  simp only [cachedOneHotHalfCertificate, Magma.DiffanPairedCarryRefutation.oneHotHalfCertificate,
    cachedRefutes_eq]

/-- A successful complete cached certificate proves the one-hot
    theorem directly, not just a family of individual SAT statuses. -/
theorem universal_oneHot_of_cached_certificate
    (h : cachedOneHotHalfCertificate = true)
    (k₀ k₁ k₂ k₃ k₄ : Word) (i j : Fin 32) :
    xorDDT_rounds 5 (fiveRoundKeys k₀ k₁ k₂ k₃ k₄)
      (Magma.DiffanFiveRoundUniversalSupport.oneHotDifference i, 0#32)
      (0#32, Magma.DiffanFiveRoundUniversalSupport.oneHotDifference j) = 0 :=
  Magma.DiffanPairedCarryRefutation.universal_oneHot_of_half_certificate
    (cachedOneHotHalfCertificate_eq ▸ h) k₀ k₁ k₂ k₃ k₄ i j

end Magma.DiffanCachedPairedCarry
