module

public import Magma.DDT.TwoHot.OutputOne.Exact.OutputOneSevenExactCounts
public import Magma.Search.FastSearch
meta import Magma.DDT.TwoHot.OutputOne.Exact.OutputOneSevenExactCounts
meta import Magma.Search.FastSearch
import all Init.Data.Range.Basic
import Magma.DDT.TwoHot.OutputOne.Exact.OutputOneSevenExactCounts
import Magma.Search.FastSearch

@[expose] public section

/-!
Evidence 21, fast executable DP-vs-formula regression (single scan).

Algorithmic optimization:
  * Old DP: 4x4 transition matrix, each entry scans all 16 inputs.
  * New DP: for each of 4 current states, scan 16 inputs ONCE;
            the resulting next state is deterministic.
  * Counts are stored as 4 Nat values in an Array.
  * S-box tables and the fast carry step are REUSED from Magma.FastSearch.

This is executable regression evidence, NOT a proof of the universal
`sevenWeightFiberBridge` theorem. The fast transition semantics can be
proved separately against `sboxCarryStep` and `carryDPCount`.

-/

namespace Magma.Evidence.TwoHotDPAgreementFast

open Magma
open Magma.CarryAutomaton
open Magma.FastSearch
open Magma.TwoHotOutputOneFirstActive
open Magma.TwoHotOutputOneSevenLocal
open Magma.TwoHotOutputOneSevenExactCounts

private abbrev Word :=
  V 32

private abbrev PairBits :=
  Fin 32 × Fin 32

/-- Computable enumeration of exactly `sevenPairs`, without repetitions. -/
private def regressionPairs : List PairBits :=
  [(20, 21), (20, 22), (20, 23), (21, 22), (21, 23), (22, 23), (23, 24)]

private theorem regressionPairs_correct :
    regressionPairs.toFinset = sevenPairs ∧ regressionPairs.Nodup := by decide +kernel

/-- Executable four-state path counter, using 16 deterministic input
    digits per source carry state instead of a 4x4 matrix of Finsets. -/
def fastFourStateCount (k : Word) (p : PairBits) : Nat := Id.run do
  let boxes := fastSboxTables
  let inputDiff := twoHot p.1 p.2
  let outputDiff : Word := 0x00200000#32
  let mut row : Array Nat := #[1, 0, 0, 0]
  for index in [:8] do
    let i : Fin 8 := Fin.ofNat 8 index
    let box := boxes.getD index #[]
    let keyDigit := (wordDigits k i).val
    let inDigit := (wordDigits inputDiff i).val
    let outDigit := (wordDigits outputDiff i).val
    let mut next : Array Nat := #[0, 0, 0, 0]
    for state in [:4] do
      let count := row.getD state 0
      if count != 0 then
        for x in [:16] do
          let (out, nextState) :=
            fastSboxCarryStep box keyDigit inDigit x state
          if out == outDigit then
            next := next.set! nextState
              ((next.getD nextState 0) + count)
    row := next
  return row.foldl (fun acc n => acc + n) 0

/-- Compare genuinely different executable algorithms: the 4-state
    scan and the seven-pair closed weighted formula. -/
def fastAgreementForKey (k : Word) : Bool :=
  regressionPairs.all fun p =>
    fastFourStateCount k p == weightedSevenCount k p

def fastAgreementCount (k : Word) : Nat :=
  (regressionPairs.filter fun p => fastFourStateCount k p == weightedSevenCount k p).length

/-- A bounded diagnostic; all rows should print `agree=7/7`.
    `#eval` uses the compiled evaluator rather than kernel reduction.
    It does NOT establish a universal theorem about arbitrary keys. -/
def runEvidence21Fast : IO Unit := do
  let t0 ← IO.monoMsNow
  let keys : List Word :=
    [0#32, 1#32, 2#32, 3#32, 0x00700000#32,
     0x06120010#32, 0xFFFFFFFF#32, 0x10020020#32]
  IO.println "[Evidence21] beginning fast 4-state DP vs weighted formula"
  for k in keys do
    let start ← IO.monoMsNow
    IO.println s!"[Evidence21] begin key={k.toNat}"
    let _matches := fastAgreementCount k
    let stop ← IO.monoMsNow
    IO.println s!"[Evidence21] key={k.toNat}; agree={_matches}/7; time={stop-start} ms"
  let t1 ← IO.monoMsNow
  IO.println s!"[Evidence21] total={t1-t0} ms"

#eval runEvidence21Fast

end Magma.Evidence.TwoHotDPAgreementFast
