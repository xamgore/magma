module

import Lean
import all Magma.Differential.Windows.BoundaryWindowIntersections
import all Init.Data.Range.Basic

open Lean Elab Command Meta

run_cmd do
  let env ← getEnv
  let some (_, info) := env.constants.toList.find? (fun (n, _) =>
      n.toString.endsWith "split14._native.bv_decide.ax_5")
    | throwError "Certificate axiom not found"
  logInfo m!"Certificate proposition: {info.type}"
  let started ← IO.monoMsNow
  let proof ← runTermElabM fun _ => do
    let value ← Term.elabTerm (← `(by decide +kernel)) (some info.type)
    Term.synthesizeSyntheticMVarsNoPostponing
    let proof ← instantiateMVars value
    if proof.hasSorry then
      throwError "Kernel decide did not produce a proof"
    pure proof
  liftCoreM <| addDecl <| .thmDecl {
    name := `certificate_decide_probe
    levelParams := info.levelParams
    type := info.type
    value := proof
  }
  logInfo m!"Kernel-checked decide proof: {(← IO.monoMsNow) - started} ms"

#print axioms certificate_decide_probe
