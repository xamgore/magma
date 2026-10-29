module

import Lean
import all Init.Data.Range.Basic

public section

/-!
# Declaration dependencies

`lake exe deps` exports direct dependencies from the compiled `Diffan` and `Magma` libraries.
The `declarations` array includes generated declarations so every local dependency
has a corresponding node. Each node has `name`, `module`, `kind`,
`typeDependencies`, and `bodyDependencies`; both dependency sets are split into
`local` and `external` names. Theorem proof bodies are included in dependency
collection, but the expressions themselves are not exported.

An edge points from a declaration to a directly referenced constant.
This export does not compute a transitive closure or guarantee acyclicity:
recursive definitions can introduce cycles. Module ownership, rather than a
declaration's namespace, determines whether it belongs to the project.

`rootModules` lists both libraries. `moduleOrder` records Lean's dependency-first
import traversal; `defs` and the source bundle use the same order. Each entry in
`modules` records its source path and direct imports from either library. Module
edges also point from the importing module to its dependencies.
-/

namespace Deps

open Lean

private def isProjectModule (name : Name) : Bool :=
  (`Diffan).isPrefixOf name || (`Magma).isPrefixOf name

private def moduleOf? (env : Environment) (name : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? name
  env.header.moduleNames[idx]?

private def isLocal (env : Environment) (name : Name) : Bool :=
  (moduleOf? env name).any isProjectModule

private def kind (env : Environment) : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "def"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .inductInfo info =>
    if isClass env info.name then "class"
    else if isStructure env info.name then "structure" else "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
  | .quotInfo _ => "quotient"

private def namesJson (names : Array Name) : Json :=
  toJson <| (names.map Name.toString).qsort (· < ·)

private def dependenciesJson (env : Environment) (expr? : Option Expr) : Json :=
  Id.run do
    let names := expr?.map Expr.getUsedConstants |>.getD #[]
    return Json.mkObj
        [("local", namesJson <| names.filter (isLocal env)),
          ("external", namesJson <| names.filter (fun name => !isLocal env name))]

private def declarationJson (env : Environment) (info : ConstantInfo) : Json :=
  Json.mkObj
    [("name", toJson info.name.toString),
      ("module", toJson <| (moduleOf? env info.name).map Name.toString),
      ("kind", toJson <| kind env info),
      ("typeDependencies", dependenciesJson env (some info.type)),
      ("bodyDependencies", dependenciesJson env (info.value? (allowOpaque := true)))]

def run : IO Unit := do
  initSearchPath (← findSysroot)
  unsafe enableInitializersExecution
  let env ← importModules #[{ module := `Diffan }, { module := `Magma }] {} (loadExts := true)
  let decls :=
    env.constants.toList.toArray.filter (fun (name, _) => isLocal env name) |>.qsort
      (fun a b => a.1.toString < b.1.toString)
  let mut modules : Array Json := #[]
  let mut moduleOrder : Array String := #[]
  for idx in [:env.header.moduleNames.size] do
    let name := env.header.moduleNames[idx]!
    if !isProjectModule name then
      continue
    moduleOrder := moduleOrder.push name.toString
    let imports := env.header.moduleData[idx]!.imports.map (·.module) |>.filter isProjectModule
    modules :=
      modules.push <|
        Json.mkObj
          [("name", toJson name.toString),
            ("path",
              toJson <| String.intercalate "/" (name.components.map Name.toString) ++ ".lean"),
            ("imports", toJson <| imports.map Name.toString)]
  let report :=
    Json.mkObj
      [("schemaVersion", toJson (3 : Nat)), ("rootModules", toJson #["Diffan", "Magma"]),
        ("edgeDirection", toJson "declaration -> dependency"), ("moduleOrder", toJson moduleOrder),
        ("modules", Json.arr modules),
        ("declarations", Json.arr <| decls.map (fun (_, info) => declarationJson env info))]
  IO.println report.pretty

end Deps

def main : IO Unit :=
  Deps.run
