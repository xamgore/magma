module

import Lean
import all Init.Data.Range.Basic

public section

/-!
# Project declarations

`lake exe defs` prints authored declarations from the compiled `Magma` modules.
Definitions include their bodies; theorems and other proof-valued declarations
include only their types. Declaration ranges identify source declarations without
reading the source file. Generated helpers are omitted; inductive constructors
and structure fields are shown with their parent declaration.
-/

namespace Defs

open Lean Meta

private def isLocal (env : Environment) (name : Name) : Bool :=
  (env.getModuleIdxFor? name).any fun idx => (`Magma).isPrefixOf env.header.moduleNames[idx]!

private def kind (env : Environment) : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "def"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .inductInfo info =>
    if isClass env info.name then "class"
    else if isStructure env info.name then "structure" else "inductive"
  | _ => ""

private def printDeclarations : MetaM Unit := do
  let env ← getEnv
  let out ← IO.getStdout
  let decls :=
    env.constants.toList.toArray.filter (fun (name, _) => isLocal env name) |>.qsort
      (fun a b => a.1.toString < b.1.toString)
  for (name, info) in decls do
    if
        (← findDeclarationRangesCore? name).isNone || kind env info == "" ||
          env.isProjectionFn name then
      continue
    let type ← PrettyPrinter.ppExpr info.type
    let visibility := if isPrivateName name then "private " else ""
    let safety :=
      match info with
      | .defnInfo val =>
        match val.safety with
        | .unsafe => "unsafe "
        | .partial => "partial "
        | .safe => ""
      | _ => ""
    let displayName := privateToUserName name
    let levels :=
      if info.levelParams.isEmpty then ""
      else ".{" ++ String.intercalate ", " (info.levelParams.map Name.toString) ++ "}"
    let header := s!"{visibility}{safety}{kind env info} {displayName}{levels} : {type.pretty 100}"
    match info with
    | .defnInfo val =>
      if ← isProp info.type then
        out.putStrLn header
      else
        let body ← PrettyPrinter.ppExpr val.value
        out.putStrLn s!"{header} :=\n{body.pretty 100}"
    | .inductInfo val =>
      out.putStrLn header
      if let some structInfo := getStructureInfo? env name then
        for field in structInfo.fieldInfo do
          let signature ← PrettyPrinter.ppSignature field.projFn
          out.putStrLn s!"  -- field: {signature.fmt.pretty 100}"
      else
        for ctor in val.ctors do
          let signature ← PrettyPrinter.ppSignature ctor
          out.putStrLn s!"  -- constructor: {signature.fmt.pretty 100}"
    | _ =>
      out.putStrLn header
    out.putStrLn ""

def run : IO Unit := do
  initSearchPath (← findSysroot)
  unsafe enableInitializersExecution
  let env ← importModules #[{ module := `Magma }] {} (loadExts := true)
  let options := ({} : Options).setBool `pp.proofs false |>.setBool `pp.piBinderNames true
  let _ ←
    printDeclarations.run' {} {} |>.toIO
        { fileName := "<project declarations>", fileMap := default, options } { env }

end Defs

def main : IO Unit :=
  Defs.run
