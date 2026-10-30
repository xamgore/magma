module

import Lean
import Lean.Util.SCC
import all Init.Data.Range.Basic

public section

/-!
# Project declarations

`lake exe defs` writes authored declarations from the compiled `Diffan` and `Magma`
modules to `.lake/defs.txt` and the complete source bundle to `.lake/sources.txt`.
Modules follow Lean's dependency-first import order, also exported by `deps` for
the source bundle. Within a module, Tarjan components order declarations by all
type and body dependencies, including theorem proofs and hidden generated helpers.
Source positions break ties, preserving the progression of the research.

Namespace blocks give short declaration names and a namespace-aware pretty-printing
context. Definition bodies are included; proofs are omitted. Generated helpers are
hidden, with constructors and structure fields attached to their parent. Leading
layout whitespace is removed: this is a reading index, not compilable Lean source.
-/

namespace Defs

open Lean Meta

private def isProjectModule (name : Name) : Bool :=
  (`Diffan).isPrefixOf name || (`Magma).isPrefixOf name

private def isLocal (env : Environment) (name : Name) : Bool :=
  (env.getModuleIdxFor? name).any fun idx => isProjectModule env.header.moduleNames[idx]!

private def kind (env : Environment) : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "def"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .inductInfo info =>
    if isClass env info.name then "class"
    else if isStructure env info.name then "structure" else "inductive"
  | _ => ""

private structure Entry where
  name : Name
  info : ConstantInfo
  moduleIdx : ModuleIdx
  position : Position
  authored : Bool

private def before (a b : Entry) : Bool :=
  if a.moduleIdx != b.moduleIdx then a.moduleIdx.toNat < b.moduleIdx.toNat
  else
    if a.position != b.position then a.position.lt b.position else a.name.toString < b.name.toString

private def compact (s : String) : String :=
  String.intercalate "\n" (s.splitOn "\n" |>.map (·.trimAsciiStart.toString))

private def printDeclaration (out : IO.FS.Handle) (info : ConstantInfo) : MetaM Unit := do
  let env ← getEnv
  let type ← PrettyPrinter.ppExpr info.type
  let visibility := if isPrivateName info.name then "private " else ""
  let safety :=
    match info with
    | .defnInfo val =>
      match val.safety with
      | .unsafe => "unsafe "
      | .partial => "partial "
      | .safe => ""
    | _ => ""
  let displayName := (privateToUserName info.name).updatePrefix .anonymous
  let levels :=
    if info.levelParams.isEmpty then ""
    else ".{" ++ String.intercalate ", " (info.levelParams.map Name.toString) ++ "}"
  let header := s!"{visibility}{safety}{kind env info} {displayName}{levels} : {type.pretty 160}"
  match info with
  | .defnInfo val =>
    if ← isProp info.type then
      out.putStrLn (compact header)
    else
      let body ← PrettyPrinter.ppExpr val.value
      out.putStrLn (compact s!"{header} :=\n{body.pretty 160}")
  | .inductInfo val =>
    out.putStrLn (compact header)
    if let some structInfo := getStructureInfo? env info.name then
      for field in structInfo.fieldInfo do
        let fieldInfo ← getConstInfo field.projFn
        let type ← PrettyPrinter.ppExpr fieldInfo.type
        let name := (privateToUserName field.projFn).updatePrefix .anonymous
        out.putStrLn (compact s!"-- field {name} : {type.pretty 160}")
    else
      for ctor in val.ctors do
        let ctorInfo ← getConstInfo ctor
        let type ← PrettyPrinter.ppExpr ctorInfo.type
        let name := (privateToUserName ctor).updatePrefix .anonymous
        out.putStrLn (compact s!"-- constructor {name} : {type.pretty 160}")
  | _ =>
    out.putStrLn (compact header)
  out.putStrLn ""

private def printDeclarations (out : IO.FS.Handle) : MetaM Unit := do
  let env ← getEnv
  let mut entries : Array Entry := #[]
  for (name, info) in env.constants.toList do
    if !isLocal env name then
      continue
    let some moduleIdx := env.getModuleIdxFor? name | continue
    let ranges ← findDeclarationRangesCore? name
    entries :=
      entries.push
        { name, info, moduleIdx
          position := ranges.map (·.selectionRange.pos) |>.getD ⟨1000000000, 0⟩
          authored :=
            ranges.isSome && kind env info != "" && !env.isProjectionFn name &&
              !(privateToUserName name).isInternalDetail }
  entries := entries.qsort before
  let mut rank : Std.HashMap Name Nat := {}
  let mut authored : Std.HashSet Name := {}
  for (entry, i) in entries.zipIdx do
    rank := rank.insert entry.name i
    if entry.authored then
      authored := authored.insert entry.name
  let byRank (a b : Name) : Bool := rank[a]?.getD 0 < rank[b]?.getD 0
  out.putStrLn
      "-- Reading index: definition bodies, theorem statements; module and dependency order.\n"
  for idx in [:env.header.moduleNames.size] do
    let moduleName := env.header.moduleNames[idx]!
    if moduleName == `Magma || moduleName == `Diffan || !isProjectModule moduleName then
      continue
    let path := String.intercalate "/" (moduleName.components.map Name.toString) ++ ".lean"
    out.putStrLn s!"-- module {moduleName} | {path}\n"
    let vertices := entries.filter (·.moduleIdx.toNat == idx) |>.map (·.name) |>.toList
    let successors := fun name =>
      Id.run do
        let some info := env.find? name | return []
        let body := info.value? (allowOpaque := true) |>.map Expr.getUsedConstants |>.getD #[]
        return (info.type.getUsedConstants ++ body).toList.filter
              (fun dep => (env.getModuleIdxFor? dep).any (·.toNat == idx)) |>.mergeSort
            byRank
    let components := Lean.SCC.scc vertices successors
    let mut active : Name := .anonymous
    for component in components do
      let visible := component.filter (authored.contains ·) |>.mergeSort byRank
      if visible.length > 1 then
        out.putStrLn "-- mutually dependent declarations"
      for name in visible do
        let ns := (privateToUserName name).getPrefix
        if ns != active then
          if !active.isAnonymous then
            out.putStrLn s!"end {active}\n"
          if !ns.isAnonymous then
            out.putStrLn s!"namespace {ns}\n"
          active := ns
        withTheReader Core.Context (fun ctx => { ctx with currNamespace := ns }) do
            printDeclaration out (← getConstInfo name)
    if !active.isAnonymous then
      out.putStrLn s!"end {active}\n"

def run : IO Unit := do
  initSearchPath (← findSysroot)
  unsafe enableInitializersExecution
  let env ← importModules #[{ module := `Diffan }, { module := `Magma }] {} (loadExts := true)
  let options := ({} : Options).setBool `pp.proofs false |>.setBool `pp.piBinderNames true
  IO.FS.createDirAll ".lake"
  IO.FS.withFile ".lake/defs.txt.tmp" .write fun out => do
      let _ ←
        (printDeclarations out).run' {} {} |>.toIO
            { fileName := "<project declarations>", fileMap := default, options } { env }
      pure ()
  let sources ←
    IO.Process.output
        { cmd := "python3"
          args := #["scripts/export_sources.py", "-o", ".lake/sources.txt.tmp"] }
  if sources.exitCode != 0 then
    throw <| IO.userError s!"Source export failed:\n{sources.stderr}"
  IO.FS.rename ".lake/defs.txt.tmp" ".lake/defs.txt"
  IO.FS.rename ".lake/sources.txt.tmp" ".lake/sources.txt"

end Defs

def main : IO Unit :=
  Defs.run
