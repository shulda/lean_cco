import Lean.Environment
import Lean.Elab.ParseImportsFast
import Lake.Build.Trace
import Lean.Data.Json.Basic

private structure ModuleMetadata where
  source : String
  sourceHash : String
  imports : Array Lean.Import
  isModule : Bool
  compiledImports : Option (Array Lean.Import)
  compiledIsModule : Option Bool
  readError : Option String
  resolvedOlean : Option String
  deriving Lean.ToJson

/-- Read source headers and actual olean headers without importing CCO artifacts.
The compiler's own parser includes implicit imports and all import flags. -/
def main (args : List String) : IO UInt32 := do
  let (project, build, root) ← match args with
    | [project, build] => pure (project, build, `CCO)
    | [project, build, root] => pure (project, build, root.toName)
    | _ => throw (IO.userError "expected project/build directories and optional root module")
  Lean.initSearchPath (← Lean.findSysroot)
  let namespaceRoot := root.getRoot
  let mut pending : List Lean.Name := [root]
  let mut seen : Array Lean.Name := #[]
  let mut entries : Array ModuleMetadata := #[]
  while let some name := pending.head? do
    pending := pending.tail!
    if seen.contains name then continue
    seen := seen.push name
    let relative := name.toString.replace "." "/"
    let source := System.FilePath.mk project / (relative ++ ".lean")
    let contents ← IO.FS.readFile source
    let header ← Lean.parseImports' contents source.toString
    for imp in header.imports do
      if imp.module == namespaceRoot || imp.module.getRoot == namespaceRoot then
        pending := imp.module :: pending
    let olean := System.FilePath.mk build / "lib/lean" / (relative ++ ".olean")
    let mut compiledImports := none
    let mut compiledIsModule := none
    let mut readError := none
    let mut resolvedOlean := none
    if ← olean.pathExists then
      try
        resolvedOlean := some (← Lean.findOLean name).toString
        let (data, _) ← Lean.readModuleData olean
        compiledImports := some data.imports
        compiledIsModule := some data.isModule
      catch e => readError := some e.toString
    entries := entries.push {
      source := source.toString
      sourceHash := (Lake.Hash.ofText contents).toString
      imports := header.imports
      isModule := header.isModule
      compiledImports, compiledIsModule, readError, resolvedOlean
    }
  IO.println (Lean.toJson entries).compress
  return 0
