import Lake.Build.Trace
import Lean.Data.Json.Basic

/-- Compute actual output bytes with the repository's pinned Lake hash,
without trusting cached `.hash` sidecars or importing project artifacts. -/
def main (args : List String) : IO UInt32 := do
  let mut entries : Array (String × String) := #[]
  for file in args do
    let actual ← Lake.computeFileHash file
    entries := entries.push (file, actual.toString)
  IO.println (Lean.toJson entries).compress
  return 0
