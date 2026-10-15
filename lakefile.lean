import Lake
open Lake DSL

package KIP126 where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
    "905b95818eb32af7874a58b427f50c1711a5e96c"

-- Check every source, including modules that no facade happens to import.
@[default_target]
target sourceInventory pkg : Unit := do
  let result ← IO.Process.output {
    cmd := "python3"
    args := #[(pkg.dir / "scripts/check-source-inventory.py").toString]
  }
  unless result.exitCode == 0 do
    error (result.stdout ++ result.stderr)
  return Job.pure ()

@[default_target]
lean_lib KIP126 where
  globs := #[.andSubmodules `KIP126]

@[default_target]
lean_lib ArchitectureChecks where
  roots := #[`Tests.Architecture, `Tests.Trust]
  globs := #[.submodules `Tests]
