import Lake
open Lake DSL

package Kervaire126Main where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
    "905b95818eb32af7874a58b427f50c1711a5e96c"


-- JSON locks participate in Lake traces; changing a lock reruns its check.
input_file proofObligations where
  path := "interface/baselines/proof-obligations.json"
  text := true
input_file spectralSequenceApi where
  path := "interface/baselines/spectral-sequence-api.json"
  text := true
input_file adamsSyntheticApi where
  path := "interface/baselines/adams-synthetic-api.json"
  text := true
input_file literatureApi where
  path := "interface/baselines/literature-api.json"
  text := true
input_file adamsComputationApi where
  path := "interface/baselines/adams-computation-api.json"
  text := true
input_file ssComputationApi where
  path := "interface/baselines/ss-computation-api.json"
  text := true
input_file proofToolsApi where
  path := "interface/baselines/proof-tools-api.json"
  text := true
input_file mainApi where
  path := "interface/baselines/main-api.json"
  text := true
input_file geometryApi where
  path := "interface/baselines/geometry-api.json"
  text := true

-- Retain the original explicit whole-ledger entry for tools that request it.
-- Do not let its root prefix claim the independently traced module inputs.
lean_lib BuildCheckInputs where
  roots := #[]
  globs := #[.one `Checks.Registry]
  needs := #[.packageTarget .anonymous `proofObligations]

-- A global edit regenerates projections, but only changed output content may
-- invalidate a registry. buildFileUnlessUpToDate' returns the output's trace.
private def moduleObligationInput
    (pkg : Package) (owner : String) : FetchM (Job System.FilePath) := do
  let ledger ← inputTextFile
    (pkg.dir / "interface/baselines/proof-obligations.json")
  let generator ← inputTextFile
    (pkg.dir / "scripts/project-proof-obligations.py")
  (ledger.mix generator).mapM fun _ => do
    -- A fixed generated-input path also works with a custom Lake buildDir.
    let output := pkg.dir / ".lake" / "audit-inputs" / s!"{owner}.json"
    buildFileUnlessUpToDate' output (do
      let result ← IO.Process.output {
        cmd := "python3"
        args := #[
          (pkg.dir / "scripts/project-proof-obligations.py").toString,
          "--module", owner, "--output", output.toString
        ]
      }
      unless result.exitCode == 0 do
        error result.stderr
    ) (text := true)
    return output

target adamsSyntheticObligations pkg : System.FilePath :=
  moduleObligationInput pkg "AdamsSynthetic"

lean_lib AdamsSyntheticAuditInputs where
  roots := #[`Checks.Registry.AdamsSynthetic]
  needs := #[.packageTarget .anonymous `adamsSyntheticObligations]

target literatureObligations pkg : System.FilePath :=
  moduleObligationInput pkg "Literature"

lean_lib LiteratureAuditInputs where
  roots := #[`Checks.Registry.Literature]
  needs := #[.packageTarget .anonymous `literatureObligations]

target adamsComputationObligations pkg : System.FilePath :=
  moduleObligationInput pkg "AdamsComputation"

lean_lib AdamsComputationAuditInputs where
  roots := #[`Checks.Registry.AdamsComputation]
  needs := #[.packageTarget .anonymous `adamsComputationObligations]

target proofToolsObligations pkg : System.FilePath :=
  moduleObligationInput pkg "ProofTools"

lean_lib ProofToolsAuditInputs where
  roots := #[`Checks.Registry.ProofTools]
  needs := #[.packageTarget .anonymous `proofToolsObligations]

target ssComputationObligations pkg : System.FilePath :=
  moduleObligationInput pkg "SSComputation"

lean_lib SSComputationAuditInputs where
  roots := #[`Checks.Registry.SSComputation]
  needs := #[.packageTarget .anonymous `ssComputationObligations]

target mainObligations pkg : System.FilePath :=
  moduleObligationInput pkg "Main"

lean_lib MainAuditInputs where
  roots := #[`Checks.Registry.Main]
  needs := #[.packageTarget .anonymous `mainObligations]

target geometryObligations pkg : System.FilePath :=
  moduleObligationInput pkg "Geometry"

lean_lib GeometryAuditInputs where
  roots := #[`Checks.Registry.Geometry]
  needs := #[.packageTarget .anonymous `geometryObligations]

-- Run on every build so a newly added, unimported file cannot bypass auditing.
@[default_target]
target sourceInventory pkg : Unit := do
  let result ← IO.Process.output {
    cmd := "python3"
    args := #[(pkg.dir / "scripts/check-source-inventory.py").toString]
  }
  unless result.exitCode == 0 do
    error result.stderr
  return Job.pure ()

@[default_target]
lean_lib KIP126 where
  globs := #[.one `KIP126, .andSubmodules `KIP126.SpectralSequence,
    .andSubmodules `KIP126.AdamsSynthetic,
    .andSubmodules `KIP126.Literature,
    .andSubmodules `KIP126.AdamsComputation,
    .andSubmodules `KIP126.ProofTools,
    .andSubmodules `KIP126.SSComputation,
    .andSubmodules `KIP126.Main,
    .andSubmodules `KIP126.Geometry]

@[default_target]
lean_lib SpectralSequenceChecks where
  needs := #[.packageTarget .anonymous `spectralSequenceApi]
  roots := #[`Tests.SpectralSequence.Interface, `Tests.SpectralSequence.Visibility,
    `Tests.SpectralSequence.Consumers]

@[default_target]
lean_lib AdamsSyntheticChecks where
  needs := #[.packageTarget .anonymous `adamsSyntheticApi]
  roots := #[`Tests.AdamsSynthetic.Interface, `Tests.AdamsSynthetic.Consumers,
    `Tests.AdamsSynthetic.Detection, `Tests.AdamsSynthetic.System,
    `Tests.AdamsSynthetic.Background, `Tests.AdamsSynthetic.Filtration,
    `Tests.AdamsSynthetic.Mapping, `Tests.AdamsSynthetic.Structural]

@[default_target]
lean_lib LiteratureChecks where
  needs := #[.packageTarget .anonymous `literatureApi]
  roots := #[`Tests.Literature.Interface, `Tests.Literature.Consumers,
    `Tests.Literature.RouteConsumers, `Tests.Literature.Secondary,
    `Tests.Literature.Lift, `Tests.Literature.Geometry, `Tests.Literature.GeometryObjects]

@[default_target]
lean_lib AdamsComputationChecks where
  needs := #[.packageTarget .anonymous `adamsComputationApi]
  roots := #[`Tests.AdamsComputation.Interface, `Tests.AdamsComputation.Consumers,
    `Tests.AdamsComputation.SourceExpression, `Tests.AdamsComputation.DirectD2]

@[default_target]
lean_lib SSComputationChecks where
  needs := #[.packageTarget .anonymous `ssComputationApi]
  roots := #[`Tests.SSComputation.Interface, `Tests.SSComputation.Consumers,
    `Tests.SSComputation.SourceConsumers]

@[default_target]
lean_lib ProofToolsChecks where
  needs := #[.packageTarget .anonymous `proofToolsApi]
  roots := #[`Tests.ProofTools.Interface, `Tests.ProofTools.Consumers]

@[default_target]
lean_lib MainChecks where
  needs := #[.packageTarget .anonymous `mainApi]
  roots := #[`Tests.Main.Interface, `Tests.Main.Consumers, `Tests.Main.Boundary,
    `Tests.Main.LegacyResults]

@[default_target]
lean_lib GeometryChecks where
  needs := #[.packageTarget .anonymous `geometryApi]
  roots := #[`Tests.Geometry.Interface, `Tests.Geometry.Consumers]

@[default_target]
lean_lib ArchitectureChecks where
  roots := #[`Tests.Architecture, `Tests.Integration, `Tests.Trust]
