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
input_file e2ComputationApi where
  path := "interface/baselines/e2-computation-api.json"
  text := true
input_file adamsCalculationsApi where
  path := "interface/baselines/adams-calculations-api.json"
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

lean_lib BuildCheckInputs where
  roots := #[`Checks.Registry]
  needs := #[.packageTarget .anonymous `proofObligations]

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
    .andSubmodules `KIP126.E2Computation,
    .andSubmodules `KIP126.ProofTools,
    .andSubmodules `KIP126.AdamsCalculations,
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
lean_lib E2ComputationChecks where
  needs := #[.packageTarget .anonymous `e2ComputationApi]
  roots := #[`Tests.E2Computation.Interface, `Tests.E2Computation.Consumers,
    `Tests.E2Computation.SourceExpression]

@[default_target]
lean_lib AdamsCalculationsChecks where
  needs := #[.packageTarget .anonymous `adamsCalculationsApi]
  roots := #[`Tests.AdamsCalculations.Interface, `Tests.AdamsCalculations.Consumers,
    `Tests.AdamsCalculations.SourceConsumers]

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
