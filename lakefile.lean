import Lake
open Lake DSL

package Kervaire126Main where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
    "905b95818eb32af7874a58b427f50c1711a5e96c"


-- JSON locks participate in Lake traces; changing a lock reruns its check.
input_file proofObligations where
  path := "proof-obligations.json"
  text := true
input_file spectralSequenceApi where
  path := "spectral-sequence-api.json"
  text := true
input_file adamsSyntheticApi where
  path := "adams-synthetic-api.json"
  text := true
input_file literatureApi where
  path := "literature-api.json"
  text := true
input_file computationApi where
  path := "computation-api.json"
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
  globs := #[.one `KIP126, .andSubmodules `KIP126.Def.SpectralSequence,
    .andSubmodules `KIP126.Def.AdamsSynthetic,
    .andSubmodules `KIP126.Def.Literature,
    .andSubmodules `KIP126.Def.Computation]

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
    `Tests.Literature.Lift]

@[default_target]
lean_lib ComputationChecks where
  needs := #[.packageTarget .anonymous `computationApi]
  roots := #[`Tests.Computation.Interface, `Tests.Computation.Consumers]

@[default_target]
lean_lib IntegrationChecks where
  roots := #[`Tests.Integration, `Tests.Trust]
