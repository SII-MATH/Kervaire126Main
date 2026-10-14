import Lake
open Lake DSL

package Kervaire126Main where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
    "905b95818eb32af7874a58b427f50c1711a5e96c"

@[default_target]
lean_lib KIP126 where
  globs := #[.one `KIP126, .andSubmodules `KIP126.Def.SpectralSequence,
    .andSubmodules `KIP126.Def.AdamsSynthetic,
    .andSubmodules `KIP126.Def.Literature,
    .andSubmodules `KIP126.Def.Computation,
    .one `KIP126.Interface.Challenge2]

@[default_target]
lean_lib SpectralSequenceChecks where
  roots := #[`Tests.SpectralSequence.Interface, `Tests.SpectralSequence.Visibility,
    `Tests.SpectralSequence.Consumers]

@[default_target]
lean_lib AdamsSyntheticChecks where
  roots := #[`Tests.AdamsSynthetic.Interface, `Tests.AdamsSynthetic.Consumers,
    `Tests.AdamsSynthetic.Detection, `Tests.AdamsSynthetic.System,
    `Tests.AdamsSynthetic.Background, `Tests.AdamsSynthetic.Filtration,
    `Tests.AdamsSynthetic.Mapping, `Tests.AdamsSynthetic.Structural]

@[default_target]
lean_lib LiteratureChecks where
  roots := #[`Tests.Literature.Interface, `Tests.Literature.Consumers,
    `Tests.Literature.RouteConsumers, `Tests.Literature.Secondary,
    `Tests.Literature.Lift]

@[default_target]
lean_lib ComputationChecks where
  roots := #[`Tests.Computation.Interface, `Tests.Computation.Consumers]

@[default_target]
lean_lib DeliveryChecks where
  roots := #[`Tests.Delivery]
