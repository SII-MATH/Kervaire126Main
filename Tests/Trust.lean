module

import all Tests.AdamsSynthetic.Background
import all Tests.AdamsSynthetic.Consumers
import all Tests.AdamsSynthetic.Detection
import all Tests.AdamsSynthetic.Filtration
import all Tests.AdamsSynthetic.Interface
import all Tests.AdamsSynthetic.Mapping
import all Tests.AdamsSynthetic.Structural
import all Tests.AdamsSynthetic.System
import all Tests.Computation.Consumers
import all Tests.Computation.Interface
import all Tests.Integration
import all Tests.Literature.Consumers
import all Tests.Literature.Interface
import all Tests.Literature.Lift
import all Tests.Literature.RouteConsumers
import all Tests.Literature.Secondary
import all Tests.SpectralSequence.Consumers
import all Tests.SpectralSequence.Interface
import all Tests.SpectralSequence.Visibility
import all KIP126
import Lean
open Lean Elab Command
set_option maxHeartbeats 0
run_cmd do
  let env ← getEnv
  let mut checked : Nat := 0
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless (`Tests).isPrefixOf mod || mod == `KIP126 do continue
    if info.isAxiom || info.type.hasSorry ||
        (info.value? (allowOpaque := true)).any (·.hasSorry) then
      throwError "Consumer must use the upstream API, not a local axiom or sorry: {name}"
    checked := checked + 1
  logInfo m!"Consumer trust audit: {checked} declarations; no local axioms or sorry"
