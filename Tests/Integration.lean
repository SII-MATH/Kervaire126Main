module

import KIP126.Def.Computation
import Lean

open KIP126.Core.SpectralSequence
open KIP126.AdamsSynthetic.Standard

-- The goal uses the fixed sphere and its actual multiplication. No upstream
-- result package, construction witness, or extra theorem hypothesis is needed.
example : Prop := NonzeroSurvival model.classical.sphere (2,128)
  model.standardClasses.standardH6Square

example : KIP126.Computation.Standard.atom .g = KIP126.Literature.Standard.g :=
  KIP126.Computation.Standard.g_agrees

example : HasNonzeroDifferential model.classical.sphere 2 (1,64) (3,65)
    KIP126.Computation.Standard.h6
    (KIP126.Computation.Standard.product KIP126.Computation.Standard.h0
      KIP126.Computation.Standard.h5Square) :=
  KIP126.Computation.Standard.d2_h6

#check_failure KIP126.Challenge2
#check_failure KIP126.Literature.LiteratureInterface
#check_failure KIP126.Computation.ComputationInterface
#check_failure KIP126.Literature.LiteratureResults
#check_failure KIP126.Computation.RouteResults
#check_failure KIP126.Computation.Near126Results
#check_failure KIP126.Main.Axiom.challenge2

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for mod in env.header.moduleNames do
    if (`KIP126.Interface).isPrefixOf mod || (`KIP126.Main).isPrefixOf mod then
      throwError "Integration consumer imported a retired delivery or Main: {mod}"
  for (name, info) in env.constants.toList do
    if (env.getModuleIdxFor? name).isNone then
      if info.type.hasSorry || (info.value? (allowOpaque := true)).any (·.hasSorry) then
        throwError "Consumer supplied an unfinished proof: {name}"
