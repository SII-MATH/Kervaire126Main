module
public import KIP126.Literature
import Lean
open Lean Elab Command
run_cmd do
  let env ← getEnv
  for n in [``KIP126.Literature.Standard.tmfUnit,
      ``KIP126.Literature.Standard.tmf_convergence,
      ``KIP126.Literature.Standard.nuPage_weightShift] do
    unless env.hasExposedBody n do throwError "Lost public exposed body: {n}"
    unless ((env.setExporting true).find? n).isSome do throwError "Lost public export: {n}"
  logInfo "Public Literature consumer: original data exposure retained"
