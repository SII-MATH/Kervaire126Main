module
public import ProducerExposure
import Lean
example : ReporterExposure.exposedBox.val = 1 := rfl
example : ReporterExposure.opaqueBox.val = 1 := by
  fail_if_success rfl
  exact ReporterExposure.opaque_val
#check_failure ReporterExposure.privateProof
#print axioms ReporterExposure.opaqueBox
open Lean Elab Command
run_cmd do
  let env ← getEnv
  for (n, _) in env.constants.toList do
    if privateToUserName? n == some `ReporterExposure.privateProof then
      throwError "private body theorem leaked"
  let exposed ← getConstInfo `ReporterExposure.exposedBox
  let hiddenInfo ← getConstInfo `ReporterExposure.opaqueBox
  unless exposed.value?.isSome do throwError "expected exposed body"
  unless hiddenInfo.value?.isNone do throwError "expected opaque body"
  logInfo m!"exposed_body_available=true; no_expose_body_available=false; private_proof_absent=true; opaque_val_theorem_usable=true"
