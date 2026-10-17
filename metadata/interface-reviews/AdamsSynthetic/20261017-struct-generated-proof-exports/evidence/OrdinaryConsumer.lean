module
public import ProducerEnabled
public import ProducerPlain
import Lean
#check ReporterEnabled.box
#check_failure ReporterEnabled.privateProof
#check_failure ReporterPlain.privateProof
example : ReporterEnabled.box.val = 1 := rfl
open Lean Elab Command
run_cmd do
  let env ← getEnv
  unless !Lean.ResolveName.backward.privateInPublic.get (← getOptions) do throwError "consumer option must be false"
  for (n, _) in env.constants.toList do
    if privateToUserName? n == some `ReporterPlain.privateProof then
      throwError "ordinary private theorem unexpectedly serialized into public environment"
  let mut proofName : Name := .anonymous
  for (n, _) in env.constants.toList do
    if privateToUserName? n == some `ReporterEnabled.privateProof then proofName := n
  unless proofName != .anonymous do throwError "private proof absent"
  let accessible ← try
    let term ← liftTermElabM <| Term.withoutErrToSorry <| Term.elabTerm (mkIdent proofName) none
    unless !term.hasSorry do throwError "elaboration introduced sorry"
    let type ← liftTermElabM <| Meta.inferType term
    logInfo m!"Exact private name resolves: {proofName} : {type}"
    pure true
   catch e =>
    logInfo m!"Exact private name rejected: {e.toMessageData}"
    pure false
  unless accessible do throwError "expected exported private-name access"
  unless (env.setExporting true).find? proofName |>.isSome do
    throwError "private proof missing in exporting environment"
  logInfo m!"isPrivateName={isPrivateName proofName}; exporting_environment_contains=true; ordinary_exact_name_access=true"
