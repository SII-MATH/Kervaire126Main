module
public import Init
import Lean
set_option backward.proofsInPublic true
namespace ReporterNested
@[expose] public def complexBox : { n : Nat // n = 1 } :=
  ⟨1, Eq.trans (Eq.refl 1) (Eq.refl 1)⟩
@[expose] public def atomicBox : { n : Nat // n = 1 } :=
  ⟨1, Eq.refl 1⟩
end ReporterNested
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let complexHelpers := env.constants.toList.filter (fun (n, _) => (`ReporterNested.complexBox).isPrefixOf n && n != `ReporterNested.complexBox)
  let atomicHelpers := env.constants.toList.filter (fun (n, _) => (`ReporterNested.atomicBox).isPrefixOf n && n != `ReporterNested.atomicBox)
  unless !complexHelpers.isEmpty do throwError "expected complex proof extraction"
  unless atomicHelpers.isEmpty do throwError "atomic proof generated helpers"
  for (n, info) in complexHelpers do
    logInfo m!"complex helper: {n} : {info.type}; private={isPrivateName n}; export={(env.setExporting true).find? n |>.isSome}"
  logInfo m!"backward.proofsInPublic=true; atomic_helpers={atomicHelpers.length}"
