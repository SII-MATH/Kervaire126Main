module
import FlagToy
import Lean
example : TruePrivateToy.count = 2 := rfl
noncomputable example (i : Fin TruePrivateToy.count) : Nat := TruePrivateToy.entry i
open Lean in
run_meta do
  let env ← getEnv
  let publicEnv := env.setExporting true
  for (name, _) in publicEnv.constants.toList do
    if (privateToUserName name).toString.startsWith "TruePrivateToy" then
      logInfo m!"{name}: isPrivate={isPrivateName name}"
