module
import KIP126.Literature
import Lean
open Lean Elab Command
run_cmd do
  let env ← getEnv
  for n in [``KIP126.Literature.Standard.tmfUnit,
      ``KIP126.Literature.Standard.tmf_convergence,
      ``KIP126.Literature.Standard.nuPage_weightShift] do
    let some info := env.find? n | throwError "Missing public data: {n}"
    let some body := info.value? (allowOpaque := true)
      | throwError "Existing exposed body unavailable to ordinary consumer: {n}"
    if n != ``KIP126.Literature.Standard.tmf_convergence then
      if body.hasSorry || body.hasSyntheticSorry then throwError "Direct hole in constructed data: {n}"
    else
      unless body.hasSorry && !body.hasSyntheticSorry do
        throwError "Original tmf convergence pending implementation was not retained: {n}"
  logInfo "Ordinary Literature consumer: all three original exposed bodies available; constructed unit/weight shift have no direct holes; tmf convergence retains its original pending responsibility"
#check KIP126.Literature.Standard.tmf_algebra_unit
#check KIP126.Literature.Standard.nuCofiber_bottom_exponent
#check KIP126.Literature.Standard.nuCofiber_top_exponent
#check KIP126.Literature.Standard.theta5_lift
#check KIP126.Literature.Standard.weights_lambda
example : KIP126.Literature.Standard.tmfUnit = KIP126.Literature.Standard.tmf_algebra.one := rfl
