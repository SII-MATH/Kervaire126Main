module
public import KIP126.AdamsSynthetic.Standard.Operations
import Lean
open KIP126.AdamsSynthetic KIP126.AdamsSynthetic.Standard
private theorem reporterOriginalSignature (X Z : SyntheticSpectrum) :
    letI := graded_module X Z
    SMulCommClass (Polynomial ℤ) (Polynomial ℤ) (TotalWeightHom X Z) := by
  letI := graded_module X Z
  exact smulCommClass_self _ _
open Lean Elab Command
run_cmd do
  let ci ← getConstInfo ``reporterOriginalSignature
  logInfo m!"signature_fingerprint={hash (toString ci.type)}"
  let axioms ← collectAxioms ``reporterOriginalSignature
  logInfo m!"signature_axioms={axioms}"
