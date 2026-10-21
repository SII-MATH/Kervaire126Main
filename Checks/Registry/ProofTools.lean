module

namespace Checks.Registry.ProofTools

/-- Derived from the sole reviewed ledger; only this module's consumed inputs
participate in this registry's Lake trace. -/
@[expose] public def proofObligationLedger : String :=
  include_str "../../.lake/audit-inputs/ProofTools.json"

end Checks.Registry.ProofTools
