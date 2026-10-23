module

namespace Checks.Registry.SSComputation

/-- Derived from the sole reviewed ledger; only this module's consumed inputs
participate in this registry's Lake trace. -/
@[expose] public def proofObligationLedger : String :=
  include_str "../../.lake/audit-inputs/SSComputation.json"

end Checks.Registry.SSComputation
