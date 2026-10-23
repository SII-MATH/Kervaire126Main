module

namespace Checks.Registry.AdamsComputation

/-- Derived from the sole reviewed ledger; only this module's consumed inputs
participate in this registry's Lake trace. -/
@[expose] public def proofObligationLedger : String :=
  include_str "../../.lake/audit-inputs/AdamsComputation.json"

end Checks.Registry.AdamsComputation
