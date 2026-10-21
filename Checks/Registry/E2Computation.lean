module

namespace Checks.Registry.E2Computation

/-- Derived from the sole reviewed ledger; only this module's consumed inputs
participate in this registry's Lake trace. -/
@[expose] public def proofObligationLedger : String :=
  include_str "../../.lake/audit-inputs/E2Computation.json"

end Checks.Registry.E2Computation
