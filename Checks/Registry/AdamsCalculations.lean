module

namespace Checks.Registry.AdamsCalculations

/-- Derived from the sole reviewed ledger; only this module's consumed inputs
participate in this registry's Lake trace. -/
@[expose] public def proofObligationLedger : String :=
  include_str "../../.lake/audit-inputs/AdamsCalculations.json"

end Checks.Registry.AdamsCalculations
