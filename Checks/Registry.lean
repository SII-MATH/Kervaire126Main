module

/-- The reviewed proof ledger is a traced Lake input. Importing this constant
makes a ledger edit invalidate the audit cache without rebuilding mathematics. -/
@[expose] public def proofObligationLedger : String := include_str "../metadata/proof-obligations.json"
