module
import Lean
@[expose] public def f (n : Nat) : Nat := n + 1
run_cmd Lean.logInfo m!"before simp eq_1 exists: {(← Lean.getEnv).contains `f.eq_1}"
public theorem f_test (n : Nat) : f n = n + 1 := by simp [f]
run_cmd Lean.logInfo m!"after simp eq_1 exists: {(← Lean.getEnv).contains `f.eq_1}"
