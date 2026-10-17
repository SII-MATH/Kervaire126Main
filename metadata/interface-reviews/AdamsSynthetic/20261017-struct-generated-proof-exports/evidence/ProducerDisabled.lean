module
public import Init
import Lean

namespace ReporterDisabled
private theorem privateProof : (1 : Nat) = 1 := rfl
@[expose] public def box : { n : Nat // n = 1 } := ⟨1, privateProof⟩
end ReporterDisabled
