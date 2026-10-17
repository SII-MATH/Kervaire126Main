module
public import Init
import Lean
set_option backward.privateInPublic true
namespace ReporterEnabled
private theorem privateProof : (1 : Nat) = 1 := rfl
@[expose] public def box : { n : Nat // n = 1 } := ⟨1, privateProof⟩
end ReporterEnabled
