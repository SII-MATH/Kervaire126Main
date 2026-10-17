module
public import Init
import Lean
@[expose] section
namespace ReporterExposure
private theorem privateProof : (1 : Nat) = 1 := rfl
@[expose] public def exposedBox : { n : Nat // n = 1 } := ⟨1, Eq.refl 1⟩
@[no_expose] public def opaqueBox : { n : Nat // n = 1 } := ⟨1, privateProof⟩
public theorem opaque_val : opaqueBox.val = 1 := by rfl
end ReporterExposure
end
