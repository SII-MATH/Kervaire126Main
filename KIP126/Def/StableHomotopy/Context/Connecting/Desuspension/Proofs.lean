module

public import KIP126.Def.StableHomotopy.Context.Proofs
import all KIP126.Def.StableHomotopy.Context.Proofs
public import KIP126.Def.StableHomotopy.Context.Suspension.Data

@[expose] public section

namespace KIP126.StableHomotopy

open CategoryTheory
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]

/-- The existing connecting homomorphism is postcomposition with the
triangle's actual last map followed by the specified desuspension. -/
theorem connectingHomomorphism_eq_desuspend (T : HoCofiberSequence (C := C))
    (n : ℤ) (z : HomotopyGroup n T.Z) :
    connectingHomomorphism T n z = homotopyDesuspend T.X n (z ≫ T.h) := by
  simp only [connectingHomomorphism, homotopyDesuspend, AddMonoidHom.coe_mk,
    ZeroHom.coe_mk, Functor.id_obj, eqToHom_refl, Category.comp_id]
  change (shiftFunctorAdd' C n (-1) (n - 1) (by omega)).hom.app SphereSpectrum ≫
    𝟙 _ ≫ (shiftFunctor C (-1)).map (z ≫ T.h) ≫ 𝟙 _ ≫
      (shiftFunctorCompIsoId C 1 (-1) (by omega)).hom.app T.X = _
  simp only [Category.id_comp]
  rfl

end KIP126.StableHomotopy
