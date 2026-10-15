module

public import KIP126.Def.StableHomotopy.Toda.Predicates

@[expose] public section

namespace KIP126.AdamsSynthetic
open CategoryTheory KIP126.StableHomotopy
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]

/-- The source of <θ₅,2,B> is Σ(Σ⁶² S⁶²) = S¹²⁵, using the
category's actual shift comparisons. -/
noncomputable def thetaBTodaSource :
    Sphere (C := C) 125 ≅ ((Sphere (C := C) 62)⟦(62 : ℤ)⟧)⟦(1 : ℤ)⟧ :=
  (shiftFunctorAdd' C 124 1 125 (by norm_num)).app SphereSpectrum ≪≫
    (shiftFunctor C (1 : ℤ)).mapIso
      ((shiftFunctorAdd' C 62 62 124 (by norm_num)).app SphereSpectrum)
end KIP126.AdamsSynthetic
