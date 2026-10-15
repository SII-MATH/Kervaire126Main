module

public import KIP126.Def.AdamsSynthetic.Toda.Data

@[expose] public section

namespace KIP126.AdamsSynthetic
open CategoryTheory KIP126.StableHomotopy
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]

/-- Actual classical Toda membership, including all cofiber extensions.
No value or indeterminacy is selected as part of the definition. -/
def ThetaBToda (θ B : HomotopyGroup (C := C) 62 SphereSpectrum)
    (ξ : HomotopyGroup (C := C) 125 SphereSpectrum) : Prop :=
  Toda.Relation (thetaBTodaSource.inv ≫ ξ)
    ((shiftFunctor C (62 : ℤ)).map θ) (2 • 𝟙 (Sphere (C := C) 62)) B
end KIP126.AdamsSynthetic
