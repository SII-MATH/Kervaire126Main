module

public import KIP126.Def.ClassicalAdams.SphereClasses.Product.Data

@[expose] public section

/-! Koszul symmetry of the specified sphere E₂ product, with explicit degree transport. -/
namespace KIP126.Classical.Adams.Sphere.Internal
open CategoryTheory
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
universe u v
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  (H : Mod2EilenbergMacLane (C := C)) (M : MilnorCooperations H)

def SphereProductGradedCommutative : Prop :=
  ∀ {s t s' t' : ℕ}
    (x : (adamsTowerInternalSpectralSequence H.unit SphereSpectrum).Page 2 (s, t))
    (y : (adamsTowerInternalSpectralSequence H.unit SphereSpectrum).Page 2 (s', t')),
    product H M x y =
      ((-1 : ℤ) ^ ((((t : ℤ) - s) * ((t' : ℤ) - s')).natAbs)) •
        (spherePageDegreeTransport H s t s' t'
          (by apply Prod.ext <;> omega)).hom (product H M y x)

end
end KIP126.Classical.Adams.Sphere.Internal
