module

public import KIP126.Def.StableHomotopy.Cohomology.Data
public import KIP126.Def.ClassicalAdams.TowerNaturality.Page.Data
public import KIP126.Def.Synthetic.Sphere.Data
public import Mathlib.CategoryTheory.Monoidal.Mon

@[expose] public section

/-!
# Hurewicz maps of an algebra object

The carrier is an explicitly supplied algebra object T, with its actual
multiplication and unit; the Hurewicz maps below are induced by that unit.
-/

namespace KIP126.Classical.Adams.Tmf

noncomputable section
open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Synthetic.Context
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]

/-- The one unit used by every classical and synthetic comparison. -/
def unit (T : Mon C) : SphereSpectrum ⟶ T.X := MonObj.one

/-- Classical Hurewicz is postcomposition by that same algebra-object unit. -/
def hurewicz (T : Mon C) (n : ℤ) :
    HomotopyGroup n (SphereSpectrum : C) →+ HomotopyGroup n T.X :=
  inducedMap (unit T) n

/-- The actual E₂ map induced by the same unit on the HF₂-Adams towers. -/
def e2Hurewicz (H : Mod2EilenbergMacLane (C := C)) (T : Mon C) (p : ℤ × ℤ) :
    (adamsTowerInternalSpectralSequence H.unit SphereSpectrum).Page 2 p →ₗ[ℤ]
      (adamsTowerInternalSpectralSequence H.unit T.X).Page 2 p :=
  adamsInternalE2Induced H.unit (unit T) p

/-- Synthetic Hurewicz is induced by ν of that exact unit, on every bidegree. -/
def syntheticHurewicz {Syn : Type w} [SyntheticCategory.{w, v} Syn]
    (N : NuFunctorData C Syn) (T : Mon C) (p : ℤ × ℤ) :
    BiHom p.1 p.2 (N.functor.obj SphereSpectrum) →+
      BiHom p.1 p.2 (N.functor.obj T.X) :=
  Preadditive.rightComp (Smn p.1 p.2) (N.functor.map (unit T))

end
end KIP126.Classical.Adams.Tmf
