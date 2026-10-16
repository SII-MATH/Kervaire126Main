module

public import KIP126.AdamsSynthetic.Background
public import KIP126.AdamsSynthetic.Detection
public import KIP126.AdamsSynthetic.Sphere
public import KIP126.SpectralSequence.Multiplicative

@[expose] section

/-! Mapping spectra and their Adams systems on one given closed background.
The objects are actual internal hom objects, not freely chosen graded groups.
Convergence is requested only for pairs of objects in the specified scope.
Source: KIPBase `multiplicativeSS/Adams.lean`, baseline 5aa845241533. -/
namespace KIP126.AdamsSynthetic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy KIP126.Classical.Adams
open KIP126.Core.SpectralSequence
universe u v
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u, v} C]

/-- The internal hom belonging to this supplied closed structure. -/
public def mappingSpectrum (B : ClosedSymmetricTensorTriangulated C) (X Y : C) : C :=
  letI := B.closed
  (ihom X).obj Y

/-- The canonical closed adjunction and the same tensor-shift comparison
identify the homotopy groups with actual shifted stable maps. -/
public def mappingHomotopyEquiv (B : ClosedSymmetricTensorTriangulated C)
    (n : ℤ) (X Y : C) :
    HomotopyGroup n (mappingSpectrum B X Y) ≃ ((shiftFunctor C n).obj X ⟶ Y) := by
  letI := B.closed
  letI := B.symmetric
  exact ((ihom.adjunction X).homEquiv (Sphere n) Y).symm |>.trans
    (Iso.homCongr ((β_ X (Sphere n)).trans (B.sphereTensorShift n X)) (Iso.refl Y))

/-- At degree zero this is an actual map `X ⟶ Y`. -/
public def mappingHomotopyZeroEquiv (B : ClosedSymmetricTensorTriangulated C) (X Y : C) :
    HomotopyGroup 0 (mappingSpectrum B X Y) ≃ (X ⟶ Y) :=
  (mappingHomotopyEquiv B 0 X Y).trans
    (Iso.homCongr ((shiftFunctorZero C ℤ).app X) (Iso.refl Y))

/-- The sphere mapping spectrum is canonically isomorphic to the sphere.
This replaces the old unjustified equality of chosen objects. -/
public def sphereMappingIso (B : ClosedSymmetricTensorTriangulated C) :
    mappingSpectrum B SphereSpectrum SphereSpectrum ≅ (SphereSpectrum : C) := by
  letI := B.closed
  exact MonoidalClosed.unitIsoSelf (C := C) (X := (SphereSpectrum : C))

/-- Its Adams comparison is induced by the one given Adams functor. -/
public def sphereMappingAdamsIso (B : ClosedSymmetricTensorTriangulated C)
    (A : ClassicalAdamsFamily C) :
    A.obj (mappingSpectrum B SphereSpectrum SphereSpectrum) ≅ A.sphere :=
  A.functor.mapIso (sphereMappingIso B)

variable [HasFunctorialCofiber (C := C)] {H : C} {unit : SphereSpectrum ⟶ H}
  {A : ClassicalAdamsFamily C}

/-- Convergence of the actual internal hom Adams sequences. `scope` may be
finite spectra or a specified object closure; no global convergence follows. -/
public structure MappingSpectrumSystem (B : ClosedSymmetricTensorTriangulated C)
    (P : ClassicalTowerPresentation unit A) (scope : C → Prop) where
  convergence : ∀ X Y : C, scope X → scope Y →
    ClassicalTowerConvergence P (mappingSpectrum B X Y)

namespace MappingSpectrumSystem
variable {B : ClosedSymmetricTensorTriangulated C}
  {P : ClassicalTowerPresentation unit A} {scope : C → Prop}

public abbrev sequence (_S : MappingSpectrumSystem B P scope) (X Y : C) :=
  A.obj (mappingSpectrum B X Y)

public def converging (S : MappingSpectrumSystem B P scope) (X Y : C)
    (hX : scope X) (hY : scope Y) : ConvergingSS (ModuleCat.{v} ℤ) (ℤ × ℤ) ℤ where
  E := S.sequence X Y
  A := AbstractAdamsTower.homotopy (mappingSpectrum B X Y)
  F := (P.tower (mappingSpectrum B X Y)).filtration
  conv := (S.convergence X Y hX hY).toConvergence

public theorem reindex (S : MappingSpectrumSystem B P scope) (X Y : C)
    (hX : scope X) (hY : scope Y) (p : ℤ × ℤ) :
    (S.converging X Y hX hY).conv.reindex p = (p.1, p.2 - p.1) := rfl

public def homotopyEquiv (_S : MappingSpectrumSystem B P scope) (n : ℤ) (X Y : C) :
    HomotopyGroup n (mappingSpectrum B X Y) ≃ ((shiftFunctor C n).obj X ⟶ Y) :=
  mappingHomotopyEquiv B n X Y

end MappingSpectrumSystem
end
end KIP126.AdamsSynthetic
