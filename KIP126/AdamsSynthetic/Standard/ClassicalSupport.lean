module

public import KIP126.AdamsSynthetic.Standard.Background
import all KIP126.AdamsSynthetic.Internal.SphereBHS.Tower

/-! Support properties of the fixed classical Adams system, retained from
bbac1fc05843: ClassicalAdams/TowerVanishing/Proofs:72–75 and
ClassicalAdams/SphereVanishing/Proofs:46–51. Their construction belongs
to the Adams system; the paper uses these original upstream facts. -/
namespace KIP126.AdamsSynthetic.Standard
open CategoryTheory CategoryTheory.Limits
open KIP126.Kervaire.Route KIP126.StableHomotopy

public theorem classical_page_negative (X : ClassicalObject) (r s t : ℤ)
    (hs : s < 0) :
    Subsingleton ((model.classical.obj (X.obj model.auxiliary)).Page r (s,t)) := by
  sorry

public theorem sphere_page_filtration_zero (r : ℤ) (t : ℕ) (ht : t ≠ 0) :
    Subsingleton (model.classical.sphere.Page r (0,t)) := by
  sorry

/-- The original classical sphere Hausdorff condition used by the paper.
It is a foundational producer obligation (ClassicalSphereSeparated), not
implied merely by the associated-graded convergence isomorphism.
The migrated private `Internal.SphereBHS.Tower` proves the finite-kernel
route to completeness and separation. Specializing its actual residual
1-shift hypothesis to this model is still pending; the old completed-source
argument must not be applied to the recognized ordinary source silently. -/
public theorem classical_sphere_separated (m : ℤ)
    (a : HomotopyGroup (C := Spectrum) m SphereSpectrum)
    (ha : ∀ s : ℕ, a ∈ (model.classicalTower.tower SphereSpectrum).filtrationSubmodule s m) :
    a = 0 := by
  sorry

/-- The migrated argument specializes to exactly the tower in the public
obligation above. Its residual-acyclicity and finite-kernel premises remain
explicit; neither is obtained from the separation conclusion. -/
private theorem classical_sphere_separated_of_residual_acyclic
    (products : HasProductsOfShape ℕ Spectrum)
    (hacyclic : letI := products;
      IsIso (Internal.SphereBHS.Tower.oneSubShift
        (model.classicalTower.tower SphereSpectrum)))
    (m : ℤ)
    (hfinite : ∀ s : ℕ, Finite (inducedMap
      ((model.classicalTower.tower SphereSpectrum).map (Nat.le_succ s)) m).ker)
    (a : HomotopyGroup (C := Spectrum) m SphereSpectrum)
    (ha : ∀ s : ℕ,
      a ∈ (model.classicalTower.tower SphereSpectrum).filtrationSubmodule s m) :
    a = 0 := by
  letI := products
  exact Internal.SphereBHS.Tower.filtration_element_separated
    (model.classicalTower.tower SphereSpectrum) m hfinite
    (Internal.SphereBHS.Tower.hom_delta_bijective
      (model.classicalTower.tower SphereSpectrum) hacyclic (Sphere m)).injective a ha

end KIP126.AdamsSynthetic.Standard
