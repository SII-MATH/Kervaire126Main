module

public import KIP126.Def.AdamsSynthetic.Standard.Background

/-! Support properties of the fixed classical Adams system, retained from
bbac1fc05843: ClassicalAdams/TowerVanishing/Proofs:72–75 and
ClassicalAdams/SphereVanishing/Proofs:46–51. Their construction belongs
to the Adams system; the paper uses these original upstream facts. -/
namespace KIP126.AdamsSynthetic.Standard
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
implied merely by the associated-graded convergence isomorphism. -/
public theorem classical_sphere_separated (m : ℤ)
    (a : HomotopyGroup (C := Spectrum) m SphereSpectrum)
    (ha : ∀ s : ℕ, a ∈ (model.classicalTower.tower SphereSpectrum).filtrationSubmodule s m) :
    a = 0 := by
  sorry

end KIP126.AdamsSynthetic.Standard
