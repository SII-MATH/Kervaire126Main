module

public import KIP126.AdamsSynthetic.Standard.Background
import all KIP126.AdamsSynthetic.Internal.SphereBHS.Tower

/-! Support properties of the fixed classical Adams system, retained from
bbac1fc05843: ClassicalAdams/TowerVanishing/Proofs:72–75 and
ClassicalAdams/SphereVanishing/Proofs:46–51. Their construction belongs
to the Adams system; the paper uses these original upstream facts. -/
namespace KIP126.AdamsSynthetic.Standard
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open KIP126.Kervaire.Route KIP126.StableHomotopy

private theorem page_subsingleton_of_ambient
    (D : KIP126.Core.SpectralSequence.SSData (ModuleCat.{0} ℤ))
    (r : WithTop ℕ) [Subsingleton D.V] : Subsingleton (D.page r) := by
  have hV : IsZero D.V := ModuleCat.isZero_of_subsingleton D.V
  have hZ : IsZero (Subobject.underlying.obj (D.Z r)) :=
    IsZero.of_mono (D.Z r).arrow hV
  letI : Epi (D.pageπ r) := coequalizer.π_epi
  exact ModuleCat.subsingleton_of_isZero (IsZero.of_epi (D.pageπ r) hZ)

public theorem classical_page_negative (X : ClassicalObject) (r s t : ℤ)
    (hs : s < 0) :
    Subsingleton ((model.classical.obj (X.obj model.auxiliary)).Page r (s,t)) := by
  let T := model.classicalTower.tower (X.obj model.auxiliary)
  have hi (a b : ℕ) (hab : a ≤ b) (h : a = b) : IsIso (T.map hab) := by
    subst b
    rw [T.map_self]
    infer_instance
  let f := T.mapAt (show s ≤ s+1 by omega)
  haveI : IsIso f := hi s.toNat (s+1).toNat (by omega) (by omega)
  have hLayer : IsZero (T.layer s) :=
    Pretriangulated.Triangle.isZero₃_of_isIso₁
      (Pretriangulated.Triangle.mk f (HasFunctorialCofiber.cofibι f)
        (HasFunctorialCofiber.cofibδ f))
      (HasFunctorialCofiber.cofib_distinguished f) (show IsIso f from inferInstance)
  letI : Subsingleton (T.FirstPage (s,t)) := ⟨fun a b => hLayer.eq_of_tgt a b⟩
  let D := (model.classical.obj (X.obj model.auxiliary)).ssData (s,t)
  letI : Subsingleton D.V :=
    (model.classicalTower.sequence (X.obj model.auxiliary)).ambient (s,t)
      |>.toLinearEquiv.injective.subsingleton
  exact page_subsingleton_of_ambient D _

public theorem sphere_page_filtration_zero (r : ℤ) (t : ℕ) (ht : t ≠ 0) :
    Subsingleton (model.classical.sphere.Page r (0,t)) := by
  let T := model.classicalTower.tower (SphereSpectrum (C := Spectrum))
  let e : T.layer 0 ≅ model.coefficients.object :=
    T.layerIso 0 ≪≫ (tensorLeft model.coefficients.object).mapIso T.zeroIso ≪≫
      ρ_ model.coefficients.object
  letI := model.coefficients.homotopy_vanishes (t : ℤ) (by exact_mod_cast ht)
  letI : Subsingleton (T.FirstPage (0,t)) := by
    change Subsingleton (HomotopyGroup (t : ℤ) (T.layer 0))
    exact (Iso.homCongr (Iso.refl (Sphere (C := Spectrum) (t : ℤ))) e).injective.subsingleton
  let D := model.classical.sphere.ssData (0,t)
  letI : Subsingleton D.V :=
    (model.classicalTower.sequence (SphereSpectrum (C := Spectrum))).ambient (0,t)
      |>.toLinearEquiv.injective.subsingleton
  exact page_subsingleton_of_ambient D _

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
