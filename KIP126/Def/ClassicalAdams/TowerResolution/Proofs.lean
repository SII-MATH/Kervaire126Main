module

public import KIP126.Def.ClassicalAdams.TowerResolution.Data
public import KIP126.Def.ClassicalAdams.TowerLayer.Proofs
public import KIP126.Def.ClassicalAdams.TowerDifferential.Proofs

import all KIP126.Def.StableHomotopy.Context.Proofs

@[expose] public section

/-! Comparison of the actual first differential with the resolution formula. -/

namespace KIP126.Classical.Adams

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Pretriangulated
  KIP126.StableHomotopy

universe u v

set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {H : C} (unit : 𝟙_ C ⟶ H) (X : C)

/-- Correct the two signs of inverse rotation by the negative identity on the
fiber. The result uses exactly the positive inclusion defining the tower. -/
theorem adamsResolutionTriangle_distinguished (s : ℕ) :
    adamsResolutionTriangle unit X s ∈ distTriang C := by
  apply isomorphic_distinguished _
    (adamsFiberTriangle_distinguished (adamsUnit unit (adamsTower unit X s)))
  exact Triangle.isoMk _ _ (-(Iso.refl _)) (Iso.refl _) (Iso.refl _)
    (by simp [adamsResolutionTriangle, adamsFiberTriangle_mor₁, adamsTowerStep])
    (by simp [adamsResolutionTriangle, adamsFiberTriangle, Triangle.invRotate])
    (by simp [adamsResolutionTriangle, adamsResolutionConnecting])

/-- The exact-couple boundary agrees with the unit-triangle boundary under
the constructed layer comparison. -/
theorem adamsK_eq_resolutionBoundary (s : ℕ) (t : ℤ) (x : adamsE1 unit X s t) :
    adamsK unit X s t x =
      adamsResolutionBoundary unit X s (t - s) (adamsE1HomologyEquiv unit X s t x) := by
  change connectingHomomorphism
    (HoCofiberSequence.ofMorphism (adamsTowerMapAt unit X s ((s : ℤ) + 1) (by omega)))
      (t - s) x = _
  simp only [connectingHomomorphism, HoCofiberSequence.ofMorphism,
    AddMonoidHom.coe_mk, ZeroHom.coe_mk, eqToHom_refl, Category.id_comp, Category.comp_id,
    adamsResolutionBoundary, adamsE1HomologyEquiv_apply]
  rw [adamsLayerIso_δ]
  simp only [adamsResolutionConnecting, Category.assoc, Preadditive.comp_neg]
  rfl

/-- At page one the tower lift is forced to be the connecting image. -/
theorem adamsCycleLift_one (s t : ℤ) (x : adamsCycles unit X 1 (by decide) s t) :
    adamsCycleLift unit X 1 (by decide) s t x = adamsK unit X s t x := by
  have h := adamsCycleLift_spec unit X 1 (by decide) s t x
  change adamsI unit X (t - s - 1) (s + 1) (s + 1) le_rfl
    (adamsCycleLift unit X 1 (by decide) s t x) = _ at h
  simpa only [adamsI_self, LinearMap.id_apply] using h

/-- The actual first quotient differential is `j ∘ k`, with explicit indices. -/
theorem adamsDifferential_one (s t : ℤ) (x : adamsPage unit X 1 (by decide) s t) :
    adamsPageOneEquiv unit X (s + 1) (t + 1 - 1)
      (adamsDifferential unit X 1 (by decide) s t x) =
        adamsJ unit X (s + 1) (t + 1 - 1)
          (Eq.mp (congrArg (fun n => HomotopyGroup n (adamsTowerAt unit X (s + 1)))
            (by omega : t - s - 1 = (t + 1 - 1) - (s + 1)))
            (adamsK unit X s t (adamsPageOneEquiv unit X s t x))) := by
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    change adamsJ unit X (s + 1) (t + 1 - 1)
      (adamsDifferentialLift unit X 1 (by decide) s t x) = _
    rw [adamsDifferentialLift, adamsCycleLift_one]
    rfl

/-- The same formula for the normalized bidegree `(s + 1, t)`. -/
theorem adamsPageD_one (s t : ℤ) (x : adamsPage unit X 1 (by decide) s t) :
    adamsPageOneEquiv unit X (s + 1) t
      ((adamsPageD unit X 1 (by decide) (s, t) (s + 1, t)).hom x) =
        adamsJ unit X (s + 1) t
          (Eq.mp (congrArg (fun n => HomotopyGroup n (adamsTowerAt unit X (s + 1)))
            (by omega : t - s - 1 = t - (s + 1)))
            (adamsK unit X s t (adamsPageOneEquiv unit X s t x))) := by
  have h (t' : ℤ) (ht : t + 1 - 1 = t') :
      adamsPageOneEquiv unit X (s + 1) t'
        ((adamsPageD unit X 1 (by decide) (s, t) (s + 1, t')).hom x) =
          adamsJ unit X (s + 1) t'
            (Eq.mp (congrArg (fun n => HomotopyGroup n (adamsTowerAt unit X (s + 1)))
              (by omega : t - s - 1 = t' - (s + 1)))
              (adamsK unit X s t (adamsPageOneEquiv unit X s t x))) := by
    subst t'
    erw [adamsPageD_target unit X 1 (by decide) s t]
    exact adamsDifferential_one unit X s t x
  exact h t (by omega)

/-- The actual first page differential, in coefficient homology coordinates,
is the boundary followed by the next unit. No Milnor coordinates are used. -/
theorem adamsPageD_one_homology (s : ℕ) (t : ℤ)
    (x : adamsPage unit X 1 (by decide) s t) :
    adamsPageOneHomologyEquiv unit X (s + 1) t
      ((adamsPageD unit X 1 (by decide) (s, t) ((s + 1 : ℕ), t)).hom x) =
        adamsResolutionDifferential unit X s t (adamsPageOneHomologyEquiv unit X s t x) := by
  change adamsE1HomologyEquiv unit X (s + 1) t
    (adamsPageOneEquiv unit X ((s : ℤ) + 1) t
      ((adamsPageD unit X 1 (by decide) (s, t) ((s : ℤ) + 1, t)).hom x)) = _
  rw [adamsPageD_one]
  change adamsE1HomologyEquiv unit X (s + 1) t (adamsJ unit X (s + 1 : ℕ) t _) = _
  rw [adamsE1HomologyEquiv_J, adamsK_eq_resolutionBoundary]
  rfl

/-- The independently defined resolution formula squares to zero, by comparison
with the constructed quotient-page differential. -/
theorem adamsResolutionDifferential_comp (s : ℕ) (t : ℤ)
    (x : HomotopyGroup (t - s) (H ⊗ adamsTower unit X s)) :
    adamsResolutionDifferential unit X (s + 1) t (adamsResolutionDifferential unit X s t x) = 0 := by
  obtain ⟨y, rfl⟩ := (adamsPageOneHomologyEquiv unit X s t).surjective x
  rw [← adamsPageD_one_homology, ← adamsPageD_one_homology]
  have h := congrArg (fun f => f.hom y)
    (adamsPageD_comp unit X 1 (by decide)
      (s, t) ((s + 1 : ℕ), t) ((s + 1 + 1 : ℕ), t))
  change ((adamsPageD unit X 1 (by decide) ((s + 1 : ℕ), t)
    ((s + 1 + 1 : ℕ), t)).hom
      ((adamsPageD unit X 1 (by decide) (s, t) ((s + 1 : ℕ), t)).hom y)) = 0 at h
  rw [h, map_zero]

end

end KIP126.Classical.Adams
