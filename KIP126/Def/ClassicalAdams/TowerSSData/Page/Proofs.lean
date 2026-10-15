module

public import KIP126.Def.ClassicalAdams.TowerSSData.Page.Data
public import KIP126.Def.SpectralSequence.ModuleQuotient.Proofs

@[expose] public section

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
  KIP126.StableHomotopy KIP126.SpectralSequence
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : 𝟙_ C ⟶ H) (X : C)

set_option backward.isDefEq.respectTransparency false in
/-- The page comparison sends an internal cycle to the very same tower class. -/
theorem adamsTowerSSDataPageIso_π (s t : ℤ) (n : ℕ) :
    (submoduleUnderlyingIso (M := ModuleCat.of ℤ (adamsCycleAmbient unit X s t))
      (adamsFiniteCycleSubmodule unit X s t n)).inv ≫
      (adamsTowerSSData unit X s t).pageπ (n : WithTop ℕ) ≫
      (adamsTowerSSDataPageIso unit X s t n).hom =
    ModuleCat.ofHom ((adamsCycleBoundaries unit X (n + 2) (by omega) s t).mkQ.comp
      (adamsFiniteCycleEquiv unit X s t n).toLinearMap) := by
  unfold adamsTowerSSDataPageIso
  unfold submoduleUnderlyingIso
  rw [Iso.trans_hom]
  refine (submoduleCokernelIso_π_assoc
    (M := ModuleCat.of ℤ (adamsCycleAmbient unit X s t))
    (adamsFiniteBoundarySubmodule unit X s t n)
    (adamsFiniteCycleSubmodule unit X s t n)
    (adamsFiniteBoundarySubmodule_le_cycle unit X s t n n) _).trans ?_
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Projection from any specified submodule of cycles preserves its representatives. -/
theorem adamsTowerSSDataPageIso_submodule_π (s t : ℤ) (n : ℕ)
    (W : Submodule ℤ (adamsCycleAmbient unit X s t))
    (hW : W ≤ adamsFiniteCycleSubmodule unit X s t n) :
    (submoduleUnderlyingIso (M := ModuleCat.of ℤ (adamsCycleAmbient unit X s t)) W).inv ≫
      Subobject.ofLE
        ((ModuleCat.subobjectModule (ModuleCat.of ℤ (adamsCycleAmbient unit X s t))).symm W)
        ((adamsTowerSSData unit X s t).Z (n : WithTop ℕ))
        ((ModuleCat.subobjectModule _).symm.monotone hW) ≫
      (adamsTowerSSData unit X s t).pageπ (n : WithTop ℕ) ≫
      (adamsTowerSSDataPageIso unit X s t n).hom =
    ModuleCat.ofHom ((adamsCycleBoundaries unit X (n + 2) (by omega) s t).mkQ.comp
      ((adamsFiniteCycleEquiv unit X s t n).toLinearMap.comp
        (Submodule.inclusion hW))) := by
  refine (submoduleUnderlyingIso_inv_ofLE_assoc
    (M := ModuleCat.of ℤ (adamsCycleAmbient unit X s t)) W
    (adamsFiniteCycleSubmodule unit X s t n) hW _).trans ?_
  rw [adamsTowerSSDataPageIso_π unit X s t n]
  rfl

/-- Every internal page element has an actual finite-cycle representative. -/
theorem adamsTowerSSData_projection_surjective (s t : ℤ) (n : ℕ) :
    Function.Surjective (fun x : adamsFiniteCycleSubmodule unit X s t n =>
      (adamsTowerSSData unit X s t).pageπ (n : WithTop ℕ)
        ((submoduleUnderlyingIso (M := ModuleCat.of ℤ (adamsCycleAmbient unit X s t))
          (adamsFiniteCycleSubmodule unit X s t n)).inv x)) := by
  apply Function.Surjective.comp
  · exact (ModuleCat.epi_iff_surjective _).mp
      (inferInstanceAs (CategoryTheory.Epi (CategoryTheory.Limits.cokernel.π _)))
  · exact (ModuleCat.epi_iff_surjective _).mp inferInstance

end
end KIP126.Classical.Adams
