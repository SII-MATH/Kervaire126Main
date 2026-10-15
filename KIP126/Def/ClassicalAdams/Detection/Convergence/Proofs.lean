module

public import KIP126.Def.ClassicalAdams.Detection.Convergence.Data

@[expose] public section

namespace KIP126.Classical.Adams.TowerDetection
open CategoryTheory CategoryTheory.MonoidalCategory KIP126.StableHomotopy
open KIP126.SpectralSequence
universe u v
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : 𝟙_ C ⟶ H)
/-- KJ=0 puts the cofiber image of an ACTUAL tower lift in every cycle
submodule, with one common E₁ representative.  The class may be zero; no
nonzero permanent survival or convergence assertion is included here. -/
theorem exists_liftRepresentative (X : C) (p : ℤ × ℤ)
    (a : HomotopyGroup (p.2-p.1) (adamsTowerAt unit X p.1)) :
    ∃ z : InfiniteRepresentative unit X p,
      infiniteRepresentativeE1 unit X p z = adamsJ unit X p.1 p.2 a := by
  let x : adamsCycleAmbient unit X p.1 p.2 :=
    ⟨adamsJ unit X p.1 p.2 a, adamsJ_mem_cycles unit X 2 (by decide) p.1 p.2 a⟩
  have hx : x ∈ adamsCycleSubmodule unit X p.1 p.2 ⊤ := by
    apply (Submodule.mem_iInf _).mpr
    intro m
    exact adamsJ_mem_cycles unit X (m + 2) (by omega) p.1 p.2 a
  have hrange : x ∈ (ModuleCat.subobjectModule (ModuleCat.of ℤ (adamsCycleAmbient unit X p.1 p.2)))
      (((adamsTowerInternalSpectralSequence unit X).ssData p).Z ⊤) := by
    change x ∈ (ModuleCat.subobjectModule (ModuleCat.of ℤ (adamsCycleAmbient unit X p.1 p.2)))
      ((ModuleCat.subobjectModule (ModuleCat.of ℤ (adamsCycleAmbient unit X p.1 p.2))).symm (adamsCycleSubmodule unit X p.1 p.2 ⊤))
    rwa [OrderIso.apply_symm_apply]
  obtain ⟨z, hz⟩ := hrange
  exact ⟨z, congrArg Subtype.val hz⟩

end
end KIP126.Classical.Adams.TowerDetection
