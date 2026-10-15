module

public import KIP126.Def.ClassicalAdams.TowerFiltration.Proofs
public import KIP126.Def.SpectralSequence.Basic.Data
public import Mathlib.Algebra.Category.ModuleCat.Subobject

@[expose] public section

/-!
# SSData constructed from the Adams tower

This is the actual nested-subobject model of the tower, based at page two.
It has no dependency on a selected sphere foundation, a Lin comparison,
or Mathlib's spectral-sequence type. Its proved differential and
successor laws are assembled in `TowerSSData/Sequence/Data.lean`.
-/

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
  KIP126.StableHomotopy KIP126.SpectralSequence
universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : 𝟙_ C ⟶ H) (X : C)

/-- The internal cycle/boundary object of the constructed tower. Stage zero is E₂. -/
def adamsTowerSSData (s t : ℤ) : SSData (ModuleCat.{v} ℤ) where
  V := ModuleCat.of ℤ (adamsCycleAmbient unit X s t)
  Z r := (ModuleCat.subobjectModule _).symm (adamsCycleSubmodule unit X s t r)
  B r := (ModuleCat.subobjectModule _).symm (adamsBoundarySubmodule unit X s t r)
  Z_anti := (ModuleCat.subobjectModule _).symm.monotone.comp_antitone
    (adamsCycleSubmodule_antitone unit X s t)
  B_mono := (ModuleCat.subobjectModule _).symm.monotone.comp
    (adamsBoundarySubmodule_monotone unit X s t)
  Z_zero := by
    change (ModuleCat.subobjectModule (ModuleCat.of ℤ (adamsCycleAmbient unit X s t))).symm
      (adamsFiniteCycleSubmodule unit X s t 0) = ⊤
    rw [adamsFiniteCycleSubmodule_zero, OrderIso.map_top]
  B_le_Z r := (ModuleCat.subobjectModule _).symm.monotone
    (adamsBoundarySubmodule_le_cycle unit X s t r)
  Z_top_greatest A h := by
    apply (ModuleCat.subobjectModule _).le_iff_le.mp
    change (ModuleCat.subobjectModule _) A ≤
      (ModuleCat.subobjectModule _) ((ModuleCat.subobjectModule _).symm _)
    rw [OrderIso.apply_symm_apply]
    change (ModuleCat.subobjectModule _) A ≤
      ⨅ n : ℕ, adamsFiniteCycleSubmodule unit X s t n
    refine le_iInf fun (n : ℕ) => ?_
    have hn := (ModuleCat.subobjectModule _).monotone (h n)
    rw [OrderIso.apply_symm_apply] at hn
    exact hn
  B_top_least A h := by
    apply (ModuleCat.subobjectModule _).le_iff_le.mp
    change (ModuleCat.subobjectModule _) ((ModuleCat.subobjectModule _).symm _) ≤
      (ModuleCat.subobjectModule _) A
    rw [OrderIso.apply_symm_apply]
    change (⨆ n : ℕ, adamsFiniteBoundarySubmodule unit X s t n) ≤
      (ModuleCat.subobjectModule _) A
    refine iSup_le fun (n : ℕ) => ?_
    have hn := (ModuleCat.subobjectModule _).monotone (h n)
    rw [OrderIso.apply_symm_apply] at hn
    exact hn

end
end KIP126.Classical.Adams
