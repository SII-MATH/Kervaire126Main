module

public import Mathlib.Algebra.Category.ModuleCat.Subobject
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Images
public import Mathlib.LinearAlgebra.Quotient.Basic

@[expose] public section

namespace KIP126.SpectralSequence

open CategoryTheory CategoryTheory.Limits
universe u v
variable {R : Type u} [Ring R] {M : ModuleCat.{v} R}

/-- The categorical inclusion of subobjects is the usual submodule inclusion
under the specified representative isomorphisms. -/
theorem submodule_ofLE_underlyingIso (B Z : Submodule R M) (h : B ≤ Z) :
    Subobject.ofLE ((ModuleCat.subobjectModule M).symm B)
      ((ModuleCat.subobjectModule M).symm Z)
      ((ModuleCat.subobjectModule _).symm.monotone h) ≫
        (Subobject.underlyingIso (ModuleCat.ofHom Z.subtype)).hom =
      (Subobject.underlyingIso (ModuleCat.ofHom B.subtype)).hom ≫
        ModuleCat.ofHom (Submodule.inclusion h) := by
  change Subobject.ofLE (Subobject.mk (ModuleCat.ofHom B.subtype))
    (Subobject.mk (ModuleCat.ofHom Z.subtype)) _ ≫ _ = _
  rw [Subobject.ofLE_mk_le_mk_of_comm
    (ModuleCat.ofHom (Submodule.inclusion h)) (by rfl)]
  simp

/-- The categorical image has exactly the ordinary linear-map range. -/
theorem subobjectModule_image {L : ModuleCat.{v} R} (f : L ⟶ M) :
    (ModuleCat.subobjectModule M) (imageSubobject f) = LinearMap.range f.hom := by
  have h : imageSubobject f =
      (ModuleCat.subobjectModule M).symm (LinearMap.range f.hom) :=
    Subobject.mk_eq_mk_of_comm _ _ (ModuleCat.imageIsoRange f)
      (ModuleCat.imageIsoRange_hom_subtype f)
  rw [h, OrderIso.apply_symm_apply]

/-- The categorical kernel has exactly the ordinary linear-map kernel. -/
theorem subobjectModule_kernel {N : ModuleCat.{v} R} (f : M ⟶ N) :
    (ModuleCat.subobjectModule M) (kernelSubobject f) = LinearMap.ker f.hom := by
  have h : kernelSubobject f =
      (ModuleCat.subobjectModule M).symm (LinearMap.ker f.hom) :=
    Subobject.mk_eq_mk_of_comm _ _ (ModuleCat.kernelIsoKer f) (by simp)
  rw [h, OrderIso.apply_symm_apply]

/-- A categorical cokernel class is zero exactly on the ordinary range. -/
theorem cokernel_π_eq_zero_iff_mem_range {L N : ModuleCat.{v} R}
    (f : L ⟶ N) (x : N) :
    cokernel.π f x = 0 ↔ x ∈ LinearMap.range f.hom := by
  rw [← (ModuleCat.cokernelIsoRangeQuotient f).toLinearEquiv.map_eq_zero_iff]
  change ((cokernel.π f ≫ (ModuleCat.cokernelIsoRangeQuotient f).hom) x = 0) ↔ _
  rw [ModuleCat.cokernel_π_cokernelIsoRangeQuotient_hom]
  exact Submodule.Quotient.mk_eq_zero _

/-- The class of a cycle is zero exactly when its ambient representative
belongs to the boundary subobject. -/
theorem subobject_cokernel_π_eq_zero_iff (B Z : Subobject M) (h : B ≤ Z)
    (z : (Subobject.underlying.obj Z : ModuleCat R)) :
    cokernel.π (Subobject.ofLE B Z h) z = 0 ↔
      Z.arrow z ∈ (ModuleCat.subobjectModule M) B := by
  rw [cokernel_π_eq_zero_iff_mem_range]
  change (∃ b, (Subobject.ofLE B Z h).hom b = z) ↔
    ∃ b, B.arrow.hom b = Z.arrow z
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨b, (ConcreteCategory.congr_hom (Subobject.ofLE_arrow h) b).symm⟩
  · rintro ⟨b, hb⟩
    refine ⟨b, (ModuleCat.mono_iff_injective Z.arrow).mp inferInstance ?_⟩
    change (Subobject.ofLE B Z h ≫ Z.arrow) b = Z.arrow z
    rw [Subobject.ofLE_arrow]
    exact hb

end KIP126.SpectralSequence
