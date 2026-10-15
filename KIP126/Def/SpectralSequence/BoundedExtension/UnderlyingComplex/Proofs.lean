module

public import KIP126.Def.SpectralSequence.BoundedExtension.UnderlyingComplex.Data
public import KIP126.Def.SpectralSequence.Convergence.Data

@[expose] public section

/-!
# Boundedness of the filtered two-term complex
-/

namespace KIP126.SpectralSequence

open CategoryTheory CategoryTheory.Limits

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {ω' : Type w}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem underlyingComplex_d_one
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    (aMap : ∀ k', A₁ k' ⟶ A₂ k')
    (hcompat : ∀ (s : ℤ) (k' : ω'),
      ∃ φ : Subobject.underlying.obj (F₁.F s k') ⟶
          Subobject.underlying.obj (F₂.F s k'),
        φ ≫ (F₂.F s k').arrow = (F₁.F s k').arrow ≫ aMap k')
    (t : ω') :
    (underlyingComplex aMap hcompat t).d 1 = aMap t := by
  change (BoundedExtension.twoTermComplex (A₁ t) (A₂ t) (aMap t)).d 1 0 = aMap t
  exact BoundedExtension.twoTermComplex_d_one (A₁ t) (A₂ t) (aMap t)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem underlyingComplex_filDiff_one
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    (aMap : ∀ k', A₁ k' ⟶ A₂ k')
    (hcompat : ∀ (s : ℤ) (k' : ω'),
      ∃ φ : Subobject.underlying.obj (F₁.F s k') ⟶
          Subobject.underlying.obj (F₂.F s k'),
        φ ≫ (F₂.F s k').arrow = (F₁.F s k').arrow ≫ aMap k')
    (t : ω') (s : ℤ) :
    (underlyingComplex aMap hcompat t).filDiff s 1 =
      (hcompat s t).choose := by
  apply (cancel_mono (F₂.F s t).arrow).mp
  calc
    (underlyingComplex aMap hcompat t).filDiff s 1 ≫ (F₂.F s t).arrow =
        (F₁.F s t).arrow ≫ aMap t :=
      by
        simpa [FilteredComplex.filDiff, FilteredComplex.fil, FilteredComplex.d,
          underlyingComplex, twoTermFil, BoundedExtension.twoTermFil,
          BoundedExtension.twoTermComplex_d_one] using
          (underlyingComplex aMap hcompat t).differential_preserves s 1 |>.choose_spec
    _ = (hcompat s t).choose ≫ (F₂.F s t).arrow :=
      (hcompat s t).choose_spec.symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem underlyingComplex_filToAssocGraded_one
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    (aMap : ∀ k', A₁ k' ⟶ A₂ k')
    (hcompat : ∀ (s : ℤ) (k' : ω'),
      ∃ φ : Subobject.underlying.obj (F₁.F s k') ⟶
          Subobject.underlying.obj (F₂.F s k'),
        φ ≫ (F₂.F s k').arrow = (F₁.F s k').arrow ≫ aMap k')
    (t : ω') (s : ℤ) :
    (underlyingComplex aMap hcompat t).filToAssocGraded s 1 =
      F₁.toAssociatedGraded s t := by
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem underlyingComplex_filToAssocGraded_zero
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    (aMap : ∀ k', A₁ k' ⟶ A₂ k')
    (hcompat : ∀ (s : ℤ) (k' : ω'),
      ∃ φ : Subobject.underlying.obj (F₁.F s k') ⟶
          Subobject.underlying.obj (F₂.F s k'),
        φ ≫ (F₂.F s k').arrow = (F₁.F s k').arrow ≫ aMap k')
    (t : ω') (s : ℤ) :
    (underlyingComplex aMap hcompat t).filToAssocGraded s 0 =
      F₂.toAssociatedGraded s t := by
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Compatibility of the page-zero differential with the filtration quotient
maps, specialized to the nonzero differential of the two-term complex. -/
theorem underlyingComplex_assocGradedDiff_compat_one
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    (aMap : ∀ k', A₁ k' ⟶ A₂ k')
    (hcompat : ∀ (s : ℤ) (k' : ω'),
      ∃ φ : Subobject.underlying.obj (F₁.F s k') ⟶
          Subobject.underlying.obj (F₂.F s k'),
        φ ≫ (F₂.F s k').arrow = (F₁.F s k').arrow ≫ aMap k')
    (t : ω') (s : ℤ) :
    F₁.toAssociatedGraded s t ≫
        (underlyingComplex aMap hcompat t).assocGradedDiff s 1 =
      (hcompat s t).choose ≫ F₂.toAssociatedGraded s t := by
  rw [← underlyingComplex_filToAssocGraded_one aMap hcompat t s]
  rw [FilteredComplex.assocGradedDiff_compat]
  change (underlyingComplex aMap hcompat t).filDiff s 1 ≫
      (underlyingComplex aMap hcompat t).filToAssocGraded s 0 =
    (hcompat s t).choose ≫ F₂.toAssociatedGraded s t
  simp only [underlyingComplex_filDiff_one,
    underlyingComplex_filToAssocGraded_zero]

end KIP126.SpectralSequence
