module

public import KIP126.Def.SpectralSequence.Extension.Data

@[expose] public section

/-!
# Two-term extension complexes

The two-term graded object, differential and filtration are the
constructions defined in `BoundedExtension`.
-/

namespace KIP126.SpectralSequence

open CategoryTheory CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The graded object supported in degrees `1` and `0`. -/
noncomputable def twoTermObj (X₁ X₂ : C) : ℤ → C :=
  BoundedExtension.twoTermObj X₁ X₂

/-- The two-term filtration inherited from the source and target. -/
noncomputable def twoTermFil {X₁ X₂ : C}
    (fil₁ : ℤ → Subobject X₁) (fil₂ : ℤ → Subobject X₂) :
    ℤ → (k : ℤ) → Subobject (twoTermObj X₁ X₂ k) :=
  BoundedExtension.twoTermFil fil₁ fil₂

end KIP126.SpectralSequence
