module

public import KIP126.SpectralSequence.Basic.Category.Data
import all KIP126.SpectralSequence.Basic.Category.Data

@[expose] section

/-!
# Categorical predicates for nested-subobject spectral sequences
-/

namespace KIP126.Core.SpectralSequence

open CategoryTheory

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A commutative square in the category of nested-subobject spectral sequences. -/
public abbrev CommSq
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    {W X Y Z : SpectralSequence C ι}
    (f : W ⟶ X) (g : W ⟶ Y) (h : X ⟶ Z) (i : Y ⟶ Z) : Prop :=
  CategoryTheory.CommSq f g h i

end KIP126.Core.SpectralSequence
