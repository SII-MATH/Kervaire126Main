module

public import KIP126.Def.SpectralSequence.Convergence.Data
public import KIP126.Def.SpectralSequence.Internal.Algebra.Filtration.Predicates

import all KIP126.Def.SpectralSequence.Convergence.Data

@[expose] section

/-!
# Convergence predicates for nested-subobject spectral sequences
-/

namespace KIP126.Core.SpectralSequence

open CategoryTheory

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The infinity-page class `y` detects the filtered class represented by `x`. -/
public def Detects
    {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E : SpectralSequence C ω} {ω' : Type w} {A : ω' → C} {F : Filtration A}
    (conv : Convergence E A F)
    {T : C} {k : ω}
    (y : T ⟶ (E.ssData k).eInfty)
    (x : T ⟶ Subobject.underlying.obj
      (F.F (conv.reindex k).1 (conv.reindex k).2)) : Prop :=
  y ≫ (conv.iso k).hom =
    x ≫ F.toAssociatedGraded (conv.reindex k).1 (conv.reindex k).2

end KIP126.Core.SpectralSequence
