module

public import KIP126.Def.StableHomotopy.Spectra.Prespectrum.Colimit.Proofs
public import Mathlib.CategoryTheory.Limits.Preserves.Basic

@[expose] public section

namespace KIP126.StableHomotopy.Spectra.Prespectrum

open CategoryTheory CategoryTheory.Limits

universe u

set_option backward.isDefEq.respectTransparency false

/-- Evaluation carries the displayed actual prespectrum colimit to the
actual based-space colimit at that level. -/
noncomputable def evaluation_pointwiseColimit_isColimit {J : Type u} [Category.{u} J]
    (F : J ⥤ Prespectrum.{u}) (n : ℕ) :
    IsColimit ((evaluationFunctor n).mapCocone (pointwiseColimitCocone F)) :=
  colimit.isColimit (F ⋙ evaluationFunctor n)

instance evaluationFunctor_preservesColimit {J : Type u} [Category.{u} J]
    (F : J ⥤ Prespectrum.{u}) (n : ℕ) : PreservesColimit F (evaluationFunctor n) :=
  preservesColimit_of_preserves_colimit_cocone
    (pointwiseColimitCocone_isColimit F) (evaluation_pointwiseColimit_isColimit F n)

instance evaluationFunctor_preservesColimits (n : ℕ) :
    PreservesColimitsOfSize.{u,u} (evaluationFunctor.{u} n) where
  preservesColimitsOfShape := { preservesColimit := evaluationFunctor_preservesColimit _ n }

end KIP126.StableHomotopy.Spectra.Prespectrum
