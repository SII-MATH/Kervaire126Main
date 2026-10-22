module

/-
Copyright (c) 2026 Jiashuo Zhang and KIP126 contributors.
Released under the MIT license; see LICENSE.
Privately adapted from SII-MATH/Kervaire126Main, commit
c60fbbbb93ee1f225e69bb8b93d06b4f842d031d,
KIP126/Def/StableHomotopy/Spectra/Prespectrum/Colimit/Evaluation/Proofs.lean.
-/

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum.Colimit.Proofs
import Mathlib.CategoryTheory.Limits.Preserves.Basic

@[expose] section

namespace KIP126.AdamsSynthetic.Source.Prespectrum

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

end KIP126.AdamsSynthetic.Source.Prespectrum
