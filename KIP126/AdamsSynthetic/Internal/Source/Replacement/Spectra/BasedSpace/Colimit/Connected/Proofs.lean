module

/-
Copyright (c) 2026 Jiashuo Zhang and KIP126 contributors.
Released under the MIT license; see LICENSE.
Privately adapted from SII-MATH/Kervaire126Main, commit
c60fbbbb93ee1f225e69bb8b93d06b4f842d031d,
KIP126/Def/StableHomotopy/Spectra/BasedSpace/Colimit/Connected/Proofs.lean.
-/

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.BasedSpace.Under.Data
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Adjunction.Limits

@[expose] section

namespace KIP126.AdamsSynthetic.Source.BasedSpace

open CategoryTheory CategoryTheory.Limits

universe u v w

/-- In a connected based diagram the basepoints already have a common
image, so its based colimit is also the actual topological colimit. -/
noncomputable instance forgetToTop_preservesConnectedColimits
    (J : Type w) [Category.{v} J] [IsConnected J] :
    PreservesColimitsOfShape J forgetToTop.{u} := by
  change PreservesColimitsOfShape J (underEquivalence.functor ⋙ Under.forget pointSpace)
  infer_instance

end KIP126.AdamsSynthetic.Source.BasedSpace
