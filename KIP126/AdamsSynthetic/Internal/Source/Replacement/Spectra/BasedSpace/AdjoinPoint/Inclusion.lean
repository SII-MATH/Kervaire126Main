module

/-
Copyright (c) 2026 Jiashuo Zhang and KIP126 contributors.
Released under the MIT license; see LICENSE.
Privately adapted from SII-MATH/Kervaire126Main, commit
c60fbbbb93ee1f225e69bb8b93d06b4f842d031d,
KIP126/Def/StableHomotopy/Spectra/BasedSpace/AdjoinPoint/Inclusion.lean.
-/

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.BasedSpace.AdjoinPoint.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.Pushout.Proofs

@[expose] section

section

namespace KIP126.AdamsSynthetic.Source.BasedSpace

open CategoryTheory

universe u

/-- The original summand inclusion into the actual disjoint-basepoint space. -/
def adjoinPointInclusion (A : TopCat.{u}) : A ⟶ (adjoinPoint A).space :=
  TopCat.ofHom ⟨Sum.inl,continuous_inl⟩

end KIP126.AdamsSynthetic.Source.BasedSpace

end

section

namespace KIP126.AdamsSynthetic.Source.BasedSpace

open CategoryTheory CategoryTheory.Limits

universe u

set_option backward.isDefEq.respectTransparency false

/-- Adding the same disjoint basepoint to both ends of an original map
gives its actual topological pushout along the source summand inclusion. -/
theorem adjoinPointMap_isPushout {A B : TopCat.{u}} (f : A ⟶ B) :
    IsPushout f (adjoinPointInclusion A) (adjoinPointInclusion B)
      (TopCat.ofHom (adjoinPointMap f).map) := by
  apply IsPushout.of_isColimit (c := PushoutCocone.mk _ _ (show
    f ≫ adjoinPointInclusion B = adjoinPointInclusion A ≫
      TopCat.ofHom (adjoinPointMap f).map from rfl))
  let d (s : PushoutCocone f (adjoinPointInclusion A)) :
      (adjoinPoint B).space ⟶ s.pt := TopCat.ofHom
    ⟨Sum.elim s.inl (fun _ => s.inr (adjoinPoint A).point),
      s.inl.hom.continuous.sumElim continuous_const⟩
  refine PushoutCocone.IsColimit.mk _ d ?_ ?_ ?_
  · intro s
    rfl
  · intro s
    ext x
    cases x with
    | inl a => exact ConcreteCategory.congr_hom s.condition a
    | inr p => cases p; rfl
  · intro s m hm₁ hm₂
    ext x
    cases x with
    | inl b => exact ConcreteCategory.congr_hom hm₁ b
    | inr p => cases p; exact ConcreteCategory.congr_hom hm₂ (adjoinPoint A).point

end KIP126.AdamsSynthetic.Source.BasedSpace

end
