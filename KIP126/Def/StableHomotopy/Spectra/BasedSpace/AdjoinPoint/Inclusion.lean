module

public import KIP126.Def.StableHomotopy.Spectra.BasedSpace.AdjoinPoint.Data
public import KIP126.Def.Topology.Pushout.Proofs

@[expose] public section

section

namespace KIP126.StableHomotopy.Spectra.BasedSpace

open CategoryTheory

universe u

/-- The original summand inclusion into the actual disjoint-basepoint space. -/
def adjoinPointInclusion (A : TopCat.{u}) : A ⟶ (adjoinPoint A).space :=
  TopCat.ofHom ⟨Sum.inl,continuous_inl⟩

end KIP126.StableHomotopy.Spectra.BasedSpace

end

section

namespace KIP126.StableHomotopy.Spectra.BasedSpace

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

end KIP126.StableHomotopy.Spectra.BasedSpace

end
