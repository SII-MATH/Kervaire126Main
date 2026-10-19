module

import KIP126.Literature.Standard

/- Review-only candidate type for a smaller pure triangulated route.
No inhabitant is asserted. Arbitrary inclusion-compatible comparisons are
not required to give globally distinguished triangles. -/

open CategoryTheory CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.AdamsSynthetic
open KIP126.Kervaire.Route KIP126.Literature
open KIP126.AdamsSynthetic.Standard

namespace KIP126.InterfaceReview.MHLambdaTensor

noncomputable section
set_option backward.isDefEq.respectTransparency false

def NormalizedFiniteQuotientHorizontalRows : Prop :=
  ∀ (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g +
      normalizedExponent model.classicalTower T.h = 1)
    (_hT : NormalizedTriangleCompatible model T he)
    (q : ℕ) (_hq : 0 < q),
    let N := normalizedTriangle model T he
    ∃ esusp : XModLambdaN (N.obj₂⟦(1 : ℤ)⟧) q ≅
        (XModLambdaN N.obj₂ q)⟦(1 : ℤ)⟧,
      XModLambdaN.incl (N.obj₂⟦(1 : ℤ)⟧) q ≫ esusp.hom =
        (shiftFunctor SyntheticSpectrum (1 : ℤ)).map (XModLambdaN.incl N.obj₂ q) ∧
      Triangle.mk (XModLambdaN.map N.mor₂ q) (XModLambdaN.map N.mor₃ q)
        (-(XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1 : ℤ)).map N.mor₁) q ≫
          esusp.hom)) ∈ distTriang SyntheticSpectrum

#check NormalizedFiniteQuotientHorizontalRows

end
end KIP126.InterfaceReview.MHLambdaTensor
