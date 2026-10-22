module

public import KIP126.Literature.Triangles
public import KIP126.AdamsSynthetic.Standard.Ext

/-! The selected special-fiber/Ext comparison, restricted to the same
cofiber sequence needed by finite-layer composition. Sources: BHS,
Theorem 9.12(5), Corollary 9.13; Pstragowski, Lemma 4.56.
This is a registered literature comparison, not a proof of composition. -/

@[expose] section
namespace KIP126.Literature.Standard
open CategoryTheory CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.AdamsSynthetic KIP126.AdamsSynthetic.Standard KIP126.Kervaire.Route
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-- The normalized first-quotient operation equals the genuine Ext boundary
of the same g/h homology short exact sequence. The source coordinates,
suspension, and normalization are fixed; no caller comparison or
finite-layer composition assumptions occur here. -/
public theorem firstQuotient_ext_boundary
    (T : TriangleData model.auxiliary)
    (hf : normalizedExponent model.classicalTower T.f = 1)
    (hg : normalizedExponent model.classicalTower T.g = 0)
    (hh : normalizedExponent model.classicalTower T.h = 0)
    (hT : NormalizedTriangleCompatible model T (by simp [hf,hg,hh]))
    (hH : HomologyShortExact coefficients (Triangle.mk T.f T.g T.h).rotate)
    (s t : ℤ) (x : (classical.obj (T.X.obj auxiliary)).Page 2 (s,t)) :
    (let F : (SyntheticCategory.biShift (Syn := SyntheticSpectrum) (0,1)).obj
          (model.nu.functor.obj (T.X.obj model.auxiliary)) ⟶
          model.nu.functor.obj (T.Y.obj model.auxiliary) := by
        simpa only [hf, Nat.cast_one] using (model.normalizedMap T.X T.Y T.f).map
     let a := (model.firstQuotient T.X 1 s t).symm x
     let b := a ≫ XModLambdaN.map F 1 ≫
       XModLambdaN.map (SyntheticCategory.biShift_zero.inv.app
         (model.nu.functor.obj (T.Y.obj model.auxiliary))) 1
     model.firstQuotient T.Y 0 (s+1) (t+1)
       (homotopyRegrade (by omega) (by omega) b)) = cofiberExtBoundary T hH s t x := by
  sorry

end
end KIP126.Literature.Standard
