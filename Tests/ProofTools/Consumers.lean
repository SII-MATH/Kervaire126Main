module

import KIP126.Def.ProofTools

/-! The fixed tools preserve genuine page, cycle, extension, triangle and
crossing hypotheses; their callers never supply upstream result packages. -/
namespace Tests.ProofTools
open CategoryTheory KIP126.StableHomotopy
open KIP126.Kervaire.Route KIP126.ProofTools
open KIP126.AdamsSynthetic
open KIP126.AdamsSynthetic.Standard (model)

example (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary) :
    FinitePageExtensionStretchingLaw model X Y f :=
  KIP126.ProofTools.Standard.finitePageExtensionStretching X Y f

example (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary) :
    GeneralizedLeibnizLaw model X Y f :=
  KIP126.ProofTools.Standard.generalizedLeibniz X Y f

example (T : TriangleData model.auxiliary) : GeneralizedMahowaldLaw model T :=
  KIP126.ProofTools.Standard.generalizedMahowald T

example (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (rEarlier rLater : ℕ) (n s t : ℤ)
    (x : Ambient model X (s,t)) (y : Ambient model Y (s+n,t+n))
    (hr : 2 ≤ rEarlier) (hle : rEarlier ≤ rLater)
    (hn : (normalizedExponent model.classicalTower f : ℤ) ≤ n)
    (hnUpper : n ≤ (rEarlier : ℤ)-2+normalizedExponent model.classicalTower f)
    (hx : IsCycle model X ((rLater : ℤ)-1) (s,t) x)
    (hy : IsCycle model Y ((rLater : ℤ)-1-n+normalizedExponent model.classicalTower f)
      (s+n,t+n) y)
    (hW : FiniteExtension model X Y f rEarlier n s t x y)
    (hcross : ¬ FiniteExtensionNonliftableCrossing model X Y f rEarlier rLater n s t) :
    FiniteExtension model X Y f rLater n s t x y :=
  KIP126.ProofTools.Standard.finitePageExtensionStretching X Y f
    rEarlier rLater n s t x y hr hle hn hnUpper hx hy hW hcross

#check_failure KIP126.ProofTools.Standard.lambda_target_class
#check_failure KIP126.Challenge2
#check_failure KIP126.Literature.LiteratureResults
#check_failure KIP126.Main.h6_sq_permanent
end Tests.ProofTools
