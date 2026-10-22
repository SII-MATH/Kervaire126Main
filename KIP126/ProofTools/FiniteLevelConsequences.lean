module

public import KIP126.ProofTools.LevelLanguage
public import KIP126.Literature.LambdaInversionAdams
import all KIP126.ProofTools.FiniteLifting.CutoffDifferential
import all KIP126.ProofTools.FiniteLifting.LevelClassicalLift

@[expose] section
namespace KIP126.ProofTools.Standard
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Standard
open KIP126.ProofTools.Internal.Mahowald
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

public theorem cutoffAdamsDifferentialAtLevel
    (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (page level : ℕ) (r m l s t κ : ℤ)
    (x : Ambient model X (s,t)) (y : Ambient model Y (s+m,t+m))
    (u : Ambient model X (s+r,t+r-1))
    (v : Ambient model Y (s+r+l,t+r-1+l))
    (hpage : 2≤page) (hpr : (page:ℤ)≤r)
    (hm : (normalizedExponent model.classicalTower f:ℤ)≤m)
    (hmUpper : m≤(page:ℤ)-2+normalizedExponent model.classicalTower f)
    (hl : (normalizedExponent model.classicalTower f:ℤ)≤l)
    (hu : IsPermanent model X (s+r,t+r-1) u)
    (hv : IsPermanent model Y (s+r+l,t+r-1+l) v)
    (hdx : DifferentialAt model X r (s,t) (s+r,t+r-1) x u)
    (hFinite : KIP126.ProofTools.Standard.LevelFiniteExtension X Y f page level m s t x y)
    (hInfinity : InfiniteExtension model X Y f l (s+r) (t+r-1) u v)
    (hκ : 1≤κ) (hκD : κ≤r+l-m)
    (hsource : KIP126.ProofTools.Standard.LevelBoundaryNoCrossing X Y f page level r s t ∨
      KIP126.ProofTools.Standard.LevelFiniteNoCrossing X Y f page level m s t)
    (hbottom : ∀ a c : ℤ, s+r<a → a≤c → s+m+κ≤c → c≤s+r+l →
      ∀ source target, ¬ TowerEssentialExtension
        (model.convergentMap
          (.shift (1,-((page+level-1:ℕ):ℤ)) (extensionSourceObject model X Y f))
          (.shift (1,-((page+level-1:ℕ):ℤ)) (.nu Y))
          ((SyntheticCategory.biShift (1,-((page+level-1:ℕ):ℤ))).map
            (model.normalizedMap X Y f).map))
        (t-s,t+normalizedExponent model.classicalTower f-level) a (c-a) source target)
    (hzero : ∃ η : ((model.family.obj ((SyntheticObject.quotient (page+level-1) (.nu Y)).obj
        model.nu model.auxiliary)).sequence.ssData
          (s+m,(t-s)+(s+m),t+normalizedExponent model.classicalTower f-level)).eInfty,
      HasInfinityRepresentative _ 2 _
        (regradeE2 (by ext <;> dsimp; omega)
          ((model.family.quotientProjection (model.nu.functor.obj (Y.obj model.auxiliary))
            (page+level-1)).pageMap 2
            (s+m,t+m,t+normalizedExponent model.classicalTower f-level)
            (nuWeightLabel model Y (s+m) (t+m)
              (t+normalizedExponent model.classicalTower f-level) (by omega) y))) η ∧
      TowerExtensionEquation
        (model.convergentMap (.quotient (page+level-1) (.nu Y))
          (.shift (1,-((page+level-1:ℕ):ℤ)) (.nu Y))
          (XModLambdaN.proj ((SyntheticObject.nu Y).obj model.nu model.auxiliary) (page+level-1) ≫
            (biSuspensionIso ((page+level-1:ℕ):ℤ)
              ((SyntheticObject.nu Y).obj model.nu model.auxiliary)).inv))
        (t-s,t+normalizedExponent model.classicalTower f-level) (s+m) (κ-1) η 0)
    (hzeroCrossing : ∀ a c : ℤ, s+m<a → a≤c → c≤s+m+(κ-1) →
      ∀ source target, ¬ TowerEssentialExtension
        (model.convergentMap (.quotient (page+level-1) (.nu Y))
          (.shift (1,-((page+level-1:ℕ):ℤ)) (.nu Y))
          (XModLambdaN.proj ((SyntheticObject.nu Y).obj model.nu model.auxiliary) (page+level-1) ≫
            (biSuspensionIso ((page+level-1:ℕ):ℤ)
              ((SyntheticObject.nu Y).obj model.nu model.auxiliary)).inv))
        (t-s,t+normalizedExponent model.classicalTower f-level) a (c-a) source target) :
    DifferentialAt model Y (r+l-m) (s+m,t+m) (s+r+l,t+r-1+l) y v := by
  exact KIP126.ProofTools.Internal.FiniteLifting.cutoffAdamsDifferentialAtLevel
    X Y f page level r m l s t κ x y u v hpage hpr hm hmUpper hl hu hv hdx
    hFinite hInfinity hκ hκD hsource hbottom hzero hzeroCrossing

public theorem finiteLevelExtensionToClassical
    (R : RealizationCoordinates model)
    (hcomp : LambdaInversionAdamsComparison model R)
    (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (page level : ℕ) (m s t : ℤ)
    (x : Ambient model X (s,t)) (y : Ambient model Y (s+m,t+m))
    (hx : IsPermanentCycle (model.classical.obj (X.obj model.auxiliary)) (s,t) x)
    (he : KIP126.ProofTools.Standard.LevelFiniteExtension X Y f page level m s t x y)
    (hnc : KIP126.ProofTools.Standard.LevelFiniteNoCrossing X Y f page level m s t) :
    IsPermanentCycle (model.classical.obj (Y.obj model.auxiliary)) (s+m,t+m) y ∧
      ∃ a : HomotopyGroup (t-s) (X.obj model.auxiliary),
        ClassicalDetects (model.classicalConvergence X) (s,t) x a ∧
        ClassicalDetects (model.classicalConvergence Y) (s+m,t+m) y
          (eqToHom (congrArg (Sphere (C := Spectrum))
            (show (t+m)-(s+m)=t-s by omega)) ≫ a ≫ f) := by
  exact KIP126.ProofTools.Internal.FiniteLifting.finiteLevelExtensionToClassical
    R hcomp X Y f page level m s t x y hx he hnc

end
end KIP126.ProofTools.Standard
