module

import all KIP126.ProofTools.GeneralizedLeibniz.LevelSource
import all KIP126.ProofTools.GeneralizedLeibniz.Propagation
import all KIP126.ProofTools.GeneralizedLeibniz.Square

/-! Private level-indexed language for AimPaper's GL square.
The classical page is `page`, the source lambda level is `level`, and the
actual quotient exponent is `page + level - 1`. Crossing is tested in this
actual quotient at the fixed weight, never reset to a smaller zero-level
extension. The normalized source label is the actual shifted native label;
no unproved calibration of `comparison.nuE2` at positive level is assumed.
-/

@[expose] section
namespace KIP126.ProofTools.Internal.Leibniz
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Standard
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

private def levelFiniteTargetLabel (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (q level : ℕ) (m s t : ℤ)
    (hm : (normalizedExponent model.classicalTower f : ℤ) ≤ m)
    (y : Ambient model Y (s+m,t+m)) :
    (model.family.obj ((SyntheticObject.quotient q (.nu Y)).obj
      model.nu model.auxiliary)).E₂
      (s+m,(t-s)+(s+m),t+normalizedExponent model.classicalTower f-level) :=
  regradeE2 (by ext <;> dsimp; omega)
    ((model.family.quotientProjection (model.nu.functor.obj (Y.obj model.auxiliary)) q).pageMap
      2 (s+m,t+m,t+normalizedExponent model.classicalTower f-level)
      (nuWeightLabel model Y (s+m) (t+m)
        (t+normalizedExponent model.classicalTower f-level) (by omega) y))

private structure LevelFiniteExtensionWitness (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (page level : ℕ) (m s t : ℤ)
    (x : Ambient model X (s,t)) (y : Ambient model Y (s+m,t+m)) where
  page_ge_two : 2 ≤ page
  length_lower : (normalizedExponent model.classicalTower f : ℤ) ≤ m
  length_upper : m ≤ (page:ℤ)-2+normalizedExponent model.classicalTower f
  source : ((model.family.obj ((SyntheticObject.quotient (page+level-1)
    (extensionSourceObject model X Y f)).obj model.nu model.auxiliary)).sequence.ssData
      (s,(t-s)+s,t+normalizedExponent model.classicalTower f-level)).eInfty
  target : ((model.family.obj ((SyntheticObject.quotient (page+level-1) (.nu Y)).obj
    model.nu model.auxiliary)).sequence.ssData
      (s+m,(t-s)+(s+m),t+normalizedExponent model.classicalTower f-level)).eInfty
  source_rep : HasInfinityRepresentative _ 2 _
    (levelFiniteSourceLabel X (page+level-1) (normalizedExponent model.classicalTower f)
      s t level x) source
  target_rep : HasInfinityRepresentative _ 2 _
    (levelFiniteTargetLabel X Y f (page+level-1) level m s t length_lower y) target
  equation : TowerExtensionEquation
    (model.convergentMap (.quotient (page+level-1) (extensionSourceObject model X Y f))
      (.quotient (page+level-1) (.nu Y)) (finiteExtensionMap model X Y f (page+level-1)))
    (t-s,t+normalizedExponent model.classicalTower f-level) s m source target

private def LevelFiniteExtension (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (page level : ℕ) (m s t : ℤ)
    (x : Ambient model X (s,t)) (y : Ambient model Y (s+m,t+m)) : Prop :=
  Nonempty (LevelFiniteExtensionWitness X Y f page level m s t x y)

private def LevelFiniteNoCrossing (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (page level : ℕ) (m s t : ℤ) : Prop :=
  TowerNoCrossing (model.convergentMap
    (.quotient (page+level-1) (extensionSourceObject model X Y f))
    (.quotient (page+level-1) (.nu Y)) (finiteExtensionMap model X Y f (page+level-1)))
    (t-s,t+normalizedExponent model.classicalTower f-level) s m

private def LevelBoundaryNoCrossing (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (page level : ℕ) (r s t : ℤ) : Prop :=
  TowerNoCrossing (model.convergentMap
    (.quotient (page+level-1) (extensionSourceObject model X Y f))
    (.shift (1,-((page+level-1:ℕ):ℤ)) (extensionSourceObject model X Y f))
    (absoluteBoundary ((extensionSourceObject model X Y f).obj model.nu model.auxiliary)
      (page+level-1)))
    (t-s,t+normalizedExponent model.classicalTower f-level) s r

private def LevelBottomNoCrossing (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (page level : ℕ) (r l s t : ℤ) : Prop :=
  TowerNoCrossing (model.convergentMap
    (.shift (1,-((page+level-1:ℕ):ℤ)) (extensionSourceObject model X Y f))
    (.shift (1,-((page+level-1:ℕ):ℤ)) (.nu Y))
    ((SyntheticCategory.biShift (1,-((page+level-1:ℕ):ℤ))).map
      (model.normalizedMap X Y f).map))
    (t-s,t+normalizedExponent model.classicalTower f-level) (s+r) l

private theorem level_gl_bottom_point (page level : ℕ) (r s t e : ℤ)
    (hpage : 2 ≤ page) (hpr : (page:ℤ) ≤ r) :
    lambdaBoundaryPoint (r-page).toNat (page+level-1)
      ((t+r-1)-(s+r),(t+r-1)+e) = (t-s,t+e-level) := by
  have hk : ((r-page).toNat:ℤ) = r-page := Int.toNat_of_nonneg (by omega)
  have hq : ((page+level-1:ℕ):ℤ) = (page:ℤ)+level-1 := by omega
  ext <;> dsimp [lambdaBoundaryPoint] <;> omega

private def levelGLBottomSource (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (page level : ℕ) (r l s t : ℤ) (hpage : 2≤page) (hpr : (page:ℤ)≤r)
    {xInfinity : Ambient model X (s+r,t+r-1)}
    {yInfinity : Ambient model Y (s+r+l,t+r-1+l)}
    (W : InfiniteExtensionWitness model X Y f l (s+r) (t+r-1) xInfinity yInfinity) :
    ((model.family.obj ((SyntheticObject.shift (1,-((page+level-1:ℕ):ℤ))
      (extensionSourceObject model X Y f)).obj model.nu model.auxiliary)).sequence.ssData
      (s+r,(t-s)+(s+r),t+normalizedExponent model.classicalTower f-level)).eInfty :=
  (eqToHom (congrArg (fun p : ℤ×ℤ =>
    ((model.family.obj ((SyntheticObject.shift (1,-((page+level-1:ℕ):ℤ))
      (extensionSourceObject model X Y f)).obj model.nu model.auxiliary)).sequence.ssData
      (s+r,p.1+(s+r),p.2)).eInfty)
    (level_gl_bottom_point page level r s t (normalizedExponent model.classicalTower f) hpage hpr)))
      (lambdaBoundaryInfinity (extensionSourceObject model X Y f) (r-page).toNat (page+level-1)
        ((t+r-1)-(s+r),(t+r-1)+normalizedExponent model.classicalTower f) (s+r) W.source)

private def levelGLBottomTarget (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (page level : ℕ) (r l s t : ℤ) (hpage : 2≤page) (hpr : (page:ℤ)≤r)
    {xInfinity : Ambient model X (s+r,t+r-1)}
    {yInfinity : Ambient model Y (s+r+l,t+r-1+l)}
    (W : InfiniteExtensionWitness model X Y f l (s+r) (t+r-1) xInfinity yInfinity) :
    ((model.family.obj ((SyntheticObject.shift (1,-((page+level-1:ℕ):ℤ)) (.nu Y)).obj
      model.nu model.auxiliary)).sequence.ssData
      (s+r+l,(t-s)+(s+r+l),t+normalizedExponent model.classicalTower f-level)).eInfty :=
  (eqToHom (congrArg (fun p : ℤ×ℤ =>
    ((model.family.obj ((SyntheticObject.shift (1,-((page+level-1:ℕ):ℤ)) (.nu Y)).obj
      model.nu model.auxiliary)).sequence.ssData
      (s+r+l,p.1+(s+r+l),p.2)).eInfty)
    (level_gl_bottom_point page level r s t (normalizedExponent model.classicalTower f) hpage hpr)))
      (lambdaBoundaryInfinity (.nu Y) (r-page).toNat (page+level-1)
        ((t+r-1)-(s+r),(t+r-1)+normalizedExponent model.classicalTower f) (s+r+l) W.target)

private theorem level_gl_bottom_extension (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (page level : ℕ) (r l s t : ℤ) (hpage : 2≤page) (hpr : (page:ℤ)≤r)
    {xInfinity : Ambient model X (s+r,t+r-1)}
    {yInfinity : Ambient model Y (s+r+l,t+r-1+l)}
    (W : InfiniteExtensionWitness model X Y f l (s+r) (t+r-1) xInfinity yInfinity) :
    TowerExtensionEquation
      (model.convergentMap
        (.shift (1,-((page+level-1:ℕ):ℤ)) (extensionSourceObject model X Y f))
        (.shift (1,-((page+level-1:ℕ):ℤ)) (.nu Y))
        ((SyntheticCategory.biShift (1,-((page+level-1:ℕ):ℤ))).map (model.normalizedMap X Y f).map))
      (t-s,t+normalizedExponent model.classicalTower f-level) (s+r) l
      (levelGLBottomSource X Y f page level r l s t hpage hpr W)
      (levelGLBottomTarget X Y f page level r l s t hpage hpr W) := by
  obtain ⟨hbottom,_,_⟩ := infinite_extension_lambda_boundary_shift X Y f
    (r-page).toNat (page+level-1) l (s+r) (t+r-1) xInfinity yInfinity W
  let A := SyntheticObject.shift (1,-((page+level-1:ℕ):ℤ)) (extensionSourceObject model X Y f)
  let B := SyntheticObject.shift (1,-((page+level-1:ℕ):ℤ)) (.nu Y)
  let g := (SyntheticCategory.biShift (1,-((page+level-1:ℕ):ℤ))).map (model.normalizedMap X Y f).map
  have transport (p p' : ℤ×ℤ) (hp : p=p')
      (x : ((model.family.obj (A.obj model.nu model.auxiliary)).sequence.ssData
        (s+r,p.1+(s+r),p.2)).eInfty)
      (y : ((model.family.obj (B.obj model.nu model.auxiliary)).sequence.ssData
        (s+r+l,p.1+(s+r+l),p.2)).eInfty)
      (he : TowerExtensionEquation (model.convergentMap A B g) p (s+r) l x y) :
      TowerExtensionEquation (model.convergentMap A B g) p' (s+r) l
        ((eqToHom (congrArg (fun p : ℤ×ℤ => ((model.family.obj (A.obj model.nu model.auxiliary)).sequence.ssData
          (s+r,p.1+(s+r),p.2)).eInfty) hp)) x)
        ((eqToHom (congrArg (fun p : ℤ×ℤ => ((model.family.obj (B.obj model.nu model.auxiliary)).sequence.ssData
          (s+r+l,p.1+(s+r+l),p.2)).eInfty) hp)) y) := by
    subst p'
    exact he
  exact transport _ _ (level_gl_bottom_point page level r s t (normalizedExponent model.classicalTower f) hpage hpr)
    _ _ hbottom

end
end KIP126.ProofTools.Internal.Leibniz
