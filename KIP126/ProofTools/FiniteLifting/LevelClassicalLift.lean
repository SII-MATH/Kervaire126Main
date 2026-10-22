module

import all KIP126.ProofTools.FiniteLifting.ClassicalLift
import all KIP126.ProofTools.FiniteLifting.LevelSourceLift
import all KIP126.ProofTools.GeneralizedLeibniz.LevelLanguage
import all KIP126.ProofTools.LevelLanguage

@[expose] section
namespace KIP126.ProofTools.Internal.FiniteLifting
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
open KIP126.ProofTools.Internal.Leibniz
open KIP126.ProofTools.Internal.MahowaldLeibniz
open KIP126.ProofTools.Paper.NuNumericalExtensions
open KIP126.AdamsSynthetic.Standard (model Spectrum SyntheticSpectrum)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

/-- No crossing transports the specified full source to the finite target
at the original quotient and weight, including the terminal layer. -/
private theorem level_finite_target_of_full_source
    (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (page level : ℕ) (m s t : ℤ)
    (x : Ambient model X (s,t)) (y : Ambient model Y (s+m,t+m))
    (W : LevelFiniteExtensionWitness X Y f page level m s t x y)
    (hnc : LevelFiniteNoCrossing X Y f page level m s t)
    (a : BiHom (t-s) (t+normalizedExponent model.classicalTower f-level)
      ((extensionSourceObject model X Y f).obj model.nu model.auxiliary))
    (ha : Detects (model.convergence (.quotient (page+level-1)
        (extensionSourceObject model X Y f)))
      (s,(t-s)+s,t+normalizedExponent model.classicalTower f-level)
      (levelFiniteSourceLabel X (page+level-1) (normalizedExponent model.classicalTower f)
        s t level x)
      (homotopyRegrade (by dsimp; omega) rfl (a ≫ XModLambdaN.incl _ (page+level-1)))) :
    Detects (model.convergence (.quotient (page+level-1) (.nu Y)))
      (s+m,(t-s)+(s+m),t+normalizedExponent model.classicalTower f-level)
      (levelFiniteTargetLabel X Y f (page+level-1) level m s t W.length_lower y)
      (homotopyRegrade (by dsimp; omega) rfl
        ((a ≫ (model.normalizedMap X Y f).map) ≫ XModLambdaN.incl _ (page+level-1))) := by
  let q := page+level-1
  let A := extensionSourceObject model X Y f
  let p : ℤ × ℤ := (t-s,t+normalizedExponent model.classicalTower f-level)
  obtain ⟨source,hsource,ar,har,hgar⟩ := frame_of_source_detects
    (model.convergence (.quotient q A)) p s _ (a ≫ XModLambdaN.incl _ q) ha
  have hs : source=W.source := hsource.unique W.source_rep
  rw [hs] at hgar
  obtain ⟨br,hbr,hgbr⟩ := tower_target_of_any_source_frame
    (model.convergentMap (.quotient q A) (.quotient q (.nu Y))
      (finiteExtensionMap model X Y f q)) p s m W.source W.target
    W.equation hnc ar hgar
  have hb := source_frame_detects (model.convergence (.quotient q (.nu Y)))
    p (s+m) W.target _ W.target_rep br hgbr
  rw [←hbr,har] at hb
  have hnat : (a ≫ XModLambdaN.incl _ q) ≫ finiteExtensionMap model X Y f q =
      (a ≫ (model.normalizedMap X Y f).map) ≫ XModLambdaN.incl _ q := by
    change (a ≫ XModLambdaN.incl
        ((SyntheticCategory.biShift (0,(normalizedExponent model.classicalTower f:ℤ))).obj
          (model.nu.functor.obj (X.obj model.auxiliary))) q) ≫
        XModLambdaN.map (model.normalizedMap X Y f).map q = _
    simpa only [Category.assoc] using congrArg (fun z => a ≫ z)
      (XModLambdaN.incl_naturality (model.normalizedMap X Y f).map q).symm
  rw [hnat] at hb
  exact hb

/-- The actual image of a full source supplies both target permanence and
full target detection, without assuming a lift of the finite target. -/
private theorem level_finite_image_detects
    (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (page level : ℕ) (m s t : ℤ)
    (x : Ambient model X (s,t)) (y : Ambient model Y (s+m,t+m))
    (W : LevelFiniteExtensionWitness X Y f page level m s t x y)
    (hnc : LevelFiniteNoCrossing X Y f page level m s t)
    (a : BiHom (t-s) (t+normalizedExponent model.classicalTower f-level)
      ((extensionSourceObject model X Y f).obj model.nu model.auxiliary))
    (ha : Detects (model.convergence (.quotient (page+level-1)
        (extensionSourceObject model X Y f)))
      (s,(t-s)+s,t+normalizedExponent model.classicalTower f-level)
      (levelFiniteSourceLabel X (page+level-1) (normalizedExponent model.classicalTower f)
        s t level x)
      (homotopyRegrade (by dsimp; omega) rfl (a ≫ XModLambdaN.incl _ (page+level-1)))) :
    IsPermanentCycle (model.classical.obj (Y.obj model.auxiliary)) (s+m,t+m) y ∧
    Detects (model.convergence (.nu Y))
      (s+m,t+m,t+normalizedExponent model.classicalTower f-level)
      (nuWeightLabel model Y (s+m) (t+m) (t+normalizedExponent model.classicalTower f-level)
        (by have := W.length_lower; omega) y)
      (homotopyRegrade (by dsimp; omega) rfl (a ≫ (model.normalizedMap X Y f).map)) := by
  have hb := level_finite_target_of_full_source X Y f page level m s t x y W hnc a ha
  let e : ℤ := normalizedExponent model.classicalTower f
  let w : ℤ := t+e-level
  let q := page+level-1
  have hw : 0 ≤ (t+m)-w ∧ (t+m)-w < (q:ℤ) := by
    have := W.length_lower
    have := W.length_upper
    have := W.page_ge_two
    constructor <;> dsimp [w,e,q] <;> omega
  have hq : 0<q := by have := W.page_ge_two; dsimp [q]; omega
  have hi : (s+m,(t-s)+(s+m),w)=(s+m,t+m,w) := by ext <;> dsimp; omega
  have hb' := detects_transport hi _ _ hb
  dsimp only [levelFiniteTargetLabel] at hb'
  rw [normalized_regrade_trans,normalized_homotopy_regrade_trans,regrade_comp_map] at hb'
  have hbfinite : Detects (model.convergence (.quotient q (.nu Y))) (s+m,t+m,w)
      ((model.family.quotientProjection (model.nu.functor.obj (Y.obj model.auxiliary)) q).pageMap
        2 (s+m,t+m,w) (nuWeightLabel model Y (s+m) (t+m) w (by omega) y))
      ((homotopyRegrade (show t-s=(t+m)-(s+m) by omega) rfl
        (a ≫ (model.normalizedMap X Y f).map)) ≫ XModLambdaN.incl _ q) := hb'
  have hy := finite_target_from_full_lift_is_permanent Y q hq (s+m) (t+m) w hw y _ hbfinite
  have hbfull := finite_projection_detects_reflect Y q hq (s+m) (t+m) w hw y _ hbfinite
  exact ⟨permanent_cycle_of_member Y (s+m,t+m) y hy,hbfull⟩

/-- Realizing the same full source and its actual normalized image gives
the classical extension; the target is proved permanent along the way. -/
private theorem level_extension_with_realized_source
    (R : RealizationCoordinates model)
    (hcomp : LambdaInversionAdamsComparison model R)
    (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (page level : ℕ) (m s t : ℤ)
    (x : Ambient model X (s,t)) (y : Ambient model Y (s+m,t+m))
    (W : LevelFiniteExtensionWitness X Y f page level m s t x y)
    (hnc : LevelFiniteNoCrossing X Y f page level m s t)
    (a : BiHom (t-s) (t+normalizedExponent model.classicalTower f-level)
      ((extensionSourceObject model X Y f).obj model.nu model.auxiliary))
    (ha : Detects (model.convergence (.quotient (page+level-1)
        (extensionSourceObject model X Y f)))
      (s,(t-s)+s,t+normalizedExponent model.classicalTower f-level)
      (levelFiniteSourceLabel X (page+level-1) (normalizedExponent model.classicalTower f)
        s t level x)
      (homotopyRegrade (by dsimp; omega) rfl (a ≫ XModLambdaN.incl _ (page+level-1))))
    (hclass : ClassicalDetects (model.classicalConvergence X) (s,t) x
      ((R.sphere (t-s) (t+normalizedExponent model.classicalTower f-level)).hom ≫
        model.recovery.realization.map a ≫
          (hcomp.shiftedNu X (normalizedExponent model.classicalTower f)).target.hom)) :
    IsPermanentCycle (model.classical.obj (Y.obj model.auxiliary)) (s+m,t+m) y ∧
      ∃ b : HomotopyGroup (t-s) (X.obj model.auxiliary),
        ClassicalDetects (model.classicalConvergence X) (s,t) x b ∧
        ClassicalDetects (model.classicalConvergence Y) (s+m,t+m) y
          (eqToHom (congrArg (Sphere (C := Spectrum))
            (show (t+m)-(s+m)=t-s by omega)) ≫ b ≫ f) := by
  obtain ⟨hy,hb⟩ := level_finite_image_detects X Y f page level m s t x y W hnc a ha
  let e := normalizedExponent model.classicalTower f
  let w : ℤ := t+e-level
  let b : HomotopyGroup (t-s) (X.obj model.auxiliary) :=
    (R.sphere (t-s) w).hom ≫ model.recovery.realization.map a ≫
      (hcomp.shiftedNu X e).target.hom
  have hstem : t-s=(t+m)-(s+m) := by omega
  have hw : w≤t+m := by have := W.length_lower; dsimp [w,e]; omega
  have hweight : (t+m)-(((t+m)-w).toNat:ℤ)=w := by
    rw [Int.toNat_of_nonneg (by omega)]
    omega
  have hc := (hcomp.nu Y).detects (s+m) (t+m) w _
    (homotopyRegrade hstem rfl (a ≫ (model.normalizedMap X Y f).map)) hb
  have hc' : ClassicalDetects (model.classicalConvergence Y) (s+m,t+m) y
      ((R.sphere ((t+m)-(s+m)) w).hom ≫
        model.recovery.realization.map
          (homotopyRegrade hstem rfl (a ≫ (model.normalizedMap X Y f).map)) ≫
            (hcomp.nu Y).target.hom) := by
    dsimp only [nuWeightLabel] at hc
    rw [KIP126.ProofTools.Paper.paper_e2Map_regrade model _ (s+m) (t+m) _ w hweight,
      hcomp.nu_e2] at hc
    exact hc
  refine ⟨hy,b,hclass,?_⟩
  convert hc' using 1
  symm
  calc
    _ = (eqToHom (congrArg (Sphere (C := Spectrum)) hstem.symm) ≫
        (R.sphere (t-s) w).hom ≫
          model.recovery.realization.map (a ≫ (model.normalizedMap X Y f).map)) ≫
            (hcomp.nu Y).target.hom := by
      simpa only [Category.assoc] using congrArg
        (fun z => z ≫ (hcomp.nu Y).target.hom)
        (KIP126.ProofTools.Paper.realization_homotopy_regrade model R
          (t-s) ((t+m)-(s+m)) w hstem (a ≫ (model.normalizedMap X Y f).map))
    _ = _ := by
      dsimp only [b]
      rw [Functor.map_comp]
      simp only [Category.assoc]
      rw [KIP126.ProofTools.Paper.normalized_realization_square model R hcomp X Y f]

/-- Complete level-indexed lifting: source permanence supplies the full
source, and actual no crossing preserves the prescribed finite target. -/
private theorem level_finite_extension_of_permanent_to_classical
    (R : RealizationCoordinates model)
    (hcomp : LambdaInversionAdamsComparison model R)
    (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (page level : ℕ) (m s t : ℤ)
    (x : Ambient model X (s,t)) (y : Ambient model Y (s+m,t+m))
    (hx : IsPermanentCycle (model.classical.obj (X.obj model.auxiliary)) (s,t) x)
    (W : LevelFiniteExtensionWitness X Y f page level m s t x y)
    (hnc : LevelFiniteNoCrossing X Y f page level m s t) :
    IsPermanentCycle (model.classical.obj (Y.obj model.auxiliary)) (s+m,t+m) y ∧
      ∃ a : HomotopyGroup (t-s) (X.obj model.auxiliary),
        ClassicalDetects (model.classicalConvergence X) (s,t) x a ∧
        ClassicalDetects (model.classicalConvergence Y) (s+m,t+m) y
          (eqToHom (congrArg (Sphere (C := Spectrum))
            (show (t+m)-(s+m)=t-s by omega)) ≫ a ≫ f) := by
  obtain ⟨a,ha,hclass⟩ := level_full_source_with_realization R hcomp X (page+level-1) level
    (normalizedExponent model.classicalTower f)
    (by have := normalizedExponent_le_one model.classicalTower f; omega)
    s t x (permanent_member_of_cycle X (s,t) x hx)
  exact level_extension_with_realized_source R hcomp X Y f page level m s t x y
    W hnc a ha hclass

/-- Public-interface candidate using only the existing finite-level
extension, no-crossing, permanence, and realization language. -/
private theorem finiteLevelExtensionToClassical
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
  obtain ⟨W⟩ :=
    (KIP126.ProofTools.Standard.levelFiniteExtension_iff_internal X Y f page level m s t x y).mp he
  exact level_finite_extension_of_permanent_to_classical R hcomp X Y f page level m s t x y
    hx W hnc

end
end KIP126.ProofTools.Internal.FiniteLifting
