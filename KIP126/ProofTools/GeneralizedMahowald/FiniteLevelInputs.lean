module

import all KIP126.ProofTools.GeneralizedMahowald.ActualNoCrossing
import all KIP126.ProofTools.DetectionOperations
import all KIP126.ProofTools.StretchingRepresentatives
import all KIP126.ProofTools.GeneralizedMahowald.Filtration

/-! Synchronization of the actual finite-level MH inputs.
No May conclusion is used here. All declarations are private.
-/

@[expose] section
namespace KIP126.ProofTools.Internal.Mahowald
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard KIP126.Literature
open KIP126.ProofTools.Internal
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

/-- The finite visibility bound for a quotient of an actually shifted nu object. -/
private theorem inside_shift_quotient_high_zero
    (X : ClassicalObject) (q : ℕ) (hq : 0 < q) (e m w s : ℤ)
    (hs : (q:ℤ) ≤ m+s-(w-e))
    (a : BiHom m w (XModLambdaN
      ((SyntheticCategory.biShift (0,e)).obj (model.nu.functor.obj (X.obj model.auxiliary))) q))
    (ha : FiltrationAtLeast model.syntheticTower s a) : a=0 := by
  apply synthetic_homotopy_separated (.shift (0,e) (.nu X)) q m w a
  intro j
  by_cases hj : s ≤ (j:ℤ)
  · exact (filtration_iff_of_infinity_zero
      (model.convergence (.quotient q (.shift (0,e) (.nu X)))) s j m w hj
      (fun v hv _ => shifted_quotient_eInfty_zero X q hq e v (m+v) w (by omega)) a).mp ha
  · exact model.syntheticTower.filtrationSubmodule_antitone _ (m,w) (by omega) ha

/-- Actual filtered shift transport reflects vanishing at a fixed filtration. -/
private theorem shifted_high_zero_of_base
    (X : SyntheticObject) (δ : ℤ × ℤ) (m w s : ℤ)
    (hzero : ∀ a : BiHom (m-δ.1) (w-δ.2) (X.obj model.nu model.auxiliary),
      FiltrationAtLeast model.syntheticTower s a → a=0)
    (a : BiHom m w ((SyntheticCategory.biShift δ).obj (X.obj model.nu model.auxiliary)))
    (ha : FiltrationAtLeast model.syntheticTower s a) : a=0 := by
  let p : ℤ × ℤ := (m-δ.1,w-δ.2)
  have hp : p+δ=(m,w) := by ext <;> simp [p]
  let E : FilteredPieceIso (model.convergence X).filtration
      (model.convergence (.shift δ X)).filtration p (m,w) :=
    hp ▸ (essShift δ).filtered X p
  have ha' : E.ambient.inv a ∈ ModuleCat.subobjectModule _
      ((model.convergence X).filtration.F s p) := by
    have hm : a ∈ ModuleCat.subobjectModule _
        ((model.convergence (.shift δ X)).filtration.F s (m,w)) := by
      simpa only [SyntheticTowerConvergence.filtration,
        SyntheticTowerPresentation.filtration,OrderIso.apply_symm_apply,
        FiltrationAtLeast,SyntheticObject.obj] using ha
    obtain ⟨ar,har⟩ := hm
    refine ⟨(E.level s).inv ar,?_⟩
    have he := ConcreteCategory.congr_hom (E.symm.level_arrow s) ar
    simpa only [ModuleCat.comp_apply,FilteredPieceIso.symm,Iso.symm_hom,har] using he
  have hz := hzero (E.ambient.inv a) (by
    simpa only [SyntheticTowerConvergence.filtration,
      SyntheticTowerPresentation.filtration,OrderIso.apply_symm_apply,
      FiltrationAtLeast] using ha')
  apply (ModuleCat.mono_iff_injective E.ambient.inv).mp inferInstance
  simpa only [map_zero] using hz

/-- Vanishing above the top visible layer of the actual shifted short quotient.
The source suspension and the normalized Z weight are both retained.
-/
private theorem finite_mh_target_high_zero
    (Z : ClassicalObject) (B : ℕ) (hB : 0 < B) (A e m w v : ℤ)
    (hwindow : (B:ℤ) ≤ m+v-w-A+e)
    (a : BiHom m w
      ((SyntheticObject.shift (1,0) (.shift (0,-A)
        (.quotient B (.shift (0,e) (.nu Z))))).obj model.nu model.auxiliary))
    (ha : FiltrationAtLeast model.syntheticTower (v+1) a) : a=0 := by
  apply shifted_high_zero_of_base (.shift (0,-A) (.quotient B (.shift (0,e) (.nu Z))))
    (1,0) m w (v+1) ?_ a ha
  intro b hb
  apply shifted_high_zero_of_base (.quotient B (.shift (0,e) (.nu Z)))
    (0,-A) (m-1) (w-0) (v+1) ?_ b hb
  intro c hc
  exact inside_shift_quotient_high_zero Z B hB e ((m-1)-0) ((w-0)-(-A))
    (v+1) (by dsimp at *; omega) c hc


/-- Reindex the target filtration of one actual extension equation. -/
private theorem equation_frames_at_target
    (X Y : SyntheticObject)
    (f : X.obj model.nu model.auxiliary ⟶ Y.obj model.nu model.auxiliary)
    (p : ℤ × ℤ) (s n v : ℤ) (hv : s+n=v)
    (x : ((model.family.obj (X.obj model.nu model.auxiliary)).sequence.ssData
      (s,p.1+s,p.2)).eInfty)
    (y : ((model.family.obj (Y.obj model.nu model.auxiliary)).sequence.ssData
      (v,p.1+v,p.2)).eInfty)
    (he : TowerExtensionEquation (model.convergentMap X Y f) p s n x
      ((eqToHom (congrArg (fun q =>
        ((model.family.obj (Y.obj model.nu model.auxiliary)).sequence.ssData q).eInfty)
        (show (v,p.1+v,p.2)=(s+n,p.1+(s+n),p.2) by rw [hv]))) y)) :
    0 ≤ n ∧ ∃
      (ar : (Subobject.underlying.obj ((model.syntheticTower.filtration
        (X.obj model.nu model.auxiliary)).F s p) : ModuleCat ℤ))
      (br : (Subobject.underlying.obj ((model.syntheticTower.filtration
        (Y.obj model.nu model.auxiliary)).F v p) : ModuleCat ℤ)),
      ((model.syntheticTower.filtration (X.obj model.nu model.auxiliary)).F s p).arrow ar ≫ f =
        ((model.syntheticTower.filtration (Y.obj model.nu model.auxiliary)).F v p).arrow br ∧
      (model.syntheticTower.filtration (X.obj model.nu model.auxiliary)).toAssociatedGraded s p ar =
        (infinityGradedIso (model.convergence X) p s).hom x ∧
      (model.syntheticTower.filtration (Y.obj model.nu model.auxiliary)).toAssociatedGraded v p br =
        (infinityGradedIso (model.convergence Y) p v).hom y := by
  subst v
  simpa using (tower_extension_iff (model.convergentMap X Y f) p s n x y).mp he

/-- Actual no-crossing synchronizes the two outgoing edges. Equality of the
highest-visible target then identifies their common target with the image
of the independently supplied third edge. No May lift is invoked.
-/
private theorem synchronized_detected_inputs
    (XA XH XB XD : SyntheticObject)
    (hmap : XA.obj model.nu model.auxiliary ⟶ XH.obj model.nu model.auxiliary)
    (dmap : XA.obj model.nu model.auxiliary ⟶ XD.obj model.nu model.auxiliary)
    (gmap : XB.obj model.nu model.auxiliary ⟶ XD.obj model.nu model.auxiliary)
    (p : ℤ × ℤ) (s l r sg m : ℤ) (hfil : sg+m=s+r)
    (x0 : (model.family.obj (XA.obj model.nu model.auxiliary)).E₂ (s,p.1+s,p.2))
    (xh : (model.family.obj (XH.obj model.nu model.auxiliary)).E₂ (s+l,p.1+(s+l),p.2))
    (yg : (model.family.obj (XB.obj model.nu model.auxiliary)).E₂ (sg,p.1+sg,p.2))
    (zd : (model.family.obj (XD.obj model.nu model.auxiliary)).E₂ (s+r,p.1+(s+r),p.2))
    (e0 : ((model.family.obj (XA.obj model.nu model.auxiliary)).sequence.ssData
      (s,p.1+s,p.2)).eInfty)
    (eh : ((model.family.obj (XH.obj model.nu model.auxiliary)).sequence.ssData
      (s+l,p.1+(s+l),p.2)).eInfty)
    (eg : ((model.family.obj (XB.obj model.nu model.auxiliary)).sequence.ssData
      (sg,p.1+sg,p.2)).eInfty)
    (ed : ((model.family.obj (XD.obj model.nu model.auxiliary)).sequence.ssData
      (s+r,p.1+(s+r),p.2)).eInfty)
    (hx0 : HasInfinityRepresentative _ 2 _ x0 e0)
    (hxh : HasInfinityRepresentative _ 2 _ xh eh)
    (hyg : HasInfinityRepresentative _ 2 _ yg eg)
    (hzd : HasInfinityRepresentative _ 2 _ zd ed)
    (hh : TowerExtensionEquation (model.convergentMap XA XH hmap) p s l e0 eh)
    (hd : TowerExtensionEquation (model.convergentMap XA XD dmap) p s r e0 ed)
    (hg : TowerExtensionEquation (model.convergentMap XB XD gmap) p sg m eg
      ((eqToHom (congrArg (fun q =>
        ((model.family.obj (XD.obj model.nu model.auxiliary)).sequence.ssData q).eInfty)
        (show (s+r,p.1+(s+r),p.2)=(sg+m,p.1+(sg+m),p.2) by rw [hfil]))) ed))
    (hnc : ActualNoCrossing (model.convergentMap XA XH hmap) p s l ∨
      ActualNoCrossing (model.convergentMap XA XD dmap) p s r)
    (htop : ∀ d : BiHom p.1 p.2 (XD.obj model.nu model.auxiliary),
      FiltrationAtLeast model.syntheticTower (s+r+1) d → d=0) :
    ∃ (a : BiHom p.1 p.2 (XA.obj model.nu model.auxiliary))
      (b : BiHom p.1 p.2 (XB.obj model.nu model.auxiliary)),
      Detects (model.convergence XA) (s,p.1+s,p.2) x0
        (homotopyRegrade (by dsimp; omega) rfl a) ∧
      Detects (model.convergence XH) (s+l,p.1+(s+l),p.2) xh
        (homotopyRegrade (by dsimp; omega) rfl (a≫hmap)) ∧
      Detects (model.convergence XD) (s+r,p.1+(s+r),p.2) zd
        (homotopyRegrade (by dsimp; omega) rfl (a≫dmap)) ∧
      Detects (model.convergence XB) (sg,p.1+sg,p.2) yg
        (homotopyRegrade (by dsimp; omega) rfl b) ∧
      Detects (model.convergence XD) (s+r,p.1+(s+r),p.2) zd
        (homotopyRegrade (by dsimp; omega) rfl (b≫gmap)) ∧
      a≫dmap=b≫gmap := by
  obtain ⟨ar,hr,dr,hga,hgh,hgd,hah,had⟩ := actual_common_source_frames
    (model.convergentMap XA XH hmap) (model.convergentMap XA XD dmap)
    p s l r e0 eh ed hh hd hnc
  obtain ⟨_,br,er,hbg,hgb,hge⟩ := equation_frames_at_target XB XD gmap p sg m (s+r)
    hfil eg ed hg
  let a := ((model.syntheticTower.filtration (XA.obj model.nu model.auxiliary)).F s p).arrow ar
  let b := ((model.syntheticTower.filtration (XB.obj model.nu model.auxiliary)).F sg p).arrow br
  have hdetA := source_frame_detects (model.convergence XA) p s e0 x0 hx0 ar hga
  have hdetH := source_frame_detects (model.convergence XH) p (s+l) eh xh hxh hr hgh
  have hdetD := source_frame_detects (model.convergence XD) p (s+r) ed zd hzd dr hgd
  have hdetB := source_frame_detects (model.convergence XB) p sg eg yg hyg br hgb
  have hdetG := source_frame_detects (model.convergence XD) p (s+r) ed zd hzd er hge
  rw [←hah] at hdetH
  rw [←had] at hdetD
  rw [←hbg] at hdetG
  refine ⟨a,b,hdetA,hdetH,hdetD,hdetB,hdetG,?_⟩
  dsimp only [a,b]
  rw [had,hbg]
  apply sub_eq_zero.mp
  apply htop
  have hdiff := (element_grade_equal_iff
    (model.syntheticTower.filtration (XD.obj model.nu model.auxiliary)) (s+r) p dr er).mp
      (hgd.trans hge.symm)
  simpa only [SyntheticTowerPresentation.filtration,OrderIso.apply_symm_apply,
    FiltrationAtLeast] using hdiff


private def mhInputZ (Z : ClassicalObject) (e : ℤ) : SyntheticObject :=
  .shift (0,e) (.nu Z)
private def mhInputA (Z : ClassicalObject) (e : ℤ) (A : ℕ) : SyntheticObject :=
  .quotient A (mhInputZ Z e)
private def mhInputH (VX : SyntheticObject) (A : ℕ) : SyntheticObject :=
  .shift (1,0) (.quotient A VX)
private def mhInputG (VY : SyntheticObject) (A B : ℕ) : SyntheticObject :=
  .shift (1,0) (.shift (0,-(A:ℤ)) (.quotient B VY))
private def mhInputD (Z : ClassicalObject) (e : ℤ) (A B : ℕ) : SyntheticObject :=
  .shift (1,0) (.shift (0,-(A:ℤ)) (.quotient B (mhInputZ Z e)))

private def mhInputDelta (Z : ClassicalObject) (e : ℤ) (A B : ℕ)
    (hA : 0 < A) (hB : 0 < B) :
    (mhInputA Z e A).obj model.nu model.auxiliary ⟶
      (((SyntheticCategory.biShift (0,-(A:ℤ))).obj
        (XModLambdaN ((mhInputZ Z e).obj model.nu model.auxiliary) B))⟦(1:ℤ)⟧) := by
  simpa only [mhInputA,SyntheticObject.obj,Nat.add_sub_cancel_left] using
    ((model.quotients.tower ((mhInputZ Z e).obj model.nu model.auxiliary)).triangle
      hA (show A < A+B by omega)).delta

private def mhInputHMap (VX : SyntheticObject) (Z : ClassicalObject) (e : ℤ) (A : ℕ)
    (h : (mhInputZ Z e).obj model.nu model.auxiliary ⟶
      (VX.obj model.nu model.auxiliary)⟦(1:ℤ)⟧)
    (exA : XModLambdaN ((VX.obj model.nu model.auxiliary)⟦(1:ℤ)⟧) A ≅
      (XModLambdaN (VX.obj model.nu model.auxiliary) A)⟦(1:ℤ)⟧) :
    (mhInputA Z e A).obj model.nu model.auxiliary ⟶
      (mhInputH VX A).obj model.nu model.auxiliary :=
  XModLambdaN.map h A ≫ exA.hom ≫
    (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).inv.app _

private def mhInputDMap (Z : ClassicalObject) (e : ℤ) (A B : ℕ)
    (hA : 0 < A) (hB : 0 < B) :
    (mhInputA Z e A).obj model.nu model.auxiliary ⟶
      (mhInputD Z e A B).obj model.nu model.auxiliary :=
  mhInputDelta Z e A B hA hB ≫
    (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).inv.app _

private def mhInputGMap (VY : SyntheticObject) (Z : ClassicalObject) (e : ℤ) (A B : ℕ)
    (g : VY.obj model.nu model.auxiliary ⟶ (mhInputZ Z e).obj model.nu model.auxiliary) :
    (mhInputG VY A B).obj model.nu model.auxiliary ⟶
      (mhInputD Z e A B).obj model.nu model.auxiliary :=
  (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).hom.app _ ≫
    (shiftFunctor SyntheticSpectrum (1:ℤ)).map
      ((SyntheticCategory.biShift (0,-(A:ℤ))).map (XModLambdaN.map g B)) ≫
    (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).inv.app _

/-- The native finite May inputs, constructed from the actual MH premises.
The only bound is the explicit finite visibility inequality; in the complete
statement it is the identity B=r+i-A. The E₂ labels are arbitrary specified
labels equipped with the four prescribed infinity representatives, so this
lemma applies directly to the statement's intrinsic classical labels.
-/
private theorem finite_level_synchronized_inputs
    (VX VY : SyntheticObject) (Z : ClassicalObject) (e : ℤ)
    (h : (mhInputZ Z e).obj model.nu model.auxiliary ⟶
      (VX.obj model.nu model.auxiliary)⟦(1:ℤ)⟧)
    (g : VY.obj model.nu model.auxiliary ⟶ (mhInputZ Z e).obj model.nu model.auxiliary)
    (A B : ℕ) (hA : 0 < A) (hB : 0 < B)
    (exA : XModLambdaN ((VX.obj model.nu model.auxiliary)⟦(1:ℤ)⟧) A ≅
      (XModLambdaN (VX.obj model.nu model.auxiliary) A)⟦(1:ℤ)⟧)
    (p : ℤ × ℤ) (s l r sg m : ℤ) (hfil : sg+m=s+r)
    (hwindow : (B:ℤ) ≤ p.1+(s+r)-p.2-A+e)
    (x0 : (model.family.obj ((mhInputA Z e A).obj model.nu model.auxiliary)).E₂
      (s,p.1+s,p.2))
    (xh : (model.family.obj ((mhInputH VX A).obj model.nu model.auxiliary)).E₂
      (s+l,p.1+(s+l),p.2))
    (yg : (model.family.obj ((mhInputG VY A B).obj model.nu model.auxiliary)).E₂
      (sg,p.1+sg,p.2))
    (zd : (model.family.obj ((mhInputD Z e A B).obj model.nu model.auxiliary)).E₂
      (s+r,p.1+(s+r),p.2))
    (e0 : ((model.family.obj ((mhInputA Z e A).obj model.nu model.auxiliary)).sequence.ssData
      (s,p.1+s,p.2)).eInfty)
    (eh : ((model.family.obj ((mhInputH VX A).obj model.nu model.auxiliary)).sequence.ssData
      (s+l,p.1+(s+l),p.2)).eInfty)
    (eg : ((model.family.obj ((mhInputG VY A B).obj model.nu model.auxiliary)).sequence.ssData
      (sg,p.1+sg,p.2)).eInfty)
    (ed : ((model.family.obj ((mhInputD Z e A B).obj model.nu model.auxiliary)).sequence.ssData
      (s+r,p.1+(s+r),p.2)).eInfty)
    (hx0 : HasInfinityRepresentative _ 2 _ x0 e0)
    (hxh : HasInfinityRepresentative _ 2 _ xh eh)
    (hyg : HasInfinityRepresentative _ 2 _ yg eg)
    (hzd : HasInfinityRepresentative _ 2 _ zd ed)
    (hh : TowerExtensionEquation
      (model.convergentMap (mhInputA Z e A) (mhInputH VX A) (mhInputHMap VX Z e A h exA))
      p s l e0 eh)
    (hd : TowerExtensionEquation
      (model.convergentMap (mhInputA Z e A) (mhInputD Z e A B) (mhInputDMap Z e A B hA hB))
      p s r e0 ed)
    (hg : TowerExtensionEquation
      (model.convergentMap (mhInputG VY A B) (mhInputD Z e A B) (mhInputGMap VY Z e A B g))
      p sg m eg
      ((eqToHom (congrArg (fun q =>
        ((model.family.obj ((mhInputD Z e A B).obj model.nu model.auxiliary)).sequence.ssData q).eInfty)
        (show (s+r,p.1+(s+r),p.2)=(sg+m,p.1+(sg+m),p.2) by rw [hfil]))) ed))
    (hnc : ActualNoCrossing
      (model.convergentMap (mhInputA Z e A) (mhInputH VX A) (mhInputHMap VX Z e A h exA))
        p s l ∨
      ActualNoCrossing
      (model.convergentMap (mhInputA Z e A) (mhInputD Z e A B) (mhInputDMap Z e A B hA hB))
        p s r) :
    ∃ (a : BiHom p.1 p.2 ((mhInputA Z e A).obj model.nu model.auxiliary))
      (b : BiHom p.1 p.2
        ((((SyntheticCategory.biShift (0,-(A:ℤ))).obj
          (XModLambdaN (VY.obj model.nu model.auxiliary) B)))⟦(1:ℤ)⟧)),
      Detects (model.convergence (mhInputA Z e A)) (s,p.1+s,p.2) x0
        (homotopyRegrade (by dsimp; omega) rfl a) ∧
      Detects (model.convergence (mhInputH VX A)) (s+l,p.1+(s+l),p.2) xh
        (homotopyRegrade (by dsimp; omega) rfl (a≫mhInputHMap VX Z e A h exA)) ∧
      Detects (model.convergence (mhInputD Z e A B)) (s+r,p.1+(s+r),p.2) zd
        (homotopyRegrade (by dsimp; omega) rfl (a≫mhInputDMap Z e A B hA hB)) ∧
      Detects (model.convergence (mhInputG VY A B)) (sg,p.1+sg,p.2) yg
        (homotopyRegrade (by dsimp; omega) rfl
          (b≫(SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).inv.app _)) ∧
      Detects (model.convergence (mhInputD Z e A B)) (s+r,p.1+(s+r),p.2) zd
        (homotopyRegrade (by dsimp; omega) rfl
          (b≫(shiftFunctor SyntheticSpectrum (1:ℤ)).map
            ((SyntheticCategory.biShift (0,-(A:ℤ))).map (XModLambdaN.map g B)) ≫
            (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).inv.app _)) ∧
      a≫mhInputDelta Z e A B hA hB =
        b≫(shiftFunctor SyntheticSpectrum (1:ℤ)).map
          ((SyntheticCategory.biShift (0,-(A:ℤ))).map (XModLambdaN.map g B)) := by
  have htop : ∀ d : BiHom p.1 p.2 ((mhInputD Z e A B).obj model.nu model.auxiliary),
      FiltrationAtLeast model.syntheticTower (s+r+1) d → d=0 := by
    simpa only [mhInputD,mhInputZ] using
      (finite_mh_target_high_zero Z B hB A e p.1 p.2 (s+r) hwindow)
  obtain ⟨a,b,ha,hh',hd',hb,hg',he⟩ := synchronized_detected_inputs
    (mhInputA Z e A) (mhInputH VX A) (mhInputG VY A B) (mhInputD Z e A B)
    (mhInputHMap VX Z e A h exA) (mhInputDMap Z e A B hA hB) (mhInputGMap VY Z e A B g)
    p s l r sg m hfil x0 xh yg zd e0 eh eg ed hx0 hxh hyg hzd hh hd hg hnc htop
  let bn := b≫(SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).hom.app _
  refine ⟨a,bn,ha,hh',hd',?_,?_,?_⟩
  · simpa [bn,mhInputG,SyntheticObject.obj,Category.assoc] using hb
  · simpa only [bn,mhInputGMap,Category.assoc] using hg'
  · apply (cancel_mono
      ((SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).inv.app
        ((SyntheticCategory.biShift (0,-(A:ℤ))).obj
          (XModLambdaN ((mhInputZ Z e).obj model.nu model.auxiliary) B)))).mp
    simpa only [mhInputDMap,mhInputGMap,bn,Category.assoc] using he


/-- The complete statement's top-window inequality is an equality. This
calculation uses the actual normalized source weight, including -e_g.
-/
private theorem finite_level_input_top_window
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g +
      normalizedExponent model.classicalTower T.h = 1)
    (n₁ m₁ k i j : ℕ) (hj : j < n₁) (s t : ℤ) :
    let ef : ℤ := normalizedExponent model.classicalTower T.f
    let eg : ℤ := normalizedExponent model.classicalTower T.g
    let eh : ℤ := normalizedExponent model.classicalTower T.h
    let r : ℤ := (n₁+ef)+(m₁+eg)+(k+eh)
    let A : ℕ := n₁+k+i-j
    let B : ℕ := m₁+j+1
    let p : ℤ × ℤ := (t-s,t-i-eg)
    (B:ℤ) = p.1+(s+r)-p.2-A+(-eg) := by
  have hja : j ≤ n₁+k+i := by omega
  dsimp only
  simp only [Nat.cast_sub hja,Nat.cast_add,Nat.cast_one]
  omega

end
end KIP126.ProofTools.Internal.Mahowald
