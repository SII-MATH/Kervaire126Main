module

import all KIP126.ProofTools.MahowaldLeibniz.TerminalSource
import all KIP126.ProofTools.MahowaldLeibniz.Corollaries
import all KIP126.ProofTools.LastLayerComparison.Boundary

/-! The zero-coordinate comparison between the actual positive normalized
Q₁ operation and the suspended first arrow of the same normalized row. -/

@[expose] section
namespace KIP126.ProofTools.Internal.LastLayerComparison
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Standard
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
open KIP126.ProofTools.Internal.Leibniz
open KIP126.ProofTools.Internal.MahowaldLeibniz
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 4000000

private def positiveFirstSuspensionComparison (X : ClassicalObject)
    (ε : XModLambdaN ((SyntheticCategory.biShift (1,1)).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) 1 ≅
      (SyntheticCategory.biShift (1,1)).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) 1)) :
    XModLambdaN (((SyntheticCategory.biShift (0,1)).obj
      (model.nu.functor.obj (X.obj model.auxiliary)))⟦(1:ℤ)⟧) 1 ≅
      (XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) 1)⟦(1:ℤ)⟧ :=
  (model.quotients.functoriality.functor 1).mapIso (positiveSuspensionIso _) ≪≫
    ε ≪≫ (positiveSuspensionIso _).symm ≪≫
      (shiftFunctor SyntheticSpectrum (1:ℤ)).mapIso (levelQuotientShiftIso X 1 1).symm

private theorem positiveFirstSuspensionComparison_incl (X : ClassicalObject)
    (ε : XModLambdaN ((SyntheticCategory.biShift (1,1)).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) 1 ≅
      (SyntheticCategory.biShift (1,1)).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) 1))
    (hε : XModLambdaN.incl _ 1 ≫ ε.hom =
      (SyntheticCategory.biShift (1,1)).map (XModLambdaN.incl _ 1)) :
    XModLambdaN.incl _ 1 ≫ (positiveFirstSuspensionComparison X ε).hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ 1) := by
  let A := model.nu.functor.obj (X.obj model.auxiliary)
  let P : (SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,1) ⋙
        shiftFunctor SyntheticSpectrum (1:ℤ)) ≅
      SyntheticCategory.biShift (1,1) :=
    Functor.isoWhiskerLeft (SyntheticCategory.biShift (0,1))
      (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).symm ≪≫
        biShiftAddIso (0,1) (1,0) (1,1) (by ext <;> simp)
  have hp : (positiveSuspensionIso A).hom ≫
      (SyntheticCategory.biShift (1,1)).map (XModLambdaN.incl A 1) =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map
        ((SyntheticCategory.biShift (0,1)).map (XModLambdaN.incl A 1)) ≫
          (positiveSuspensionIso (XModLambdaN A 1)).hom := by
    exact (P.hom.naturality (XModLambdaN.incl A 1)).symm

  dsimp only [A] at hp
  simp only [positiveFirstSuspensionComparison, Iso.trans_hom,
    Functor.mapIso_hom, Iso.symm_hom, LambdaQuotientFunctoriality.functor]
  simp only [←Category.assoc]
  rw [←XModLambdaN.incl_naturality]
  rw [Category.assoc (positiveSuspensionIso A).hom _ ε.hom, hε, hp]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [←level_quotient_shift_incl X 1 1, Functor.map_comp]
  simp only [Category.assoc, ←Functor.map_comp, Iso.hom_inv_id, Category.comp_id]

private theorem normalized_source_suspension_inv
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g +
      normalizedExponent model.classicalTower T.h = 1)
    (hf : normalizedExponent model.classicalTower T.f = 1) :
    (normalizedSuspensionNativeIso T he hf).inv ≫
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (positiveNormalizedSourceIso T he hf).hom =
      (model.nu.suspensionIso (T.X.obj model.auxiliary)).hom ≫
        (positiveSuspensionIso _).inv := by
  have H := positive_normalized_source_suspension T he hf
  change _ = (positiveSuspensionIso _).hom at H
  have HH := congrArg (fun k => (normalizedSuspensionNativeIso T he hf).inv ≫
    (shiftFunctor SyntheticSpectrum (1:ℤ)).map (positiveNormalizedSourceIso T he hf).hom ≫
      k ≫ (positiveSuspensionIso _).inv) H
  simp only [←Category.assoc, ←Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
    Category.comp_id, Category.id_comp, Iso.inv_hom_id] at HH
  exact HH.symm

private theorem native_label_zero_iff
    (X : ClassicalObject) (s t : ℤ) (x : Ambient model X (s,t)) :
    nativeFirstLabel X s t x = 0 ↔ x = 0 := by
  constructor
  · exact first_label_zero X s t x
  · intro hx
    subst x
    rw [nativeFirstLabel_eq_regrade, map_zero]
    have hz {A : SyntheticSpectrum} {m m' w w' : ℤ} (hm : m=m') (hw : w=w') :
        homotopyRegrade hm hw (0 : BiHom m w A) = 0 := by
      subst m'; subst w'; rfl
    rw [hz, zero_comp]

private theorem vertical_translate_regrade {A : SyntheticSpectrum}
    (e : ℤ) {m m' w w' : ℤ} (hm : m=m') (hw : w=w') (a : BiHom m w A) :
    homotopyRegrade hm (show w+e=w'+e by omega) (verticalTranslate A e m w a) =
      verticalTranslate A e m' w' (homotopyRegrade hm hw a) := by
  subst m'; subst w'; rfl

private theorem shift_input_regrade {A : SyntheticSpectrum}
    (δ : ℤ×ℤ) {m m' w w' : ℤ} (hm : m=m') (hw : w=w') (a : BiHom m w A) :
    shiftHomotopyClass δ (m',w') (homotopyRegrade hm hw a) =
      homotopyRegrade (show m+δ.1=m'+δ.1 by omega)
        (show w+δ.2=w'+δ.2 by omega) (shiftHomotopyClass δ (m,w) a) := by
  subst m'; subst w'; rfl

private theorem positive_first_suspended_coordinates
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g +
      normalizedExponent model.classicalTower T.h = 1)
    (hf : normalizedExponent model.classicalTower T.f = 1)
    (s t : ℤ) (x : Ambient model T.X (s,t))
    (sx : Ambient model (.shift 1 T.X) (s,t+1))
    (hsx : (model.classicalSuspension T.X).DesuspendsClass s (t+1) sx
      (by simpa only [add_sub_cancel_right] using x))
    (ε : XModLambdaN ((SyntheticCategory.biShift (1,1)).obj
        (model.nu.functor.obj (T.X.obj model.auxiliary))) 1 ≅
      (SyntheticCategory.biShift (1,1)).obj
        (XModLambdaN (model.nu.functor.obj (T.X.obj model.auxiliary)) 1))
    (hε : XModLambdaN.incl _ 1 ≫ ε.hom =
      (SyntheticCategory.biShift (1,1)).map (XModLambdaN.incl _ 1)) :
    homotopyRegrade (show (t+1)-s=t-s+1 by omega) rfl
      ((nativeFirstLabel (.shift 1 T.X) s (t+1) sx ≫
        XModLambdaN.map (normalizedSuspensionNativeIso T he hf).inv 1) ≫
        XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
          (positiveNormalizedSourceIso T he hf).hom) 1 ≫
        (positiveFirstSuspensionComparison T.X ε).hom) =
    ordinarySuspendedRepresentative _ (t-s+1) (t+1)
      (homotopyRegrade (show t-s=(t-s+1)-1 by omega) rfl
        ((model.firstQuotient T.X 1 s t).symm x)) := by
  let A := model.nu.functor.obj (T.X.obj model.auxiliary)
  have hsusp : nativeFirstLabel (.shift 1 T.X) s (t+1) sx ≫
      XModLambdaN.map (model.nu.suspensionIso (T.X.obj model.auxiliary)).hom 1 ≫ ε.hom =
      homotopyRegrade (by dsimp; omega) (by simp)
        (shiftHomotopyClass (1,1) (t-s,t) (nativeFirstLabel T.X s t x)) := by
    have H := firstQuotient_suspension T.X s t x sx ε hε hsx
    simpa only [nativeFirstLabel_eq_regrade] using H
  have hE : XModLambdaN.map (normalizedSuspensionNativeIso T he hf).inv 1 ≫
      XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
        (positiveNormalizedSourceIso T he hf).hom) 1 =
      XModLambdaN.map (model.nu.suspensionIso (T.X.obj model.auxiliary)).hom 1 ≫
        XModLambdaN.map (positiveSuspensionIso A).inv 1 := by
    rw [←model.quotients.functoriality.map_comp,
      normalized_source_suspension_inv, model.quotients.functoriality.map_comp]
  have hcancel : XModLambdaN.map (positiveSuspensionIso A).inv 1 ≫
      (positiveFirstSuspensionComparison T.X ε).hom =
      ε.hom ≫ (positiveSuspensionIso (XModLambdaN A 1)).inv ≫
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map (levelQuotientShiftIso T.X 1 1).inv := by
    simp only [positiveFirstSuspensionComparison, Iso.trans_hom,
      Functor.mapIso_hom, Iso.symm_hom, LambdaQuotientFunctoriality.functor]
    rw [←Category.assoc, ←model.quotients.functoriality.map_comp,
      Iso.inv_hom_id, model.quotients.functoriality.map_id, Category.id_comp]
  have hpre : (nativeFirstLabel (.shift 1 T.X) s (t+1) sx ≫
        XModLambdaN.map (normalizedSuspensionNativeIso T he hf).inv 1) ≫
        XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
          (positiveNormalizedSourceIso T he hf).hom) 1 ≫
        (positiveFirstSuspensionComparison T.X ε).hom =
      homotopyRegrade (by dsimp; omega) (by simp)
        (shiftHomotopyClass (1,1) (t-s,t) (nativeFirstLabel T.X s t x)) ≫
        (positiveSuspensionIso (XModLambdaN A 1)).inv ≫
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map (levelQuotientShiftIso T.X 1 1).inv := by
    rw [Category.assoc, ←Category.assoc _ _ (positiveFirstSuspensionComparison T.X ε).hom,
      hE]
    simp only [Category.assoc]
    rw [hcancel]
    simpa only [Category.assoc] using congrArg (fun k => k ≫
      (positiveSuspensionIso (XModLambdaN A 1)).inv ≫
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (levelQuotientShiftIso T.X 1 1).inv) hsusp
  rw [hpre]
  have hp := positive_ordinary_suspension_class (XModLambdaN A 1) (t-s+1) t
    (homotopyRegrade (show t-s=(t-s+1)-1 by omega) rfl (nativeFirstLabel T.X s t x))
  rw [←positive_first_label_shift T.X s t x]
  simp only [regrade_comp]
  rw [ordinarySuspendedRepresentative_natural]
  have hp' := congrArg (fun k => k ≫
    (positiveSuspensionIso (XModLambdaN A 1)).inv ≫
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (levelQuotientShiftIso T.X 1 1).inv) hp
  rw [←vertical_translate_regrade] at hp'
  simp only [shift_input_regrade,
    normalized_homotopy_regrade_trans, Category.assoc, Iso.hom_inv_id_assoc] at hp'
  simpa only [regrade_comp, normalized_homotopy_regrade_trans] using hp'.symm

private theorem normalized_suspended_image_coordinates
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g +
      normalizedExponent model.classicalTower T.h = 1)
    (hf : normalizedExponent model.classicalTower T.f = 1)
    (s t : ℤ) (x : Ambient model T.X (s,t))
    (sx : Ambient model (.shift 1 T.X) (s,t+1))
    (hsx : (model.classicalSuspension T.X).DesuspendsClass s (t+1) sx
      (by simpa only [add_sub_cancel_right] using x))
    (ε : XModLambdaN ((SyntheticCategory.biShift (1,1)).obj
        (model.nu.functor.obj (T.X.obj model.auxiliary))) 1 ≅
      (SyntheticCategory.biShift (1,1)).obj
        (XModLambdaN (model.nu.functor.obj (T.X.obj model.auxiliary)) 1))
    (hε : XModLambdaN.incl _ 1 ≫ ε.hom =
      (SyntheticCategory.biShift (1,1)).map (XModLambdaN.incl _ 1))
    (ey : XModLambdaN ((model.nu.functor.obj (T.Y.obj model.auxiliary))⟦(1:ℤ)⟧) 1 ≅
      (XModLambdaN (model.nu.functor.obj (T.Y.obj model.auxiliary)) 1)⟦(1:ℤ)⟧)
    (hey : XModLambdaN.incl _ 1 ≫ ey.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ 1)) :
    homotopyRegrade (show (t+1)-s=t-s+1 by omega) rfl
      (((nativeFirstLabel (.shift 1 T.X) s (t+1) sx ≫
        XModLambdaN.map (normalizedSuspensionNativeIso T he hf).inv 1) ≫
        XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
          (normalizedTriangle model T he).mor₁) 1) ≫ ey.hom) =
    ordinarySuspendedRepresentative _ (t-s+1) (t+1)
      (homotopyRegrade (show t-s=(t-s+1)-1 by omega) rfl
        ((model.firstQuotient T.X 1 s t).symm x ≫
          XModLambdaN.map (normalizedFirstMap T hf) 1)) := by
  let c := nativeFirstLabel (.shift 1 T.X) s (t+1) sx ≫
    XModLambdaN.map (normalizedSuspensionNativeIso T he hf).inv 1
  let a := c ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
    (positiveNormalizedSourceIso T he hf).hom) 1
  have hinv : a ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
      (positiveNormalizedSourceIso T he hf).inv) 1 = c := by
    dsimp only [a]
    rw [Category.assoc, ←model.quotients.functoriality.map_comp,
      ←Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
      model.quotients.functoriality.map_id, Category.comp_id]
  have hraw := positive_normalized_source_raw_image T he hf 1 ((t+1)-s) (t+1) a
  rw [hinv] at hraw
  have hn := finite_suspension_normalized_map_on_spheres T.X T.Y 1 (by decide) 1
    (by decide) (normalizedFirstMap T hf) (positiveFirstSuspensionComparison T.X ε)
    ey (positiveFirstSuspensionComparison_incl T.X ε hε) hey ((t+1)-s) (t+1) a
  simp only [←Category.assoc] at hn
  rw [←hraw] at hn
  have hc : homotopyRegrade (show (t+1)-s=t-s+1 by omega) rfl
      (a ≫ (positiveFirstSuspensionComparison T.X ε).hom) =
      ordinarySuspendedRepresentative _ (t-s+1) (t+1)
        (homotopyRegrade (show t-s=(t-s+1)-1 by omega) rfl
          ((model.firstQuotient T.X 1 s t).symm x)) := by
    simpa only [a,c,Category.assoc] using
      positive_first_suspended_coordinates T he hf s t x sx hsx ε hε
  have HR := congrArg (homotopyRegrade (show (t+1)-s=t-s+1 by omega)
    (rfl : t+1=t+1)) hn
  simp only [regrade_comp] at HR hc
  rw [hc, ←ordinarySuspendedRepresentative_natural] at HR
  simpa only [c,regrade_comp] using HR

private theorem ordinary_suspended_zero (A : SyntheticSpectrum) (m w : ℤ) :
    ordinarySuspendedRepresentative A m w 0 = 0 := by
  simp only [ordinarySuspendedRepresentative, shiftHomotopyClass,
    Functor.map_zero, comp_zero, regrade_zero, zero_comp]

/-- The zero image in the actual suspended normalized Q₁ row is equivalent
to the zero of the same positive normalized first-quotient operation. -/
private theorem cofiber_boundary_zero_iff_normalized_suspended_image
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g +
      normalizedExponent model.classicalTower T.h = 1)
    (hf : normalizedExponent model.classicalTower T.f = 1)
    (s t : ℤ) (x : Ambient model T.X (s,t))
    (sx : Ambient model (.shift 1 T.X) (s,t+1))
    (hsx : (model.classicalSuspension T.X).DesuspendsClass s (t+1) sx
      (by simpa only [add_sub_cancel_right] using x)) :
    KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t x = 0 ↔
      (nativeFirstLabel (.shift 1 T.X) s (t+1) sx ≫
        XModLambdaN.map (normalizedSuspensionNativeIso T he hf).inv 1) ≫
        XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
          (normalizedTriangle model T he).mor₁) 1 = 0 := by
  letI := model.exactness.shiftCommShift (1,1)
  letI := model.exactness.shiftExact (1,1)
  obtain ⟨ε,hε,_⟩ := quotient_shift_exists model.quotients.coherence (1,1) 1
    (model.nu.functor.obj (T.X.obj model.auxiliary))
  obtain ⟨ey,hey⟩ := quotient_suspension_inclusion_exists
    (model.nu.functor.obj (T.Y.obj model.auxiliary)) 1
  have H := normalized_suspended_image_coordinates T he hf s t x sx hsx ε hε ey hey
  have hlabel := cofiberFirstQuotientBoundary_native_label T hf s t x
  constructor
  · intro hδ
    rw [hδ, (native_label_zero_iff T.Y (s+1) (t+1) 0).mpr rfl] at hlabel
    have hpos : (model.firstQuotient T.X 1 s t).symm x ≫
        XModLambdaN.map (normalizedFirstMap T hf) 1 = 0 := by
      apply homotopy_regrade_injective (m' := (t+1)-(s+1)) (w' := t+1)
        (by omega) rfl
      simpa only [regrade_zero] using hlabel.symm
    rw [hpos, regrade_zero, ordinary_suspended_zero] at H
    have H₀ := homotopy_regrade_injective
      (show (t+1)-s=t-s+1 by omega) (rfl : t+1=t+1)
      (H.trans (regrade_zero _ _).symm)
    exact (cancel_mono ey.hom).mp (by simpa only [zero_comp] using H₀)
  · intro hc
    rw [hc, zero_comp, regrade_zero] at H
    have hb := ordinary_suspended_representative_injective _ (t-s+1) (t+1)
      (H.symm.trans (ordinary_suspended_zero _ _ _).symm)
    have hpos := homotopy_regrade_injective
      (show t-s=(t-s+1)-1 by omega) (rfl : t+1=t+1)
      (hb.trans (regrade_zero _ _).symm)
    apply (native_label_zero_iff T.Y (s+1) (t+1) _).mp
    rw [hlabel, hpos, regrade_zero]

end
end KIP126.ProofTools.Internal.LastLayerComparison
