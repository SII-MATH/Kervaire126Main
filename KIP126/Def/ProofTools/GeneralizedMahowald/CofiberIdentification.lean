module

import all KIP126.Def.ProofTools.GeneralizedMahowald.Coherence

/-! Identify the cofiber of the selected normalized g with the third vertex
of the rotated normalized triangle. Both arrow equations are retained, so
the identification includes the actual connecting map and rotation sign. -/

@[expose] section
namespace KIP126.ProofTools.Internal.Mahowald
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.AdamsSynthetic
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Standard
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

private def normalized_g_source_iso (T : TriangleData model.auxiliary) :
    (SyntheticCategory.biShift (0,-(normalizedExponent model.classicalTower T.g : ℤ))).obj
      ((SyntheticCategory.biShift (0,(normalizedExponent model.classicalTower T.g : ℤ))).obj
        (model.nu.functor.obj (T.Y.obj model.auxiliary))) ≅
      model.nu.functor.obj (T.Y.obj model.auxiliary) :=
  (biShiftAddIso (0,(normalizedExponent model.classicalTower T.g : ℤ))
    (0,-(normalizedExponent model.classicalTower T.g : ℤ)) (0,0)
    (by ext <;> simp)).app _ ≪≫ SyntheticCategory.biShift_zero.app _

private theorem normalized_g_source_square (T : TriangleData model.auxiliary) :
    (SyntheticCategory.biShift (0,-(normalizedExponent model.classicalTower T.g : ℤ))).map
      (model.normalizedMap T.Y T.Z T.g).map =
      (normalized_g_source_iso T).hom ≫
        negativeLift (normalizedExponent model.classicalTower T.g)
          (model.normalizedMap T.Y T.Z T.g).map := by
  simp only [normalized_g_source_iso, biShiftAddIso, Iso.trans_hom,
    Iso.app_hom, NatTrans.comp_app, eqToIso.hom, eqToHom_app, negativeLift,
    Category.assoc, Iso.hom_inv_id_app_assoc, eqToHom_trans_assoc]
  simp

private def normalized_g_cofiber_triangle_iso (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g + normalizedExponent model.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible model T he) :
    letI := model.exactness.shiftCommShift
      (0,-(normalizedExponent model.classicalTower T.g : ℤ))
    (SyntheticCategory.biShift (0,-(normalizedExponent model.classicalTower T.g : ℤ))).mapTriangle.obj
      (Triangle.mk (model.normalizedMap T.Y T.Z T.g).map
        (HasFunctorialCofiber.cofibι (model.normalizedMap T.Y T.Z T.g).map)
        (HasFunctorialCofiber.cofibδ (model.normalizedMap T.Y T.Z T.g).map)) ≅
      (normalizedTriangle model T he).rotate := by
  letI := model.exactness.shiftCommShift
    (0,-(normalizedExponent model.classicalTower T.g : ℤ))
  letI := model.exactness.shiftExact
    (0,-(normalizedExponent model.classicalTower T.g : ℤ))
  refine isoTriangleOfIso₁₂ _ _
    ((SyntheticCategory.biShift _).map_distinguished _
      (HasFunctorialCofiber.cofib_distinguished (model.normalizedMap T.Y T.Z T.g).map))
    (rot_of_distTriang _ hT) (normalized_g_source_iso T) (Iso.refl _) ?_
  change (SyntheticCategory.biShift
      (0,-(normalizedExponent model.classicalTower T.g : ℤ))).map
      (model.normalizedMap T.Y T.Z T.g).map ≫ 𝟙 _ =
    (normalized_g_source_iso T).hom ≫ negativeLift
      (normalizedExponent model.classicalTower T.g) (model.normalizedMap T.Y T.Z T.g).map
  simpa only [Category.comp_id] using normalized_g_source_square T

private def normalized_g_shifted_cofiber_iso (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g + normalizedExponent model.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible model T he) :
    (SyntheticCategory.biShift (0,-(normalizedExponent model.classicalTower T.g : ℤ))).obj
      (HasFunctorialCofiber.cofib (model.normalizedMap T.Y T.Z T.g).map) ≅
      ((SyntheticCategory.biShift (0,(normalizedExponent model.classicalTower T.f : ℤ))).obj
        (model.nu.functor.obj (T.X.obj model.auxiliary)))⟦(1 : ℤ)⟧ :=
  Triangle.π₃.mapIso (normalized_g_cofiber_triangle_iso T he hT)

private theorem normalized_g_shifted_cofiber_inclusion (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g + normalizedExponent model.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible model T he) :
    (SyntheticCategory.biShift (0,-(normalizedExponent model.classicalTower T.g : ℤ))).map
      (HasFunctorialCofiber.cofibι (model.normalizedMap T.Y T.Z T.g).map) ≫
        (normalized_g_shifted_cofiber_iso T he hT).hom = normalizedConnecting model T he := by
  have h := (normalized_g_cofiber_triangle_iso T he hT).hom.comm₂
  have h₂ : (normalized_g_cofiber_triangle_iso T he hT).hom.hom₂ = 𝟙 _ := by
    simp only [normalized_g_cofiber_triangle_iso, isoTriangleOfIso₁₂_hom_hom₂,
      Iso.refl_hom]
  rw [h₂, Category.id_comp] at h
  exact h

private theorem normalized_g_shifted_cofiber_boundary (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g + normalizedExponent model.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible model T he) :
    letI := model.exactness.shiftCommShift
      (0,-(normalizedExponent model.classicalTower T.g : ℤ))
    let F := SyntheticCategory.biShift (Syn := SyntheticSpectrum)
      (0,-(normalizedExponent model.classicalTower T.g : ℤ))
    F.map (HasFunctorialCofiber.cofibδ (model.normalizedMap T.Y T.Z T.g).map) ≫
      (F.commShiftIso (1 : ℤ)).hom.app _ ≫
        (shiftFunctor SyntheticSpectrum (1 : ℤ)).map (normalized_g_source_iso T).hom =
      -((normalized_g_shifted_cofiber_iso T he hT).hom ≫
        (shiftFunctor SyntheticSpectrum (1 : ℤ)).map (model.normalizedMap T.X T.Y T.f).map) := by
  letI := model.exactness.shiftCommShift
    (0,-(normalizedExponent model.classicalTower T.g : ℤ))
  have h := (normalized_g_cofiber_triangle_iso T he hT).hom.comm₃
  have h₁ : (normalized_g_cofiber_triangle_iso T he hT).hom.hom₁ =
      (normalized_g_source_iso T).hom := by
    simp only [normalized_g_cofiber_triangle_iso, isoTriangleOfIso₁₂_hom_hom₁]
  rw [h₁] at h
  change (_ ≫ _) ≫ _ = (normalized_g_shifted_cofiber_iso T he hT).hom ≫
    (-((shiftFunctor SyntheticSpectrum (1 : ℤ)).map (model.normalizedMap T.X T.Y T.f).map)) at h
  simpa only [Category.assoc, Preadditive.comp_neg, Triangle.mk_mor₃,
    Triangle.mk_obj₁] using h

private def normalized_connecting_tail_iso (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g + normalizedExponent model.classicalTower T.h = 1) :
    (SyntheticCategory.biShift (0,-(normalizedExponent model.classicalTower T.g : ℤ))).obj
      ((SyntheticCategory.biShift (0,-(normalizedExponent model.classicalTower T.h : ℤ))).obj
        ((SyntheticCategory.biShift (1,1)).obj
          (model.nu.functor.obj (T.X.obj model.auxiliary)))) ≅
      ((SyntheticCategory.biShift (0,(normalizedExponent model.classicalTower T.f : ℤ))).obj
        (model.nu.functor.obj (T.X.obj model.auxiliary)))⟦(1 : ℤ)⟧ := by
  let eg : ℤ := normalizedExponent model.classicalTower T.g
  let eh : ℤ := normalizedExponent model.classicalTower T.h
  let X := model.nu.functor.obj (T.X.obj model.auxiliary)
  exact (SyntheticCategory.biShift (0,-eg)).mapIso
      ((SyntheticCategory.biShift_comp (1,1) (0,-eh)).app X) ≪≫
    (SyntheticCategory.biShift_comp ((1,1)+(0,-eh)) (0,-eg)).app X ≪≫
    eqToIso (congrArg (fun p => (SyntheticCategory.biShift p).obj X)
      (show ((1,1)+(0,-eh))+(0,-eg) =
          (0,(normalizedExponent model.classicalTower T.f : ℤ))+(1,0) from by
        dsimp [eg,eh]; ext <;> simp only []; omega)) ≪≫
    (SyntheticCategory.biShift_comp (0,(normalizedExponent model.classicalTower T.f : ℤ))
      (1,0)).symm.app X ≪≫
    (SyntheticCategory.biShift_compat (Syn := SyntheticSpectrum) 1).app _

private def normalized_g_raw_cofiber_iso (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g + normalizedExponent model.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible model T he) :
    HasFunctorialCofiber.cofib (model.normalizedMap T.Y T.Z T.g).map ≅
      (SyntheticCategory.biShift (0,-(normalizedExponent model.classicalTower T.h : ℤ))).obj
        ((SyntheticCategory.biShift (1,1)).obj
          (model.nu.functor.obj (T.X.obj model.auxiliary))) :=
  (SyntheticCategory.biShift_fullyFaithful
    (0,-(normalizedExponent model.classicalTower T.g : ℤ))).preimageIso
      (normalized_g_shifted_cofiber_iso T he hT ≪≫ (normalized_connecting_tail_iso T he).symm)

private theorem normalized_g_raw_cofiber_inclusion (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g + normalizedExponent model.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible model T he) :
    HasFunctorialCofiber.cofibι (model.normalizedMap T.Y T.Z T.g).map ≫
      (normalized_g_raw_cofiber_iso T he hT).hom =
      negativeLift (normalizedExponent model.classicalTower T.h)
        (model.normalizedMap T.Z (.shift 1 T.X) T.h).map ≫
      (SyntheticCategory.biShift (0,-(normalizedExponent model.classicalTower T.h : ℤ))).map
        (model.nu.suspensionIso (T.X.obj model.auxiliary)).hom := by
  apply (SyntheticCategory.biShift_fullyFaithful
    (0,-(normalizedExponent model.classicalTower T.g : ℤ))).map_injective
  simp only [Functor.map_comp,normalized_g_raw_cofiber_iso,Functor.FullyFaithful.preimageIso_hom,
    Functor.FullyFaithful.map_preimage,Iso.trans_hom,Iso.symm_hom,←Category.assoc]
  rw [normalized_g_shifted_cofiber_inclusion]
  apply (cancel_mono (normalized_connecting_tail_iso T he).hom).mp
  simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id]
  rfl

private theorem normalized_g_raw_cofiber_shift (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g + normalizedExponent model.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible model T he) :
    (SyntheticCategory.biShift (0,-(normalizedExponent model.classicalTower T.g : ℤ))).map
        (normalized_g_raw_cofiber_iso T he hT).hom ≫ (normalized_connecting_tail_iso T he).hom =
      (normalized_g_shifted_cofiber_iso T he hT).hom := by
  simp [normalized_g_raw_cofiber_iso]

private theorem normalized_g_raw_cofiber_boundary (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g + normalizedExponent model.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible model T he) :
    letI := model.exactness.shiftCommShift
      (0,-(normalizedExponent model.classicalTower T.g : ℤ))
    let F := SyntheticCategory.biShift (Syn := SyntheticSpectrum)
      (0,-(normalizedExponent model.classicalTower T.g : ℤ))
    F.map (HasFunctorialCofiber.cofibδ (model.normalizedMap T.Y T.Z T.g).map) ≫
      (F.commShiftIso (1 : ℤ)).hom.app _ ≫
        (shiftFunctor SyntheticSpectrum (1 : ℤ)).map (normalized_g_source_iso T).hom =
      -(F.map (normalized_g_raw_cofiber_iso T he hT).hom ≫ (normalized_connecting_tail_iso T he).hom ≫
        (shiftFunctor SyntheticSpectrum (1 : ℤ)).map (model.normalizedMap T.X T.Y T.f).map) := by
  have h := normalized_g_shifted_cofiber_boundary T he hT
  rw [←normalized_g_raw_cofiber_shift T he hT] at h
  simpa only [Category.assoc] using h

private def normalized_g_cofiber_iso (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g + normalizedExponent model.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible model T he) :
    HasFunctorialCofiber.cofib (model.normalizedMap T.Y T.Z T.g).map ≅
      (SyntheticCategory.biShift
        (1,(normalizedExponent model.classicalTower T.f : ℤ) +
          normalizedExponent model.classicalTower T.g)).obj
        (model.nu.functor.obj (T.X.obj model.auxiliary)) :=
  normalized_g_raw_cofiber_iso T he hT ≪≫
    (biShiftAddIso (1,1) (0,-(normalizedExponent model.classicalTower T.h : ℤ))
      (1,(normalizedExponent model.classicalTower T.f : ℤ) +
        normalizedExponent model.classicalTower T.g) (by ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> omega)).app _

private theorem normalized_g_cofiber_inclusion (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g + normalizedExponent model.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible model T he) :
    HasFunctorialCofiber.cofibι (model.normalizedMap T.Y T.Z T.g).map ≫
      (normalized_g_cofiber_iso T he hT).hom =
      negativeLift (normalizedExponent model.classicalTower T.h)
        (model.normalizedMap T.Z (.shift 1 T.X) T.h).map ≫
      (SyntheticCategory.biShift (0,-(normalizedExponent model.classicalTower T.h : ℤ))).map
        (model.nu.suspensionIso (T.X.obj model.auxiliary)).hom ≫
      (biShiftAddIso (1,1) (0,-(normalizedExponent model.classicalTower T.h : ℤ))
        (1,(normalizedExponent model.classicalTower T.f : ℤ) +
          normalizedExponent model.classicalTower T.g) (by ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> omega)).hom.app _ := by
  simp only [normalized_g_cofiber_iso,Iso.trans_hom,Iso.app_hom,←Category.assoc,
    normalized_g_raw_cofiber_inclusion]


end
end KIP126.ProofTools.Internal.Mahowald
