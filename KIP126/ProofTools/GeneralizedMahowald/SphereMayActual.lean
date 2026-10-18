module
import all KIP126.ProofTools.GeneralizedMahowald.CommonCoordinates
import all KIP126.ProofTools.GeneralizedMahowald.MayCorrection
import all KIP126.ProofTools.GeneralizedMahowald.SphereMayCorrection
import all KIP126.ProofTools.GeneralizedMahowald.SphereResidualLabels

@[expose] section
namespace KIP126.ProofTools.Internal.Mahowald
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard KIP126.Literature
open KIP126.ProofTools.Internal
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2000000

private theorem common_bi_susp_inverse
    (i : ℕ) (m w : ℤ) (U : SyntheticSpectrum)
    (a : BiHom (m-1) (w+i) U) :
    (biShiftAddIso (m-1,w+i) (1,-(i:ℤ)) (m,w)
      (by ext <;> dsimp; all_goals omega)).hom.app S_0_0 ≫
        (biSuspensionHomEquiv m w i U).symm a =
      (SyntheticCategory.biShift (1,-(i:ℤ))).map a ≫ (biSuspensionIso (i:ℤ) U).hom := by
  rw [bi_susp_symm_eq,susp_regrade_eq]
  simp only [←Category.assoc,Iso.hom_inv_id_app,Category.id_comp]

/- Common desuspension preserves the second image of the very same
geometric v. This consumes the actual K square and the original hvSecond. -/
private theorem common_desuspended_geometric_second_image
    {A C₀ D₀ V Cr Dr : SyntheticSpectrum} (i : ℕ) (m w : ℤ)
    (eC : Cr ≅ (SyntheticCategory.biShift (1,-(i:ℤ))).obj C₀)
    (eD : Dr ≅ (SyntheticCategory.biShift (1,-(i:ℤ))).obj D₀)
    (φ : V ⟶ Cr) (δ : V ⟶ (((SyntheticCategory.biShift (0,-(i:ℤ))).obj A)⟦(1:ℤ)⟧))
    (K : (((SyntheticCategory.biShift (0,-(i:ℤ))).obj A)⟦(1:ℤ)⟧) ⟶ Dr)
    (h : Cr ⟶ Dr) (hK : φ≫h=δ≫K)
    (v : BiHom m w V) (ag : BiHom (m-1) (w+i) A)
    (hvSecond : biSuspensionHomEquiv m w i A (v≫δ)=ag) :
    let ff := SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) (1,-(i:ℤ))
    let c₀ := ff.preimage ((biShiftAddIso (m-1,w+i) (1,-(i:ℤ)) (m,w)
      (by ext <;> dsimp; all_goals omega)).hom.app S_0_0 ≫ v ≫ φ ≫ eC.hom)
    let h₀ := ff.preimage (eC.inv≫h≫eD.hom)
    let K₀ := ff.preimage ((biSuspensionIso (i:ℤ) A).hom≫K≫eD.hom)
    c₀≫h₀=ag≫K₀ := by
  dsimp only
  let ff := SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) (1,-(i:ℤ))
  have hv : v≫δ=(biSuspensionHomEquiv m w i A).symm ag := by
    rw [←hvSecond]
    exact (AddEquiv.symm_apply_apply _ _).symm
  apply ff.map_injective
  simp only [Functor.map_comp,Functor.FullyFaithful.map_preimage,Category.assoc,
    Iso.hom_inv_id_assoc]
  rw [←Category.assoc φ h,hK]
  simp only [Category.assoc]
  rw [←Category.assoc v δ,hv]
  rw [←Category.assoc _ ((biSuspensionHomEquiv m w i A).symm ag),common_bi_susp_inverse]
  simp only [Category.assoc]

/- Normalize the short quotient length before using the strict geometric
square; this avoids introducing independent transports of δ and K. -/
private theorem common_desuspended_quotient_second_image
    (A B Cr C₀ Dr D₀ : SyntheticSpectrum) (i j q : ℕ) (hj : j=q) (M W : ℤ)
    (eC : Cr ≅ (SyntheticCategory.biShift (1,-(i:ℤ))).obj C₀)
    (eD : Dr ≅ (SyntheticCategory.biShift (1,-(i:ℤ))).obj D₀)
    (f : (SyntheticCategory.biShift (0,-(i:ℤ))).obj (XModLambdaN A j) ⟶ B)
    (φ : HasFunctorialCofiber.cofib f ⟶ Cr)
    (K : (((SyntheticCategory.biShift (0,-(i:ℤ))).obj (XModLambdaN A j))⟦(1:ℤ)⟧) ⟶ Dr)
    (h : Cr ⟶ Dr)
    (hK : HasFunctorialCofiber.cofibδ f≫K=φ≫h)
    (v : BiHom M W (HasFunctorialCofiber.cofib f))
    (ag : BiHom (M-1) (W+i) (XModLambdaN A q))
    (hvSecond : biSuspensionHomEquiv M W i (XModLambdaN A q)
      (by simpa only [hj] using v≫HasFunctorialCofiber.cofibδ f)=ag) :
    let ff := SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) (1,-(i:ℤ))
    let c₀ := ff.preimage ((biShiftAddIso (M-1,W+i) (1,-(i:ℤ)) (M,W)
      (by ext <;> dsimp; all_goals omega)).hom.app S_0_0≫v≫φ≫eC.hom)
    let h₀ := ff.preimage (eC.inv≫h≫eD.hom)
    let K₀ := ff.preimage ((biSuspensionIso (i:ℤ) (XModLambdaN A q)).hom≫
      (by simpa only [hj] using K)≫eD.hom)
    c₀≫h₀=ag≫K₀ := by
  subst j
  exact common_desuspended_geometric_second_image i M W eC eD φ
    (HasFunctorialCofiber.cofibδ f) K h hK.symm v ag hvSecond

private theorem normalize_common_edge_source_length
    (A D U : SyntheticSpectrum) (i j q : ℕ) (hj : j=q)
    (eD : U ≅ (SyntheticCategory.biShift (1,-(i:ℤ))).obj D)
    (K : (((SyntheticCategory.biShift (0,-(i:ℤ))).obj (XModLambdaN A j))⟦(1:ℤ)⟧) ⟶ U)
    (J : XModLambdaN A j ⟶ D) (rhs : A ⟶ D)
    (hedge : XModLambdaN.incl A j≫
      (SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) (1,-(i:ℤ))).preimage
        ((biSuspensionIso (i:ℤ) (XModLambdaN A j)).hom≫K≫eD.hom) -
      XModLambdaN.incl A j≫J=rhs) :
    XModLambdaN.incl A q≫
      (SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) (1,-(i:ℤ))).preimage
        ((biSuspensionIso (i:ℤ) (XModLambdaN A q)).hom≫
          (by simpa only [hj] using K)≫eD.hom) -
      XModLambdaN.incl A q≫(by simpa only [hj] using J)=rhs := by
  subst j
  exact hedge

/- The actual sphere-source MH2 edge, with the original φ/K/v/ag and Wg.
The conclusion retains the same first rho_i image and detects the prescribed
finite Jq image. It is only the sphere-source branch of the May comparison. -/
private theorem sphere_source_actual_mahowald_second_image
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g + normalizedExponent model.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible model T he) (hY : T.Y = .sphere)
    (i q : ℕ) (hi : 0 < i) (hq : 0 < q)
    (M W m sy ty : ℤ) (hM : M-1=ty-sy)
    (hW : W+i=ty+normalizedExponent model.classicalTower T.g)
    (hqZ : (q:ℤ)=m-normalizedExponent model.classicalTower T.g+1)
    (y : Ambient model T.Y (sy,ty)) (yBar : Ambient model T.Z (sy+m,ty+m))
    (Wg : FiniteExtensionWitness model T.Y T.Z T.g (q+1) m sy ty y yBar)
    (pBar : ℤ×ℤ) (xBar : Ambient model T.Z pBar)
    (hd : HasDifferential (model.classical.obj (T.Z.obj model.auxiliary))
      (i+q) pBar (sy+m,ty+m) xBar yBar)
    (hyBar : yBar ∈ permanentCycles model T.Z (sy+m,ty+m)) :
    let a : ℤ := normalizedExponent model.classicalTower T.g
    let e : ℤ := normalizedExponent model.classicalTower T.f+a
    let b : ℤ := (i:ℤ)+e
    let A := extensionSourceObject model T.Y T.Z T.g
    let G : A.obj model.nu model.auxiliary ⟶ model.nu.functor.obj (T.Z.obj model.auxiliary) :=
      (model.normalizedMap T.Y T.Z T.g).map
    let Cg := HasFunctorialCofiber.cofib G
    let Xν := model.nu.functor.obj (T.X.obj model.auxiliary)
    let Yν := model.nu.functor.obj (T.Y.obj model.auxiliary)
    let Zν := model.nu.functor.obj (T.Z.obj model.auxiliary)
    let C₀ := SyntheticObject.shift (0,b) (.quotient (i+q) (.nu T.X))
    let D₀ := SyntheticObject.shift (0,(i:ℤ)+a) (.quotient (i+q) (.nu T.Y))
    ∀ (eQ : XModLambdaN ((SyntheticCategory.biShift (1,e)).obj Xν) (i+q) ≅
          (SyntheticCategory.biShift (1,e)).obj (XModLambdaN Xν (i+q)))
      (eA : XModLambdaN (A.obj model.nu model.auxiliary) (i+q) ≅
          (SyntheticCategory.biShift (0,a)).obj (XModLambdaN Yν (i+q)))
      (esusp : XModLambdaN ((A.obj model.nu model.auxiliary)⟦(1:ℤ)⟧) (i+q) ≅
          (XModLambdaN (A.obj model.nu model.auxiliary) (i+q))⟦(1:ℤ)⟧)
      (_hesusp : XModLambdaN.incl ((A.obj model.nu model.auxiliary)⟦(1:ℤ)⟧) (i+q)≫esusp.hom =
          (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl (A.obj model.nu model.auxiliary) (i+q))),
      let eC : XModLambdaN (HasFunctorialCofiber.cofib G) (i+q) ≅
        (SyntheticCategory.biShift (1,-(i:ℤ))).obj (C₀.obj model.nu model.auxiliary) :=
        commonCofiberTargetIso e (normalized_g_cofiber_iso T he hT) i (i+q) eQ
      let eD : XModLambdaN ((A.obj model.nu model.auxiliary)⟦(1:ℤ)⟧) (i+q) ≅
        (SyntheticCategory.biShift (1,-(i:ℤ))).obj (D₀.obj model.nu model.auxiliary) :=
        commonEdgeTargetFlatIso Yν a i q esusp eA
      let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(i:ℤ))
      let L := (model.quotients.tower Zν).triangle hi (show i < i+q by omega)
      let f := F.map (XModLambdaN.map G (i+q-i))≫L.lambdaMap
      let ff := SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) (1,-(i:ℤ))
      ∀ (φ : HasFunctorialCofiber.cofib f ⟶ XModLambdaN Cg (i+q))
        (K : (F.obj (XModLambdaN (A.obj model.nu model.auxiliary) (i+q-i)))⟦(1:ℤ)⟧ ⟶
          XModLambdaN ((A.obj model.nu model.auxiliary)⟦(1:ℤ)⟧) (i+q))
        (_hφ : HasFunctorialCofiber.cofibι f≫φ=XModLambdaN.map (HasFunctorialCofiber.cofibι G) (i+q))
        (_hK : HasFunctorialCofiber.cofibδ f≫K=φ≫XModLambdaN.map (HasFunctorialCofiber.cofibδ G) (i+q))
        (v : BiHom M W (HasFunctorialCofiber.cofib f))
        (ag : BiHom (ty-sy) (ty+a) (XModLambdaN (A.obj model.nu model.auxiliary) q))
        (_hag : Detects (model.convergence (.quotient q A)) (sy,(ty-sy)+sy,ty+a)
          (finiteSourceForExtension model T.Y T.Z T.g q sy ty y)
          (homotopyRegrade (by simp) rfl ag))
        (_hvSecond : biSuspensionHomEquiv M W i (XModLambdaN (A.obj model.nu model.auxiliary) q)
          (by simpa only [Nat.add_sub_cancel_left,F,A,extensionSourceObject,SyntheticObject.obj,Yν,Zν,a,D₀] using v≫HasFunctorialCofiber.cofibδ f) =
          homotopyRegrade hM.symm hW.symm ag),
        let p : Tridegree := (sy,ty,ty+a)
        let source := regradeE2 (by simp [p,a]) (infiniteSourceForExtension model T.Y T.Z T.g sy ty y)
        let h₀ := ff.preimage (eC.inv≫XModLambdaN.map (HasFunctorialCofiber.cofibδ G) (i+q)≫eD.hom)
        let Jq := ff.preimage ((biSuspensionIso (i:ℤ) (XModLambdaN (A.obj model.nu model.auxiliary) (i+q-i))).hom≫
          (shiftFunctor SyntheticSpectrum (1:ℤ)).map
            ((model.quotients.tower (A.obj model.nu model.auxiliary)).triangle hi (show i < i+q by omega)).lambdaMap≫
          esusp.inv≫eD.hom)
        let c := homotopyRegrade hM hW
          (ff.preimage ((biShiftAddIso (M-1,W+i) (1,-(i:ℤ)) (M,W)
            (by ext <;> dsimp; all_goals omega)).hom.app S_0_0≫v≫φ≫eC.hom))
        let rho := (SyntheticCategory.biShift (0,b)).map ((model.quotients.tower Xν).rho i (i+q) (by omega))
        ∃ c' : BiHom (ty-sy) (ty+a) (C₀.obj model.nu model.auxiliary),
          c'≫rho=c≫rho ∧
          Detects (model.convergence D₀) p
            (familyPageMap model.family
              (by simpa only [Nat.add_sub_cancel_left,F,A,extensionSourceObject,SyntheticObject.obj,Yν,Zν,a,D₀] using Jq) 2 p
              (familyPageMap model.family (XModLambdaN.incl (A.obj model.nu model.auxiliary) q) 2 p source))
            (c'≫h₀) := by
  dsimp only
  intro eQ eA esusp hesusp φ K hφ hK v ag hag hvSecond
  let a : ℤ := normalizedExponent model.classicalTower T.g
  let e : ℤ := normalizedExponent model.classicalTower T.f+a
  let b : ℤ := (i:ℤ)+e
  let A := extensionSourceObject model T.Y T.Z T.g
  let G : A.obj model.nu model.auxiliary ⟶ model.nu.functor.obj (T.Z.obj model.auxiliary) :=
      (model.normalizedMap T.Y T.Z T.g).map
  let Xν := model.nu.functor.obj (T.X.obj model.auxiliary)
  let Yν := model.nu.functor.obj (T.Y.obj model.auxiliary)
  let Zν := model.nu.functor.obj (T.Z.obj model.auxiliary)
  let C₀ := SyntheticObject.shift (0,b) (.quotient (i+q) (.nu T.X))
  let D₀ := SyntheticObject.shift (0,(i:ℤ)+a) (.quotient (i+q) (.nu T.Y))
  let eC : XModLambdaN (HasFunctorialCofiber.cofib G) (i+q) ≅
        (SyntheticCategory.biShift (1,-(i:ℤ))).obj (C₀.obj model.nu model.auxiliary) :=
        commonCofiberTargetIso e (normalized_g_cofiber_iso T he hT) i (i+q) eQ
  let eD : XModLambdaN ((A.obj model.nu model.auxiliary)⟦(1:ℤ)⟧) (i+q) ≅
        (SyntheticCategory.biShift (1,-(i:ℤ))).obj (D₀.obj model.nu model.auxiliary) :=
        commonEdgeTargetFlatIso Yν a i q esusp eA
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(i:ℤ))
  let L := (model.quotients.tower Zν).triangle hi (show i < i+q by omega)
  let f := F.map (XModLambdaN.map G (i+q-i))≫L.lambdaMap
  let ff := SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) (1,-(i:ℤ))
  let h₀ := ff.preimage (eC.inv≫XModLambdaN.map (HasFunctorialCofiber.cofibδ G) (i+q)≫eD.hom)
  let K₀ := ff.preimage ((biSuspensionIso (i:ℤ) (XModLambdaN (A.obj model.nu model.auxiliary) q)).hom≫
    (by simpa only [Nat.add_sub_cancel_left,F,A,extensionSourceObject,SyntheticObject.obj,Yν,Zν,a,D₀] using K)≫eD.hom)
  let Jq := ff.preimage ((biSuspensionIso (i:ℤ) (XModLambdaN (A.obj model.nu model.auxiliary) (i+q-i))).hom≫
    (shiftFunctor SyntheticSpectrum (1:ℤ)).map
      ((model.quotients.tower (A.obj model.nu model.auxiliary)).triangle hi (show i < i+q by omega)).lambdaMap≫
    esusp.inv≫eD.hom)
  let c := homotopyRegrade hM hW
    (ff.preimage ((biShiftAddIso (M-1,W+i) (1,-(i:ℤ)) (M,W)
      (by ext <;> dsimp; all_goals omega)).hom.app S_0_0≫v≫φ≫eC.hom))
  let rho := (SyntheticCategory.biShift (0,b)).map ((model.quotients.tower Xν).rho i (i+q) (by omega))
  let epsilon : (SyntheticCategory.biShift (0,-(i:ℤ))).obj (D₀.obj model.nu model.auxiliary) ≅
      (SyntheticCategory.biShift (0,a)).obj (XModLambdaN Yν (i+q)) :=
    (biShiftAddIso (0,(i:ℤ)+a) (0,-(i:ℤ)) (0,a) (by ext <;> dsimp; all_goals omega)).app _
  obtain ⟨d,raw,hedge,htranspose⟩ :=
    quotient_common_desuspended_boundary_defect_with_transpose G i q hi hq eC eD epsilon φ K hφ hK
  let d₀ := ff.preimage ((biSuspensionIso (i:ℤ) (A.obj model.nu model.auxiliary)).hom≫d≫eC.hom)
  let t₀ := ff.preimage ((biSuspensionIso (i:ℤ) Zν).hom≫
    (shiftFunctor SyntheticSpectrum (1:ℤ)).map (lambdaPow i Zν)≫raw≫eD.hom)
  have hfactor := common_desuspended_edge_factors_finite_lambda
    (A.obj model.nu model.auxiliary) (D₀.obj model.nu model.auxiliary) i q hi hq esusp hesusp eD
  have hedge' : XModLambdaN.incl (A.obj model.nu model.auxiliary) q≫K₀-
      XModLambdaN.incl (A.obj model.nu model.auxiliary) q≫
        (by simpa only [Nat.add_sub_cancel_left,F,A,extensionSourceObject,SyntheticObject.obj,Yν,Zν,a,D₀] using Jq) = d₀≫h₀-G≫t₀ := by
    dsimp only at hfactor
    rw [←hfactor] at hedge
    exact normalize_common_edge_source_length (A.obj model.nu model.auxiliary)
      (D₀.obj model.nu model.auxiliary) _ i (i+q-i) q (by omega) eD K Jq _ hedge
  have hgeom := common_desuspended_quotient_second_image
    (A.obj model.nu model.auxiliary) (XModLambdaN Zν (i+q))
    (XModLambdaN (HasFunctorialCofiber.cofib G) (i+q))
    (C₀.obj model.nu model.auxiliary)
    (XModLambdaN ((A.obj model.nu model.auxiliary)⟦(1:ℤ)⟧) (i+q))
    (D₀.obj model.nu model.auxiliary) i (i+q-i) q (by omega) M W
    eC eD f φ K (XModLambdaN.map (HasFunctorialCofiber.cofibδ G) (i+q)) hK
    v (homotopyRegrade hM.symm hW.symm ag) hvSecond
  have hv : c≫h₀=ag≫K₀ := by
    have hgeom' := congrArg (homotopyRegrade hM hW) hgeom
    simpa only [c,h₀,K₀,ff,regrade_comp,homotopy_regrade_inverse,id_eq] using hgeom'
  have hα := actual_extension_source_native_detects T.Y T.Z T.g q sy ty y ag hag
  have hm : 0≤m := by have := Wg.length_lower; omega
  have hd0 (hm0 : m=0) : HasDifferential
      (model.classical.obj (T.Z.obj model.auxiliary)) (i+1) pBar (sy+m,ty+m) xBar yBar := by
    have ha0 : a=0 := by have := Wg.length_lower; dsimp [a]; omega
    have hq1 : q=1 := by dsimp [a] at ha0; omega
    simpa only [hq1,Nat.cast_one] using hd
  have hRzero := actual_raw_residual_flat_detects_zero T.Y T.Z T.g (q+1) (i+q) i hi
    m sy ty hm y yBar Wg pBar xBar hd0 hyBar D₀ rfl _ eD raw
  let eY : Yν ≅ Smn 0 0 :=
    eqToIso (congrArg (fun Y => model.nu.functor.obj (Y.obj model.auxiliary)) hY) ≪≫
      model.nu.unitIso ≪≫ SyntheticCategory.biShift_zero.symm.app S_0_0
  obtain ⟨dQ,c',_,_,_,hρ,hdetect⟩ := sphere_source_actual_edge_correction T.Y T.X T.Y
    0 0 a b ((i:ℤ)+a) q (i+q) i (by omega) hi
    (by dsimp [b,e]; omega) (by omega) (by dsimp [b,e]; omega)
    eY A C₀ D₀ rfl rfl rfl d₀ h₀ (G≫t₀) K₀
    (by simpa only [Nat.add_sub_cancel_left,F,A,extensionSourceObject,SyntheticObject.obj,Yν,Zν,a,D₀] using Jq) rho hedge'
    (sy,ty,ty+a) (regradeE2 (by simp [a]) (infiniteSourceForExtension model T.Y T.Z T.g sy ty y))
    ag c hα hv hRzero
  exact ⟨c',hρ,hdetect⟩

end
end KIP126.ProofTools.Internal.Mahowald
