module
import all KIP126.Def.ProofTools.GeneralizedMahowald.CommonShiftEdge
import all KIP126.Def.ProofTools.GeneralizedMahowald.SuspensionDetection

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

/- A quotient comparison with ordinary suspension, requiring only its
   inclusion equation. No choice of exact commShift is identified with the
   canonical bigraded shift comparison. -/
private theorem quotient_suspension_inclusion_exists
    (A : SyntheticSpectrum) (r : ℕ) :
    ∃ e : XModLambdaN (A⟦(1:ℤ)⟧) r ≅ (XModLambdaN A r)⟦(1:ℤ)⟧,
      XModLambdaN.incl (A⟦(1:ℤ)⟧) r ≫ e.hom =
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl A r) := by
  letI := model.exactness.shiftCommShift (1,0)
  letI := model.exactness.shiftExact (1,0)
  obtain ⟨ε,hε,_⟩ := quotient_shift_exists model.quotients.coherence (1,0) r A
  let κ := (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).app A
  let κr := (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).app (XModLambdaN A r)
  let e : XModLambdaN (A⟦(1:ℤ)⟧) r ≅ (XModLambdaN A r)⟦(1:ℤ)⟧ :=
    (model.quotients.functoriality.functor r).mapIso κ.symm ≪≫ ε ≪≫ κr
  refine ⟨e,?_⟩
  change XModLambdaN.incl _ r ≫ XModLambdaN.map κ.inv r ≫ ε.hom ≫ κr.hom = _
  rw [←Category.assoc,←XModLambdaN.incl_naturality,Category.assoc,←Category.assoc _ ε.hom,hε]
  have hn := (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).hom.naturality
    (XModLambdaN.incl A r)
  change (SyntheticCategory.biShift (1,0)).map (XModLambdaN.incl A r) ≫ κr.hom =
    κ.hom ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl A r) at hn
  rw [hn,Iso.inv_hom_id_assoc]

/- For arbitrary final coordinates D₀, the unquotiented edge factors through
   the actual finite lambda transition. This identifies its action on a
   finite representative without requiring that the source class is permanent. -/
private theorem common_desuspended_edge_factors_finite_lambda
    (A D₀ : SyntheticSpectrum) (i q : ℕ) (hi : 0 < i) (hq : 0 < q)
    (esusp : XModLambdaN (A⟦(1:ℤ)⟧) (i+q) ≅ (XModLambdaN A (i+q))⟦(1:ℤ)⟧)
    (hesusp : XModLambdaN.incl (A⟦(1:ℤ)⟧) (i+q) ≫ esusp.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl A (i+q)))
    (eD : XModLambdaN (A⟦(1:ℤ)⟧) (i+q) ≅
      (SyntheticCategory.biShift (1,-(i:ℤ))).obj D₀) :
    let ff := SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) (1,-(i:ℤ))
    let Jedge := ff.preimage ((biSuspensionIso (i:ℤ) A).hom ≫
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (lambdaPow i A) ≫
      XModLambdaN.incl (A⟦(1:ℤ)⟧) (i+q) ≫ eD.hom)
    let Jq := ff.preimage ((biSuspensionIso (i:ℤ) (XModLambdaN A (i+q-i))).hom ≫
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map
        ((model.quotients.tower A).triangle hi (show i < i+q by omega)).lambdaMap ≫
      esusp.inv ≫ eD.hom)
    XModLambdaN.incl A (i+q-i) ≫ Jq = Jedge := by
  dsimp only
  apply (SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) (1,-(i:ℤ))).map_injective
  simp only [Functor.map_comp,Functor.FullyFaithful.map_preimage]
  rw [←Category.assoc _ (biSuspensionIso (i:ℤ) (XModLambdaN A (i+q-i))).hom,
    biSuspensionIso_natural]
  simp only [Category.assoc]
  rw [←Category.assoc ((shiftFunctor SyntheticSpectrum (1:ℤ)).map _),←Functor.map_comp,
    ((model.quotients.tower A).triangle hi (show i < i+q by omega)).lambda_quotient,
    Functor.map_comp]
  have hsusp : (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl A (i+q)) ≫ esusp.inv =
      XModLambdaN.incl (A⟦(1:ℤ)⟧) (i+q) := by
    rw [←hesusp,Category.assoc,Iso.hom_inv_id,Category.comp_id]
  simp only [Category.assoc]
  rw [←Category.assoc ((shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl A (i+q))),hsusp]

/- The prescribed normalized y label may be evaluated using its actual
   finite representative. In MH2, hfactor is supplied by the preceding
   theorem and ag is exactly the chosen original g-extension source. -/
private theorem normalized_common_edge_detection
    (X Y : ClassicalObject) (g : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (q : ℕ) (s t : ℤ) (y : Ambient model X (s,t))
    (D : SyntheticObject)
    (Jedge : (extensionSourceObject model X Y g).obj model.nu model.auxiliary ⟶
      D.obj model.nu model.auxiliary)
    (Jq : XModLambdaN ((extensionSourceObject model X Y g).obj model.nu model.auxiliary) q ⟶
      D.obj model.nu model.auxiliary)
    (hfactor : XModLambdaN.incl _ q ≫ Jq = Jedge)
    (ag : BiHom (t-s) (t+normalizedExponent model.classicalTower g)
      (XModLambdaN ((extensionSourceObject model X Y g).obj model.nu model.auxiliary) q))
    (hag : Detects (model.convergence (.quotient q (extensionSourceObject model X Y g)))
      (s,(t-s)+s,t+normalizedExponent model.classicalTower g)
      (finiteSourceForExtension model X Y g q s t y)
      (homotopyRegrade (by simp) rfl ag)) :
    Detects (model.convergence D)
      (s,(t-s)+s,t+normalizedExponent model.classicalTower g)
      (familyPageMap model.family Jedge 2
        (s,(t-s)+s,t+normalizedExponent model.classicalTower g)
        (infiniteSourceForExtension model X Y g s t y))
      (homotopyRegrade (by simp) rfl (ag ≫ Jq)) := by
  let p : Tridegree := (s,(t-s)+s,t+normalizedExponent model.classicalTower g)
  have hsource : finiteSourceForExtension model X Y g q s t y =
      familyPageMap model.family (XModLambdaN.incl _ q) 2 p
        (infiniteSourceForExtension model X Y g s t y) := by
    unfold finiteSourceForExtension infiniteSourceForExtension finiteNuLabel
    rw [page_regrade]
    rfl
  have h := detects_map (.quotient q (extensionSourceObject model X Y g)) D
    Jq p _ _ hag
  have hlabel : familyPageMap model.family Jq 2 p (finiteSourceForExtension model X Y g q s t y) =
      familyPageMap model.family Jedge 2 p (infiniteSourceForExtension model X Y g s t y) := by
    rw [hsource,←ModuleCat.comp_apply,family_page_comp,hfactor]
  have h' := (congrArg (fun z => Detects (model.convergence D) p z
    (homotopyRegrade (show t-s=((t-s)+s)-s by omega) rfl ag ≫ Jq)) hlabel).mp h
  convert h' using 1
  have hr {a b w : ℤ} (ha : a=b) {S U : SyntheticSpectrum}
      (v : BiHom a w S) (f : S ⟶ U) :
      homotopyRegrade ha rfl (v ≫ f) = homotopyRegrade ha rfl v ≫ f := by
    subst b
    rfl
  exact hr _ _ _

private def edgeVerticalCancelIso (i : ℕ) (U : SyntheticSpectrum) :
    U ≅ (SyntheticCategory.biShift (0,(i:ℤ))).obj
      ((SyntheticCategory.biShift (0,-(i:ℤ))).obj U) :=
  SyntheticCategory.biShift_zero.symm.app U ≪≫
    (biShiftAddIso (0,-(i:ℤ)) (0,(i:ℤ)) 0 (by ext <;> simp)).symm.app U

private theorem edge_vertical_cancel_common_shift
    (i : ℕ) (U : SyntheticSpectrum) :
    (SyntheticCategory.biShift (1,-(i:ℤ))).map (edgeVerticalCancelIso i U).hom =
      (biShiftAddIso (0,-(i:ℤ)) (1,0) (1,-(i:ℤ)) (by ext <;> simp)).inv.app U ≫
        (biShiftAddIso (0,(i:ℤ)) (1,-(i:ℤ)) (1,0) (by ext <;> simp)).inv.app
          ((SyntheticCategory.biShift (0,-(i:ℤ))).obj U) := by
  let e := (biShiftAddIso (0,-(i:ℤ)) (0,(i:ℤ)) 0 (by ext <;> simp)).app U ≪≫
    SyntheticCategory.biShift_zero.app U
  let a := (biShiftAddIso (0,-(i:ℤ)) (1,0) (1,-(i:ℤ)) (by ext <;> simp)).app U
  let b := (biShiftAddIso (0,(i:ℤ)) (1,-(i:ℤ)) (1,0) (by ext <;> simp)).app
    ((SyntheticCategory.biShift (0,-(i:ℤ))).obj U)
  have hh := model.quotients.coherence.associativity
    (0,-(i:ℤ)) (0,(i:ℤ)) (1,-(i:ℤ)) 0 (1,0) (1,-(i:ℤ))
    (by ext <;> simp) (by ext <;> simp) (by ext <;> simp) (by ext <;> simp) U
  rw [model.quotients.coherence.left_unit,←Functor.map_comp] at hh
  have he : (SyntheticCategory.biShift (1,-(i:ℤ))).mapIso e = b ≪≫ a := Iso.ext hh
  have hh' := congrArg Iso.inv he
  simpa only [e,a,b,edgeVerticalCancelIso,Functor.mapIso_inv,Iso.trans_inv,
    Iso.trans_hom,Iso.symm_hom,Iso.symm_inv,Iso.app_hom,Iso.app_inv,Functor.id_obj,Functor.comp_obj] using hh'

/- A canonical choice of coordinates for the final edge target.
   D₀ = Σ^(0,i) Q_r A. It leaves normalization eg inside A throughout. -/
private def commonEdgeTargetIso (A : SyntheticSpectrum) (i q : ℕ)
    (esusp : XModLambdaN (A⟦(1:ℤ)⟧) (i+q) ≅ (XModLambdaN A (i+q))⟦(1:ℤ)⟧) :
    XModLambdaN (A⟦(1:ℤ)⟧) (i+q) ≅
      (SyntheticCategory.biShift (1,-(i:ℤ))).obj
        ((SyntheticCategory.biShift (0,(i:ℤ))).obj (XModLambdaN A (i+q))) :=
  esusp ≪≫ (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).symm.app _ ≪≫
    (biShiftAddIso (0,(i:ℤ)) (1,-(i:ℤ)) (1,0) (by ext <;> simp)).symm.app _

/- With these coordinates Jq is exactly the canonical positive shift of the
   actual finite lambda map, with no residual sign or sphere automorphism. -/
private theorem common_desuspended_finite_edge_canonical
    (A : SyntheticSpectrum) (i q : ℕ) (hi : 0 < i) (hq : 0 < q)
    (esusp : XModLambdaN (A⟦(1:ℤ)⟧) (i+q) ≅ (XModLambdaN A (i+q))⟦(1:ℤ)⟧) :
    let ff := SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) (1,-(i:ℤ))
    let L := ((model.quotients.tower A).triangle hi (show i < i+q by omega)).lambdaMap
    ff.preimage ((biSuspensionIso (i:ℤ) (XModLambdaN A (i+q-i))).hom ≫
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map L ≫ esusp.inv ≫
        (commonEdgeTargetIso A i q esusp).hom) =
      (edgeVerticalCancelIso i (XModLambdaN A (i+q-i))).hom ≫
        (SyntheticCategory.biShift (0,(i:ℤ))).map L := by
  dsimp only
  apply (SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) (1,-(i:ℤ))).map_injective
  simp only [Functor.map_comp,Functor.FullyFaithful.map_preimage]
  rw [edge_vertical_cancel_common_shift]
  simp only [commonEdgeTargetIso,Iso.trans_hom,Iso.symm_hom,Iso.app_hom,
    Iso.inv_hom_id_assoc,Category.assoc]
  rw [bi_susp_iso_hom_eq]
  simp only [Category.assoc]
  have hn := (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).inv.naturality
    (((model.quotients.tower A).triangle hi (show i < i+q by omega)).lambdaMap)
  change (shiftFunctor SyntheticSpectrum (1:ℤ)).map _ ≫
      (SyntheticCategory.biShift_compat 1).inv.app _ =
    (SyntheticCategory.biShift_compat 1).inv.app _ ≫
      (SyntheticCategory.biShift (1,0)).map _ at hn
  erw [←Category.assoc ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
    (((model.quotients.tower A).triangle hi (show i < i+q by omega)).lambdaMap)),hn]
  simp only [Category.assoc,Iso.hom_inv_id_app_assoc]
  have hb := (biShiftAddIso (0,(i:ℤ)) (1,-(i:ℤ)) (1,0) (by ext <;> simp)).inv.naturality
    (((model.quotients.tower A).triangle hi (show i < i+q by omega)).lambdaMap)
  simpa only [Functor.comp_map,Category.assoc] using
    congrArg (fun f => (biShiftAddIso (0,-(i:ℤ)) (1,0) (1,-(i:ℤ)) (by ext <;> simp)).inv.app
      (XModLambdaN A (i+q-i)) ≫ f) hb

private theorem common_desuspended_edge_canonical_factor
    (A : SyntheticSpectrum) (i q : ℕ) (hi : 0 < i) (hq : 0 < q)
    (esusp : XModLambdaN (A⟦(1:ℤ)⟧) (i+q) ≅ (XModLambdaN A (i+q))⟦(1:ℤ)⟧)
    (hesusp : XModLambdaN.incl (A⟦(1:ℤ)⟧) (i+q) ≫ esusp.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl A (i+q))) :
    let ff := SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) (1,-(i:ℤ))
    let eD := commonEdgeTargetIso A i q esusp
    let Jedge := ff.preimage ((biSuspensionIso (i:ℤ) A).hom ≫
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (lambdaPow i A) ≫
      XModLambdaN.incl (A⟦(1:ℤ)⟧) (i+q) ≫ eD.hom)
    XModLambdaN.incl A (i+q-i) ≫
        (edgeVerticalCancelIso i (XModLambdaN A (i+q-i))).hom ≫
          (SyntheticCategory.biShift (0,(i:ℤ))).map
            ((model.quotients.tower A).triangle hi (show i < i+q by omega)).lambdaMap = Jedge := by
  have h := common_desuspended_edge_factors_finite_lambda A
    ((SyntheticCategory.biShift (0,(i:ℤ))).obj (XModLambdaN A (i+q)))
    i q hi hq esusp hesusp (commonEdgeTargetIso A i q esusp)
  dsimp only at h ⊢
  rw [common_desuspended_finite_edge_canonical A i q hi hq esusp] at h
  simpa only [Category.assoc] using h

/- Sphere evaluation of the canonical positive shift identifies the output
   with the ordinary lambda class, so it is available for later division. -/
private theorem edge_double_vertical_shift
    (i : ℕ) (m w : ℤ) {U : SyntheticSpectrum} (a : BiHom m w U) :
    homotopyRegrade (by simp) (by dsimp; omega)
      (shiftHomotopyClass (0,(i:ℤ)) (m,w-i)
        (homotopyRegrade (by simp) (by simp [sub_eq_add_neg])
          (shiftHomotopyClass (0,-(i:ℤ)) (m,w) a))) =
      a ≫ (edgeVerticalCancelIso i U).hom := by
  rw [shift_regrade,shift_regrade]
  have h := shift_hom_associativity model.quotients.coherence
    (m,w) (0,-(i:ℤ)) (0,(i:ℤ)) (m,w-i) 0 (m,w)
    (by ext <;> dsimp <;> omega) (by ext <;> simp)
    (by ext <;> dsimp <;> omega) (by ext <;> simp) a
  rw [←h]
  have hunit := model.quotients.coherence.right_unit (m,w) S_0_0
  have hiunit : (biShiftAddIso (m,w) 0 (m,w) (by ext <;> simp)).inv.app (S_0_0 : SyntheticSpectrum) =
      SyntheticCategory.biShift_zero.inv.app (Smn m w) := by
    apply (cancel_mono (SyntheticCategory.biShift_zero.hom.app (Smn m w))).mp
    erw [←hunit,Iso.inv_hom_id_app,hunit,Iso.inv_hom_id_app]
    rfl
  rw [hiunit]
  have hn := SyntheticCategory.biShift_zero.inv.naturality a
  change a ≫ SyntheticCategory.biShift_zero.inv.app U =
    SyntheticCategory.biShift_zero.inv.app (Smn m w) ≫
      (SyntheticCategory.biShift 0).map a at hn
  rw [←Category.assoc,←hn]
  simp only [edgeVerticalCancelIso,Iso.trans_hom,Iso.symm_hom,Iso.app_hom,Category.assoc]


/- Transport of the actual finite lambda class through an arbitrary vertical
   normalization, using only quotient inclusion comparisons on spheres. -/
private theorem vertical_normalized_finite_lambda_class
    (X : ClassicalObject) (r i : ℕ) (hi : 0 < i) (hir : i < r) (s t e : ℤ)
    (εq : XModLambdaN ((SyntheticCategory.biShift (0,e)).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) (r-i) ≅
      (SyntheticCategory.biShift (0,e)).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (r-i)))
    (εr : XModLambdaN ((SyntheticCategory.biShift (0,e)).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) r ≅
      (SyntheticCategory.biShift (0,e)).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) r))
    (hεq : XModLambdaN.incl _ (r-i) ≫ εq.hom =
      (SyntheticCategory.biShift (0,e)).map (XModLambdaN.incl _ (r-i)))
    (hεr : XModLambdaN.incl _ r ≫ εr.hom =
      (SyntheticCategory.biShift (0,e)).map (XModLambdaN.incl _ r))
    (b : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (r-i))) :
    homotopyRegrade (m' := t-s) (w' := t+e-i) (by simp) (by simp; omega)
        (shiftHomotopyClass (0,e) (t-s,t-i) (Leibniz.finiteLambdaClass X r i hi hir s t b)) ≫ εr.inv =
      homotopyRegrade (m' := t-s) (w' := t+e-i) (by simp) (by simp [sub_eq_add_neg])
          (shiftHomotopyClass (0,-(i:ℤ)) (t-s,t+e)
            (homotopyRegrade (m' := t-s) (w' := t+e) (by simp) rfl
              (shiftHomotopyClass (0,e) (t-s,t) b) ≫ εq.inv)) ≫
        ((model.quotients.tower _).triangle hi hir).lambdaMap := by
  apply (cancel_mono εr.hom).mp
  simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id]
  unfold Leibniz.finiteLambdaClass
  rw [shift_hom_comp,regrade_comp,shift_hom_comp,regrade_comp]
  simp only [Category.assoc]
  rw [quotient_shift_lambda_on_spheres X (0,e) r i hi hir εq εr hεq hεr]
  rw [shift_regrade,shift_regrade,shift_regrade,shift_regrade]
  rw [←Category.assoc]
  apply congrArg (fun z => z ≫ (SyntheticCategory.biShift (0,e)).map
    ((model.quotients.tower _).triangle hi hir).lambdaMap)
  simpa only [Category.assoc] using
    (shift_hom_swap (t-s,t) (0,e) (0,-(i:ℤ)) (t-s,t+e) (t-s,t-i) (t-s,t+e-i)
      (by ext <;> simp) (by ext <;> dsimp <;> omega)
      (by ext <;> dsimp <;> omega) (by ext <;> dsimp <;> omega) b).symm


/- The original source relation and its first label identify the normalized
   finite lambda target with the prescribed y label in native ν coordinates. -/
private theorem vertical_normalized_finite_lambda_detects
    (X : ClassicalObject) (r i : ℕ) (hi : 0 < i) (hir : i < r) (s t e : ℤ)
    (y : Ambient model X (s,t))
    (εq : XModLambdaN ((SyntheticCategory.biShift (0,e)).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) (r-i) ≅
      (SyntheticCategory.biShift (0,e)).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (r-i)))
    (εr : XModLambdaN ((SyntheticCategory.biShift (0,e)).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) r ≅
      (SyntheticCategory.biShift (0,e)).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) r))
    (hεq : XModLambdaN.incl _ (r-i) ≫ εq.hom =
      (SyntheticCategory.biShift (0,e)).map (XModLambdaN.incl _ (r-i)))
    (hεr : XModLambdaN.incl _ r ≫ εr.hom =
      (SyntheticCategory.biShift (0,e)).map (XModLambdaN.incl _ r))
    (b : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (r-i)))
    (hb : b ≫ (model.quotients.tower _).rho 1 (r-i) (by omega) =
      firstLabel model X s t y ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1)
    (ag : BiHom (t-s) (t+e) (XModLambdaN ((SyntheticCategory.biShift (0,e)).obj
      (model.nu.functor.obj (X.obj model.auxiliary))) (r-i)))
    (hback : homotopyRegrade (m' := t-s) (w' := t+e) (by simp) rfl
        (shiftHomotopyClass (0,e) (t-s,t) b) ≫ εq.inv = ag) :
    Detects (model.convergence (.quotient r (.nu X))) (s,t,t-i)
      (finiteTargetLabel model X r s t i y)
      (quotientUnshift X (0,e) (t-s,t-i) r εr
        (homotopyRegrade (by simp) (by dsimp; omega)
          (homotopyRegrade (m' := t-s) (w' := t+e-i) (by simp) (by simp [sub_eq_add_neg])
            (shiftHomotopyClass (0,-(i:ℤ)) (t-s,t+e) ag) ≫
              ((model.quotients.tower _).triangle hi hir).lambdaMap))) := by
  have h := vertical_normalized_finite_lambda_class X r i hi hir s t e εq εr hεq hεr b
  rw [hback] at h
  rw [←h,regrade_comp,homotopy_regrade_inverse,quotient_unshift_shift]
  exact Leibniz.finite_quotient_lambda_detects X r i hi hir s t y b hb


private def zeroEdgeQuotientShiftIso (A : SyntheticSpectrum) (q : ℕ) :
    XModLambdaN ((SyntheticCategory.biShift (0,0)).obj A) q ≅
      (SyntheticCategory.biShift (0,0)).obj (XModLambdaN A q) :=
  (model.quotients.functoriality.functor q).mapIso (SyntheticCategory.biShift_zero.app A) ≪≫
    SyntheticCategory.biShift_zero.symm.app (XModLambdaN A q)

private theorem zero_edge_quotient_shift_inclusion (A : SyntheticSpectrum) (q : ℕ) :
    XModLambdaN.incl _ q ≫ (zeroEdgeQuotientShiftIso A q).hom =
      (SyntheticCategory.biShift (0,0)).map (XModLambdaN.incl A q) := by
  change XModLambdaN.incl _ q ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app A) q ≫
    SyntheticCategory.biShift_zero.inv.app (XModLambdaN A q) = _
  rw [←Category.assoc,←XModLambdaN.incl_naturality]
  have hn := SyntheticCategory.biShift_zero.hom.naturality (XModLambdaN.incl A q)
  change (SyntheticCategory.biShift (0,0)).map (XModLambdaN.incl A q) ≫
      SyntheticCategory.biShift_zero.hom.app (XModLambdaN A q) =
    SyntheticCategory.biShift_zero.hom.app A ≫ XModLambdaN.incl A q at hn
  erw [←hn,Category.assoc,Iso.hom_inv_id_app,Category.comp_id]

private theorem zero_edge_shift_homotopy_class
    (m w : ℤ) {U : SyntheticSpectrum} (b : BiHom m w U) :
    homotopyRegrade (m' := m) (w' := w) (by simp) (by simp)
      (shiftHomotopyClass (0,0) (m,w) b) =
      b ≫ SyntheticCategory.biShift_zero.inv.app U := by
  rw [shift_regrade]
  have hunit := model.quotients.coherence.right_unit (m,w) S_0_0
  have hiunit : (biShiftAddIso (m,w) 0 (m,w) (by ext <;> simp)).inv.app (S_0_0 : SyntheticSpectrum) =
      SyntheticCategory.biShift_zero.inv.app (Smn m w) := by
    apply (cancel_mono (SyntheticCategory.biShift_zero.hom.app (Smn m w))).mp
    erw [←hunit,Iso.inv_hom_id_app,hunit,Iso.inv_hom_id_app]
    rfl
  erw [hiunit]
  exact (SyntheticCategory.biShift_zero.inv.naturality b).symm

private theorem zero_edge_quotient_source_back
    (X : ClassicalObject) (q : ℕ) (s t : ℤ)
    (b : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q)) :
    homotopyRegrade (m' := t-s) (w' := t+0) (by simp) rfl
        (shiftHomotopyClass (0,0) (t-s,t) b) ≫
          (zeroEdgeQuotientShiftIso (model.nu.functor.obj (X.obj model.auxiliary)) q).inv =
      homotopyRegrade rfl (by simp) b ≫
        XModLambdaN.map (SyntheticCategory.biShift_zero.inv.app _) q := by
  have h := zero_edge_shift_homotopy_class (t-s) t b
  have hcast := congrArg (fun z => homotopyRegrade rfl (show t=t+0 by simp) z) h
  have hc {m m' m'' w w' w'' : ℤ} {V : SyntheticSpectrum}
      (hm : m=m') (hw : w=w') (hm' : m'=m'') (hw' : w'=w'') (a : BiHom m w V) :
      homotopyRegrade hm' hw' (homotopyRegrade hm hw a) =
        homotopyRegrade (hm.trans hm') (hw.trans hw') a := by
    subst m'; subst m''; subst w'; subst w''; rfl
  rw [hc,regrade_comp] at hcast
  rw [hcast]
  change (homotopyRegrade rfl (by simp) b ≫ SyntheticCategory.biShift_zero.inv.app _) ≫
    SyntheticCategory.biShift_zero.hom.app _ ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.inv.app _) q = _
  simp only [Category.assoc,Iso.inv_hom_id_app_assoc]

end
end KIP126.ProofTools.Internal.Mahowald
