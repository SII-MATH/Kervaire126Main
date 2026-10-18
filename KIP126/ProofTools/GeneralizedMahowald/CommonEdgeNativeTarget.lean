module
import all KIP126.ProofTools.GeneralizedMahowald.SphereMayActual
import all KIP126.ProofTools.GeneralizedMahowald.FTransport

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

private def commonTargetUnshift (δ p : ℤ×ℤ) (V : SyntheticSpectrum)
    (a : BiHom (p+δ).1 (p+δ).2 ((SyntheticCategory.biShift δ).obj V)) : BiHom p.1 p.2 V :=
  (SyntheticCategory.biShift_fullyFaithful δ).preimage
    ((SyntheticCategory.biShift_comp p δ).hom.app S_0_0 ≫ a)

private theorem common_target_unshift_shift (δ p : ℤ×ℤ) (V : SyntheticSpectrum)
    (a : BiHom p.1 p.2 V) :
    commonTargetUnshift δ p V (shiftHomotopyClass δ p a) = a := by
  apply (SyntheticCategory.biShift_fullyFaithful δ).map_injective
  simp [commonTargetUnshift,shiftHomotopyClass]

private theorem common_target_shift_unshift (δ p : ℤ×ℤ) (V : SyntheticSpectrum)
    (a : BiHom (p+δ).1 (p+δ).2 ((SyntheticCategory.biShift δ).obj V)) :
    shiftHomotopyClass δ p (commonTargetUnshift δ p V a) = a := by
  simp [commonTargetUnshift,shiftHomotopyClass]

private theorem common_target_unshift_sub (δ p : ℤ×ℤ) (V : SyntheticSpectrum)
    (a b : BiHom (p+δ).1 (p+δ).2 ((SyntheticCategory.biShift δ).obj V)) :
    commonTargetUnshift δ p V (a-b) = commonTargetUnshift δ p V a-commonTargetUnshift δ p V b := by
  apply (SyntheticCategory.biShift_fullyFaithful δ).map_injective
  simp [commonTargetUnshift,Functor.map_sub,Preadditive.comp_sub]

private theorem common_target_unshift_filtration
    (A : SyntheticObject) (δ p : ℤ×ℤ) (s : ℤ)
    (a : BiHom (p+δ).1 (p+δ).2 ((SyntheticCategory.biShift δ).obj (A.obj model.nu model.auxiliary)))
    (ha : FiltrationAtLeast model.syntheticTower s a) :
    FiltrationAtLeast model.syntheticTower s (commonTargetUnshift δ p _ a) := by
  let E := (essShift δ).filtered A p
  obtain ⟨b,hb⟩ := filtration_representative_exists model.syntheticTower _ (p+δ) s a ha
  have he : E.ambient.hom (commonTargetUnshift δ p _ a) = a := by
    rw [(essShift δ).ambient_eq,common_target_shift_unshift]
  have hi : E.ambient.inv a = commonTargetUnshift δ p _ a := by
    exact (congrArg E.ambient.inv he.symm).trans (E.ambient.toLinearEquiv.symm_apply_apply _)
  have hc := ConcreteCategory.congr_hom (E.symm.level_arrow s) b
  change ((model.syntheticTower.filtration _).F s p).arrow ((E.level s).inv b) =
    E.ambient.inv (((model.syntheticTower.filtration _).F s (p+δ)).arrow b) at hc
  erw [hb,hi] at hc
  have hm : commonTargetUnshift δ p _ a ∈ ModuleCat.subobjectModule _
      ((model.syntheticTower.filtration _).F s p) := ⟨(E.level s).inv b,hc⟩
  simpa only [SyntheticTowerPresentation.filtration,OrderIso.apply_symm_apply,
    FiltrationAtLeast] using hm

private theorem common_target_double_vertical_unshift
    (a b c m w : ℤ) (hab : a+b=c) (V : SyntheticSpectrum)
    (v : BiHom ((m,w)+(0,a)).1 ((m,w)+(0,a)).2 ((SyntheticCategory.biShift (0,a)).obj V)) :
    commonTargetUnshift (0,c) (m,w) V
      (homotopyRegrade (by simp) (by dsimp; omega)
        (shiftHomotopyClass (0,b) ((m,w)+(0,a)) v ≫
          (biShiftAddIso (0,a) (0,b) (0,c) (by ext <;> dsimp; omega)).hom.app V)) =
      commonTargetUnshift (0,a) (m,w) V v := by
  let z := commonTargetUnshift (0,a) (m,w) V v
  have hz : shiftHomotopyClass (0,a) (m,w) z = v :=
    common_target_shift_unshift (0,a) (m,w) V v
  have hshift : homotopyRegrade (m' := ((m,w)+(0,c)).1) (w' := ((m,w)+(0,c)).2)
        (by simp) (by dsimp; omega)
        (shiftHomotopyClass (0,b) ((m,w)+(0,a)) v ≫
          (biShiftAddIso (0,a) (0,b) (0,c) (by ext <;> dsimp; omega)).hom.app V) =
      shiftHomotopyClass (0,c) (m,w) z := by
    rw [←hz,regrade_comp,shift_regrade]
    have h := shift_hom_associativity model.quotients.coherence
      (m,w) (0,a) (0,b) ((m,w)+(0,a)) (0,c) ((m,w)+(0,c))
      rfl (by ext <;> dsimp; omega) (by ext <;> dsimp <;> omega) rfl z
    have h' := congrArg (fun v => v ≫
      (biShiftAddIso (0,a) (0,b) (0,c) (by ext <;> dsimp; omega)).hom.app V) h.symm
    simp only [Category.assoc,Iso.inv_hom_id_app,Category.comp_id] at h'
    simpa [shiftHomotopyClass,biShiftAddIso,Category.assoc] using h'
  rw [hshift,common_target_unshift_shift]

private theorem common_edge_positive_shift_evaluation
    (i : ℕ) (m w : ℤ) (U V : SyntheticSpectrum)
    (L : (SyntheticCategory.biShift (0,-(i:ℤ))).obj U ⟶ V)
    (a : BiHom m w U) :
    homotopyRegrade (by simp) (by dsimp; omega)
      (shiftHomotopyClass (0,(i:ℤ)) (m,w-i)
        (homotopyRegrade (by simp) (by simp [sub_eq_add_neg])
          (shiftHomotopyClass (0,-(i:ℤ)) (m,w) a) ≫ L)) =
      a ≫ (edgeVerticalCancelIso i U).hom ≫ (SyntheticCategory.biShift (0,(i:ℤ))).map L := by
  rw [shift_hom_comp,regrade_comp,edge_double_vertical_shift]
  simp only [Category.assoc]

private theorem common_shift_regrade (δ : ℤ×ℤ)
    {m m' w w' : ℤ} (hm : m=m') (hw : w=w') {V : SyntheticSpectrum} (a : BiHom m w V) :
    shiftHomotopyClass δ (m',w') (homotopyRegrade hm hw a) =
      homotopyRegrade (congrArg (fun z => z+δ.1) hm) (congrArg (fun z => z+δ.2) hw)
        (shiftHomotopyClass δ (m,w) a) := by
  subst m'; subst w'; rfl

private theorem common_regrade_trans
    {m m' m'' w w' w'' : ℤ} {V : SyntheticSpectrum}
    (hm : m=m') (hw : w=w') (hm' : m'=m'') (hw' : w'=w'') (a : BiHom m w V) :
    homotopyRegrade hm' hw' (homotopyRegrade hm hw a) =
      homotopyRegrade (hm.trans hm') (hw.trans hw') a := by
  subst m'; subst m''; subst w'; subst w''; rfl

private theorem common_flat_lambda_unshift
    (i : ℕ) (e m t : ℤ) (U V W : SyntheticSpectrum)
    (L : (SyntheticCategory.biShift (0,-(i:ℤ))).obj U ⟶ V)
    (ε : V ≅ (SyntheticCategory.biShift (0,e)).obj W)
    (a : BiHom m (t+e) U) :
    commonTargetUnshift (0,(i:ℤ)+e) (m,t-i) W
      (homotopyRegrade (by simp) (by dsimp; omega)
        (a ≫ (edgeVerticalCancelIso i U).hom ≫
          (SyntheticCategory.biShift (0,(i:ℤ))).map L ≫
          (SyntheticCategory.biShift (0,(i:ℤ))).map ε.hom ≫
          (biShiftAddIso (0,e) (0,(i:ℤ)) (0,(i:ℤ)+e) (by ext <;> dsimp; omega)).hom.app W)) =
      commonTargetUnshift (0,e) (m,t-i) W
        (homotopyRegrade (by simp) (by dsimp; omega)
          (homotopyRegrade (m' := m) (w' := t+e-i) (by simp) (by simp [sub_eq_add_neg])
            (shiftHomotopyClass (0,-(i:ℤ)) (m,t+e) a) ≫ L ≫ ε.hom)) := by
  let v : BiHom ((m,t-i)+(0,e)).1 ((m,t-i)+(0,e)).2 ((SyntheticCategory.biShift (0,e)).obj W) :=
    homotopyRegrade (by simp) (by dsimp; omega)
      (homotopyRegrade (m' := m) (w' := t+e-i) (by simp) (by simp [sub_eq_add_neg])
        (shiftHomotopyClass (0,-(i:ℤ)) (m,t+e) a) ≫ L ≫ ε.hom)
  have hd := common_target_double_vertical_unshift e (i:ℤ) ((i:ℤ)+e) m (t-i)
    (by omega) W v
  have hp := common_edge_positive_shift_evaluation i m (t+e) U V L a
  have hp' := congrArg (fun z => z ≫ (SyntheticCategory.biShift (0,(i:ℤ))).map ε.hom ≫
    (biShiftAddIso (0,e) (0,(i:ℤ)) (0,(i:ℤ)+e) (by ext <;> dsimp; omega)).hom.app W) hp
  simp only [Category.assoc] at hp'
  erw [←hp']
  convert hd using 1
  apply congrArg (commonTargetUnshift (0,(i:ℤ)+e) (m,t-i) W)
  simp only [v,Prod.mk_add_mk,common_shift_regrade,shift_hom_comp,regrade_comp,common_regrade_trans,Functor.map_comp,Category.assoc]


private theorem common_target_same_detection_transfer
    (A : SyntheticObject) (δ p : ℤ×ℤ) (s : ℤ)
    (z : (model.family.obj ((SyntheticCategory.biShift δ).obj
      (A.obj model.nu model.auxiliary))).E₂ (s,(p+δ).1+s,(p+δ).2))
    (x : (model.family.obj (A.obj model.nu model.auxiliary)).E₂ (s,p.1+s,p.2))
    (a b : BiHom (p+δ).1 (p+δ).2 ((SyntheticCategory.biShift δ).obj
      (A.obj model.nu model.auxiliary)))
    (ha : Detects (model.convergence (.shift δ A)) (s,(p+δ).1+s,(p+δ).2) z
      (homotopyRegrade (by dsimp; omega) rfl a))
    (hb : Detects (model.convergence (.shift δ A)) (s,(p+δ).1+s,(p+δ).2) z
      (homotopyRegrade (by dsimp; omega) rfl b))
    (hbx : Detects (model.convergence A) (s,p.1+s,p.2) x
      (homotopyRegrade (by dsimp; omega) rfl (commonTargetUnshift δ p _ b))) :
    Detects (model.convergence A) (s,p.1+s,p.2) x
      (homotopyRegrade (by dsimp; omega) rfl (commonTargetUnshift δ p _ a)) := by
  have hd := detects_sub_filtration (model.convergence (.shift δ A))
    (s,(p+δ).1+s,(p+δ).2) ha hb
  rw [←homotopy_regrade_sub] at hd
  have hd' := homotopy_regrade_filtration
    (show ((p+δ).1+s)-s=(p+δ).1 by omega) rfl (s+1) _ hd
  rw [homotopy_regrade_inverse] at hd'
  have hu := common_target_unshift_filtration A δ p (s+1) (a-b) hd'
  rw [common_target_unshift_sub] at hu
  have hur := homotopy_regrade_filtration
    (show p.1=(p.1+s)-s by omega) rfl (s+1) _ hu
  rw [homotopy_regrade_sub] at hur
  exact detects_of_high_difference A (s,p.1+s,p.2) _ _ _ hbx hur


private theorem common_desuspended_finite_edge_flat_canonical
    (V : SyntheticSpectrum) (e : ℤ) (i q : ℕ) (hi : 0 < i) (hq : 0 < q)
    (esusp : XModLambdaN (((SyntheticCategory.biShift (0,e)).obj V)⟦(1:ℤ)⟧) (i+q) ≅
      (XModLambdaN ((SyntheticCategory.biShift (0,e)).obj V) (i+q))⟦(1:ℤ)⟧)
    (eA : XModLambdaN ((SyntheticCategory.biShift (0,e)).obj V) (i+q) ≅
      (SyntheticCategory.biShift (0,e)).obj (XModLambdaN V (i+q))) :
    let A := (SyntheticCategory.biShift (0,e)).obj V
    let U := XModLambdaN A (i+q-i)
    let L := ((model.quotients.tower A).triangle hi (show i < i+q by omega)).lambdaMap
    let ff := SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) (1,-(i:ℤ))
    ff.preimage ((biSuspensionIso (i:ℤ) U).hom≫
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map L≫esusp.inv≫
        (commonEdgeTargetFlatIso V e i q esusp eA).hom) =
      (edgeVerticalCancelIso i U).hom≫
        (SyntheticCategory.biShift (0,(i:ℤ))).map L≫
          (commonEdgeFlattenIso V e i (i+q) eA).hom := by
  dsimp only
  let A := (SyntheticCategory.biShift (0,e)).obj V
  let U := XModLambdaN A (i+q-i)
  let L := ((model.quotients.tower A).triangle hi (show i < i+q by omega)).lambdaMap
  let p := (biSuspensionIso (i:ℤ) U).hom≫
    (shiftFunctor SyntheticSpectrum (1:ℤ)).map L≫esusp.inv
  have h := common_edge_flatten_preimage V U e i q esusp eA p
  dsimp only [p] at h
  simp only [Category.assoc] at h
  rw [common_desuspended_finite_edge_canonical A i q hi hq esusp] at h
  simpa only [A,U,L,Category.assoc] using h


private theorem normalized_edge_source_native_lift
    (X : ClassicalObject) (q : ℕ) (hq : 0 < q) (s t e : ℤ) (he : e=0 ∨ e=1)
    (y : Ambient model X (s,t))
    (ag : BiHom (t-s) (t+e) (XModLambdaN ((SyntheticCategory.biShift (0,e)).obj
      (model.nu.functor.obj (X.obj model.auxiliary))) q))
    (hag : Detects (model.convergence (.quotient q (.shift (0,e) (.nu X)))) (s,t,t+e)
      (regradeE2 (by simp) (finiteNuLabel model X q e s t 0 y)) ag) :
    ∃ εq : XModLambdaN ((SyntheticCategory.biShift (0,e)).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) q ≅
      (SyntheticCategory.biShift (0,e)).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q),
      XModLambdaN.incl _ q≫εq.hom =
        (SyntheticCategory.biShift (0,e)).map (XModLambdaN.incl _ q) ∧
      ∃ b : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q),
        b≫(model.quotients.tower _).rho 1 q hq =
          firstLabel model X s t y≫XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1 ∧
        homotopyRegrade (m' := t-s) (w' := t+e) (by simp) rfl
          (shiftHomotopyClass (0,e) (t-s,t) b)≫εq.inv=ag := by
  rcases he with rfl | rfl
  · obtain ⟨b,hb,_,hback⟩ := zero_finite_source_unshifted X q hq s t y ag hag
    exact ⟨zeroEdgeQuotientShiftIso _ q,zero_edge_quotient_shift_inclusion _ q,b,hb,
      (zero_edge_quotient_source_back X q s t b).trans hback⟩
  · obtain ⟨εq,hεq,b,hb,_,hback⟩ := positive_finite_source_unshifted X q hq s t y ag hag
    exact ⟨εq,hεq,b,hb,hback⟩


private theorem actual_common_edge_native_detects
    (X : ClassicalObject) (e : ℤ) (he : e=0 ∨ e=1)
    (i q : ℕ) (hi : 0 < i) (hq : 0 < q) (s t : ℤ) (y : Ambient model X (s,t))
    (esusp : XModLambdaN (((SyntheticCategory.biShift (0,e)).obj
      (model.nu.functor.obj (X.obj model.auxiliary)))⟦(1:ℤ)⟧) (i+q) ≅
      (XModLambdaN ((SyntheticCategory.biShift (0,e)).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) (i+q))⟦(1:ℤ)⟧)
    (eA : XModLambdaN ((SyntheticCategory.biShift (0,e)).obj
      (model.nu.functor.obj (X.obj model.auxiliary))) (i+q) ≅
      (SyntheticCategory.biShift (0,e)).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (i+q)))
    (heA : XModLambdaN.incl _ (i+q)≫eA.hom =
      (SyntheticCategory.biShift (0,e)).map (XModLambdaN.incl _ (i+q)))
    (ag : BiHom (t-s) (t+e) (XModLambdaN ((SyntheticCategory.biShift (0,e)).obj
      (model.nu.functor.obj (X.obj model.auxiliary))) (i+q-i)))
    (hag : Detects (model.convergence (.quotient (i+q-i) (.shift (0,e) (.nu X)))) (s,t,t+e)
      (regradeE2 (by simp) (finiteNuLabel model X (i+q-i) e s t 0 y)) ag) :
    let V := model.nu.functor.obj (X.obj model.auxiliary)
    let A := (SyntheticCategory.biShift (0,e)).obj V
    let U := XModLambdaN A (i+q-i)
    let L := ((model.quotients.tower A).triangle hi (show i < i+q by omega)).lambdaMap
    let ff := SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) (1,-(i:ℤ))
    let Jq := ff.preimage ((biSuspensionIso (i:ℤ) U).hom≫
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map L≫esusp.inv≫
        (commonEdgeTargetFlatIso V e i q esusp eA).hom)
    Detects (model.convergence (.quotient (i+q) (.nu X))) (s,t,t-i)
      (finiteTargetLabel model X (i+q) s t i y)
      (commonTargetUnshift (0,(i:ℤ)+e) (t-s,t-i) (XModLambdaN V (i+q))
        (homotopyRegrade (by simp) (by dsimp; omega) (ag≫Jq))) := by
  dsimp only
  obtain ⟨εn,hεn,b,hb,hback⟩ := normalized_edge_source_native_lift X (i+q-i) (by omega)
    s t e he y ag hag
  have hd := vertical_normalized_finite_lambda_detects X (i+q) i hi (by omega) s t e y
    εn eA hεn heA b hb ag hback
  rw [common_desuspended_finite_edge_flat_canonical _ e i q hi hq esusp eA]
  simp only [commonEdgeFlattenIso,Iso.trans_hom,Functor.mapIso_hom,Iso.app_hom]
  erw [common_flat_lambda_unshift]
  convert hd using 1
  simp only [commonTargetUnshift,quotientUnshift,regrade_comp,Category.assoc]


private theorem corrected_actual_common_edge_native_detects
    (X : ClassicalObject) (e : ℤ) (he : e=0 ∨ e=1)
    (i q : ℕ) (hi : 0 < i) (hq : 0 < q) (s t : ℤ) (y : Ambient model X (s,t))
    (esusp : XModLambdaN (((SyntheticCategory.biShift (0,e)).obj
      (model.nu.functor.obj (X.obj model.auxiliary)))⟦(1:ℤ)⟧) (i+q) ≅
      (XModLambdaN ((SyntheticCategory.biShift (0,e)).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) (i+q))⟦(1:ℤ)⟧)
    (eA : XModLambdaN ((SyntheticCategory.biShift (0,e)).obj
      (model.nu.functor.obj (X.obj model.auxiliary))) (i+q) ≅
      (SyntheticCategory.biShift (0,e)).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (i+q)))
    (heA : XModLambdaN.incl _ (i+q)≫eA.hom =
      (SyntheticCategory.biShift (0,e)).map (XModLambdaN.incl _ (i+q)))
    (ag : BiHom (t-s) (t+e) (XModLambdaN ((SyntheticCategory.biShift (0,e)).obj
      (model.nu.functor.obj (X.obj model.auxiliary))) (i+q-i)))
    (hag : Detects (model.convergence (.quotient (i+q-i) (.shift (0,e) (.nu X)))) (s,t,t+e)
      (regradeE2 (by simp) (finiteNuLabel model X (i+q-i) e s t 0 y)) ag) :
    let V := model.nu.functor.obj (X.obj model.auxiliary)
    let A := (SyntheticCategory.biShift (0,e)).obj V
    let U := XModLambdaN A (i+q-i)
    let L := ((model.quotients.tower A).triangle hi (show i < i+q by omega)).lambdaMap
    let ff := SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) (1,-(i:ℤ))
    let Jq := ff.preimage ((biSuspensionIso (i:ℤ) U).hom≫
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map L≫esusp.inv≫
        (commonEdgeTargetFlatIso V e i q esusp eA).hom)
    ∀ (u : BiHom (t-s) (t+e)
      ((SyntheticCategory.biShift (0,(i:ℤ)+e)).obj (XModLambdaN V (i+q))))
      (_hu : Detects (model.convergence (.shift (0,(i:ℤ)+e) (.quotient (i+q) (.nu X))))
        (s,t,t+e)
        (familyPageMap model.family Jq 2 (s,t,t+e)
          (regradeE2 (by simp) (finiteNuLabel model X (i+q-i) e s t 0 y))) u),
    Detects (model.convergence (.quotient (i+q) (.nu X))) (s,t,t-i)
      (finiteTargetLabel model X (i+q) s t i y)
      (commonTargetUnshift (0,(i:ℤ)+e) (t-s,t-i) (XModLambdaN V (i+q))
        (homotopyRegrade (by simp) (by dsimp; omega) u)) := by
  dsimp only
  intro u hu
  let V := model.nu.functor.obj (X.obj model.auxiliary)
  let A := (SyntheticCategory.biShift (0,e)).obj V
  let U := XModLambdaN A (i+q-i)
  let L := ((model.quotients.tower A).triangle hi (show i < i+q by omega)).lambdaMap
  let ff := SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) (1,-(i:ℤ))
  let Jq := ff.preimage ((biSuspensionIso (i:ℤ) U).hom≫
    (shiftFunctor SyntheticSpectrum (1:ℤ)).map L≫esusp.inv≫
      (commonEdgeTargetFlatIso V e i q esusp eA).hom)
  let D := SyntheticObject.shift (0,(i:ℤ)+e) (.quotient (i+q) (.nu X))
  have hb := detects_map (.quotient (i+q-i) (.shift (0,e) (.nu X))) D Jq
    (s,t,t+e) _ ag hag
  have hd := detects_sub_filtration (model.convergence D) (s,t,t+e) hu hb
  have hdc := homotopy_regrade_filtration
    (show t-s=((t-s,t-i)+(0,(i:ℤ)+e)).1 by dsimp; omega)
    (show t+e=((t-s,t-i)+(0,(i:ℤ)+e)).2 by dsimp; omega) (s+1) _ hd
  have hdn := common_target_unshift_filtration (.quotient (i+q) (.nu X))
    (0,(i:ℤ)+e) (t-s,t-i) (s+1) _ hdc
  rw [homotopy_regrade_sub,common_target_unshift_sub] at hdn
  have hbn := actual_common_edge_native_detects X e he i q hi hq s t y esusp eA heA ag hag
  exact detects_of_high_difference (.quotient (i+q) (.nu X)) (s,t,t-i) _ _ _ hbn hdn

end
end KIP126.ProofTools.Internal.Mahowald
