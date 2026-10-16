module
import all KIP126.Def.ProofTools.GeneralizedMahowald.SourceBoundaryReview
@[expose] section
namespace KIP126.ProofTools.Internal.Mahowald
open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
open KIP126.Core.SpectralSequence KIP126.AdamsSynthetic KIP126.Literature
open KIP126.AdamsSynthetic.Standard (model Spectrum)
open KIP126.Kervaire.Route
open KIP126.Core.SpectralSequence.FinitePageCalculus
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
universe u v
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
private theorem desuspend_bijective (X : C) (n : ℤ) :
    Function.Bijective (AbstractAdamsTower.desuspend X n) := by
  let e := (shiftFunctorAdd' C n (-1) (n - 1) (by omega)).app SphereSpectrum
  let d := (shiftFunctorCompIsoId C 1 (-1) (by omega)).app X
  constructor
  · intro a b h
    change e.hom ≫ (shiftFunctor C (-1 : ℤ)).map a ≫ d.hom =
      e.hom ≫ (shiftFunctor C (-1 : ℤ)).map b ≫ d.hom at h
    apply (shiftFunctor C (-1 : ℤ)).map_injective
    apply (cancel_epi e.hom).mp
    apply (cancel_mono d.hom).mp
    simpa only [Category.assoc] using h
  · intro b
    refine ⟨(shiftFunctor C (-1 : ℤ)).preimage (e.inv ≫ b ≫ d.inv), ?_⟩
    change e.hom ≫ (shiftFunctor C (-1 : ℤ)).map
      ((shiftFunctor C (-1 : ℤ)).preimage _) ≫ d.hom = b
    rw [Functor.map_preimage]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.hom_inv_id_assoc]

/-- Desuspension commutes with the actual shifted target map. -/
private theorem desuspend_postcompose {X Y : C} (f : X ⟶ Y) (n : ℤ)
    (a : HomotopyGroup n (X⟦(1 : ℤ)⟧)) :
    AbstractAdamsTower.desuspend Y n (a ≫ f⟦(1 : ℤ)⟧') = AbstractAdamsTower.desuspend X n a ≫ f := by
  change _ ≫ (shiftFunctor C (-1 : ℤ)).map (a ≫ f⟦(1 : ℤ)⟧') ≫ _ = _
  rw [Functor.map_comp]
  have h := (shiftFunctorCompIsoId C 1 (-1) (by omega)).hom.naturality f
  change (shiftFunctor C (-1 : ℤ)).map (f⟦(1 : ℤ)⟧') ≫ _ = _ ≫ f at h
  simp only [Category.assoc]
  rw [h]
  simp only [AbstractAdamsTower.desuspend, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Category.assoc]

private theorem raw_cycles_iff [HasFunctorialCofiber (C:=C)] {H : C} {unit : SphereSpectrum ⟶ H}
    {X : C} (T : AbstractAdamsTower unit X) (r : ℕ) (hr : 1≤r) (s t : ℤ)
    (a : T.FirstPage (s,t)) :
    a∈T.cycles r hr (s,t) ↔
    ∃ c : HomotopyGroup (t-s) ((T.stageAt (s+r))⟦(1:ℤ)⟧),
      c≫(T.mapAt (show s+1≤s+r by omega))⟦(1:ℤ)⟧' =
      a≫HasFunctorialCofiber.cofibδ (T.mapAt (show s≤s+1 by omega)) := by
  constructor
  · rintro ⟨b,hb⟩
    obtain ⟨c,hc⟩ := (desuspend_bijective (T.stageAt (s+r)) (t-s)).2 b
    refine ⟨c,?_⟩
    apply (desuspend_bijective (T.stageAt (s+1)) (t-s)).1
    rw [desuspend_postcompose,hc]
    exact hb
  · rintro ⟨c,hc⟩
    refine ⟨AbstractAdamsTower.desuspend (T.stageAt (s+r)) (t-s) c,?_⟩
    change _≫T.mapAt (show s+1≤s+r by omega)=
      AbstractAdamsTower.desuspend (T.stageAt (s+1)) (t-s)
        (a≫HasFunctorialCofiber.cofibδ (T.mapAt (show s≤s+1 by omega)))
    rw [←desuspend_postcompose,hc]

private theorem desuspend_mem_raw_cycles (X : ClassicalObject)
    (r : ℕ) (hr : 1≤r) (s t : ℤ)
    (a : (model.classicalTower.tower ((X.obj model.auxiliary)⟦(1:ℤ)⟧)).FirstPage (s,t))
    (ha : a∈(model.classicalTower.tower ((X.obj model.auxiliary)⟦(1:ℤ)⟧)).cycles r hr (s,t)) :
    (model.classicalSuspension X).desuspendFirstPage s t a ∈
      (model.classicalTower.tower (X.obj model.auxiliary)).cycles r hr (s,t-1) := by
  let S := model.classicalSuspension X
  let T := model.classicalTower.tower (X.obj model.auxiliary)
  obtain ⟨c,hc⟩ := (raw_cycles_iff _ r hr s t a).mp ha
  let R := shiftFunctorComm Spectrum (1:ℤ) (1:ℤ)
  let e := c≫(S.tower (s+r)).hom⟦(1:ℤ)⟧'≫R.inv.app (T.stageAt (s+r))
  have he : e≫(T.mapAt (show s+1≤s+r by omega))⟦(1:ℤ)⟧'⟦(1:ℤ)⟧' =
      -(a≫(S.layer s).hom≫(HasFunctorialCofiber.cofibδ
        (T.mapAt (show s≤s+1 by omega)))⟦(1:ℤ)⟧') := by
    dsimp only [e]
    simp only [Category.assoc]
    erw [←R.inv.naturality]
    simp only [Functor.comp_map]
    rw [←Functor.map_comp_assoc,S.tower_comm,Functor.map_comp]
    simp only [←Category.assoc]
    erw [hc]
    simp only [Category.assoc]
    have hs := S.layer_connecting s
    have hs' := congrArg (fun f=>f≫R.inv.app (T.stageAt (s+1))) hs
    dsimp only [T,AbstractAdamsTower.layer] at hs'
    simp only [R,Category.assoc,Iso.hom_inv_id_app,Preadditive.neg_comp] at hs'
    erw [Category.comp_id] at hs'
    erw [hs']
    simp only [Preadditive.comp_neg,neg_neg]
    rfl
  apply (raw_cycles_iff T r hr s (t-1) _).mpr
  let j := eqToHom (congrArg (Sphere (C:=Spectrum)) (show (t-1)-s=(t-s)-1 by omega))
  refine ⟨-(j≫AbstractAdamsTower.desuspend ((T.stageAt (s+r))⟦(1:ℤ)⟧) (t-s) e),?_⟩
  rw [Preadditive.neg_comp,Category.assoc,←desuspend_postcompose,he,map_neg]
  simp only [Preadditive.comp_neg,neg_neg]
  rw [←Category.assoc a]
  erw [desuspend_postcompose]
  exact (Category.assoc _ _ _).symm


private theorem desuspendFirstPage_bijective (X : ClassicalObject) (s t : ℤ) :
    Function.Bijective ((model.classicalSuspension X).desuspendFirstPage s t) := by
  let S := model.classicalSuspension X
  let T := model.classicalTower.tower (X.obj model.auxiliary)
  let j := eqToIso (congrArg (Sphere (C:=Spectrum)) (show (t-1)-s=(t-s)-1 by omega))
  constructor
  · intro a b h
    apply (cancel_mono (S.layer s).hom).mp
    apply (desuspend_bijective (T.layer s) (t-s)).1
    apply (cancel_epi j.hom).mp
    exact h
  · intro b
    obtain ⟨c,hc⟩ := (desuspend_bijective (T.layer s) (t-s)).2 (j.inv ≫ b)
    refine ⟨c ≫ (S.layer s).inv,?_⟩
    change j.hom ≫ AbstractAdamsTower.desuspend (T.layer s) (t-s)
      ((c ≫ (S.layer s).inv) ≫ (S.layer s).hom) = b
    rw [Category.assoc,Iso.inv_hom_id,Category.comp_id,hc,Iso.hom_inv_id_assoc]

private def lift_desuspend (X : ClassicalObject) (d n : ℤ) :
    HomotopyGroup n (((model.classicalTower.tower ((X.obj model.auxiliary)⟦(1:ℤ)⟧)).stageAt d)⟦(1:ℤ)⟧) →+
      HomotopyGroup (n-1) (((model.classicalTower.tower (X.obj model.auxiliary)).stageAt d)⟦(1:ℤ)⟧) where
  toFun c := AbstractAdamsTower.desuspend
    (((model.classicalTower.tower (X.obj model.auxiliary)).stageAt d)⟦(1:ℤ)⟧) n
      (c ≫ ((model.classicalSuspension X).tower d).hom⟦(1:ℤ)⟧' ≫
        (shiftFunctorComm Spectrum (1:ℤ) (1:ℤ)).inv.app
          ((model.classicalTower.tower (X.obj model.auxiliary)).stageAt d))
  map_zero' := by simp only [Limits.zero_comp, map_zero]
  map_add' a b := by simp only [Preadditive.add_comp,map_add]

private theorem lift_desuspend_bijective (X : ClassicalObject) (d n : ℤ) :
    Function.Bijective (lift_desuspend X d n) := by
  let S := model.classicalSuspension X
  let T := model.classicalTower.tower (X.obj model.auxiliary)
  let R := shiftFunctorComm Spectrum (1:ℤ) (1:ℤ)
  constructor
  · intro a b h
    have h' := (desuspend_bijective ((T.stageAt d)⟦(1:ℤ)⟧) n).1 h
    apply (cancel_mono ((S.tower d).hom⟦(1:ℤ)⟧')).mp
    apply (cancel_mono (R.inv.app (T.stageAt d))).mp
    simpa only [Category.assoc] using h'
  · intro b
    obtain ⟨e,he⟩ := (desuspend_bijective ((T.stageAt d)⟦(1:ℤ)⟧) n).2 b
    refine ⟨e ≫ R.hom.app (T.stageAt d) ≫ (S.tower d).inv⟦(1:ℤ)⟧', ?_⟩
    change AbstractAdamsTower.desuspend ((T.stageAt d)⟦(1:ℤ)⟧) n
      ((e ≫ R.hom.app (T.stageAt d) ≫ (S.tower d).inv⟦(1:ℤ)⟧') ≫
        (S.tower d).hom⟦(1:ℤ)⟧' ≫ R.inv.app (T.stageAt d))=b
    simp only [Category.assoc]
    let E := (shiftFunctor Spectrum (1:ℤ)).mapIso (S.tower d)
    change AbstractAdamsTower.desuspend ((T.stageAt d)⟦(1:ℤ)⟧) n
      (e ≫ R.hom.app (T.stageAt d) ≫ E.inv ≫ E.hom ≫ R.inv.app (T.stageAt d))=b
    simp only [Iso.inv_hom_id_assoc,Iso.hom_inv_id_app]
    erw [Category.comp_id]
    exact he

private theorem lift_desuspend_natural (X : ClassicalObject) (d e n : ℤ) (hde : d≤e)
    (c : HomotopyGroup n
      (((model.classicalTower.tower ((X.obj model.auxiliary)⟦(1:ℤ)⟧)).stageAt e)⟦(1:ℤ)⟧)) :
    lift_desuspend X d n (c ≫
      (model.classicalTower.tower ((X.obj model.auxiliary)⟦(1:ℤ)⟧)).mapAt hde⟦(1:ℤ)⟧') =
      lift_desuspend X e n c ≫
        ((model.classicalTower.tower (X.obj model.auxiliary)).mapAt hde)⟦(1:ℤ)⟧' := by
  let S := model.classicalSuspension X
  let T := model.classicalTower.tower (X.obj model.auxiliary)
  let R := shiftFunctorComm Spectrum (1:ℤ) (1:ℤ)
  dsimp only [lift_desuspend,AddMonoidHom.coe_mk,ZeroHom.coe_mk]
  rw [←desuspend_postcompose]
  congr 1
  simp only [Category.assoc]
  erw [←R.inv.naturality]
  simp only [Functor.comp_map]
  rw [←Functor.map_comp_assoc,←S.tower_comm,Functor.map_comp]
  simp only [Category.assoc]
  rfl

private theorem lift_desuspend_connecting (X : ClassicalObject) (s t : ℤ)
    (a : (model.classicalTower.tower ((X.obj model.auxiliary)⟦(1:ℤ)⟧)).FirstPage (s,t)) :
    lift_desuspend X (s+1) (t-s) (a ≫ HasFunctorialCofiber.cofibδ
      ((model.classicalTower.tower ((X.obj model.auxiliary)⟦(1:ℤ)⟧)).mapAt (show s≤s+1 by omega))) =
      -(AbstractAdamsTower.desuspend
        ((model.classicalTower.tower (X.obj model.auxiliary)).layer s) (t-s)
          (a≫((model.classicalSuspension X).layer s).hom) ≫
        HasFunctorialCofiber.cofibδ
          ((model.classicalTower.tower (X.obj model.auxiliary)).mapAt (show s≤s+1 by omega))) := by
  let S := model.classicalSuspension X
  let T := model.classicalTower.tower (X.obj model.auxiliary)
  let R := shiftFunctorComm Spectrum (1:ℤ) (1:ℤ)
  have hs := S.layer_connecting s
  have hs' := congrArg (fun f=>f≫R.inv.app (T.stageAt (s+1))) hs
  dsimp only [T,AbstractAdamsTower.layer] at hs'
  simp only [R,Category.assoc,Iso.hom_inv_id_app,Preadditive.neg_comp] at hs'
  erw [Category.comp_id] at hs'
  have hs'' := congrArg (fun f=>a≫f) hs'
  simp only [Preadditive.comp_neg] at hs''
  dsimp only [lift_desuspend,AddMonoidHom.coe_mk,ZeroHom.coe_mk]
  rw [←neg_eq_iff_eq_neg] at hs''
  simp only [Category.assoc]
  erw [←hs'']
  rw [map_neg,←Category.assoc a,desuspend_postcompose]
  rfl

private theorem desuspend_mem_raw_cycles_iff (X : ClassicalObject)
    (r : ℕ) (hr : 1≤r) (s t : ℤ)
    (a : (model.classicalTower.tower ((X.obj model.auxiliary)⟦(1:ℤ)⟧)).FirstPage (s,t)) :
    (model.classicalSuspension X).desuspendFirstPage s t a ∈
      (model.classicalTower.tower (X.obj model.auxiliary)).cycles r hr (s,t-1) ↔
    a∈(model.classicalTower.tower ((X.obj model.auxiliary)⟦(1:ℤ)⟧)).cycles r hr (s,t) := by
  refine ⟨?_,desuspend_mem_raw_cycles X r hr s t a⟩
  intro ha
  let S := model.classicalSuspension X
  let T := model.classicalTower.tower (X.obj model.auxiliary)
  let U := model.classicalTower.tower ((X.obj model.auxiliary)⟦(1:ℤ)⟧)
  let j := eqToIso (congrArg (Sphere (C:=Spectrum)) (show (t-1)-s=(t-s)-1 by omega))
  obtain ⟨d,hd⟩ := (raw_cycles_iff T r hr s (t-1) _).mp ha
  obtain ⟨c,hc⟩ := (lift_desuspend_bijective X (s+r) (t-s)).2 (-(j.inv≫d))
  apply (raw_cycles_iff U r hr s t a).mpr
  refine ⟨c,?_⟩
  apply (lift_desuspend_bijective X (s+1) (t-s)).1
  rw [lift_desuspend_natural,lift_desuspend_connecting,hc]
  rw [Preadditive.neg_comp,neg_inj,Category.assoc,hd]
  change j.inv ≫ (j.hom ≫ _) ≫ _ = _
  simp only [←Category.assoc,Iso.inv_hom_id,Category.id_comp]
  rfl

private theorem exists_suspendsClass (X : ClassicalObject) (s t : ℤ)
    (x : Ambient model X (s,t-1)) :
    ∃ sx : Ambient model (.shift 1 X) (s,t),
      (model.classicalSuspension X).DesuspendsClass s t sx x := by
  let S := model.classicalSuspension X
  let DX := (model.classical.obj (X.obj model.auxiliary)).ssData (s,t-1)
  let DU := (model.classical.obj ((X.obj model.auxiliary)⟦(1:ℤ)⟧)).ssData (s,t)
  let PX := model.classicalTower.sequence (X.obj model.auxiliary)
  let PU := model.classicalTower.sequence ((X.obj model.auxiliary)⟦(1:ℤ)⟧)
  let TX := model.classicalTower.tower (X.obj model.auxiliary)
  let TU := model.classicalTower.tower ((X.obj model.auxiliary)⟦(1:ℤ)⟧)
  let qx : Subobject.underlying.obj (DX.Z 0) ⟶ Ambient model X (s,t-1) := DX.pageπ 0 ≫
    eqToHom (by simp only [Ambient,DX,KIP126.Core.SpectralSequence.Page,
      model.classical.firstPage,sub_self,Int.toNat_zero,Nat.cast_zero])
  haveI : Epi (DX.pageπ 0) := inferInstanceAs (Epi (cokernel.π _))
  haveI : Epi qx := by
    dsimp only [qx]
    infer_instance
  obtain ⟨b,hb⟩ := (ModuleCat.epi_iff_surjective qx).mp inferInstance x
  let xb := ((PX.ambient (s,t-1)).hom ((DX.Z 0).arrow b)).val
  obtain ⟨sa,hsa⟩ := (desuspendFirstPage_bijective X s t).2 xb
  have hsa_cycle : sa∈TU.cycles 2 (by omega) (s,t) := by
    apply (desuspend_mem_raw_cycles_iff X 2 (by omega) s t sa).mp
    rw [hsa]
    exact ((PX.ambient (s,t-1)).hom ((DX.Z 0).arrow b)).property
  let v := (PU.ambient (s,t)).inv ⟨sa,hsa_cycle⟩
  have hv : v ∈ (ModuleCat.subobjectModule DU.V) (DU.Z 0) := by
    apply (PU.cycles (s,t) 0 v).mpr
    have he : (PU.ambient (s,t)).hom v = ⟨sa,hsa_cycle⟩ := by
      change ((PU.ambient (s,t)).inv ≫ (PU.ambient (s,t)).hom) _ = _
      rw [Iso.inv_hom_id]
      rfl
    rw [he]
    exact hsa_cycle
  obtain ⟨a,ha⟩ := hv
  let qu : Subobject.underlying.obj (DU.Z 0) ⟶ Ambient model (.shift 1 X) (s,t) := DU.pageπ 0 ≫
    eqToHom (by simp only [Ambient,DU,ClassicalObject.obj,KIP126.Core.SpectralSequence.Page,
      model.classical.firstPage,sub_self,Int.toNat_zero,Nat.cast_zero])
  refine ⟨qu a,a,b,rfl,hb,?_⟩
  have heav : (PU.ambient (s,t)).hom ((DU.Z 0).arrow a)=⟨sa,hsa_cycle⟩ := by
    rw [ha]
    change ((PU.ambient (s,t)).inv ≫ (PU.ambient (s,t)).hom) _ = _
    rw [Iso.inv_hom_id]
    rfl
  change S.desuspendFirstPage s t
    (((PU.ambient (s,t)).hom ((DU.Z 0).arrow a)).val)=xb
  rw [heav]
  exact hsa

private theorem boundary_desuspend_bijective (X : C) (n : ℤ) :
    Function.Bijective (AbstractAdamsTower.desuspend X n) := by
  let e := (shiftFunctorAdd' C n (-1) (n - 1) (by omega)).app SphereSpectrum
  let d := (shiftFunctorCompIsoId C 1 (-1) (by omega)).app X
  constructor
  · intro a b h
    change e.hom ≫ (shiftFunctor C (-1 : ℤ)).map a ≫ d.hom =
      e.hom ≫ (shiftFunctor C (-1 : ℤ)).map b ≫ d.hom at h
    apply (shiftFunctor C (-1 : ℤ)).map_injective
    apply (cancel_epi e.hom).mp
    apply (cancel_mono d.hom).mp
    simpa only [Category.assoc] using h
  · intro b
    refine ⟨(shiftFunctor C (-1 : ℤ)).preimage (e.inv ≫ b ≫ d.inv), ?_⟩
    change e.hom ≫ (shiftFunctor C (-1 : ℤ)).map
      ((shiftFunctor C (-1 : ℤ)).preimage _) ≫ d.hom = b
    rw [Functor.map_preimage]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.hom_inv_id_assoc]
private theorem boundary_desuspend_postcompose {X Y : C} (f : X ⟶ Y) (n : ℤ)
    (a : HomotopyGroup n (X⟦(1 : ℤ)⟧)) :
    AbstractAdamsTower.desuspend Y n (a ≫ f⟦(1 : ℤ)⟧') = AbstractAdamsTower.desuspend X n a ≫ f := by
  change _ ≫ (shiftFunctor C (-1 : ℤ)).map (a ≫ f⟦(1 : ℤ)⟧') ≫ _ = _
  rw [Functor.map_comp]
  have h := (shiftFunctorCompIsoId C 1 (-1) (by omega)).hom.naturality f
  change (shiftFunctor C (-1 : ℤ)).map (f⟦(1 : ℤ)⟧') ≫ _ = _ ≫ f at h
  simp only [Category.assoc]
  rw [h]
  simp only [AbstractAdamsTower.desuspend, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Category.assoc]

private def boundary_desuspendHom {U V : C} (e : U ≅ V⟦(1 : ℤ)⟧) (s t : ℤ)
    (b : HomotopyGroup (t-s) U) : HomotopyGroup ((t-1)-s) V :=
  eqToHom (congrArg (Sphere (C := C)) (show (t-1)-s=(t-s)-1 by omega)) ≫
    AbstractAdamsTower.desuspend V (t-s) (b ≫ e.hom)

private theorem boundary_desuspendHom_bijective {U V : C} (e : U ≅ V⟦(1 : ℤ)⟧) (s t : ℤ) :
    Function.Bijective (boundary_desuspendHom e s t) := by
  let j := eqToIso (congrArg (Sphere (C := C)) (show (t-1)-s=(t-s)-1 by omega))
  constructor
  · intro a b h
    apply (cancel_mono e.hom).mp
    apply (boundary_desuspend_bijective V (t-s)).1
    apply (cancel_epi j.hom).mp
    exact h
  · intro b
    obtain ⟨c,hc⟩ := (boundary_desuspend_bijective V (t-s)).2 (j.inv ≫ b)
    refine ⟨c ≫ e.inv, ?_⟩
    simp only [boundary_desuspendHom, Category.assoc, Iso.inv_hom_id, Category.comp_id, hc]
    exact j.hom_inv_id_assoc b

private theorem boundary_desuspendHom_zero {U V : C} (e : U ≅ V⟦(1 : ℤ)⟧) (s t : ℤ) :
    boundary_desuspendHom e s t 0 = 0 := by
  simp only [boundary_desuspendHom, zero_comp, map_zero, comp_zero]

private theorem boundary_desuspendHom_natural {U U' V V' : C}
    (e : U ≅ V⟦(1 : ℤ)⟧) (e' : U' ≅ V'⟦(1 : ℤ)⟧)
    (f : U ⟶ U') (g : V ⟶ V') (h : e.hom ≫ g⟦(1 : ℤ)⟧'=f≫e'.hom)
    (s t : ℤ) (b : HomotopyGroup (t-s) U) :
    boundary_desuspendHom e' s t (b≫f) = boundary_desuspendHom e s t b ≫ g := by
  unfold boundary_desuspendHom
  rw [Category.assoc, ←h, ←Category.assoc, boundary_desuspend_postcompose]
  exact (Category.assoc _ _ _).symm

private theorem raw_boundaries_iff [HasFunctorialCofiber (C:=C)] {H : C} {unit : SphereSpectrum ⟶ H}
    {X : C} (T : AbstractAdamsTower unit X) (r : ℕ) (hr : 1≤r) (s t : ℤ)
    (a : T.FirstPage (s,t)) :
    a∈T.boundaries r hr (s,t) ↔
    ∃ b : HomotopyGroup (t-s) (T.stageAt s),
      b≫T.mapAt (show s-r+1≤s by omega)=0 ∧
      b≫HasFunctorialCofiber.cofibι (T.mapAt (show s≤s+1 by omega))=a := by
  rfl

private theorem desuspend_mem_raw_boundaries_iff (X : ClassicalObject)
    (r : ℕ) (hr : 1≤r) (s t : ℤ)
    (a : (model.classicalTower.tower ((X.obj model.auxiliary)⟦(1:ℤ)⟧)).FirstPage (s,t)) :
    (model.classicalSuspension X).desuspendFirstPage s t a ∈
      (model.classicalTower.tower (X.obj model.auxiliary)).boundaries r hr (s,t-1) ↔
    a∈(model.classicalTower.tower ((X.obj model.auxiliary)⟦(1:ℤ)⟧)).boundaries r hr (s,t) := by
  let S := model.classicalSuspension X
  let T := model.classicalTower.tower (X.obj model.auxiliary)
  let U := model.classicalTower.tower ((X.obj model.auxiliary)⟦(1:ℤ)⟧)
  have hi (b : HomotopyGroup (t-s) (U.stageAt s)) :
      boundary_desuspendHom (S.layer s) s t
        (b≫HasFunctorialCofiber.cofibι (U.mapAt (show s≤s+1 by omega))) =
      boundary_desuspendHom (S.tower s) s t b≫
        HasFunctorialCofiber.cofibι (T.mapAt (show s≤s+1 by omega)) :=
    boundary_desuspendHom_natural _ _ _ _ (S.layer_inclusion s).symm s t b
  have hm (b : HomotopyGroup (t-s) (U.stageAt s)) :
      boundary_desuspendHom (S.tower (s-r+1)) s t
        (b≫U.mapAt (show s-r+1≤s by omega)) =
      boundary_desuspendHom (S.tower s) s t b≫T.mapAt (show s-r+1≤s by omega) :=
    boundary_desuspendHom_natural _ _ _ _ (S.tower_comm _ _ _) s t b
  constructor
  · intro ha
    obtain ⟨b,hb,he⟩ := (raw_boundaries_iff T r hr s (t-1) _).mp ha
    obtain ⟨c,hc⟩ := (boundary_desuspendHom_bijective (S.tower s) s t).2 b
    apply (raw_boundaries_iff U r hr s t a).mpr
    refine ⟨c,?_,?_⟩
    · apply (boundary_desuspendHom_bijective (S.tower (s-r+1)) s t).1
      rw [hm,hc,hb,boundary_desuspendHom_zero]
    · apply (boundary_desuspendHom_bijective (S.layer s) s t).1
      rw [hi,hc]
      exact he
  · intro ha
    obtain ⟨b,hb,he⟩ := (raw_boundaries_iff U r hr s t a).mp ha
    apply (raw_boundaries_iff T r hr s (t-1) _).mpr
    refine ⟨boundary_desuspendHom (S.tower s) s t b,?_,?_⟩
    · rw [←hm,hb,boundary_desuspendHom_zero]
    · rw [←hi,he]
      rfl

private theorem initial_class_boundary_iff (D : SSData (ModuleCat.{0} ℤ))
    (n : WithTop ℕ) (z : (Subobject.underlying.obj (D.Z 0) : ModuleCat ℤ)) :
    (∃ b : (Subobject.underlying.obj (D.B n) : ModuleCat ℤ),
      (Subobject.ofLE (D.B n) (D.Z 0)
        ((D.B_le_Z n).trans (D.Z_anti bot_le)) ≫ D.pageπ 0) b=D.pageπ 0 z) ↔
      (D.Z 0).arrow z∈(ModuleCat.subobjectModule D.V) (D.B n) := by
  let i := Subobject.ofLE (D.B n) (D.Z 0)
    ((D.B_le_Z n).trans (D.Z_anti bot_le))
  constructor
  · rintro ⟨b,hb⟩
    have hz : D.pageπ 0 (z-i b)=0 := by
      rw [map_sub]
      exact sub_eq_zero.mpr hb.symm
    have h0 := (subobject_cokernel_π_eq_zero_iff (D.B 0) (D.Z 0) (D.B_le_Z 0) _).mp hz
    have h0' : (D.Z 0).arrow (z-i b)∈(ModuleCat.subobjectModule D.V) (D.B n) :=
      (ModuleCat.subobjectModule D.V).monotone (D.B_mono bot_le) h0
    have hb' : (D.Z 0).arrow (i b)∈(ModuleCat.subobjectModule D.V) (D.B n) := by
      change (i≫(D.Z 0).arrow) b∈_
      rw [Subobject.ofLE_arrow]
      exact ⟨b,rfl⟩
    have h := ((ModuleCat.subobjectModule D.V) (D.B n)).add_mem h0' hb'
    rw [map_sub,sub_add_cancel] at h
    exact h
  · rintro ⟨b,hb⟩
    refine ⟨b,?_⟩
    have he : i b=z := by
      apply (ModuleCat.mono_iff_injective (D.Z 0).arrow).mp inferInstance
      change (i≫(D.Z 0).arrow) b=(D.Z 0).arrow z
      rw [Subobject.ofLE_arrow]
      exact hb
    change D.pageπ 0 (i b)=D.pageπ 0 z
    rw [he]

private theorem class_boundary_iff (X : ClassicalObject)
    (b : ℤ) (p : ℤ×ℤ)
    (z : (Subobject.underlying.obj (((model.classical.obj (X.obj model.auxiliary)).ssData p).Z 0) : ModuleCat ℤ)) :
    cycleLabel model X 0 p z∈boundaries model X b p ↔
      ((((model.classicalTower.sequence (X.obj model.auxiliary)).ambient p).hom
        ((((model.classical.obj (X.obj model.auxiliary)).ssData p).Z 0).arrow z)).val)∈
          (model.classicalTower.tower (X.obj model.auxiliary)).boundaries ((b-1).toNat+2) (by omega) p := by
  let D := (model.classical.obj (X.obj model.auxiliary)).ssData p
  rw [←(model.classicalTower.sequence (X.obj model.auxiliary)).boundaries p (b-1).toNat]
  rw [←initial_class_boundary_iff D (↑(b-1).toNat) z]
  change (∃v, boundaryLabel model X (↑(b-1).toNat) p v=cycleLabel model X 0 p z) ↔ _
  simp only [cycleLabel,boundaryLabel,Subobject.ofLE_refl,Category.id_comp]
  constructor
  · rintro ⟨v,hv⟩
    refine ⟨v,?_⟩
    apply (ModuleCat.mono_iff_injective (eqToHom _)).mp inferInstance
    exact hv
  · rintro ⟨v,hv⟩
    refine ⟨v,?_⟩
    exact congrArg (fun a=>(eqToHom _ : D.page 0 ⟶ (model.classical.obj (X.obj model.auxiliary)).Page 2 p) a) hv

private theorem desuspendsClass_boundary_iff (X : ClassicalObject)
    (k s t : ℤ)
    (sx : (model.classical.obj ((X.obj model.auxiliary)⟦(1:ℤ)⟧)).Page 2 (s,t))
    (x : (model.classical.obj (X.obj model.auxiliary)).Page 2 (s,t-1))
    (h : (model.classicalSuspension X).DesuspendsClass s t sx x) :
    sx∈boundaries model (.shift 1 X) k (s,t) ↔
      x∈boundaries model X k (s,t-1) := by
  obtain ⟨a,b,ha,hb,hab⟩ := h
  have ha' : cycleLabel model (.shift 1 X) 0 (s,t) a=sx := by
    simpa only [cycleLabel,Subobject.ofLE_refl,Category.id_comp,ClassicalObject.obj] using ha
  have hb' : cycleLabel model X 0 (s,t-1) b=x := by
    simpa only [cycleLabel,Subobject.ofLE_refl,Category.id_comp] using hb
  rw [←ha',←hb',class_boundary_iff,class_boundary_iff,←hab]
  exact (desuspend_mem_raw_boundaries_iff X ((k-1).toNat+2) (by omega) s t _).symm

private theorem desuspendsClass_eq_zero_iff (X : ClassicalObject)
    (s t : ℤ)
    (sx : (model.classical.obj ((X.obj model.auxiliary)⟦(1:ℤ)⟧)).Page 2 (s,t))
    (x : (model.classical.obj (X.obj model.auxiliary)).Page 2 (s,t-1))
    (h : (model.classicalSuspension X).DesuspendsClass s t sx x) :
    sx=0 ↔ x=0 := by
  have hb := desuspendsClass_boundary_iff X 1 s t sx x h
  rw [boundaries_one model (.shift 1 X) (s,t),boundaries_one model X (s,t-1)] at hb
  exact hb

private theorem desuspendsClass_ne_zero_iff (X : ClassicalObject)
    (s t : ℤ)
    (sx : (model.classical.obj ((X.obj model.auxiliary)⟦(1:ℤ)⟧)).Page 2 (s,t))
    (x : (model.classical.obj (X.obj model.auxiliary)).Page 2 (s,t-1))
    (h : (model.classicalSuspension X).DesuspendsClass s t sx x) :
    sx≠0 ↔ x≠0 :=
  not_congr (desuspendsClass_eq_zero_iff X s t sx x h)


private theorem suspension_desuspends_sub (X : ClassicalObject) (s t : ℤ)
    (sx sy : Ambient model (.shift 1 X) (s,t))
    (x y : Ambient model X (s,t-1))
    (hx : (model.classicalSuspension X).DesuspendsClass s t sx x)
    (hy : (model.classicalSuspension X).DesuspendsClass s t sy y) :
    (model.classicalSuspension X).DesuspendsClass s t (sx-sy) (x-y) := by
  obtain ⟨a,b,ha,hb,hab⟩ := hx
  obtain ⟨a',b',ha',hb',hab'⟩ := hy
  refine ⟨a-a',b-b',?_,?_,?_⟩
  · rw [map_sub,ha,ha']
  · rw [map_sub,hb,hb']
  · simpa only [map_sub,Submodule.coe_sub] using congrArg₂ (fun x y => x-y) hab hab'

private theorem desuspendsClass_eq_iff (X : ClassicalObject) (s t : ℤ)
    (sx sy : Ambient model (.shift 1 X) (s,t))
    (x y : Ambient model X (s,t-1))
    (hx : (model.classicalSuspension X).DesuspendsClass s t sx x)
    (hy : (model.classicalSuspension X).DesuspendsClass s t sy y) :
    sx=sy ↔ x=y := by
  have h := desuspendsClass_eq_zero_iff X s t (sx-sy) (x-y)
    (suspension_desuspends_sub X s t sx sy x y hx hy)
  simpa only [sub_eq_zero] using h

private theorem exists_suspendsClass_mem_boundary (X : ClassicalObject) (k s t : ℤ)
    (x : Ambient model X (s,t-1)) (hx : x∈boundaries model X k (s,t-1)) :
    ∃ sx : Ambient model (.shift 1 X) (s,t),
      (model.classicalSuspension X).DesuspendsClass s t sx x ∧
      sx∈boundaries model (.shift 1 X) k (s,t) := by
  obtain ⟨sx,hsx⟩ := exists_suspendsClass X s t x
  exact ⟨sx,hsx,(desuspendsClass_boundary_iff X k s t sx x hsx).mpr hx⟩

private theorem mh2BoundaryClass_suspends :
    ∃ sx : Ambient model (.shift 1 .sphere) (3,18),
      (model.classicalSuspension .sphere).DesuspendsClass 3 18 sx mh2BoundaryClass ∧
      sx∈boundaries model (.shift 1 .sphere) 2 (3,18) := by
  exact exists_suspendsClass_mem_boundary .sphere 2 3 18 mh2BoundaryClass
    mh2BoundaryClass_boundary

private theorem mh2BoundaryClass_suspends_nonzero :
    ∃ sx : Ambient model (.shift 1 .sphere) (3,18),
      (model.classicalSuspension .sphere).DesuspendsClass 3 18 sx mh2BoundaryClass ∧
      sx∈boundaries model (.shift 1 .sphere) 2 (3,18) ∧ sx≠0 := by
  obtain ⟨sx,hsx,hb⟩ := mh2BoundaryClass_suspends
  exact ⟨sx,hsx,hb,(desuspendsClass_ne_zero_iff .sphere 3 18 sx
    mh2BoundaryClass hsx).mpr mh2BoundaryClass_nonzero⟩

end
end KIP126.ProofTools.Internal.Mahowald
