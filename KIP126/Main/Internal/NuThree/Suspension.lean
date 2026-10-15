module
public import KIP126.Def.ProofTools.Representatives
public import KIP126.Def.ProofTools.Operations
/-! Desuspension preserves the same tower cycle representatives. The original
NuFifth:105–220 and StableHomotopy/Context/Suspension proofs at bbac1fc05843
(MIT) are expressed on the given abstract tower presentation. -/
@[expose] section
namespace KIP126.Main.Internal.NuThree
open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
open KIP126.Core.SpectralSequence KIP126.AdamsSynthetic KIP126.Literature
open KIP126.AdamsSynthetic.Standard (model Spectrum)
open KIP126.ProofTools KIP126.Kervaire.Route
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
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

private theorem initial_class_cycle_iff (D : SSData (ModuleCat.{0} ℤ))
    (n : WithTop ℕ) (z : (Subobject.underlying.obj (D.Z 0) : ModuleCat ℤ)) :
    (∃ v : (Subobject.underlying.obj (D.Z n) : ModuleCat ℤ),
      (Subobject.ofLE (D.Z n) (D.Z 0) (D.Z_anti bot_le) ≫ D.pageπ 0) v=D.pageπ 0 z) ↔
      (D.Z 0).arrow z∈(ModuleCat.subobjectModule D.V) (D.Z n) := by
  let i := Subobject.ofLE (D.Z n) (D.Z 0) (D.Z_anti bot_le)
  constructor
  · rintro ⟨v,hv⟩
    have hz : D.pageπ 0 (z-i v)=0 := by
      rw [map_sub]
      exact sub_eq_zero.mpr hv.symm
    have hb := (subobject_cokernel_π_eq_zero_iff (D.B 0) (D.Z 0) (D.B_le_Z 0) _).mp hz
    have hb' : (D.Z 0).arrow (z-i v)∈(ModuleCat.subobjectModule D.V) (D.Z n) := (ModuleCat.subobjectModule D.V).monotone
      ((D.B_mono le_top).trans ((D.B_le_Z ⊤).trans (D.Z_anti le_top))) hb
    have hv' : (D.Z 0).arrow (i v)∈(ModuleCat.subobjectModule D.V) (D.Z n) := by
      change (i≫(D.Z 0).arrow) v∈_
      rw [Subobject.ofLE_arrow]
      exact ⟨v,rfl⟩
    have h := ((ModuleCat.subobjectModule D.V) (D.Z n)).add_mem hb' hv'
    rw [map_sub,sub_add_cancel] at h
    exact h
  · rintro ⟨v,hv⟩
    refine ⟨v,?_⟩
    have he : i v=z := by
      apply (ModuleCat.mono_iff_injective (D.Z 0).arrow).mp inferInstance
      change (i≫(D.Z 0).arrow) v=(D.Z 0).arrow z
      rw [Subobject.ofLE_arrow]
      exact hv
    change D.pageπ 0 (i v)=D.pageπ 0 z
    rw [he]

private theorem class_cycle_iff (X : ClassicalObject)
    (c : ℤ) (p : ℤ×ℤ)
    (z : (Subobject.underlying.obj (((model.classical.obj (X.obj model.auxiliary)).ssData p).Z 0) : ModuleCat ℤ)) :
    cycleLabel model X 0 p z∈cycles model X c p ↔
      ((((model.classicalTower.sequence (X.obj model.auxiliary)).ambient p).hom
        ((((model.classical.obj (X.obj model.auxiliary)).ssData p).Z 0).arrow z)).val)∈
          (model.classicalTower.tower (X.obj model.auxiliary)).cycles ((c-1).toNat+2) (by omega) p := by
  let D := (model.classical.obj (X.obj model.auxiliary)).ssData p
  rw [←(model.classicalTower.sequence (X.obj model.auxiliary)).cycles p (c-1).toNat]
  rw [←initial_class_cycle_iff D (↑(c-1).toNat) z]
  change (∃v, cycleLabel model X (↑(c-1).toNat) p v=cycleLabel model X 0 p z) ↔ _
  simp only [cycleLabel,Subobject.ofLE_refl,Category.id_comp]
  constructor
  · rintro ⟨v,hv⟩
    refine ⟨v,?_⟩
    apply (ModuleCat.mono_iff_injective (eqToHom _)).mp inferInstance
    exact hv
  · rintro ⟨v,hv⟩
    refine ⟨v,?_⟩
    exact congrArg (fun a=>(eqToHom _ : D.page 0 ⟶ (model.classical.obj (X.obj model.auxiliary)).Page 2 p) a) hv

private theorem desuspendsClass_isCycle (X : ClassicalObject)
    (level s t : ℤ)
    (sx : (model.classical.obj ((X.obj model.auxiliary)⟦(1:ℤ)⟧)).Page 2 (s,t))
    (x : (model.classical.obj (X.obj model.auxiliary)).Page 2 (s,t-1))
    (h : (model.classicalSuspension X).DesuspendsClass s t sx x)
    (hc : IsCycle model (.shift 1 X) level (s,t) sx) :
    IsCycle model X level (s,t-1) x := by
  obtain ⟨a,b,ha,hb,hab⟩ := h
  refine ⟨hc.1,?_⟩
  have ha' : cycleLabel model (.shift 1 X) 0 (s,t) a=sx := by
    simpa only [cycleLabel,Subobject.ofLE_refl,Category.id_comp,ClassicalObject.obj] using ha
  have hb' : cycleLabel model X 0 (s,t-1) b=x := by
    simpa only [cycleLabel,Subobject.ofLE_refl,Category.id_comp] using hb
  rw [←hb']
  apply (class_cycle_iff X level (s,t-1) b).mpr
  rw [←hab]
  exact desuspend_mem_raw_cycles X ((level-1).toNat+2) (by omega) s t _
    ((class_cycle_iff (.shift 1 X) level (s,t) a).mp (ha'.symm ▸ hc.2))

end
end KIP126.Main.Internal.NuThree
