module

public import KIP126.Literature.Classical
public import KIP126.AdamsSynthetic.ExtensionLabels

/-! Realization comparisons between the actual synthetic and classical
coefficient towers. The data are stage maps, cofiber squares, and maps of
cycle/boundary presentations; detection is a theorem derived below. -/

@[expose] section
namespace KIP126.Literature
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.AdamsSynthetic KIP126.Classical.Adams KIP126.Synthetic.SpectralSequence
open KIP126.Core.SpectralSequence KIP126.Kervaire.Route
universe u v w
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w,v} Syn]
  [HasFunctorialCofiber (C := Syn)] (D : Model C Syn)
set_option backward.isDefEq.respectTransparency false

/-- The ordinary synthetic sphere coordinate induced by the specified
weight-zero realization coordinate and the actual shift compatibility. -/
public def realizationSphereCoordinate (R : RealizationCoordinates D) (m : ℤ) :
    Sphere (C := C) m ≅ D.recovery.realization.obj (Sphere (C := Syn) m) :=
  R.sphere m 0 ≪≫ D.recovery.realization.mapIso
    ((SyntheticCategory.biShift_compat (Syn := Syn) m).app S_0_0)

/-- One object-level comparison of the supplied coefficient towers after
lambda inversion. All maps have the original stages and cofibers as their
sources. No detection or extension conclusion is a field. -/
public structure LambdaInversionAdamsObjectComparison (R : RealizationCoordinates D)
    (U : SyntheticObject) (X : ClassicalObject) where
  target : D.recovery.realization.obj (U.obj D.nu D.auxiliary) ≅ X.obj D.auxiliary
  weightedTarget : ∀ w : ℤ, D.recovery.realization.obj
    ((SyntheticCategory.biShift (0,-w)).obj (U.obj D.nu D.auxiliary)) ≅ X.obj D.auxiliary
  coordinates : ∀ (m w : ℤ) (a : BiHom m w (U.obj D.nu D.auxiliary)),
    (realizationSphereCoordinate D R m).hom ≫
      D.recovery.realization.map (weightHomotopyMap m w _ a) ≫ (weightedTarget w).hom =
    (R.sphere m w).hom ≫ D.recovery.realization.map a ≫ target.hom
  stage : ∀ (w s : ℤ), D.recovery.realization.obj
    ((D.syntheticTower.tower ((SyntheticCategory.biShift (0,-w)).obj
      (U.obj D.nu D.auxiliary))).stageAt s) ⟶
    (D.classicalTower.tower (X.obj D.auxiliary)).stageAt s
  transition : ∀ (w s t : ℤ) (h : s ≤ t),
    D.recovery.realization.map ((D.syntheticTower.tower
      ((SyntheticCategory.biShift (0,-w)).obj (U.obj D.nu D.auxiliary))).mapAt h) ≫ stage w s =
    stage w t ≫ (D.classicalTower.tower (X.obj D.auxiliary)).mapAt h
  projection : ∀ (w s : ℤ),
    D.recovery.realization.map ((D.syntheticTower.tower
      ((SyntheticCategory.biShift (0,-w)).obj (U.obj D.nu D.auxiliary))).projection s) ≫
        (weightedTarget w).hom =
    stage w s ≫ (D.classicalTower.tower (X.obj D.auxiliary)).projection s
  layer : ∀ (w s : ℤ), D.recovery.realization.obj
    ((D.syntheticTower.tower ((SyntheticCategory.biShift (0,-w)).obj
      (U.obj D.nu D.auxiliary))).layer s) ⟶
    (D.classicalTower.tower (X.obj D.auxiliary)).layer s
  cofiber : ∀ (w s : ℤ),
    D.recovery.realization.map (HasFunctorialCofiber.cofibι
      ((D.syntheticTower.tower ((SyntheticCategory.biShift (0,-w)).obj
        (U.obj D.nu D.auxiliary))).mapAt (show s ≤ s+1 by omega))) ≫ layer w s =
    stage w s ≫ HasFunctorialCofiber.cofibι
      ((D.classicalTower.tower (X.obj D.auxiliary)).mapAt (show s ≤ s+1 by omega))
  spectral : ∀ w : ℤ, SSDataMorphism Bidegree
    (fun p => ((D.family.obj (U.obj D.nu D.auxiliary)).sequence.ssData (p.1,p.2,w)))
    (D.classical.obj (X.obj D.auxiliary)).ssData
  ambient : ∀ (w : ℤ) (p : Bidegree)
      (a : ((D.family.obj (U.obj D.nu D.auxiliary)).sequence.ssData (p.1,p.2,w)).V),
    (((D.classicalTower.sequence (X.obj D.auxiliary)).ambient p).hom
      ((spectral w).φ p a)).val =
    (realizationSphereCoordinate D R (p.2-p.1)).hom ≫ D.recovery.realization.map
      ((((D.syntheticTower.sequence (U.obj D.nu D.auxiliary) w).ambient p).hom a).val) ≫
        layer w p.1

/-- An ambient element in every finite cycle module belongs to the specified limit subobject. -/
private theorem mem_top_cycles (D : SSData (ModuleCat.{v} ℤ)) (a : D.V)
    (ha : ∀ n : ℕ, a ∈ ModuleCat.subobjectModule _ (D.Z n)) :
    a ∈ ModuleCat.subobjectModule _ (D.Z ⊤) := by
  have hspan : (ModuleCat.subobjectModule _).symm (Submodule.span ℤ {a}) ≤ D.Z ⊤ := by
    apply D.Z_top_greatest
    intro n
    apply (ModuleCat.subobjectModule _).le_iff_le.mp
    simp only [OrderIso.apply_symm_apply, Submodule.span_le, Set.singleton_subset_iff]
    exact ha n
  have h := (ModuleCat.subobjectModule _).monotone hspan
  apply h
  rw [OrderIso.apply_symm_apply]
  exact Submodule.subset_span (by simp)

private theorem layerMap_mem_cycles {C : Type u} [StableHomotopyCategory.{u,v} C]
    [HasFunctorialCofiber (C := C)] {H : C} {unit : SphereSpectrum ⟶ H}
    {X : C} (T : AbstractAdamsTower unit X) (p : ℤ × ℤ)
    (a : HomotopyGroup (p.2-p.1) (T.stageAt p.1))
    (r : ℕ) (hr : 1 ≤ r) : T.layerMap p a ∈ T.cycles r hr p := by
  change T.connecting p (T.layerMap p a) ∈ LinearMap.range _
  have hz : T.connecting p (T.layerMap p a) = 0 := by
    change AbstractAdamsTower.desuspend _ _
      ((a ≫ HasFunctorialCofiber.cofibι _) ≫ HasFunctorialCofiber.cofibδ _) = 0
    have he : HasFunctorialCofiber.cofibι (T.mapAt (show p.1 ≤ p.1+1 by omega)) ≫
        HasFunctorialCofiber.cofibδ (T.mapAt (show p.1 ≤ p.1+1 by omega)) = 0 :=
      comp_distTriang_mor_zero₂₃ _ (HasFunctorialCofiber.cofib_distinguished _)
    rw [Category.assoc, he, comp_zero, map_zero]
  rw [hz]
  exact Submodule.zero_mem _

/-- Actual tower lifts supply common infinite representatives without a separation premise. -/
private theorem representative_of_lift {C : Type u} [StableHomotopyCategory.{u,v} C]
    [HasFunctorialCofiber (C := C)] {H : C} {unit : SphereSpectrum ⟶ H}
    {X : C} {T : AbstractAdamsTower unit X}
    {D : (ℤ × ℤ) → SSData (ModuleCat.{v} ℤ)}
    {d : ∀ (r : ℤ) (p : ℤ × ℤ), (D p).page (↑(r - 2).toNat : WithTop ℕ) ⟶
      (D (p + (r, r - 1))).page (↑(r - 2).toNat : WithTop ℕ)}
    (P : TowerSequencePresentation unit T D d) (p : ℤ × ℤ)
    (a : HomotopyGroup (p.2-p.1) (T.stageAt p.1)) :
    ∃ z : (Subobject.underlying.obj ((D p).Z ⊤) : ModuleCat ℤ),
      P.infiniteRepresentativeE1 p z = T.layerMap p a := by
  let a₂ : T.cycles 2 (by decide) p := ⟨T.layerMap p a, layerMap_mem_cycles T p a 2 (by decide)⟩
  let v : (D p).V := (P.ambient p).inv a₂
  have hv : ∀ n : ℕ, v ∈ ModuleCat.subobjectModule _ ((D p).Z n) := by
    intro n
    apply (P.cycles p n v).mpr
    have he : (P.ambient p).hom v = a₂ := by simp only [v, Iso.inv_hom_id_apply]
    rw [he]
    exact layerMap_mem_cycles T p a (n+2) (by omega)
  obtain ⟨z, hz⟩ := mem_top_cycles (D p) v hv
  refine ⟨z, ?_⟩
  change ((P.ambient p).hom (((D p).Z ⊤).arrow z)).val = T.layerMap p a
  rw [hz]
  simp only [v, Iso.inv_hom_id_apply, a₂]

private theorem infinity_representative_map
    (A B : Bidegree → SSData (ModuleCat.{v} ℤ))
    (f : SSDataMorphism Bidegree A B) (r₀ r₀' : ℤ) (hstart : r₀=r₀')
    (p : Bidegree)
    (z : (Subobject.underlying.obj ((A p).Z ⊤) : ModuleCat.{v} ℤ))
    (x : (A p).page (↑(2-r₀).toNat : WithTop ℕ))
    (hz : (Subobject.ofLE _ _ ((A p).Z_anti le_top) ≫
      (A p).pageπ (↑(2-r₀).toNat : WithTop ℕ)) z = x) :
    (Subobject.ofLE _ _ ((B p).Z_anti le_top) ≫
      (B p).pageπ (↑(2-r₀').toNat : WithTop ℕ)) (f.cycleMap p ⊤ z) =
    (f.pageMap p (↑(2-r₀).toNat : WithTop ℕ) ≫ eqToHom (by rw [hstart])) x := by
  subst r₀'
  let n : WithTop ℕ := ↑(2-r₀).toNat
  have hs := f.cycleMap_ofLE_assoc p (r := n) (s := ⊤) le_top ((B p).pageπ n)
  have hp := f.pageπ_pageMap p n
  have hq : (Subobject.ofLE ((A p).Z ⊤) ((A p).Z n) ((A p).Z_anti le_top) ≫
      (A p).pageπ n) ≫ f.pageMap p n =
      f.cycleMap p ⊤ ≫ Subobject.ofLE ((B p).Z ⊤) ((B p).Z n) ((B p).Z_anti le_top) ≫
        (B p).pageπ n := by
    rw [Category.assoc,hp]
    exact hs
  simpa only [ModuleCat.comp_apply,hz,eqToHom_refl,Category.comp_id,n] using
    (ConcreteCategory.congr_hom hq z).symm

namespace LambdaInversionAdamsObjectComparison
variable {D} {R : RealizationCoordinates D} {U : SyntheticObject} {X : ClassicalObject}

/-- The map on the actual page-two components induced by the same
cycle/boundary morphism, with the two starting-page transports explicit. -/
public def e2Map (K : LambdaInversionAdamsObjectComparison D R U X)
    (w : ℤ) (p : Bidegree) :
    (D.family.obj (U.obj D.nu D.auxiliary)).E₂ (p.1,p.2,w) ⟶
      (D.classical.obj (X.obj D.auxiliary)).Page 2 p :=
  (K.spectral w).pageMap p
    (↑(2-(D.family.obj (U.obj D.nu D.auxiliary)).sequence.r₀).toNat : WithTop ℕ) ≫
      eqToHom (by simp only [Page,(D.family.obj (U.obj D.nu D.auxiliary)).firstPage,
        D.classical.firstPage])


/-- Detection is transported by the actual stage and cofiber maps. This
uses the same synthetic representative; zero and boundary labels are allowed. -/
public theorem detects (K : LambdaInversionAdamsObjectComparison D R U X)
    (s t w : ℤ)
    (x : (D.family.obj (U.obj D.nu D.auxiliary)).E₂ (s,t,w))
    (β : BiHom (t-s) w (U.obj D.nu D.auxiliary))
    (hβ : Detects (D.convergence U) (s,t,w) x β) :
    ClassicalDetects (D.classicalConvergence X) (s,t) (K.e2Map w (s,t) x)
      ((R.sphere (t-s) w).hom ≫ D.recovery.realization.map β ≫ K.target.hom) := by
  letI := R.additive
  obtain ⟨e,⟨_,z,hz,he⟩,b,hb,hgr⟩ := hβ
  let T := D.syntheticTower.tower
    ((SyntheticCategory.biShift (0,-w)).obj (U.obj D.nu D.auxiliary))
  let Q := D.classicalTower.tower (X.obj D.auxiliary)
  have hm : β ∈ D.syntheticTower.filtrationSubmodule (U.obj D.nu D.auxiliary) s (t-s,w) := by
    have hbmem : β ∈ ModuleCat.subobjectModule _
        ((D.syntheticTower.filtration (U.obj D.nu D.auxiliary)).F s (t-s,w)) := ⟨b,hb⟩
    simpa only [SyntheticTowerPresentation.filtration,OrderIso.apply_symm_apply] using hbmem
  obtain ⟨a,ha⟩ := ((D.convergence U).canonical.1 s (t-s) w β).mp hm
  change a ≫ T.projection s = weightHomotopyMap (t-s) w _ β at ha
  obtain ⟨z',hz'⟩ := representative_of_lift
    (D.syntheticTower.sequence (U.obj D.nu D.auxiliary) w) (s,t) a
  have he' : ((D.family.obj (U.obj D.nu D.auxiliary)).sequence.ssData (s,t,w)).pageπ ⊤ z' = e := by
    apply ((D.convergence U).identification (s,t,w)).toLinearEquiv.injective
    have hcan := (D.convergence U).canonical.2 (s,t,w) a z' hz' b
      (by rw [hb]; exact ha.symm)
    exact hcan.trans hgr.symm
  let f := K.spectral w
  let zc := f.cycleMap (s,t) ⊤ z
  let zc' := f.cycleMap (s,t) ⊤ z'
  let ac : HomotopyGroup (t-s) (Q.stageAt s) :=
    (realizationSphereCoordinate D R (t-s)).hom ≫ D.recovery.realization.map a ≫ K.stage w s
  have hzc' : (((D.classical.obj (X.obj D.auxiliary)).ssData (s,t)).Z ⊤).arrow zc' =
      f.φ (s,t) ((((D.family.obj (U.obj D.nu D.auxiliary)).sequence.ssData (s,t,w)).Z ⊤).arrow z') :=
    ConcreteCategory.congr_hom (f.preserves_Z (s,t) ⊤).choose_spec z'
  have hE1 : (D.classicalTower.sequence (X.obj D.auxiliary)).infiniteRepresentativeE1 (s,t) zc' =
      Q.layerMap (s,t) ac := by
    change (((D.classicalTower.sequence (X.obj D.auxiliary)).ambient (s,t)).hom
      ((((D.classical.obj (X.obj D.auxiliary)).ssData (s,t)).Z ⊤).arrow zc')).val = _
    rw [hzc', K.ambient]
    change (realizationSphereCoordinate D R (t-s)).hom ≫
      D.recovery.realization.map
        ((D.syntheticTower.sequence (U.obj D.nu D.auxiliary) w).infiniteRepresentativeE1 (s,t) z') ≫
          K.layer w s = _
    rw [hz']
    change _ = ac ≫ HasFunctorialCofiber.cofibι _
    change (realizationSphereCoordinate D R (t-s)).hom ≫
      D.recovery.realization.map (a ≫ HasFunctorialCofiber.cofibι _) ≫ K.layer w s = _
    rw [Functor.map_comp]
    simp only [Category.assoc,ac]
    rw [K.cofiber]
  have hproj : ac ≫ Q.projection s =
      (R.sphere (t-s) w).hom ≫ D.recovery.realization.map β ≫ K.target.hom := by
    dsimp only [ac]
    simp only [Category.assoc]
    rw [← K.projection w s]
    calc
      _ = (realizationSphereCoordinate D R (t-s)).hom ≫
          D.recovery.realization.map (a ≫ T.projection s) ≫ (K.weightedTarget w).hom := by
        simp only [Functor.map_comp,Category.assoc]
        rfl
      _ = _ := by rw [ha]; exact K.coordinates (t-s) w β
  have hmem : ((R.sphere (t-s) w).hom ≫ D.recovery.realization.map β ≫ K.target.hom) ∈
      ModuleCat.subobjectModule _ (Q.filtration.F s (t-s)) := by
    have hh : ((R.sphere (t-s) w).hom ≫ D.recovery.realization.map β ≫ K.target.hom) ∈
        Q.filtrationSubmodule s (t-s) := ⟨ac,hproj⟩
    simpa only [AbstractAdamsTower.filtration,OrderIso.apply_symm_apply] using hh
  obtain ⟨bc,hbc⟩ := hmem
  have hlabel := infinity_representative_map
    (fun p => ((D.family.obj (U.obj D.nu D.auxiliary)).sequence.ssData (p.1,p.2,w)))
    (D.classical.obj (X.obj D.auxiliary)).ssData f
    (D.family.obj (U.obj D.nu D.auxiliary)).sequence.r₀
    (D.classical.obj (X.obj D.auxiliary)).r₀
    ((D.family.obj (U.obj D.nu D.auxiliary)).firstPage.trans (D.classical.firstPage _).symm)
    (s,t) z x hz
  change (Subobject.ofLE _ _ _ ≫ ((D.classical.obj (X.obj D.auxiliary)).ssData (s,t)).pageπ _) zc =
    K.e2Map w (s,t) x at hlabel
  refine ⟨zc,hlabel,bc,hbc,?_⟩
  have hπ (q : (Subobject.underlying.obj
      (((D.family.obj (U.obj D.nu D.auxiliary)).sequence.ssData (s,t,w)).Z ⊤) : ModuleCat.{v} ℤ)) :
      ((D.classical.obj (X.obj D.auxiliary)).ssData (s,t)).pageπ ⊤ (f.cycleMap (s,t) ⊤ q) =
      f.pageMap (s,t) ⊤ (((D.family.obj (U.obj D.nu D.auxiliary)).sequence.ssData (s,t,w)).pageπ ⊤ q) :=
    (ConcreteCategory.congr_hom (f.pageπ_pageMap (s,t) ⊤) q).symm
  have hinfty : ((D.classical.obj (X.obj D.auxiliary)).ssData (s,t)).pageπ ⊤ zc =
      ((D.classical.obj (X.obj D.auxiliary)).ssData (s,t)).pageπ ⊤ zc' := by
    rw [hπ z,hπ z',he,he']
  rw [hinfty]
  exact (D.classicalConvergence X).canonical (s,t) ac zc' hE1 bc (hbc.trans hproj.symm)

end LambdaInversionAdamsObjectComparison

/-- Lambda inversion on the selected nu objects and their actual positive
weight shifts, including the prescribed page-two nu coordinates. -/
public structure LambdaInversionAdamsComparison (R : RealizationCoordinates D) where
  nu : ∀ X : ClassicalObject, LambdaInversionAdamsObjectComparison D R (.nu X) X
  shiftedNu : ∀ (X : ClassicalObject) (a : ℕ),
    LambdaInversionAdamsObjectComparison D R (.shift (0,(a:ℤ)) (.nu X)) X
  nu_target : ∀ X : ClassicalObject,
    (nu X).target.hom = D.recovery.nuRealizationIso.hom.app (X.obj D.auxiliary)
  shiftedNu_target : ∀ (X : ClassicalObject) (a : ℕ),
    D.recovery.realization.map (lambdaToPositivePow a (D.nu.functor.obj (X.obj D.auxiliary))) ≫
      (shiftedNu X a).target.hom = (nu X).target.hom
  nu_e2 : ∀ (X : ClassicalObject) (s t : ℤ) (k : ℕ)
      (x : (D.classical.obj (X.obj D.auxiliary)).Page 2 (s,t)),
    (nu X).e2Map (t-k) (s,t) (targetNuLabel D X s t k x) = x
  shiftedNu_e2 : ∀ (X : ClassicalObject) (a : ℕ) (s t : ℤ) (k : ℕ)
      (x : (D.classical.obj (X.obj D.auxiliary)).Page 2 (s,t)),
    (shiftedNu X a).e2Map (t+(a:ℤ)-k) (s,t) (D.comparison.nuE2 X a s t k x) = x

end
end KIP126.Literature

#print axioms KIP126.Literature.LambdaInversionAdamsObjectComparison.detects
#print axioms KIP126.Literature.LambdaInversionAdamsObjectComparison.e2Map
