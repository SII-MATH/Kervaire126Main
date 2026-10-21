module

public import KIP126.Literature.Standard
public import KIP126.Literature.Standard.QuotientAlgebra

/-! Structural filtration binding retained from bbac1fc05843,
Def/Kervaire/Route/SourceLanguage.lean:1135 and
Def/Kervaire/Route/Multiplication/Comparison.lean:82–89 (MIT).
This is the original selected-object action law, with no finite upper bound. -/
namespace KIP126.Literature.Standard
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy KIP126.AdamsSynthetic KIP126.Classical.Adams
open KIP126.Core.SpectralSequence
open KIP126.AdamsSynthetic.Standard (model Spectrum)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
universe u v

private theorem product_mem_top_cycles (D : SSData (ModuleCat.{v} ℤ)) (a : D.V)
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

private theorem product_layerMap_mem_cycles {C : Type u} [StableHomotopyCategory.{u,v} C]
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
      Pretriangulated.comp_distTriang_mor_zero₂₃ _ (HasFunctorialCofiber.cofib_distinguished _)
    rw [Category.assoc, he, comp_zero, map_zero]
  rw [hz]
  exact Submodule.zero_mem _

private theorem product_representative_of_lift {C : Type u} [StableHomotopyCategory.{u,v} C]
    [HasFunctorialCofiber (C := C)] {H : C} {unit : SphereSpectrum ⟶ H}
    {X : C} {T : AbstractAdamsTower unit X}
    {D : (ℤ × ℤ) → SSData (ModuleCat.{v} ℤ)}
    {d : ∀ (r : ℤ) (p : ℤ × ℤ), (D p).page (↑(r - 2).toNat : WithTop ℕ) ⟶
      (D (p + (r, r - 1))).page (↑(r - 2).toNat : WithTop ℕ)}
    (P : TowerSequencePresentation unit T D d) (p : ℤ × ℤ)
    (a : HomotopyGroup (p.2-p.1) (T.stageAt p.1)) :
    ∃ z : (Subobject.underlying.obj ((D p).Z ⊤) : ModuleCat ℤ),
      P.infiniteRepresentativeE1 p z = T.layerMap p a := by
  let a₂ : T.cycles 2 (by decide) p := ⟨T.layerMap p a, product_layerMap_mem_cycles T p a 2 (by decide)⟩
  let x : (D p).V := (P.ambient p).inv a₂
  have hx : ∀ n : ℕ, x ∈ ModuleCat.subobjectModule _ ((D p).Z n) := by
    intro n
    apply (P.cycles p n x).mpr
    have he : (P.ambient p).hom x = a₂ := by simp only [x, Iso.inv_hom_id_apply]
    rw [he]
    exact product_layerMap_mem_cycles T p a (n+2) (by omega)
  obtain ⟨z, hz⟩ := product_mem_top_cycles (D p) x hx
  refine ⟨z, ?_⟩
  change ((P.ambient p).hom (((D p).Z ⊤).arrow z)).val = T.layerMap p a
  rw [hz]
  simp only [x, Iso.inv_hom_id_apply, a₂]

private theorem product_layerMap_natural {C : Type u} [StableHomotopyCategory.{u,v} C]
    [HasFunctorialCofiber (C := C)] {H : C} {unit : SphereSpectrum ⟶ H}
    {X Y : C} {T : AbstractAdamsTower unit X} {U : AbstractAdamsTower unit Y}
    {f : X ⟶ Y} (φ : TowerMap unit T U f) (p : ℤ × ℤ)
    (a : HomotopyGroup (p.2-p.1) (T.stageAt p.1)) :
    T.layerMap p a ≫ φ.layer p.1 = U.layerMap p (a ≫ φ.stage p.1.toNat) := by
  change (a ≫ HasFunctorialCofiber.cofibι _) ≫ φ.layer p.1 =
    (a ≫ φ.stage p.1.toNat) ≫ HasFunctorialCofiber.cofibι _
  rw [Category.assoc]
  change a ≫ HasFunctorialCofiber.cofibι _ ≫
    HasFunctorialCofiber.cofibMap _ _ _ _ _ = _
  rw [← HasFunctorialCofiber.cofibMap_ι, ← Category.assoc]

private theorem product_infinite_to_page_map
    {E E' : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)}
    (f : E ⟶ E') (p : ℤ × ℤ)
    (z : (Subobject.underlying.obj ((E.ssData p).Z ⊤) : ModuleCat ℤ)) :
    (Subobject.ofLE _ _ ((E'.ssData p).Z_anti le_top) ≫
      (E'.ssData p).pageπ (↑(2-E'.r₀).toNat : WithTop ℕ))
        (f.toSSDataMorphism.cycleMap p ⊤ z) =
    f.pageMap 2 p ((Subobject.ofLE _ _ ((E.ssData p).Z_anti le_top) ≫
      (E.ssData p).pageπ (↑(2-E.r₀).toNat : WithTop ℕ)) z) := by
  have hstart := f.r₀_eq
  rcases E with ⟨⟨r₀,D,δ,d⟩,dd,Zs,Bs⟩
  rcases E' with ⟨⟨r₀',D',δ',d'⟩,dd',Zs',Bs'⟩
  dsimp at hstart
  subst r₀'
  let n : WithTop ℕ := ↑(2-r₀).toNat
  have hs := f.toSSDataMorphism.cycleMap_ofLE_assoc p
      (r := n) (s := ⊤) le_top ((D' p).pageπ n)
  have hp := f.toSSDataMorphism.pageπ_pageMap p n
  have hq : (Subobject.ofLE ((D p).Z ⊤) ((D p).Z n) ((D p).Z_anti le_top) ≫
        (D p).pageπ n) ≫ f.toSSDataMorphism.pageMap p n =
        f.toSSDataMorphism.cycleMap p ⊤ ≫
          Subobject.ofLE ((D' p).Z ⊤) ((D' p).Z n) ((D' p).Z_anti le_top) ≫ (D' p).pageπ n := by
    rw [Category.assoc,hp]
    exact hs
  dsimp only [SpectralSequenceMorphism.pageMap, SpectralSequenceMorphism.toPreSSMorphism,
    PreSSMorphism.pageMap, SSDataMorphism.pageMapAt]
  simpa only [ModuleCat.comp_apply, eqToHom_refl, Category.comp_id, n]
    using (ConcreteCategory.congr_hom hq z).symm

private theorem product_classical_detects_map
    {C : Type u} [StableHomotopyCategory.{u,v} C] [HasFunctorialCofiber (C := C)]
    {H : C} {unit : SphereSpectrum ⟶ H} {A : ClassicalAdamsFamily C}
    (P : ClassicalTowerPresentation unit A) {X Y : C} (f : X ⟶ Y)
    (cx : ClassicalTowerConvergence P X) (cy : ClassicalTowerConvergence P Y)
    (p : ℤ × ℤ) (x : (A.obj X).Page 2 p) (a : HomotopyGroup (p.2-p.1) X)
    (hx : ClassicalDetects cx p x a) :
    ClassicalDetects cy p ((A.map f).pageMap 2 p x) (a ≫ f) := by
  obtain ⟨z, hz, b, hb, hg⟩ := hx
  let FX := (P.tower X).filtration
  let FY := (P.tower Y).filtration
  have hbmem : (FX.F p.1 (p.2-p.1)).arrow b ∈
      (P.tower X).filtrationSubmodule p.1 (p.2-p.1) := by
    have he : (FX.F p.1 (p.2-p.1)).arrow b ∈
        ModuleCat.subobjectModule _ (FX.F p.1 (p.2-p.1)) := ⟨b, rfl⟩
    simpa only [FX, AbstractAdamsTower.filtration, OrderIso.apply_symm_apply] using he
  obtain ⟨l, hl⟩ := hbmem
  change l ≫ (P.tower X).projection p.1 = (FX.F p.1 (p.2-p.1)).arrow b at hl
  obtain ⟨z₀, hz₀⟩ := product_representative_of_lift (P.sequence X) p l
  have hcx := cx.canonical p l z₀ hz₀ b hl.symm
  have he : ((A.obj X).ssData p).pageπ ⊤ z = ((A.obj X).ssData p).pageπ ⊤ z₀ := by
    apply (ModuleCat.mono_iff_injective (cx.identification p).hom).mp inferInstance
    exact hg.trans hcx.symm
  let zf := (A.map f).toSSDataMorphism.cycleMap p ⊤ z
  let zf₀ := (A.map f).toSSDataMorphism.cycleMap p ⊤ z₀
  have hzf (zz : (Subobject.underlying.obj (((A.obj X).ssData p).Z ⊤) : ModuleCat ℤ)) :
      (((A.obj Y).ssData p).Z ⊤).arrow ((A.map f).toSSDataMorphism.cycleMap p ⊤ zz) =
        (A.map f).φ p ((((A.obj X).ssData p).Z ⊤).arrow zz) :=
    ConcreteCategory.congr_hom ((A.map f).preserves_Z p ⊤).choose_spec zz
  let l' := l ≫ (P.map f).stage p.1.toNat
  have hzf₀ : (P.sequence Y).infiniteRepresentativeE1 p zf₀ = (P.tower Y).layerMap p l' := by
    change (((P.sequence Y).ambient p).hom
      ((((A.obj Y).ssData p).Z ⊤).arrow zf₀)).val = _
    rw [hzf, P.natural]
    change (P.sequence X).infiniteRepresentativeE1 p z₀ ≫ (P.map f).layer p.1 = _
    rw [hz₀, product_layerMap_natural]
  have hb'mem : a ≫ f ∈ ModuleCat.subobjectModule _ (FY.F p.1 (p.2-p.1)) := by
    change a ≫ f ∈ (ModuleCat.subobjectModule (AbstractAdamsTower.homotopy Y (p.2-p.1)))
      ((ModuleCat.subobjectModule (AbstractAdamsTower.homotopy Y (p.2-p.1))).symm ((P.tower Y).filtrationSubmodule p.1 (p.2-p.1)))
    rw [OrderIso.apply_symm_apply]
    refine ⟨l', ?_⟩
    change (l ≫ (P.map f).stage p.1.toNat) ≫ (P.tower Y).projection p.1 = a ≫ f
    rw [Category.assoc, (P.map f).projection, ← Category.assoc, hl, hb]
  obtain ⟨b', hb'⟩ := hb'mem
  have hbl : (FY.F p.1 (p.2-p.1)).arrow b' = l' ≫ (P.tower Y).projection p.1 := by
    rw [hb']
    dsimp only [l']
    rw [Category.assoc, (P.map f).projection, ← Category.assoc, hl, hb]
  have hcy := cy.canonical p l' zf₀ hzf₀ b' hbl
  have he' : ((A.obj Y).ssData p).pageπ ⊤ zf = ((A.obj Y).ssData p).pageπ ⊤ zf₀ := by
    have hm := congrArg ((A.map f).eInftyMap p) he
    have h₁ := ConcreteCategory.congr_hom ((A.map f).toSSDataMorphism.pageπ_pageMap p ⊤) z
    have h₂ := ConcreteCategory.congr_hom ((A.map f).toSSDataMorphism.pageπ_pageMap p ⊤) z₀
    exact h₁.symm.trans (hm.trans h₂)
  refine ⟨zf, ?_, b', hb', ?_⟩
  · simpa only [hz, zf] using product_infinite_to_page_map (A.map f) p z
  · rw [he']
    exact hcy

end
end KIP126.Literature.Standard

namespace KIP126.Literature.Standard
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy KIP126.AdamsSynthetic
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {C : Type u} [StableHomotopyCategory.{u,v} C]

private def product_shift_conjugate (F : C ⥤ C) [F.CommShift ℤ]
    (j : F.obj (SphereSpectrum : C) ≅ SphereSpectrum) (n : ℤ)
    (a : HomotopyGroup (C := C) n SphereSpectrum) : HomotopyGroup (C := C) n SphereSpectrum :=
  (shiftFunctor C n).map j.inv ≫ (F.commShiftIso n).inv.app SphereSpectrum ≫ F.map a ≫ j.hom

private theorem product_shift_conjugate_mul (F : C ⥤ C) [F.CommShift ℤ]
    (j : F.obj (SphereSpectrum : C) ≅ SphereSpectrum) (m n : ℤ)
    (a : HomotopyGroup (C := C) m SphereSpectrum)
    (b : HomotopyGroup (C := C) n SphereSpectrum) :
    product_shift_conjugate F j (m+n)
      ((shiftFunctorAdd C m n).hom.app SphereSpectrum ≫ (shiftFunctor C n).map a ≫ b) =
    (shiftFunctorAdd C m n).hom.app SphereSpectrum ≫
      (shiftFunctor C n).map (product_shift_conjugate F j m a) ≫
        product_shift_conjugate F j n b := by
  simp only [product_shift_conjugate, Functor.map_comp, Category.assoc]
  rw [F.commShiftIso_add, Functor.CommShift.isoAdd_inv_app]
  simp only [Category.assoc]
  have h0 : F.map ((shiftFunctorAdd C m n).inv.app SphereSpectrum) ≫
      F.map ((shiftFunctorAdd C m n).hom.app SphereSpectrum) = 𝟙 _ := by
    rw [← F.map_comp, Iso.inv_hom_id_app, F.map_id]
  rw [← Category.assoc (F.map ((shiftFunctorAdd C m n).inv.app SphereSpectrum))
    (F.map ((shiftFunctorAdd C m n).hom.app SphereSpectrum)), h0, Category.id_comp]
  have hn := (F.commShiftIso n).inv.naturality_assoc a (F.map b ≫ j.hom)
  dsimp only [Functor.comp_map] at hn
  erw [← hn]
  erw [(shiftFunctorAdd C m n).hom.naturality_assoc j.inv]
  simp only [Functor.comp_map, ← Functor.map_comp_assoc,
    Iso.hom_inv_id, Category.comp_id]

private theorem product_unit_adjunction (B : ClosedSymmetricTensorTriangulated C)
    (n : ℤ) (f : HomotopyGroup n (mappingSpectrum B SphereSpectrum SphereSpectrum)) :
    letI := B.closed
    ((ihom.adjunction (SphereSpectrum : C)).homEquiv (Sphere n) SphereSpectrum).symm f =
      (λ_ (Sphere n : C)).hom ≫ f ≫ (sphereMappingIso B).hom := by
  letI := B.closed
  change (𝟙_ C ◁ f) ≫ (ihom.adjunction (𝟙_ C)).counit.app (𝟙_ C) = _
  have he : (sphereMappingIso B).hom =
      (λ_ ((ihom (𝟙_ C)).obj (𝟙_ C))).inv ≫
        (ihom.adjunction (𝟙_ C)).counit.app (𝟙_ C) := by
    change (conjugateEquiv (ihom.adjunction (𝟙_ C)) Adjunction.id
      (leftUnitorNatIso C).inv).app (𝟙_ C) = _
    exact conjugateEquiv_adjunction_id _ _ _
  rw [he]
  rw [← Category.assoc]
  erw [← leftUnitor_naturality f]
  dsimp only [mappingSpectrum, SphereSpectrum] at f ⊢
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

private theorem product_mapping_equiv_formula (B : ClosedSymmetricTensorTriangulated C)
    (n : ℤ) (f : HomotopyGroup n (mappingSpectrum B SphereSpectrum SphereSpectrum)) :
    letI := B.tensorShift (SphereSpectrum : C)
    mappingHomotopyEquiv B n SphereSpectrum SphereSpectrum f =
      product_shift_conjugate (tensorRight (SphereSpectrum : C)) (ρ_ (SphereSpectrum : C)) n
        (f ≫ (sphereMappingIso B).hom) := by
  letI := B.closed
  letI := B.symmetric
  letI := B.tensorShift (SphereSpectrum : C)
  dsimp only [mappingHomotopyEquiv, Equiv.trans_apply, Iso.homCongr, Equiv.coe_fn_mk]
  erw [product_unit_adjunction B n f]
  simp only [Iso.refl_hom, Category.comp_id, Iso.trans_inv, Category.assoc]
  have hβ : (β_ (𝟙_ C) (Sphere n)).inv ≫ (λ_ (Sphere n : C)).hom =
      (ρ_ (Sphere n : C)).hom := by
    rw [← SymmetricCategory.braiding_swap_eq_inv_braiding (𝟙_ C) (Sphere n)]
    exact braiding_leftUnitor _
  rw [← Category.assoc (β_ (𝟙_ C) (Sphere n)).inv, hβ]
  dsimp only [product_shift_conjugate, ClosedSymmetricTensorTriangulated.sphereTensorShift]
  simp only [Iso.trans_inv, Functor.mapIso_inv, Category.assoc]
  have hu : (λ_ (SphereSpectrum : C)).inv = (ρ_ (SphereSpectrum : C)).inv := by
    exact congrArg Iso.inv (Iso.ext (unitors_equal (C := C)))
  rw [hu]
  erw [← rightUnitor_naturality (f ≫ (sphereMappingIso B).hom)]
  rfl

private theorem product_mapping_composition (B : ClosedSymmetricTensorTriangulated C)
    (m n : ℤ)
    (a : HomotopyGroup m (mappingSpectrum B SphereSpectrum SphereSpectrum))
    (b : HomotopyGroup n (mappingSpectrum B SphereSpectrum SphereSpectrum)) :
    (mappingHomotopyEquiv B (m+n) SphereSpectrum SphereSpectrum).symm
      ((shiftFunctorAdd C m n).hom.app SphereSpectrum ≫
        (shiftFunctor C n).map (mappingHomotopyEquiv B m SphereSpectrum SphereSpectrum a) ≫
        mappingHomotopyEquiv B n SphereSpectrum SphereSpectrum b) ≫ (sphereMappingIso B).hom =
      (shiftFunctorAdd C m n).hom.app SphereSpectrum ≫
        (shiftFunctor C n).map (a ≫ (sphereMappingIso B).hom) ≫
          (b ≫ (sphereMappingIso B).hom) := by
  letI := B.tensorShift (SphereSpectrum : C)
  apply (cancel_mono (sphereMappingIso B).inv).mp
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply (mappingHomotopyEquiv B (m+n) SphereSpectrum SphereSpectrum).injective
  rw [Equiv.apply_symm_apply, product_mapping_equiv_formula B (m+n)]
  simp only [Category.assoc]
  rw [product_shift_conjugate_mul, ← product_mapping_equiv_formula B m a,
    ← product_mapping_equiv_formula B n b]
end
end KIP126.Literature.Standard

namespace KIP126.Literature.Standard
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy KIP126.AdamsSynthetic KIP126.Classical.Adams
open KIP126.Core.SpectralSequence
open KIP126.AdamsSynthetic.Standard (model Spectrum)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

private theorem product_mapping_composition_regrade (m n r : ℤ) (h : r=m+n)
    (a : HomotopyGroup m (mappingSpectrum closedTensor SphereSpectrum SphereSpectrum))
    (b : HomotopyGroup n (mappingSpectrum closedTensor SphereSpectrum SphereSpectrum)) :
    (mappingHomotopyEquiv closedTensor r SphereSpectrum SphereSpectrum).symm
      (eqToHom (congrArg (Sphere (C := Spectrum)) h) ≫
        (shiftFunctorAdd Spectrum m n).hom.app SphereSpectrum ≫
        (shiftFunctor Spectrum n).map (mappingHomotopyEquiv closedTensor m SphereSpectrum SphereSpectrum a) ≫
        mappingHomotopyEquiv closedTensor n SphereSpectrum SphereSpectrum b) ≫ (sphereMappingIso closedTensor).hom =
      eqToHom (congrArg (Sphere (C := Spectrum)) h) ≫
        classicalSphereProduct (a ≫ (sphereMappingIso closedTensor).hom)
          (b ≫ (sphereMappingIso closedTensor).hom) := by
  subst r
  dsimp only [classicalSphereProduct, KIP126.Literature.classicalSphereProduct]
  simpa only [eqToHom_refl, Category.id_comp] using
    product_mapping_composition closedTensor m n a b

private theorem product_mapping_detects_iff
    (X Y : MappingObject (fun X : Spectrum => X = SphereSpectrum))
    (p : ℤ × ℤ) (x : (Moss.sequence mapping X Y).Page 2 p)
    (a : Moss.abutment (B := closedTensor) X Y (p.2-p.1)) :
    Moss.DetectsAbutment mapping X Y 2 p x a ↔
      ClassicalDetects (mapping.convergence X.val Y.val X.property Y.property) p x a := by
  constructor
  · rintro ⟨e, ⟨z, hz, he⟩, b, hb, hg⟩
    subst e
    exact ⟨z, hz, b, hb, hg⟩
  · rintro ⟨z, hz, b, hb, hg⟩
    exact ⟨_, ⟨z, hz, rfl⟩, b, hb, hg⟩

private theorem product_classical_detects_regrade
    {X : Spectrum} (c : ClassicalTowerConvergence model.classicalTower X)
    {p q : ℤ × ℤ} (h : p=q) (x : (model.classical.obj X).Page 2 p)
    (a : HomotopyGroup (p.2-p.1) X) (ha : ClassicalDetects c p x a) :
    ClassicalDetects c q
      (eqToHom (congrArg ((model.classical.obj X).Page 2) h) x)
      (eqToHom (congrArg (fun k : ℤ × ℤ => Sphere (C := Spectrum) (k.2-k.1)) h.symm) ≫ a) := by
  subst q
  simpa only [eqToHom_refl, ModuleCat.id_apply, Category.id_comp] using ha

end
end KIP126.Literature.Standard

namespace KIP126.Literature.Standard
open CategoryTheory KIP126.StableHomotopy
open KIP126.Synthetic.Context KIP126.AdamsSynthetic KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard

public theorem action_filtration (X : SyntheticObject) (m w m' w' s s' : ℤ)
    (a : BiHom m w (S_0_0 : SyntheticSpectrum))
    (b : BiHom m' w' (X.obj model.nu model.auxiliary))
    (ha : FiltrationAtLeast model.syntheticTower s a)
    (hb : FiltrationAtLeast model.syntheticTower s' b) :
    FiltrationAtLeast model.syntheticTower (s+s') (sphereAction a b) := by
  sorry

/-- Original AlgebraBinding.finite_action: multiplication on the actual finite
quotient, with the original positive length and all weight indices. -/
public theorem finite_action (q : ℕ) (hq : 0 < q) (s t s' t' k l : ℕ)
    (x : model.classical.sphere.Page 2 (s,t))
    (y : model.classical.sphere.Page 2 (s',t'))
    (a : BiHom ((t : ℤ)-s) ((t : ℤ)-k) (S_0_0 : SyntheticSpectrum))
    (b : BiHom ((t' : ℤ)-s') ((t' : ℤ)-l) (XModLambdaN (S_0_0 : SyntheticSpectrum) q))
    (ha : Detects (model.convergence .sphere) (s,t,(t : ℤ)-k) (model.comparison.sphereE2 s t k x) a)
    (hb : Detects (model.convergence (.quotient q .sphere)) (s',t',(t' : ℤ)-l)
      ((model.family.quotientProjection (S_0_0 : SyntheticSpectrum) q).pageMap 2
        (s',t',(t' : ℤ)-l) (model.comparison.sphereE2 s' t' l y)) b) :
    Detects (model.convergence (.quotient q .sphere))
      ((s+s' : ℕ),(t+t' : ℕ),(t+t' : ℕ)-(k+l : ℕ))
      ((model.family.quotientProjection (S_0_0 : SyntheticSpectrum) q).pageMap 2
        ((s+s' : ℕ),(t+t' : ℕ),(t+t' : ℕ)-(k+l : ℕ))
        (model.comparison.sphereE2 (s+s') (t+t') (k+l)
          (by simpa only [Nat.cast_add, Prod.mk_add_mk] using
            model.sphereAlgebra.product (s,t) (s',t') x y)))
      (homotopyRegrade (by simp only [Nat.cast_add]; omega)
        (by simp only [Nat.cast_add]; omega) (sphereAction a b)) := by
  sorry

/-- The original general first-quotient multiplication comparison composed
with QuotientAlgebraBinding.sphere_action (SourceLanguage:969–971,1129–1130).
No paper-specific unit or detection conclusion is asserted. -/
public theorem first_quotient_action (s t s' t' : ℕ)
    (x : BiHom ((t : ℤ)-s) t (S_0_0 : SyntheticSpectrum))
    (y : BiHom ((t' : ℤ)-s') t' (XModLambdaN (S_0_0 : SyntheticSpectrum) 1)) :
    KIP126.Literature.sphereFirstQuotient model ((s+s' : ℕ) : ℤ) ((t+t' : ℕ) : ℤ)
      (homotopyRegrade (by simp only [Nat.cast_add]; omega)
        (by simp only [Nat.cast_add]) (sphereAction x y)) =
      (eqToHom (congrArg (model.classical.sphere.Page 2)
        (show ((s : ℤ),(t : ℤ)) + ((s' : ℤ),(t' : ℤ)) = (((s+s' : ℕ) : ℤ),((t+t' : ℕ) : ℤ)) by
          simp only [Prod.mk_add_mk,Nat.cast_add])))
        (model.sphereAlgebra.product (s,t) (s',t')
          (KIP126.Literature.sphereFirstQuotient model s t (quotientClass 1 x))
          (KIP126.Literature.sphereFirstQuotient model s' t' y)) := by
  rw [← quotientAlgebra_sphere_action 1 (by decide) ((t : ℤ)-s) t ((t' : ℤ)-s') t' x y]
  exact quotientAlgebra_first_quotient s t s' t' (quotientClass 1 x) y

open KIP126.Classical.Adams KIP126.Core.SpectralSequence in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
/-- Original AlgebraBinding.classical_detection (SourceLanguage:1061–1070,
1128), on the actual homotopy product and the same classical sphere E₂. -/
public theorem classical_product_detection (s t s' t' : ℕ)
    (x : model.classical.sphere.Page 2 (s,t))
    (y : model.classical.sphere.Page 2 (s',t'))
    (a : HomotopyGroup (C := Spectrum) ((t : ℤ)-s) SphereSpectrum)
    (b : HomotopyGroup (C := Spectrum) ((t' : ℤ)-s') SphereSpectrum)
    (ha : ClassicalDetects (model.classicalConvergence .sphere) (s,t) x a)
    (hb : ClassicalDetects (model.classicalConvergence .sphere) (s',t') y b) :
    ClassicalDetects (model.classicalConvergence .sphere) ((s+s' : ℕ),(t+t' : ℕ))
      ((eqToHom (congrArg (model.classical.sphere.Page 2)
        (show ((s : ℤ),(t : ℤ)) + ((s' : ℤ),(t' : ℤ)) = (((s+s' : ℕ) : ℤ),((t+t' : ℕ) : ℤ)) by
          simp only [Prod.mk_add_mk,Nat.cast_add])))
        (model.sphereAlgebra.product (s,t) (s',t') x y))
      (eqToHom (congrArg (fun n : ℤ => Sphere (C := Spectrum) n)
        (by simp only [Nat.cast_add]; omega : ((t+t' : ℕ) : ℤ)-(s+s') =
          ((t : ℤ)-s)+((t' : ℤ)-s'))) ≫ classicalSphereProduct a b) := by
  let S : MappingObject (fun X : Spectrum => X=SphereSpectrum) := ⟨SphereSpectrum,rfl⟩
  let e := sphereMappingIso closedTensor
  let E := sphereMappingAdamsIso closedTensor model.classical
  let xm := E.inv.pageMap 2 (s,t) x
  let ym := E.inv.pageMap 2 (s',t') y
  let am := a ≫ e.inv
  let bm := b ≫ e.inv
  have ham : ClassicalDetects (mapping.convergence S.val S.val S.property S.property) (s,t) xm am :=
    product_classical_detects_map model.classicalTower e.inv
      (model.classicalConvergence .sphere) (mapping.convergence S.val S.val S.property S.property)
      (s,t) x a ha
  have hbm : ClassicalDetects (mapping.convergence S.val S.val S.property S.property) (s',t') ym bm :=
    product_classical_detects_map model.classicalTower e.inv
      (model.classicalConvergence .sphere) (mapping.convergence S.val S.val S.property S.property)
      (s',t') y b hb
  have hm := moss_detection S S S 2 (by decide) (s,t) (s',t') xm ym am bm
    ((product_mapping_detects_iff S S (s,t) xm am).mpr ham)
    ((product_mapping_detects_iff S S (s',t') ym bm).mpr hbm)
  have hd := (product_mapping_detects_iff S S _ _ _).mp hm
  have hout := product_classical_detects_map model.classicalTower e.hom
    (mapping.convergence S.val S.val S.property S.property) (model.classicalConvergence .sphere)
    (((s:ℤ),(t:ℤ))+((s':ℤ),(t':ℤ))) _ _ hd
  have hx : E.hom.pageMap 2 (s,t) xm=x := by
    have h := ConcreteCategory.congr_hom
      (congrArg (fun f => f.pageMap 2 ((s:ℤ),(t:ℤ))) E.inv_hom_id) x
    simpa only [SpectralSequenceMorphism.pageMap_comp, SpectralSequenceMorphism.pageMap_id,
      ModuleCat.comp_apply, ModuleCat.id_apply, xm] using h
  have hy : E.hom.pageMap 2 (s',t') ym=y := by
    have h := ConcreteCategory.congr_hom
      (congrArg (fun f => f.pageMap 2 ((s':ℤ),(t':ℤ))) E.inv_hom_id) y
    simpa only [SpectralSequenceMorphism.pageMap_comp, SpectralSequenceMorphism.pageMap_id,
      ModuleCat.comp_apply, ModuleCat.id_apply, ym] using h
  have hp := KIP126.AdamsSynthetic.Standard.mapping_sphere_product (s,t) (s',t') xm ym
  change E.hom.pageMap 2 (((s:ℤ),(t:ℤ))+((s':ℤ),(t':ℤ)))
      ((mappingComposition.pairing S S S).ssPairing.pair 2 (s,t) (s',t') xm ym) =
        model.sphereAlgebra.product (s,t) (s',t')
          (E.hom.pageMap 2 (s,t) xm) (E.hom.pageMap 2 (s',t') ym) at hp
  rw [hx,hy] at hp
  have hc : Moss.abutmentComposition S S S (s,t) (s',t') am bm ≫ e.hom =
      eqToHom (congrArg (Sphere (C := Spectrum))
        (show Moss.stem (((s:ℤ),(t:ℤ))+((s':ℤ),(t':ℤ))) = Moss.stem (s,t)+Moss.stem (s',t') by
          dsimp [Moss.stem]; omega)) ≫ classicalSphereProduct a b := by
    have hh := product_mapping_composition_regrade ((t:ℤ)-s) ((t':ℤ)-s')
      (Moss.stem (((s:ℤ),(t:ℤ))+((s':ℤ),(t':ℤ)))) (by dsimp [Moss.stem]; omega) am bm
    dsimp only [Moss.stem] at hh
    dsimp only [Moss.abutmentComposition, Moss.shiftMap, Moss.abutmentMap, Moss.stem, S]
    simpa only [am,bm,e,Category.assoc,Iso.inv_hom_id,Category.comp_id] using hh
  change ClassicalDetects (model.classicalConvergence .sphere) (((s:ℤ),(t:ℤ))+((s':ℤ),(t':ℤ)))
    (E.hom.pageMap 2 _ ((mappingComposition.pairing S S S).ssPairing.pair 2 (s,t) (s',t') xm ym))
    (Moss.abutmentComposition S S S (s,t) (s',t') am bm ≫ e.hom) at hout
  rw [hp,hc] at hout
  have hdeg : ((s:ℤ),(t:ℤ))+((s':ℤ),(t':ℤ)) =
      (((s+s':ℕ):ℤ),((t+t':ℕ):ℤ)) := by simp only [Prod.mk_add_mk,Nat.cast_add]
  have hf := product_classical_detects_regrade (model.classicalConvergence .sphere) hdeg _ _ hout
  simp only [eqToHom_trans_assoc] at hf
  convert hf using 1
  rfl


end KIP126.Literature.Standard
