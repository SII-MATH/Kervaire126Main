module
import KIP126.AdamsSynthetic.Tower
import all KIP126.AdamsSynthetic.Internal.Source.AdamsTower
import all KIP126.AdamsSynthetic.Internal.Source.AdamsSequence
import all KIP126.AdamsSynthetic.Internal.Source.AdamsNaturality

@[expose] section
namespace KIP126.AdamsSynthetic.Internal.Source
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Core.SpectralSequence
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)] {H : C} {unit : SphereSpectrum ⟶ H} {X Y : C}

private def stepTriangle (T : AbstractAdamsTower unit X) (n : ℕ) : Triangle C :=
  Triangle.mk (T.map (Nat.le_succ n))
    (HasFunctorialCofiber.cofibι (T.map (Nat.le_succ n)))
    (HasFunctorialCofiber.cofibδ (T.map (Nat.le_succ n)))

private def stepNextComparison (T : AbstractAdamsTower unit X)
    (U : AbstractAdamsTower unit Y) (n : ℕ) (e : T.stage n ≅ U.stage n) :
    {e' : T.stage (n+1) ≅ U.stage (n+1) //
      e'.hom ≫ U.map (Nat.le_succ n) = T.map (Nat.le_succ n) ≫ e.hom} := by
  let e₂ : HasFunctorialCofiber.cofib (T.map (Nat.le_succ n)) ≅
      HasFunctorialCofiber.cofib (U.map (Nat.le_succ n)) :=
    T.layerIso n ≪≫ ((tensorLeft H).mapIso e : H ⊗ T.stage n ≅ H ⊗ U.stage n) ≪≫ (U.layerIso n).symm
  have hc : (stepTriangle T n).rotate.mor₁ ≫ e₂.hom =
      e.hom ≫ (stepTriangle U n).rotate.mor₁ := by
    apply (cancel_mono (U.layerIso n).hom).mp
    change (HasFunctorialCofiber.cofibι (T.map (Nat.le_succ n)) ≫
      (T.layerIso n).hom ≫ (H ◁ e.hom) ≫ (U.layerIso n).inv) ≫ (U.layerIso n).hom =
      (e.hom ≫ HasFunctorialCofiber.cofibι (U.map (Nat.le_succ n))) ≫ (U.layerIso n).hom
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [← Category.assoc, T.layer_unit, U.layer_unit]
    exact (adamsUnit_naturality unit e.hom).symm
  let E : (stepTriangle T n).rotate ≅ (stepTriangle U n).rotate :=
    isoTriangleOfIso₁₂ _ _
      (rot_of_distTriang _ (HasFunctorialCofiber.cofib_distinguished _))
      (rot_of_distTriang _ (HasFunctorialCofiber.cofib_distinguished _)) e e₂ hc
  let e' : T.stage (n+1) ≅ U.stage (n+1) :=
    (shiftFunctor C (1 : ℤ)).preimageIso (Triangle.π₃.mapIso E)
  refine ⟨e', ?_⟩
  apply (shiftFunctor C (1 : ℤ)).map_injective
  have he : (shiftFunctor C (1 : ℤ)).map e'.hom = E.hom.hom₃ := by
    dsimp only [e', Functor.preimageIso_hom, Functor.mapIso_hom]
    exact (shiftFunctor C (1 : ℤ)).map_preimage _
  have h := E.hom.comm₃
  have h₁ : E.hom.hom₁ = e.hom := by simp only [E, isoTriangleOfIso₁₂_hom_hom₁]
  rw [h₁] at h
  dsimp only [stepTriangle, Triangle.rotate, Triangle.mk] at h
  simp only [Preadditive.neg_comp, Preadditive.comp_neg, neg_inj] at h
  simpa only [Functor.map_comp, he] using h.symm

private def stageComparison (T U : AbstractAdamsTower unit X) :
    (n : ℕ) → (T.stage n ≅ U.stage n)
  | 0 => T.zeroIso ≪≫ U.zeroIso.symm
  | n+1 => (stepNextComparison T U n (stageComparison T U n)).val

private theorem stageComparison_step (T U : AbstractAdamsTower unit X) (n : ℕ) :
    (stageComparison T U (n+1)).hom ≫ U.map (Nat.le_succ n) =
      T.map (Nat.le_succ n) ≫ (stageComparison T U n).hom :=
  (stepNextComparison T U n (stageComparison T U n)).property

private theorem stageComparison_natural (T U : AbstractAdamsTower unit X)
    (s t : ℕ) (h : s ≤ t) :
    (stageComparison T U t).hom ≫ U.map h =
      T.map h ≫ (stageComparison T U s).hom := by
  induction t, h using Nat.le_induction with
  | base => simp only [T.map_self, U.map_self, Category.comp_id, Category.id_comp]
  | succ t ht ih =>
    rw [← T.map_comp ht (Nat.le_succ t), ← U.map_comp ht (Nat.le_succ t),
      ← Category.assoc, stageComparison_step, Category.assoc, ih, ← Category.assoc]

private def comparisonTowerMap (T U : AbstractAdamsTower unit X) :
    TowerMap unit T U (𝟙 X) where
  stage n := (stageComparison T U n).hom
  natural h := stageComparison_natural T U _ _ h
  zero := by simp only [stageComparison, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

private def inverseComparisonTowerMap (T U : AbstractAdamsTower unit X) :
    TowerMap unit U T (𝟙 X) where
  stage n := (stageComparison T U n).inv
  natural {s t} h := by
    apply (cancel_mono (stageComparison T U s).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [← stageComparison_natural]
    simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  zero := by simp only [stageComparison, Iso.trans_inv, Iso.symm_inv,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem cofiberMap_isIso {A B A' B' : C} (f : A ⟶ B) (g : A' ⟶ B')
    (a : A ⟶ A') (b : B ⟶ B') (h : a ≫ g = f ≫ b) [IsIso a] [IsIso b] :
    IsIso (HasFunctorialCofiber.cofibMap f g a b h) := by
  let φ : Triangle.mk f (HasFunctorialCofiber.cofibι f) (HasFunctorialCofiber.cofibδ f) ⟶
      Triangle.mk g (HasFunctorialCofiber.cofibι g) (HasFunctorialCofiber.cofibδ g) :=
    { hom₁ := a
      hom₂ := b
      hom₃ := HasFunctorialCofiber.cofibMap f g a b h
      comm₁ := h.symm
      comm₂ := (HasFunctorialCofiber.cofibMap_ι f g a b h).symm
      comm₃ := (HasFunctorialCofiber.cofibMap_δ f g a b h).symm }
  exact isIso₃_of_isIso₁₂ φ (HasFunctorialCofiber.cofib_distinguished f)
    (HasFunctorialCofiber.cofib_distinguished g) inferInstance inferInstance

section TowerIsomorphism
variable {T : AbstractAdamsTower unit X} {U : AbstractAdamsTower unit Y}
  {f : X ⟶ Y} (φ : TowerMap unit T U f) [∀ n, IsIso (φ.stage n)]

private theorem layer_isIso (s : ℤ) : IsIso (φ.layer s) := by
  exact cofiberMap_isIso _ _ _ _ _

private theorem homMap_bijective (n s : ℤ) : Function.Bijective (towerHomMap φ n s) := by
  constructor
  · intro a b hab
    exact (cancel_mono (φ.stage s.toNat)).mp hab
  · intro a
    refine ⟨a ≫ inv (φ.stage s.toNat), ?_⟩
    change (a ≫ _) ≫ _ = a
    simp

private theorem e1Map_bijective (p : ℤ × ℤ) : Function.Bijective (towerE1Map φ p) := by
  letI := layer_isIso φ p.1
  constructor
  · intro a b hab
    exact (cancel_mono (φ.layer p.1)).mp hab
  · intro a
    refine ⟨a ≫ inv (φ.layer p.1), ?_⟩
    change (a ≫ _) ≫ _ = a
    simp

private theorem e1Map_cycles_iff (r : ℕ) (hr : 1 ≤ r) (p : ℤ × ℤ)
    (a : T.FirstPage p) : towerE1Map φ p a ∈ U.cycles r hr p ↔ a ∈ T.cycles r hr p := by
  constructor
  · rintro ⟨b, hb⟩
    obtain ⟨c, rfl⟩ := (homMap_bijective φ (p.2-p.1-1) (p.1+r)).surjective b
    refine ⟨c, (homMap_bijective φ (p.2-p.1-1) (p.1+1)).injective ?_⟩
    change towerHomMap φ _ _ (towerI T _ _ _ _ c) = _
    rw [← towerI_natural, ← towerK_natural]
    exact hb
  · exact towerE1Map_cycles φ r hr p

private theorem e1Map_boundaries_iff (r : ℕ) (hr : 1 ≤ r) (p : ℤ × ℤ)
    (a : T.FirstPage p) : towerE1Map φ p a ∈ U.boundaries r hr p ↔ a ∈ T.boundaries r hr p := by
  constructor
  · rintro ⟨b, hb, hba⟩
    obtain ⟨c, rfl⟩ := (homMap_bijective φ (p.2-p.1) p.1).surjective b
    refine ⟨c, ?_, (e1Map_bijective φ p).injective ?_⟩
    · change towerI T (p.2-p.1) (p.1-r+1) p.1 _ c = 0
      apply (homMap_bijective φ (p.2-p.1) (p.1-r+1)).injective
      rw [← towerI_natural, map_zero]
      exact hb
    · rw [towerJ_natural]
      exact hba
  · exact towerE1Map_boundaries φ r hr p

private theorem cycleMap_bijective (p : ℤ × ℤ) : Function.Bijective (towerCycleMap φ p) := by
  constructor
  · intro a b hab
    apply Subtype.ext
    exact (e1Map_bijective φ p).injective (congrArg Subtype.val hab)
  · intro b
    obtain ⟨a, ha⟩ := (e1Map_bijective φ p).surjective b.val
    refine ⟨⟨a, (e1Map_cycles_iff φ 2 (by decide) p a).mp ?_⟩, ?_⟩
    · rw [ha]
      exact b.property
    · exact Subtype.ext ha

private def cycleMapEquiv (p : ℤ × ℤ) : cycleAmbient T p ≃ₗ[ℤ] cycleAmbient U p :=
  LinearEquiv.ofBijective (towerCycleMap φ p) (cycleMap_bijective φ p)

private theorem cycleMap_allCycles_iff (p : ℤ × ℤ) (r : WithTop ℕ)
    (a : cycleAmbient T p) : towerCycleMap φ p a ∈ allCycles U p r ↔ a ∈ allCycles T p r := by
  cases r using WithTop.recTopCoe with
  | top =>
    simp only [allCycles, Submodule.mem_iInf]
    exact forall_congr' fun n => e1Map_cycles_iff φ (n+2) (by omega) p a.val
  | coe n => exact e1Map_cycles_iff φ (n+2) (by omega) p a.val

private theorem cycleMap_allBoundaries_iff (p : ℤ × ℤ) (r : WithTop ℕ)
    (a : cycleAmbient T p) : towerCycleMap φ p a ∈ allBoundaries U p r ↔ a ∈ allBoundaries T p r := by
  let e := cycleMapEquiv φ p
  have hf (n : ℕ) : (finiteBoundaries T p n).map e.toLinearMap = finiteBoundaries U p n := by
    ext b
    constructor
    · rintro ⟨c,hc,rfl⟩
      exact (e1Map_boundaries_iff φ (n+2) (by omega) p c.val).mpr hc
    · intro hb
      refine ⟨e.symm b, ?_, e.apply_symm_apply b⟩
      apply (e1Map_boundaries_iff φ (n+2) (by omega) p (e.symm b).val).mp
      change e (e.symm b) ∈ finiteBoundaries U p n
      simpa only [e.apply_symm_apply] using hb
  cases r using WithTop.recTopCoe with
  | top =>
    have ht : (allBoundaries T p ⊤).map e.toLinearMap = allBoundaries U p ⊤ := by
      simp only [allBoundaries, Submodule.map_iSup, hf]
    change e a ∈ allBoundaries U p ⊤ ↔ _
    rw [← ht]
    simp only [Submodule.mem_map_equiv, e.symm_apply_apply]
  | coe n => exact e1Map_boundaries_iff φ (n+2) (by omega) p a.val

private def inverseTowerSSDataMap : SSDataMorphism (ℤ × ℤ) (towerSSData U) (towerSSData T) where
  φ p := ModuleCat.ofHom (cycleMapEquiv φ p).symm.toLinearMap
  preserves_Z p r := towerSubmoduleLift_exists _ _ _ (by
    intro a ha
    apply (cycleMap_allCycles_iff φ p r ((cycleMapEquiv φ p).symm a)).mp
    change (cycleMapEquiv φ p) ((cycleMapEquiv φ p).symm a) ∈ allCycles U p r
    simpa only [LinearEquiv.apply_symm_apply] using ha)
  preserves_B p r := towerSubmoduleLift_exists _ _ _ (by
    intro a ha
    apply (cycleMap_allBoundaries_iff φ p r ((cycleMapEquiv φ p).symm a)).mp
    change (cycleMapEquiv φ p) ((cycleMapEquiv φ p).symm a) ∈ allBoundaries U p r
    simpa only [LinearEquiv.apply_symm_apply] using ha)

private theorem forward_inverse_SSData :
    (towerSSDataMap φ).comp (inverseTowerSSDataMap φ) = SSDataMorphism.id (towerSSData T) := by
  apply SSDataMorphism.ext
  funext p
  ext a
  change (cycleMapEquiv φ p).symm ((cycleMapEquiv φ p) a) = a
  exact (cycleMapEquiv φ p).symm_apply_apply a

private theorem inverse_forward_SSData :
    (inverseTowerSSDataMap φ).comp (towerSSDataMap φ) = SSDataMorphism.id (towerSSData U) := by
  apply SSDataMorphism.ext
  funext p
  ext a
  change (cycleMapEquiv φ p) ((cycleMapEquiv φ p).symm a) = a
  exact (cycleMapEquiv φ p).apply_symm_apply a

private theorem forward_inverse_pages (p : ℤ × ℤ) (r : WithTop ℕ) :
    (towerSSDataMap φ).pageMap p r ≫ (inverseTowerSSDataMap φ).pageMap p r = 𝟙 _ := by
  have h := congrArg (fun F => F.pageMap p r) (forward_inverse_SSData φ)
  simpa only [SSDataMorphism.pageMap_comp, SSDataMorphism.pageMap_id] using h

private theorem inverse_forward_pages (p : ℤ × ℤ) (r : WithTop ℕ) :
    (inverseTowerSSDataMap φ).pageMap p r ≫ (towerSSDataMap φ).pageMap p r = 𝟙 _ := by
  have h := congrArg (fun F => F.pageMap p r) (inverse_forward_SSData φ)
  simpa only [SSDataMorphism.pageMap_comp, SSDataMorphism.pageMap_id] using h

private theorem inverseTowerSSDataMap_differential (r : ℤ) (p : ℤ × ℤ) :
    (inverseTowerSSDataMap φ).pageMap p (↑(r-2).toNat : WithTop ℕ) ≫ towerD T r p =
      towerD U r p ≫ (inverseTowerSSDataMap φ).pageMap (p+(r,r-1)) (↑(r-2).toNat : WithTop ℕ) := by
  let n : WithTop ℕ := ↑(r-2).toNat
  let F := towerSSDataMap φ
  let G := inverseTowerSSDataMap φ
  have hd : F.pageMap p n ≫ towerD U r p = towerD T r p ≫ F.pageMap (p+(r,r-1)) n :=
    towerSSDataMorphism_differential φ F (fun _ => rfl) r p
  change G.pageMap p n ≫ towerD T r p = towerD U r p ≫ G.pageMap (p+(r,r-1)) n
  calc
    G.pageMap p n ≫ towerD T r p =
        G.pageMap p n ≫ towerD T r p ≫ (F.pageMap (p+(r,r-1)) n ≫ G.pageMap (p+(r,r-1)) n) := by
      rw [forward_inverse_pages φ]
      exact congrArg (fun k => G.pageMap p n ≫ k) (Category.comp_id (towerD T r p)).symm
    _ = G.pageMap p n ≫ (towerD T r p ≫ F.pageMap (p+(r,r-1)) n) ≫ G.pageMap (p+(r,r-1)) n := by
      simp only [Category.assoc]
    _ = G.pageMap p n ≫ (F.pageMap p n ≫ towerD U r p) ≫ G.pageMap (p+(r,r-1)) n := by rw [hd]
    _ = towerD U r p ≫ G.pageMap (p+(r,r-1)) n := by
      simp only [F, G, ← Category.assoc, inverse_forward_pages φ, Category.id_comp]

private def towerSequenceIso : towerSequence T ≅ towerSequence U where
  hom := towerSequenceMap φ
  inv := towerSequenceMorphism (inverseTowerSSDataMap φ) (inverseTowerSSDataMap_differential φ)
  hom_inv_id := by
    apply SpectralSequenceMorphism.ext
    funext p
    ext a
    change (cycleMapEquiv φ p).symm ((cycleMapEquiv φ p) a) = a
    exact (cycleMapEquiv φ p).symm_apply_apply a
  inv_hom_id := by
    apply SpectralSequenceMorphism.ext
    funext p
    ext a
    change (cycleMapEquiv φ p) ((cycleMapEquiv φ p).symm a) = a
    exact (cycleMapEquiv φ p).apply_symm_apply a


end TowerIsomorphism

private def anyTowerSequenceIso (T U : AbstractAdamsTower unit X) :
    towerSequence T ≅ towerSequence U := by
  letI : ∀ n, IsIso ((comparisonTowerMap T U).stage n) := fun n =>
    (stageComparison T U n).isIso_hom
  exact towerSequenceIso (comparisonTowerMap T U)

private theorem ssData_Z_top (D : SSData (ModuleCat.{v} ℤ)) :
    ModuleCat.subobjectModule _ (D.Z ⊤) = ⨅ n : ℕ, ModuleCat.subobjectModule _ (D.Z (n : WithTop ℕ)) := by
  apply le_antisymm
  · exact le_iInf fun n => (ModuleCat.subobjectModule _).monotone (D.Z_anti le_top)
  · have h : (ModuleCat.subobjectModule _).symm
        (⨅ n : ℕ, ModuleCat.subobjectModule _ (D.Z (n : WithTop ℕ))) ≤ D.Z ⊤ := by
      apply D.Z_top_greatest
      intro n
      apply (ModuleCat.subobjectModule _).le_iff_le.mp
      rw [OrderIso.apply_symm_apply]
      exact iInf_le _ n
    have h' := (ModuleCat.subobjectModule _).monotone h
    simpa only [OrderIso.apply_symm_apply] using h'

private theorem ssData_B_top (D : SSData (ModuleCat.{v} ℤ)) :
    ModuleCat.subobjectModule _ (D.B ⊤) = ⨆ n : ℕ, ModuleCat.subobjectModule _ (D.B (n : WithTop ℕ)) := by
  apply le_antisymm
  · have h : D.B ⊤ ≤ (ModuleCat.subobjectModule _).symm
        (⨆ n : ℕ, ModuleCat.subobjectModule _ (D.B (n : WithTop ℕ))) := by
      apply D.B_top_least
      intro n
      apply (ModuleCat.subobjectModule _).le_iff_le.mp
      rw [OrderIso.apply_symm_apply]
      exact le_iSup (fun k : ℕ => (ModuleCat.subobjectModule D.V) (D.B (k : WithTop ℕ))) n
    have h' := (ModuleCat.subobjectModule _).monotone h
    simpa only [OrderIso.apply_symm_apply] using h'
  · exact iSup_le fun n => (ModuleCat.subobjectModule _).monotone (D.B_mono le_top)

section PresentationComparison
variable {T : AbstractAdamsTower unit X}
  {D : (ℤ × ℤ) → SSData (ModuleCat.{v} ℤ)}
  {d : ∀ (r : ℤ) (p : ℤ × ℤ), (D p).page (↑(r - 2).toNat : WithTop ℕ) ⟶
      (D (p + (r, r - 1))).page (↑(r - 2).toNat : WithTop ℕ)}
  (P : TowerSequencePresentation unit T D d)

private theorem presentation_allCycles (p : ℤ × ℤ) (r : WithTop ℕ) (a : (D p).V) :
    a ∈ ModuleCat.subobjectModule _ ((D p).Z r) ↔
      (P.ambient p).hom a ∈ allCycles T p r := by
  cases r using WithTop.recTopCoe with
  | top =>
    rw [ssData_Z_top]
    simp only [allCycles, Submodule.mem_iInf]
    exact forall_congr' fun n => P.cycles p n a
  | coe n => exact P.cycles p n a

private theorem presentation_allBoundaries (p : ℤ × ℤ) (r : WithTop ℕ) (a : (D p).V) :
    a ∈ ModuleCat.subobjectModule _ ((D p).B r) ↔
      (P.ambient p).hom a ∈ allBoundaries T p r := by
  let e := (P.ambient p).toLinearEquiv
  have hf (n : ℕ) : ((ModuleCat.subobjectModule _) ((D p).B (n : WithTop ℕ))).map e.toLinearMap =
      finiteBoundaries T p n := by
    ext b
    constructor
    · rintro ⟨c,hc,rfl⟩
      exact (P.boundaries p n c).mp hc
    · intro hb
      refine ⟨e.symm b, ?_, e.apply_symm_apply b⟩
      apply (P.boundaries p n (e.symm b)).mpr
      change (e (e.symm b)).val ∈ T.boundaries (n+2) (by omega) p
      change b.val ∈ T.boundaries (n+2) (by omega) p at hb
      simpa only [e.apply_symm_apply] using hb
  cases r using WithTop.recTopCoe with
  | top =>
    have ht : ((ModuleCat.subobjectModule _) ((D p).B ⊤)).map e.toLinearMap = allBoundaries T p ⊤ := by
      rw [ssData_B_top, Submodule.map_iSup]
      simp only [hf, allBoundaries]
    change a ∈ ModuleCat.subobjectModule _ ((D p).B ⊤) ↔ e a ∈ allBoundaries T p ⊤
    rw [← ht]
    simp only [Submodule.mem_map_equiv, e.symm_apply_apply]
  | coe n => exact P.boundaries p n a

private def presentationSSDataForward : SSDataMorphism (ℤ × ℤ) D (towerSSData T) where
  φ p := (P.ambient p).hom
  preserves_Z p r := by
    have h := towerSubmoduleLift_exists ((ModuleCat.subobjectModule _) ((D p).Z r))
      (allCycles T p r) (P.ambient p).hom.hom (by
        intro a ha
        exact (presentation_allCycles P p r a).mp ha)
    rw [(ModuleCat.subobjectModule (D p).V).symm_apply_apply] at h
    exact h
  preserves_B p r := by
    have h := towerSubmoduleLift_exists ((ModuleCat.subobjectModule _) ((D p).B r))
      (allBoundaries T p r) (P.ambient p).hom.hom (by
        intro a ha
        exact (presentation_allBoundaries P p r a).mp ha)
    rw [(ModuleCat.subobjectModule (D p).V).symm_apply_apply] at h
    exact h

private def presentationSSDataInverse : SSDataMorphism (ℤ × ℤ) (towerSSData T) D where
  φ p := (P.ambient p).inv
  preserves_Z p r := by
    have h := towerSubmoduleLift_exists (allCycles T p r)
      ((ModuleCat.subobjectModule _) ((D p).Z r)) (P.ambient p).inv.hom (by
        intro a ha
        apply (presentation_allCycles P p r ((P.ambient p).inv a)).mpr
        simpa only [Iso.inv_hom_id_apply] using ha)
    rw [(ModuleCat.subobjectModule (D p).V).symm_apply_apply] at h
    exact h
  preserves_B p r := by
    have h := towerSubmoduleLift_exists (allBoundaries T p r)
      ((ModuleCat.subobjectModule _) ((D p).B r)) (P.ambient p).inv.hom (by
        intro a ha
        apply (presentation_allBoundaries P p r ((P.ambient p).inv a)).mpr
        simpa only [Iso.inv_hom_id_apply] using ha)
    rw [(ModuleCat.subobjectModule (D p).V).symm_apply_apply] at h
    exact h

private theorem presentationSSData_forward_inverse :
    (presentationSSDataForward P).comp (presentationSSDataInverse P) = SSDataMorphism.id D := by
  apply SSDataMorphism.ext
  funext p
  exact (P.ambient p).hom_inv_id

private theorem presentationSSData_inverse_forward :
    (presentationSSDataInverse P).comp (presentationSSDataForward P) = SSDataMorphism.id (towerSSData T) := by
  apply SSDataMorphism.ext
  funext p
  exact (P.ambient p).inv_hom_id

private theorem presentation_forward_cycle_value (p : ℤ × ℤ) (r : WithTop ℕ)
    (z : (Subobject.underlying.obj ((D p).Z r) : ModuleCat ℤ)) :
    ((towerSSData T p).Z r).arrow ((presentationSSDataForward P).cycleMap p r z) =
      (P.ambient p).hom (((D p).Z r).arrow z) :=
  ConcreteCategory.congr_hom ((presentationSSDataForward P).cycleMap_arrow p r) z

private theorem presentation_inverse_forward_cycles (p : ℤ × ℤ) (r : WithTop ℕ) :
    (presentationSSDataInverse P).cycleMap p r ≫ (presentationSSDataForward P).cycleMap p r = 𝟙 _ := by
  have h := congrArg (fun F => F.cycleMap p r) (presentationSSData_inverse_forward P)
  simpa only [SSDataMorphism.cycleMap_comp, SSDataMorphism.cycleMap_id] using h

private theorem presentation_forward_differential (r : ℤ) (hr : 2 ≤ r) (p : ℤ × ℤ) :
    (presentationSSDataForward P).pageMap p (↑(r-2).toNat : WithTop ℕ) ≫ towerD T r p =
      d r p ≫ (presentationSSDataForward P).pageMap (p+(r,r-1)) (↑(r-2).toNat : WithTop ℕ) := by
  let n := (r-2).toNat
  let F := presentationSSDataForward P
  let G := presentationSSDataInverse P
  letI : Epi ((D p).pageπ (↑n : WithTop ℕ)) := by
    dsimp only [SSData.pageπ]; infer_instance
  apply (cancel_epi ((D p).pageπ (↑n : WithTop ℕ))).mp
  ext z
  change towerD T r p (F.pageMap p n ((D p).pageπ n z)) =
    F.pageMap (p+(r,r-1)) n (d r p ((D p).pageπ n z))
  let zw := F.cycleMap p (↑n : WithTop ℕ) z
  let a := cycleLiftAt T r hr p zw
  let q := p+(r,r-1)
  let e : p.2-p.1-1 = q.2-q.1 := by dsimp [q]; omega
  let ztw := layerCycle T q n (degreeCast e a)
  let z' := G.cycleMap q (↑n : WithTop ℕ) ztw
  have hz' : F.cycleMap q (↑n : WithTop ℕ) z' = ztw :=
    ConcreteCategory.congr_hom (presentation_inverse_forward_cycles P q n) ztw
  have hs : T.connecting p (((P.ambient p).hom (((D p).Z (↑n : WithTop ℕ)).arrow z)).val) =
      a ≫ T.mapAt (show p.1+1 ≤ p.1+r by omega) := by
    rw [← presentation_forward_cycle_value]
    exact (cycleLiftAt_spec T r hr p zw).symm
  have ht : (((P.ambient q).hom (((D q).Z (↑n : WithTop ℕ)).arrow z')).val) =
      T.layerMap q (Eq.mp (congrArg (fun m => HomotopyGroup m (T.stageAt (p.1+r))) e) a) := by
    rw [← presentation_forward_cycle_value]
    change (((towerSSData T q).Z (↑n : WithTop ℕ)).arrow (F.cycleMap q (↑n : WithTop ℕ) z')).val = _
    rw [hz']
    exact (cycleRep_layerCycle T q n (degreeCast e a)).trans (by rw [degreeCast_apply])
  have hd := P.differential r hr p z a z' hs ht
  rw [hd]
  rw [show F.pageMap p (↑n : WithTop ℕ) ((D p).pageπ (↑n : WithTop ℕ) z) =
      (towerSSData T p).pageπ (↑n : WithTop ℕ) zw from
    ConcreteCategory.congr_hom (F.pageπ_pageMap p n) z]
  rw [towerD_pageπ T r hr p]
  rw [show F.pageMap q (↑n : WithTop ℕ) ((D q).pageπ (↑n : WithTop ℕ) z') =
      (towerSSData T q).pageπ (↑n : WithTop ℕ) (F.cycleMap q (↑n : WithTop ℕ) z') from
    ConcreteCategory.congr_hom (F.pageπ_pageMap q n) z']
  rw [hz']
  rfl

private theorem presentation_to_otherTower_differential
    (U : AbstractAdamsTower unit X) (e : towerSequence T ≅ towerSequence U)
    (r : ℤ) (hr : 2 ≤ r) (p : ℤ × ℤ) :
    ((presentationSSDataForward P).comp e.hom.toSSDataMorphism).pageMap p (↑(r-2).toNat : WithTop ℕ) ≫ towerD U r p =
      d r p ≫ ((presentationSSDataForward P).comp e.hom.toSSDataMorphism).pageMap (p+(r,r-1)) (↑(r-2).toNat : WithTop ℕ) := by
  have he : e.hom.toSSDataMorphism.pageMap p (↑(r-2).toNat : WithTop ℕ) ≫ towerD U r p =
      towerD T r p ≫ e.hom.toSSDataMorphism.pageMap (p+(r,r-1)) (↑(r-2).toNat : WithTop ℕ) := by
    simpa only [towerSequence, towerPreSS, SpectralSequenceMorphism.toSSDataMorphism, PreSS.Page, SSDataMorphism.pageMapAt, eqToHom_refl, Category.comp_id] using e.hom.comm_d r p
  rw [SSDataMorphism.pageMap_comp, SSDataMorphism.pageMap_comp]
  rw [Category.assoc, he, ← Category.assoc, presentation_forward_differential P r hr p,
    Category.assoc]

end PresentationComparison

#print axioms stageComparison
#print axioms anyTowerSequenceIso
#print axioms presentationSSDataForward
#print axioms presentationSSDataInverse
#print axioms presentation_forward_differential
#print axioms presentation_to_otherTower_differential

end
end KIP126.AdamsSynthetic.Internal.Source
