module

/-
Copyright (c) 2026 Jiashuo Zhang and KIP126 contributors.
Released under the MIT license; see LICENSE.
-/

import KIP126.AdamsSynthetic.Tower
import all KIP126.AdamsSynthetic.Internal.Source.AdamsTower
import all KIP126.AdamsSynthetic.Internal.Source.AdamsSequence

/-! The actual stage, layer, and quotient-page maps of one tower map.
The construction retains every finite cycle/boundary and their intersection
and union at infinity. It does not assert identity or composition laws for
the chosen cofiber-map operation. Adapted from SII-MATH/Kervaire126 commit
8cb35dad5f75ecc095e474df6c765baec9b175bf, TowerNaturality. -/

@[expose] section
namespace KIP126.AdamsSynthetic.Internal.Source

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy KIP126.Core.SpectralSequence
universe u v
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} {unit : SphereSpectrum ⟶ H}
  {X Y : C}

private def fiberMap {A B A' B' : C} (f : A ⟶ B) (g : A' ⟶ B')
    (a : A ⟶ A') (b : B ⟶ B') (h : a ≫ g = f ≫ b) : fiber f ⟶ fiber g :=
  (HasFunctorialCofiber.cofibMap f g a b h)⟦(-1 : ℤ)⟧'

private theorem fiberMap_ι {A B A' B' : C} (f : A ⟶ B) (g : A' ⟶ B')
    (a : A ⟶ A') (b : B ⟶ B') (h : a ≫ g = f ≫ b) :
    fiberMap f g a b h ≫ fiberι g = fiberι f ≫ a := by
  dsimp [fiberMap, fiberι]
  rw [← Functor.map_comp_assoc, HasFunctorialCofiber.cofibMap_δ]
  simp only [Functor.map_comp, Category.assoc]
  exact congrArg (fun k => (HasFunctorialCofiber.cofibδ f)⟦(-1 : ℤ)⟧' ≫ k)
    ((shiftFunctorCompIsoId C (1 : ℤ) (-1 : ℤ) (by omega)).hom.naturality a)

private theorem adamsUnit_naturality (unit : SphereSpectrum ⟶ H)
    {A B : C} (f : A ⟶ B) :
    f ≫ adamsUnit unit B = adamsUnit unit A ≫ H ◁ f := by
  simp only [adamsUnit, ← Category.assoc, leftUnitor_inv_naturality]
  simp only [Category.assoc, whisker_exchange]

private def canonicalStageMap (unit : SphereSpectrum ⟶ H) (f : X ⟶ Y) :
    (s : ℕ) → adamsStage unit X s ⟶ adamsStage unit Y s
  | 0 => f
  | s + 1 => fiberMap _ _ (canonicalStageMap unit f s)
      (H ◁ canonicalStageMap unit f s) (adamsUnit_naturality unit _)

private theorem canonicalStageMap_step (unit : SphereSpectrum ⟶ H)
    (f : X ⟶ Y) (s : ℕ) :
    canonicalStageMap unit f (s+1) ≫ adamsStep unit Y s =
      adamsStep unit X s ≫ canonicalStageMap unit f s := fiberMap_ι _ _ _ _ _

private theorem canonicalStageMap_map (unit : SphereSpectrum ⟶ H)
    (f : X ⟶ Y) (s t : ℕ) (h : s ≤ t) :
    canonicalStageMap unit f t ≫ adamsMap unit Y s t h =
      adamsMap unit X s t h ≫ canonicalStageMap unit f s := by
  induction t, h using Nat.le_induction with
  | base => simp
  | succ t ht ih =>
    rw [adamsMap_succ unit Y s t ht, adamsMap_succ unit X s t ht,
      ← Category.assoc, canonicalStageMap_step, Category.assoc, ih, ← Category.assoc]

private def canonicalTowerMap (unit : SphereSpectrum ⟶ H) (f : X ⟶ Y) :
    TowerMap unit (canonicalTower unit X) (canonicalTower unit Y) f where
  stage := canonicalStageMap unit f
  natural h := canonicalStageMap_map unit f _ _ h
  zero := by
    change f ≫ 𝟙 Y = 𝟙 X ≫ f
    simp

variable {T : AbstractAdamsTower unit X} {U : AbstractAdamsTower unit Y}
  {f : X ⟶ Y} (φ : TowerMap unit T U f)

private def towerE1Map (p : ℤ × ℤ) : T.FirstPage p →ₗ[ℤ] U.FirstPage p :=
  (inducedMap (φ.layer p.1) (p.2-p.1)).toIntLinearMap

private def towerHomMap (n s : ℤ) :
    HomotopyGroup n (T.stageAt s) →ₗ[ℤ] HomotopyGroup n (U.stageAt s) :=
  (inducedMap (φ.stage s.toNat) n).toIntLinearMap

private theorem towerJ_natural (p : ℤ × ℤ)
    (a : HomotopyGroup (p.2-p.1) (T.stageAt p.1)) :
    towerE1Map φ p (T.layerMap p a) = U.layerMap p (towerHomMap φ (p.2-p.1) p.1 a) := by
  change (a ≫ _) ≫ _ = (a ≫ _) ≫ _
  simp only [Category.assoc, TowerMap.layer, ← HasFunctorialCofiber.cofibMap_ι]

private theorem towerK_natural (p : ℤ × ℤ) (a : T.FirstPage p) :
    U.connecting p (towerE1Map φ p a) =
      towerHomMap φ _ _ (T.connecting p a) := by
  change AbstractAdamsTower.desuspend _ _ ((a ≫ φ.layer p.1) ≫ _) =
    (AbstractAdamsTower.desuspend _ _ (a ≫ _)) ≫ _
  dsimp [AbstractAdamsTower.desuspend]
  rw [Category.assoc, TowerMap.layer, HasFunctorialCofiber.cofibMap_δ]
  simp only [Functor.map_comp, Category.assoc]
  have hn := (shiftFunctorCompIsoId C (1 : ℤ) (-1 : ℤ) (by omega)).hom.naturality
    (φ.stage (p.1+1).toNat)
  simp only [Functor.comp_map, Functor.id_map] at hn
  rw [hn]

private theorem towerI_natural (n s t : ℤ) (h : s ≤ t)
    (a : HomotopyGroup n (T.stageAt t)) :
    towerI U n s t h (towerHomMap φ n t a) =
      towerHomMap φ n s (towerI T n s t h a) := by
  change (a ≫ _) ≫ _ = (a ≫ _) ≫ _
  change (a ≫ _) ≫ U.map _ = (a ≫ T.map _) ≫ _
  rw [Category.assoc, φ.natural, ← Category.assoc]

private theorem towerE1Map_cycles (r : ℕ) (hr : 1 ≤ r) (p : ℤ × ℤ)
    {a : T.FirstPage p} (ha : a ∈ T.cycles r hr p) :
    towerE1Map φ p a ∈ U.cycles r hr p := by
  obtain ⟨b, hb⟩ := ha
  refine ⟨towerHomMap φ _ _ b, ?_⟩
  change towerI U _ _ _ _ _ = U.connecting _ _
  rw [towerI_natural]
  change towerI T _ _ _ _ b = _ at hb
  rw [hb, towerK_natural]

private theorem towerE1Map_boundaries (r : ℕ) (hr : 1 ≤ r) (p : ℤ × ℤ)
    {a : T.FirstPage p} (ha : a ∈ T.boundaries r hr p) :
    towerE1Map φ p a ∈ U.boundaries r hr p := by
  obtain ⟨b, hb, rfl⟩ := ha
  refine ⟨towerHomMap φ _ _ b, ?_, ?_⟩
  · change towerI U _ _ _ _ _ = 0
    rw [towerI_natural]
    change towerI T _ _ _ _ b = 0 at hb
    rw [hb, map_zero]
  · exact (towerJ_natural φ p b).symm


private def towerCycleMap (p : ℤ × ℤ) : cycleAmbient T p →ₗ[ℤ] cycleAmbient U p :=
  ((towerE1Map φ p).comp (T.cycles 2 (by decide) p).subtype).codRestrict
    (U.cycles 2 (by decide) p) (fun a => towerE1Map_cycles φ 2 (by decide) p a.property)

private theorem towerCycleMap_allCycles (p : ℤ × ℤ) (r : WithTop ℕ)
    {a : cycleAmbient T p} (ha : a ∈ allCycles T p r) :
    towerCycleMap φ p a ∈ allCycles U p r := by
  cases r using WithTop.recTopCoe with
  | top =>
    simp only [allCycles, Submodule.mem_iInf] at ha ⊢
    intro n
    exact towerE1Map_cycles φ (n+2) (by omega) p (ha n)
  | coe n => exact towerE1Map_cycles φ (n+2) (by omega) p ha

private theorem towerCycleMap_allBoundaries (p : ℤ × ℤ) (r : WithTop ℕ)
    {a : cycleAmbient T p} (ha : a ∈ allBoundaries T p r) :
    towerCycleMap φ p a ∈ allBoundaries U p r := by
  cases r using WithTop.recTopCoe with
  | top =>
    have hmap : (allBoundaries T p ⊤).map (towerCycleMap φ p) ≤ allBoundaries U p ⊤ := by
      simp only [allBoundaries, Submodule.map_iSup]
      refine iSup_le fun n => ?_
      refine le_trans ?_ (le_iSup (finiteBoundaries U p) n)
      rintro _ ⟨b, hb, rfl⟩
      exact towerE1Map_boundaries φ (n+2) (by omega) p hb
    exact hmap ⟨a, ha, rfl⟩
  | coe n => exact towerE1Map_boundaries φ (n+2) (by omega) p ha

private def towerSubmoduleUnderlyingIso {R : Type*} [Ring R] {M : ModuleCat.{v} R}
    (Z : Submodule R M) :
    Subobject.underlying.obj ((ModuleCat.subobjectModule M).symm Z) ≅ ModuleCat.of R Z :=
  Subobject.underlyingIso (ModuleCat.ofHom Z.subtype)

private theorem towerSubmoduleLift_exists {R : Type*} [Ring R] {M N : ModuleCat.{v} R}
    (A : Submodule R M) (B : Submodule R N) (g : M →ₗ[R] N)
    (hg : ∀ a ∈ A, g a ∈ B) :
    ∃ lift : Subobject.underlying.obj ((ModuleCat.subobjectModule M).symm A) ⟶
        Subobject.underlying.obj ((ModuleCat.subobjectModule N).symm B),
      lift ≫ ((ModuleCat.subobjectModule N).symm B).arrow =
        ((ModuleCat.subobjectModule M).symm A).arrow ≫ ModuleCat.ofHom g := by
  let l := (g.comp A.subtype).codRestrict B (fun a => hg a a.property)
  refine ⟨(towerSubmoduleUnderlyingIso A).hom ≫ ModuleCat.ofHom l ≫
    (towerSubmoduleUnderlyingIso B).inv, ?_⟩
  apply (cancel_epi (towerSubmoduleUnderlyingIso A).inv).mp
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  change ModuleCat.ofHom l ≫ (Subobject.underlyingIso (ModuleCat.ofHom B.subtype)).inv ≫
      (Subobject.mk (ModuleCat.ofHom B.subtype)).arrow =
    (Subobject.underlyingIso (ModuleCat.ofHom A.subtype)).inv ≫
      (Subobject.mk (ModuleCat.ofHom A.subtype)).arrow ≫ ModuleCat.ofHom g
  rw [Subobject.underlyingIso_arrow, Subobject.underlyingIso_arrow_assoc]
  rfl

private def towerSSDataMap : SSDataMorphism (ℤ × ℤ) (towerSSData T) (towerSSData U) where
  φ p := ModuleCat.ofHom (towerCycleMap φ p)
  preserves_Z p r := towerSubmoduleLift_exists _ _ _
    (fun _ ha => towerCycleMap_allCycles φ p r ha)
  preserves_B p r := towerSubmoduleLift_exists _ _ _
    (fun _ ha => towerCycleMap_allBoundaries φ p r ha)

private theorem towerHomMap_cast {n n' : ℤ} (e : n = n') (s : ℤ)
    (a : HomotopyGroup n (T.stageAt s)) :
    towerHomMap φ n' s
      (Eq.mp (congrArg (fun k => HomotopyGroup k (T.stageAt s)) e) a) =
    Eq.mp (congrArg (fun k => HomotopyGroup k (U.stageAt s)) e)
      (towerHomMap φ n s a) := by
  subst n'
  rfl

private theorem towerSSDataMorphism_cycle_value
    (F : SSDataMorphism (ℤ × ℤ) (towerSSData T) (towerSSData U))
    (hF : ∀ p, F.φ p = ModuleCat.ofHom (towerCycleMap φ p))
    (p : ℤ × ℤ) (r : WithTop ℕ)
    (z : (Subobject.underlying.obj ((towerSSData T p).Z r) : ModuleCat ℤ)) :
    (((towerSSData U p).Z r).arrow (F.cycleMap p r z)).val =
      towerE1Map φ p ((((towerSSData T p).Z r).arrow z).val) := by
  have h := ConcreteCategory.congr_hom (F.cycleMap_arrow p r) z
  rw [hF p] at h
  exact congrArg Subtype.val h

private theorem towerSSDataMorphism_page_value
    (F : SSDataMorphism (ℤ × ℤ) (towerSSData T) (towerSSData U))
    (p : ℤ × ℤ) (r : WithTop ℕ)
    (z : (Subobject.underlying.obj ((towerSSData T p).Z r) : ModuleCat ℤ)) :
    F.pageMap p r ((towerSSData T p).pageπ r z) =
      (towerSSData U p).pageπ r (F.cycleMap p r z) :=
  ConcreteCategory.congr_hom (F.pageπ_pageMap p r) z

private theorem towerSSDataMorphism_layerCycle
    (F : SSDataMorphism (ℤ × ℤ) (towerSSData T) (towerSSData U))
    (hF : ∀ p, F.φ p = ModuleCat.ofHom (towerCycleMap φ p))
    (p : ℤ × ℤ) (n : ℕ)
    (a : HomotopyGroup (p.2-p.1) (T.stageAt p.1)) :
    F.cycleMap p n (layerCycle T p n a) =
      layerCycle U p n (towerHomMap φ (p.2-p.1) p.1 a) := by
  apply cycleRep_injective U p n
  change (((towerSSData U p).Z n).arrow (F.cycleMap p n (layerCycle T p n a))).val = _
  rw [towerSSDataMorphism_cycle_value φ F hF]
  change towerE1Map φ p (cycleRep T p n (layerCycle T p n a)) = _
  rw [cycleRep_layerCycle, cycleRep_layerCycle, towerJ_natural]

private theorem towerSSDataMorphism_layerPage
    (F : SSDataMorphism (ℤ × ℤ) (towerSSData T) (towerSSData U))
    (hF : ∀ p, F.φ p = ModuleCat.ofHom (towerCycleMap φ p))
    (p : ℤ × ℤ) (n : ℕ)
    (a : HomotopyGroup (p.2-p.1) (T.stageAt p.1)) :
    F.pageMap p n (layerPage T p n a) =
      layerPage U p n (towerHomMap φ (p.2-p.1) p.1 a) := by
  change F.pageMap p n ((towerSSData T p).pageπ n (layerCycle T p n a)) = _
  rw [towerSSDataMorphism_page_value F, towerSSDataMorphism_layerCycle φ F hF]
  rfl

private theorem towerSSDataMorphism_differential
    (F : SSDataMorphism (ℤ × ℤ) (towerSSData T) (towerSSData U))
    (hF : ∀ p, F.φ p = ModuleCat.ofHom (towerCycleMap φ p))
    (r : ℤ) (p : ℤ × ℤ) :
    F.pageMap p (↑(r-2).toNat : WithTop ℕ) ≫ towerD U r p =
      towerD T r p ≫ F.pageMap (p+(r,r-1)) (↑(r-2).toNat : WithTop ℕ) := by
  by_cases hr : 2 ≤ r
  · let n := (r-2).toNat
    letI : Epi ((towerSSData T p).pageπ (↑n : WithTop ℕ)) := by
      dsimp only [SSData.pageπ]; infer_instance
    apply (cancel_epi ((towerSSData T p).pageπ (↑n : WithTop ℕ))).mp
    ext z
    change towerD U r p (F.pageMap p n ((towerSSData T p).pageπ n z)) =
      F.pageMap (p+(r,r-1)) n (towerD T r p ((towerSSData T p).pageπ n z))
    rw [towerSSDataMorphism_page_value F, towerD_pageπ U r hr p, towerD_pageπ T r hr p]
    let a := cycleLiftAt T r hr p z
    have ha : towerI U (p.2-p.1-1) (p.1+1) (p.1+r) (by omega)
        (towerHomMap φ (p.2-p.1-1) (p.1+r) a) =
        U.connecting p (cycleRep U p n (F.cycleMap p n z)) := by
      rw [towerI_natural, cycleLiftAt_spec]
      change towerHomMap φ (p.2-p.1-1) (p.1+1) (T.connecting p (cycleRep T p n z)) = _
      rw [← towerK_natural]
      exact congrArg (U.connecting p) (towerSSDataMorphism_cycle_value φ F hF p n z).symm
    rw [differentialValue_of_lift U r hr p (F.cycleMap p n z)
      (towerHomMap φ (p.2-p.1-1) (p.1+r) a) ha]
    change layerPage U (p+(r,r-1)) n
        (degreeCast _ (towerHomMap φ (p.2-p.1-1) (p.1+r) a)) =
      F.pageMap (p+(r,r-1)) n (layerPage T (p+(r,r-1)) n (degreeCast _ a))
    rw [towerSSDataMorphism_layerPage φ F hF]
    apply congrArg (layerPage U (p+(r,r-1)) n)
    simp only [degreeCast_apply]
    exact (towerHomMap_cast φ (by dsimp; omega) (p.1+r) a).symm
  · simp only [towerD, dif_neg hr, comp_zero, zero_comp]

section
attribute [local irreducible] towerSSData

private def towerSequenceMorphism
    (F : SSDataMorphism (ℤ × ℤ) (towerSSData T) (towerSSData U))
    (hd : ∀ (r : ℤ) (p : ℤ × ℤ),
      F.pageMap p (↑(r-2).toNat : WithTop ℕ) ≫ towerD U r p =
        towerD T r p ≫ F.pageMap (p+(r,r-1)) (↑(r-2).toNat : WithTop ℕ)) :
    SpectralSequenceMorphism (towerSequence T) (towerSequence U) where
  φ := F.φ
  preserves_Z := F.preserves_Z
  preserves_B := F.preserves_B
  r₀_eq := rfl
  diffDeg_eq := rfl
  comm_d r p := by
    change F.pageMapAt (E := towerPreSS T) (E' := towerPreSS U)
      rfl r p ≫ _ = _ ≫ F.pageMapAt (E := towerPreSS T) (E' := towerPreSS U) rfl r _ ≫ _
    simp only [SSDataMorphism.pageMapAt, eqToHom_refl, Category.comp_id]
    exact hd r p

end

private def towerSequenceMap :
    SpectralSequenceMorphism (towerSequence T) (towerSequence U) :=
  towerSequenceMorphism (towerSSDataMap φ)
    (towerSSDataMorphism_differential φ (towerSSDataMap φ) (fun _ => rfl))

private def canonicalSequenceMap (unit : SphereSpectrum ⟶ H) (f : X ⟶ Y) :
    SpectralSequenceMorphism (canonicalSequence unit X) (canonicalSequence unit Y) :=
  towerSequenceMap (canonicalTowerMap unit f)

end
end KIP126.AdamsSynthetic.Internal.Source
