module

public import KIP126.Literature.Standard

@[expose] section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace KIP126.Literature.TmfConvergenceProbe
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.Classical.Adams

open KIP126.AdamsSynthetic.Standard (model Spectrum)
open KIP126.Literature.Standard (tmf tmfIso)

public def directCandidate : ClassicalTowerConvergence model.classicalTower tmf := by
  let e : tmf ≅ model.auxiliary.detector := tmfIso
  let c : ClassicalTowerConvergence model.classicalTower model.auxiliary.detector :=
    model.classicalConvergence .detector
  have tmf_filtration_map {X Y : Spectrum} (f : X ⟶ Y) (s m : ℤ) (x : HomotopyGroup m X)
      (hx : x ∈ (model.classicalTower.tower X).filtrationSubmodule s m) :
      x ≫ f ∈ (model.classicalTower.tower Y).filtrationSubmodule s m := by
    obtain ⟨a, rfl⟩ := hx
    refine ⟨a ≫ (model.classicalTower.map f).stage s.toNat, ?_⟩
    change (a ≫ (model.classicalTower.map f).stage s.toNat) ≫ (model.classicalTower.tower Y).projection s =
      (a ≫ (model.classicalTower.tower X).projection s) ≫ f
    rw [Category.assoc, (model.classicalTower.map f).projection s, ← Category.assoc]

  have tmf_filtration_iso_mem {X Y : Spectrum} (e : X ≅ Y) (s m : ℤ)
      (x : AbstractAdamsTower.homotopy X m) :
      x ≫ e.hom ∈
          ModuleCat.subobjectModule _ ((model.classicalTower.tower Y).filtration.F s m) ↔
        x ∈ ModuleCat.subobjectModule _ ((model.classicalTower.tower X).filtration.F s m) := by
    simp (config := { congrConsts := false }) only [AbstractAdamsTower.filtration, OrderIso.apply_symm_apply]
    change x ≫ e.hom ∈ (model.classicalTower.tower Y).filtrationSubmodule s m ↔
      x ∈ (model.classicalTower.tower X).filtrationSubmodule s m
    constructor
    · intro hx
      simpa (config := { congrConsts := false }) only [Category.assoc, e.hom_inv_id, Category.comp_id] using
        tmf_filtration_map e.inv s m (x ≫ e.hom) hx
    · exact tmf_filtration_map e.hom s m x

  have tmf_quotient_iso {R : Type} [Ring R] {M N : ModuleCat.{0} R}
      (B Z : Subobject M) (B' Z' : Subobject N) (h : B ≤ Z) (h' : B' ≤ Z')
      (e : M ≃ₗ[R] N)
      (hB : ∀ x, e x ∈ (ModuleCat.subobjectModule N) B' ↔ x ∈ (ModuleCat.subobjectModule M) B)
      (hZ : ∀ x, e x ∈ (ModuleCat.subobjectModule N) Z' ↔ x ∈ (ModuleCat.subobjectModule M) Z) :
      ∃ q : cokernel (Subobject.ofLE B Z h) ≅ cokernel (Subobject.ofLE B' Z' h'),
        ∀ a : (Subobject.underlying.obj Z : ModuleCat R),
          ∃ b : (Subobject.underlying.obj Z' : ModuleCat R),
            Z'.arrow b = e (Z.arrow a) ∧
            q.hom (cokernel.π (Subobject.ofLE B Z h) a) =
              cokernel.π (Subobject.ofLE B' Z' h') b := by
    have restrict (S : Subobject M) (T : Subobject N)
        (he : ∀ x, e x ∈ (ModuleCat.subobjectModule N) T ↔ x ∈ (ModuleCat.subobjectModule M) S) :
        ∃ w : Subobject.underlying.obj S ≅ Subobject.underlying.obj T,
          ∀ a, T.arrow (w.hom a) = e (S.arrow a) := by
      let a := LinearEquiv.ofInjective S.arrow.hom ((ModuleCat.mono_iff_injective _).mp inferInstance)
      let b := LinearEquiv.ofInjective T.arrow.hom ((ModuleCat.mono_iff_injective _).mp inferInstance)
      have hm : ((ModuleCat.subobjectModule M) S).map e.toLinearMap =
          (ModuleCat.subobjectModule N) T := by
        ext y
        constructor
        · rintro ⟨x, hx, rfl⟩
          exact (he x).2 hx
        · intro hy
          refine ⟨e.symm y, (he (e.symm y)).1 ?_, e.apply_symm_apply y⟩
          simpa (config := { congrConsts := false }) only [e.apply_symm_apply] using hy
      let c := e.ofSubmodules ((ModuleCat.subobjectModule M) S) ((ModuleCat.subobjectModule N) T) hm
      refine ⟨((a.trans c).trans b.symm).toModuleIso, ?_⟩
      intro x
      exact congrArg Subtype.val (b.apply_symm_apply (c (a x)))
    obtain ⟨b, hb⟩ := restrict B B' hB
    obtain ⟨z, hz⟩ := restrict Z Z' hZ
    have comm : Subobject.ofLE B Z h ≫ z.hom = b.hom ≫ Subobject.ofLE B' Z' h' := by
      apply (cancel_mono Z'.arrow).1
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change Z'.arrow (z.hom (Subobject.ofLE B Z h x)) =
        Z'.arrow (Subobject.ofLE B' Z' h' (b.hom x))
      rw [hz]
      have hs := congrArg (fun f => f.hom x) (Subobject.ofLE_arrow h)
      have ht := congrArg (fun f => f.hom (b.hom x)) (Subobject.ofLE_arrow h')
      change Z.arrow (Subobject.ofLE B Z h x) = B.arrow x at hs
      change Z'.arrow (Subobject.ofLE B' Z' h' (b.hom x)) = B'.arrow (b.hom x) at ht
      rw [hs, ht, hb]
    let q := cokernel.mapIso (Subobject.ofLE B Z h) (Subobject.ofLE B' Z' h') b z comm
    refine ⟨q, fun a => ⟨z.hom a, hz a, ?_⟩⟩
    have hq : cokernel.π (Subobject.ofLE B Z h) ≫ q.hom =
        z.hom ≫ cokernel.π (Subobject.ofLE B' Z' h') := by
      simp (config := { congrConsts := false }) only [q, cokernel.mapIso_hom, cokernel.map, cokernel.π_desc]
    exact congrArg (fun f => f.hom a) hq
  let homotopyIso (m : ℤ) :
      AbstractAdamsTower.homotopy tmf m ≅ AbstractAdamsTower.homotopy model.auxiliary.detector m := {
    hom := ModuleCat.ofHom (inducedMap e.hom m).toIntLinearMap
    inv := ModuleCat.ofHom (inducedMap e.inv m).toIntLinearMap
    hom_inv_id := by
      ext a
      change (a ≫ e.hom) ≫ e.inv = a
      simp (config := { congrConsts := false }) only [Category.assoc, e.hom_inv_id, Category.comp_id]
    inv_hom_id := by
      ext a
      change (a ≫ e.inv) ≫ e.hom = a
      simp (config := { congrConsts := false }) only [Category.assoc, e.inv_hom_id, Category.comp_id] }
  let infinityIso (p : ℤ × ℤ) :
      ((model.classical.obj tmf).ssData p).eInfty ≅ ((model.classical.obj model.auxiliary.detector).ssData p).eInfty := {
    hom := (model.classical.map e.hom).eInftyMap p
    inv := (model.classical.map e.inv).eInftyMap p
    hom_inv_id := by
      rw [← SpectralSequenceMorphism.eInftyMap_comp, ← model.classical.map_comp, e.hom_inv_id,
        model.classical.map_id, SpectralSequenceMorphism.eInftyMap_id]
    inv_hom_id := by
      rw [← SpectralSequenceMorphism.eInftyMap_comp, ← model.classical.map_comp, e.inv_hom_id,
        model.classical.map_id, SpectralSequenceMorphism.eInftyMap_id] }
  have gr (s m : ℤ) :
      ∃ q : (model.classicalTower.tower tmf).filtration.associatedGraded s m ≅
        (model.classicalTower.tower model.auxiliary.detector).filtration.associatedGraded s m,
        ∀ b : (Subobject.underlying.obj ((model.classicalTower.tower tmf).filtration.F s m) : ModuleCat ℤ),
          ∃ b' : (Subobject.underlying.obj ((model.classicalTower.tower model.auxiliary.detector).filtration.F s m) : ModuleCat ℤ),
            ((model.classicalTower.tower model.auxiliary.detector).filtration.F s m).arrow b' =
              ((model.classicalTower.tower tmf).filtration.F s m).arrow b ≫ e.hom ∧
            q.hom ((model.classicalTower.tower tmf).filtration.toAssociatedGraded s m b) =
              (model.classicalTower.tower model.auxiliary.detector).filtration.toAssociatedGraded s m b' := by
    exact tmf_quotient_iso
      ((model.classicalTower.tower tmf).filtration.F (s+1) m) ((model.classicalTower.tower tmf).filtration.F s m)
      ((model.classicalTower.tower model.auxiliary.detector).filtration.F (s+1) m) ((model.classicalTower.tower model.auxiliary.detector).filtration.F s m)
      ((model.classicalTower.tower tmf).filtration.mono s m) ((model.classicalTower.tower model.auxiliary.detector).filtration.mono s m)
      (homotopyIso m).toLinearEquiv
      (tmf_filtration_iso_mem e (s+1) m) (tmf_filtration_iso_mem e s m)
  let q := fun s m => (gr s m).choose
  refine ⟨fun p => infinityIso p ≪≫ c.identification p ≪≫ (q p.1 (p.2-p.1)).symm, ?_⟩
  intro p a z hz b hb
  let z' := (model.classical.map e.hom).toSSDataMorphism.cycleMap p ⊤ z
  let a' := a ≫ (model.classicalTower.map e.hom).stage p.1.toNat
  obtain ⟨b', hb', hq⟩ := (gr p.1 (p.2-p.1)).choose_spec b
  have hz' : (model.classicalTower.sequence model.auxiliary.detector).infiniteRepresentativeE1 p z' =
      (model.classicalTower.tower model.auxiliary.detector).layerMap p a' := by
    have hc := congrArg (fun f => f.hom z)
      ((model.classical.map e.hom).toSSDataMorphism.cycleMap_arrow p ⊤)
    change (((model.classical.obj model.auxiliary.detector).ssData p).Z ⊤).arrow z' =
      (model.classical.map e.hom).φ p ((((model.classical.obj tmf).ssData p).Z ⊤).arrow z) at hc
    unfold TowerSequencePresentation.infiniteRepresentativeE1
    rw [hc, model.classicalTower.natural]
    change (model.classicalTower.sequence tmf).infiniteRepresentativeE1 p z ≫ (model.classicalTower.map e.hom).layer p.1 =
      (model.classicalTower.tower model.auxiliary.detector).layerMap p a'
    rw [hz]
    change (a ≫ HasFunctorialCofiber.cofibι _) ≫ (model.classicalTower.map e.hom).layer p.1 =
      (a ≫ (model.classicalTower.map e.hom).stage p.1.toNat) ≫ HasFunctorialCofiber.cofibι _
    dsimp only [TowerMap.layer]
    rw [Category.assoc, ← HasFunctorialCofiber.cofibMap_ι, ← Category.assoc]
  have hb'' : ((model.classicalTower.tower model.auxiliary.detector).filtration.F p.1 (p.2-p.1)).arrow b' =
      a' ≫ (model.classicalTower.tower model.auxiliary.detector).projection p.1 := by
    rw [hb', hb]
    change (a ≫ (model.classicalTower.tower tmf).projection p.1) ≫ e.hom =
      (a ≫ (model.classicalTower.map e.hom).stage p.1.toNat) ≫ (model.classicalTower.tower model.auxiliary.detector).projection p.1
    simpa (config := { congrConsts := false }) only [Category.assoc] using
      congrArg (fun f => a ≫ f) ((model.classicalTower.map e.hom).projection p.1).symm
  have hc := c.canonical p a' z' hz' b' hb''
  have hpage := congrArg (fun f => f.hom z)
    ((model.classical.map e.hom).toSSDataMorphism.pageπ_pageMap p ⊤)
  change (model.classical.map e.hom).eInftyMap p (((model.classical.obj tmf).ssData p).pageπ ⊤ z) =
    ((model.classical.obj model.auxiliary.detector).ssData p).pageπ ⊤ z' at hpage
  change (q p.1 (p.2-p.1)).inv
      ((c.identification p).hom
        ((model.classical.map e.hom).eInftyMap p (((model.classical.obj tmf).ssData p).pageπ ⊤ z))) = _
  rw [hpage, hc, ← hq]
  exact congrArg (fun f => f.hom ((model.classicalTower.tower tmf).filtration.toAssociatedGraded p.1 (p.2-p.1) b))
    (q p.1 (p.2-p.1)).hom_inv_id


end KIP126.Literature.TmfConvergenceProbe
