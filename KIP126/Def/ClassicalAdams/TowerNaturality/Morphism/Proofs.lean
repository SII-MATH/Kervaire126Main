module

public import KIP126.Def.ClassicalAdams.TowerNaturality.Differential.Proofs

@[expose] public section

/-! The morphism of Adams spectral sequences induced by the specified tower
maps. Its naturality laws follow from those maps. -/
namespace KIP126.Classical.Adams
open CategoryTheory MonoidalCategory KIP126.StableHomotopy KIP126.SpectralSequence
universe u v
set_option backward.isDefEq.respectTransparency false
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : 𝟙_ C ⟶ H)
  {X Y : C} (f : X ⟶ Y)

private theorem submodule_lift_exists {R : Type*} [Ring R] {M N : ModuleCat.{v} R}
    (U : Submodule R M) (V : Submodule R N) (g : M →ₗ[R] N)
    (hg : ∀ a ∈ U, g a ∈ V) :
    ∃ lift : Subobject.underlying.obj ((ModuleCat.subobjectModule M).symm U) ⟶
        Subobject.underlying.obj ((ModuleCat.subobjectModule N).symm V),
      lift ≫ ((ModuleCat.subobjectModule N).symm V).arrow =
        ((ModuleCat.subobjectModule M).symm U).arrow ≫ ModuleCat.ofHom g := by
  let l := (g.comp U.subtype).codRestrict V (fun a => hg a a.property)
  refine ⟨(submoduleUnderlyingIso U).hom ≫ ModuleCat.ofHom l ≫
    (submoduleUnderlyingIso V).inv, ?_⟩
  apply (cancel_epi (submoduleUnderlyingIso U).inv).mp
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  change ModuleCat.ofHom l ≫ (Subobject.underlyingIso (ModuleCat.ofHom V.subtype)).inv ≫
      (Subobject.mk (ModuleCat.ofHom V.subtype)).arrow =
    (Subobject.underlyingIso (ModuleCat.ofHom U.subtype)).inv ≫
      (Subobject.mk (ModuleCat.ofHom U.subtype)).arrow ≫ ModuleCat.ofHom g
  rw [Subobject.underlyingIso_arrow, Subobject.underlyingIso_arrow_assoc]
  rfl

theorem adamsTowerSSDataMorphism_exists :
    ∃ F : SSDataMorphism (ℤ × ℤ)
        (fun p : ℤ × ℤ => adamsTowerSSData unit X p.1 p.2)
        (fun p : ℤ × ℤ => adamsTowerSSData unit Y p.1 p.2),
      ∀ p, F.φ p = ModuleCat.ofHom (adamsCycleInduced unit f 2 (Nat.le_succ 1) p.1 p.2) := by
  refine ⟨{ φ := fun p => ModuleCat.ofHom (adamsCycleInduced unit f 2 (Nat.le_succ 1) p.1 p.2)
            preserves_Z := ?_
            preserves_B := ?_ }, fun _ => rfl⟩
  · intro p r
    exact submodule_lift_exists _ _ _ (fun _ ha => adamsCycleInduced_mem_cycleSubmodule unit f p.1 p.2 r ha)
  · intro p r
    exact submodule_lift_exists _ _ _ (fun _ ha => adamsCycleInduced_mem_boundarySubmodule unit f p.1 p.2 r ha)

theorem adamsTowerSSDataMorphism_page_comparison
    (F : SSDataMorphism (ℤ × ℤ)
      (fun p : ℤ × ℤ => adamsTowerSSData unit X p.1 p.2)
      (fun p : ℤ × ℤ => adamsTowerSSData unit Y p.1 p.2))
    (hF : ∀ p, F.φ p = ModuleCat.ofHom (adamsCycleInduced unit f 2 (Nat.le_succ 1) p.1 p.2))
    (p : ℤ × ℤ) (m : ℕ) :
    F.pageMap p (m : WithTop ℕ) ≫ (adamsTowerSSDataPageIso unit Y p.1 p.2 m).hom =
      (adamsTowerSSDataPageIso unit X p.1 p.2 m).hom ≫
        ModuleCat.ofHom (adamsPageInduced unit f (m+2) (by omega) p.1 p.2) := by
  let U := adamsFiniteCycleSubmodule unit X p.1 p.2 m
  let V := adamsFiniteCycleSubmodule unit Y p.1 p.2 m
  let eU := submoduleUnderlyingIso (M := ModuleCat.of ℤ (adamsCycleAmbient unit X p.1 p.2)) U
  let eV := submoduleUnderlyingIso (M := ModuleCat.of ℤ (adamsCycleAmbient unit Y p.1 p.2)) V
  let g := ((adamsCycleInduced unit f 2 (Nat.le_succ 1) p.1 p.2).comp U.subtype).codRestrict V
    (fun a => adamsE1Induced_mem_cycles unit f (m+2) (by omega) p.1 p.2 a.property)
  letI : Mono (ModuleCat.ofHom U.subtype) :=
    (ModuleCat.mono_iff_injective _).mpr Subtype.val_injective
  letI : Mono (ModuleCat.ofHom V.subtype) :=
    (ModuleCat.mono_iff_injective _).mpr Subtype.val_injective
  have hc : eU.inv ≫ F.cycleMap p (m : WithTop ℕ) = ModuleCat.ofHom g ≫ eV.inv := by
    apply (cancel_mono (((adamsTowerSSData unit Y p.1 p.2).Z (m : WithTop ℕ)).arrow)).mp
    have h := F.cycleMap_arrow p (m : WithTop ℕ)
    rw [hF] at h
    have hu : eU.inv ≫ ((adamsTowerSSData unit X p.1 p.2).Z (m : WithTop ℕ)).arrow =
        ModuleCat.ofHom U.subtype := Subobject.underlyingIso_arrow _
    have hv : eV.inv ≫ ((adamsTowerSSData unit Y p.1 p.2).Z (m : WithTop ℕ)).arrow =
        ModuleCat.ofHom V.subtype := Subobject.underlyingIso_arrow _
    calc
      _ = eU.inv ≫ ((adamsTowerSSData unit X p.1 p.2).Z (m : WithTop ℕ)).arrow ≫
          ModuleCat.ofHom (adamsCycleInduced unit f 2 (Nat.le_succ 1) p.1 p.2) := by
        rw [Category.assoc, h]
      _ = ModuleCat.ofHom U.subtype ≫ ModuleCat.ofHom
          (adamsCycleInduced unit f 2 (Nat.le_succ 1) p.1 p.2) := by rw [← Category.assoc, hu]
      _ = ModuleCat.ofHom g ≫ ModuleCat.ofHom V.subtype := rfl
      _ = _ := by rw [Category.assoc, hv]
  letI : Epi ((adamsTowerSSData unit X p.1 p.2).pageπ (m : WithTop ℕ)) :=
    inferInstanceAs (Epi (CategoryTheory.Limits.cokernel.π _))
  apply (cancel_epi ((adamsTowerSSData unit X p.1 p.2).pageπ (m : WithTop ℕ))).mp
  apply (cancel_epi eU.inv).mp
  rw [F.pageπ_pageMap_assoc p (m : WithTop ℕ), ← Category.assoc eU.inv, hc]
  simp only [Category.assoc]
  rw [adamsTowerSSDataPageIso_π]
  have hp := congrArg (fun k => k ≫ ModuleCat.ofHom
    (adamsPageInduced unit f (m+2) (by omega) p.1 p.2))
    (adamsTowerSSDataPageIso_π unit X p.1 p.2 m)
  have he : ModuleCat.ofHom g ≫ ModuleCat.ofHom
      ((adamsCycleBoundaries unit Y (m+2) (by omega) p.1 p.2).mkQ.comp
        (adamsFiniteCycleEquiv unit Y p.1 p.2 m).toLinearMap) =
      ModuleCat.ofHom ((adamsCycleBoundaries unit X (m+2) (by omega) p.1 p.2).mkQ.comp
        (adamsFiniteCycleEquiv unit X p.1 p.2 m).toLinearMap) ≫
      ModuleCat.ofHom (adamsPageInduced unit f (m+2) (by omega) p.1 p.2) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply congrArg (adamsCycleBoundaries unit Y (m+2) (by omega) p.1 p.2).mkQ
    apply Subtype.ext
    rfl
  exact he.trans (by simpa only [Category.assoc] using hp.symm)



variable (F : SSDataMorphism (ℤ × ℤ)
    (fun p : ℤ × ℤ => adamsTowerSSData unit X p.1 p.2)
    (fun p : ℤ × ℤ => adamsTowerSSData unit Y p.1 p.2))
  (hF : ∀ p, F.φ p = ModuleCat.ofHom (adamsCycleInduced unit f 2 (Nat.le_succ 1) p.1 p.2))

include hF

theorem adamsTowerSSDataMorphism_internalD (m : ℕ) (s t : ℤ) :
    F.pageMap (s,t) (m : WithTop ℕ) ≫ adamsTowerInternalD unit Y m s t =
      adamsTowerInternalD unit X m s t ≫ F.pageMap (s+(m+2:ℕ),t+(m+2:ℕ)-1) (m : WithTop ℕ) := by
  apply (cancel_mono (adamsTowerSSDataPageIso unit Y (s+(m+2:ℕ)) (t+(m+2:ℕ)-1) m).hom).mp
  simp only [Category.assoc]
  rw [adamsTowerInternalD_comparison, ← Category.assoc,
    adamsTowerSSDataMorphism_page_comparison unit f F hF]
  rw [adamsTowerSSDataMorphism_page_comparison unit f F hF,
    ← Category.assoc, adamsTowerInternalD_comparison]
  simp only [Category.assoc]
  congr 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  exact (adamsPageInduced_differential unit f (m+2) (by omega) s t a).symm

theorem adamsTowerSSDataMorphism_internalD_reindex (m : ℕ) (s t a b : ℤ)
    (ha : s+(m+2:ℕ) = a) (hb : t+(m+2:ℕ)-1 = b) :
    F.pageMap (s,t) (m : WithTop ℕ) ≫ adamsTowerInternalD unit Y m s t ≫
      eqToHom (show (adamsTowerSSData unit Y (s+(m+2:ℕ)) (t+(m+2:ℕ)-1)).page ↑m =
        (adamsTowerSSData unit Y a b).page ↑m by rw [ha,hb]) =
    adamsTowerInternalD unit X m s t ≫
      eqToHom (show (adamsTowerSSData unit X (s+(m+2:ℕ)) (t+(m+2:ℕ)-1)).page ↑m =
        (adamsTowerSSData unit X a b).page ↑m by rw [ha,hb]) ≫ F.pageMap (a,b) (m : WithTop ℕ) := by
  subst a
  subst b
  simpa only [eqToHom_refl, Category.comp_id, Category.id_comp] using
    adamsTowerSSDataMorphism_internalD unit f F hF m s t

section
attribute [local irreducible] adamsTowerSSData
omit hF in
private theorem spectralSequenceMorphism_of_internalD
    (hd : ∀ (m : ℕ) (s t a b : ℤ)
      (ha : s+(m+2:ℕ) = a) (hb : t+(m+2:ℕ)-1 = b),
    F.pageMap (s,t) (m : WithTop ℕ) ≫ adamsTowerInternalD unit Y m s t ≫
      eqToHom (show (adamsTowerSSData unit Y (s+(m+2:ℕ)) (t+(m+2:ℕ)-1)).page ↑m =
        (adamsTowerSSData unit Y a b).page ↑m by rw [ha,hb]) =
    adamsTowerInternalD unit X m s t ≫
      eqToHom (show (adamsTowerSSData unit X (s+(m+2:ℕ)) (t+(m+2:ℕ)-1)).page ↑m =
        (adamsTowerSSData unit X a b).page ↑m by rw [ha,hb]) ≫ F.pageMap (a,b) (m : WithTop ℕ)) :
    ∃ G : SpectralSequenceMorphism (adamsTowerInternalSpectralSequence unit X)
        (adamsTowerInternalSpectralSequence unit Y),
      G.toSSDataMorphism = F := by
  refine ⟨{ φ := F.φ
            preserves_Z := F.preserves_Z
            preserves_B := F.preserves_B
            r₀_eq := rfl
            diffDeg_eq := rfl
            comm_d := ?_ }, rfl⟩
  intro r p
  change F.pageMapAt (E := adamsTowerPreSS unit X) (E' := adamsTowerPreSS unit Y) rfl r p ≫ _ =
    _ ≫ F.pageMapAt (E := adamsTowerPreSS unit X) (E' := adamsTowerPreSS unit Y) rfl r _ ≫ _
  simp only [SSDataMorphism.pageMapAt, eqToHom_refl, Category.comp_id]
  change F.pageMap p (↑(r-2).toNat : WithTop ℕ) ≫ (adamsTowerPreSS unit Y).d r p =
    (adamsTowerPreSS unit X).d r p ≫ F.pageMap (p+(r,r-1)) (↑(r-2).toNat : WithTop ℕ)
  by_cases hr : 2 ≤ r
  · rw [adamsTowerPreSS_d_eq unit Y r p hr, adamsTowerPreSS_d_eq unit X r p hr]
    have hq : (((r-2).toNat+2:ℕ):ℤ) = r := by omega
    exact hd (r-2).toNat p.1 p.2
      (p+(r,r-1)).1 (p+(r,r-1)).2 (by dsimp; omega) (by dsimp; omega)
  · have hx : (adamsTowerPreSS unit X).d r p = 0 := dif_neg hr
    have hy : (adamsTowerPreSS unit Y).d r p = 0 := dif_neg hr
    rw [hx, hy, CategoryTheory.Limits.comp_zero, CategoryTheory.Limits.zero_comp]

end

/-- The actual spectrum map gives a morphism of the already constructed
Adams spectral sequences, with the prescribed ambient map. -/
theorem adamsTowerSpectralSequenceMorphism_exists :
    ∃ G : SpectralSequenceMorphism (adamsTowerInternalSpectralSequence unit X)
        (adamsTowerInternalSpectralSequence unit Y),
      G.toSSDataMorphism = F := by
  exact spectralSequenceMorphism_of_internalD unit F
    (adamsTowerSSDataMorphism_internalD_reindex unit f F hF)

end KIP126.Classical.Adams
