module

public import KIP126.Main.Conditions
public import KIP126.Def.ProofTools.Representatives

/-! Detection operations from Selected/DetectionData.lean:167–182,
642–672 and 964–997 at bbac1fc05843 (MIT). The last argument uses the
already proved common-representative transport instead of unfolding the
same subobject calculation again. -/
@[expose] section
namespace KIP126.Main.Internal.Selected
open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence KIP126.AdamsSynthetic
open KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard (model SyntheticSpectrum)
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem detects_infinity_equal (X : SyntheticObject) (i : Tridegree)
    (a : BiHom (i.2.1-i.1) i.2.2 (X.obj model.nu model.auxiliary))
    (x y : (model.family.obj (X.obj model.nu model.auxiliary)).E₂ i)
    (ha : Detects (model.convergence X) i x a)
    (hb : Detects (model.convergence X) i y a) :
    ∃ e, HasInfinityRepresentative (model.family.obj (X.obj model.nu model.auxiliary)) 2 i x e ∧
      HasInfinityRepresentative (model.family.obj (X.obj model.nu model.auxiliary)) 2 i y e := by
  obtain ⟨e,he,a',ha',hga⟩ := ha
  obtain ⟨f,hf,b',hb',hgb⟩ := hb
  have hab : a'=b' := (ModuleCat.mono_iff_injective _).mp inferInstance (ha'.trans hb'.symm)
  have hef : e=f := (ModuleCat.mono_iff_injective _).mp inferInstance (by rw [hga,hgb,hab])
  exact ⟨e,he,hef.symm ▸ hf⟩

theorem theta_detection_step
    (i : Tridegree) (x : model.family.sphere.E₂ i)
    (hframe : ∀ e : (model.family.sphere.sequence.ssData i).eInfty,
      e=0 ∨ HasInfinityRepresentative model.family.sphere 2 i x e)
    (a : BiHom (i.2.1-i.1) i.2.2 (S_0_0 : SyntheticSpectrum))
    (ha : FiltrationAtLeast model.syntheticTower i.1 a) :
    DetectsNonzero (model.convergence .sphere) i x a ∨
      FiltrationAtLeast model.syntheticTower (i.1+1) a := by
  classical
  let F := model.syntheticTower.filtration (S_0_0 : SyntheticSpectrum)
  have ham : a ∈ (ModuleCat.subobjectModule
      (syntheticHomotopy (S_0_0 : SyntheticSpectrum) (i.2.1-i.1,i.2.2)))
      (F.F i.1 (i.2.1-i.1,i.2.2)) := by
    simpa only [F,SyntheticTowerPresentation.filtration,OrderIso.apply_symm_apply,
      FiltrationAtLeast] using ha
  obtain ⟨a',ha'⟩ := ham
  let q := F.toAssociatedGraded i.1 (i.2.1-i.1,i.2.2) a'
  let e := ((model.convergence .sphere).identification i).inv q
  have he : ((model.convergence .sphere).identification i).hom e=q :=
    ConcreteCategory.congr_hom ((model.convergence .sphere).identification i).inv_hom_id q
  by_cases he0 : e=0
  · right
    have hq : F.toAssociatedGraded i.1 (i.2.1-i.1,i.2.2) a'=0 := by
      rw [he0,map_zero] at he
      exact he.symm
    have hmem := (F.toAssociatedGraded_eq_zero_iff i.1 (i.2.1-i.1,i.2.2) a').mp hq
    rw [ha'] at hmem
    simpa only [F,SyntheticTowerPresentation.filtration,OrderIso.apply_symm_apply,
      FiltrationAtLeast] using hmem
  · left
    have hr := (hframe e).resolve_left he0
    exact ⟨⟨e,hr,a',ha',he⟩,e,hr,he0⟩

theorem survives_twelve_not_boundary_eleven (X : ClassicalObject) (p : ℤ × ℤ)
    (x : (model.classical.obj (X.obj model.auxiliary)).Page 2 p)
    (hx : SurvivesTo (model.classical.obj (X.obj model.auxiliary)) 12 p x) :
    x ∉ KIP126.Literature.boundaries model X 11 p := by
  intro hxB
  obtain ⟨xr,hrep,hne⟩ := hx
  have hz : RepresentsOnPage (model.classical.obj (X.obj model.auxiliary)) 12 p x 0 :=
    KIP126.ProofTools.representsOnPage_of_congruent model X (by decide)
      (RepresentsOnPage.zero (by decide))
      ⟨by decide, by simpa only [sub_zero, Int.reduceSub] using hxB⟩
  exact hne (FinitePageCalculus.represents_unique hrep hz)

end
end KIP126.Main.Internal.Selected
