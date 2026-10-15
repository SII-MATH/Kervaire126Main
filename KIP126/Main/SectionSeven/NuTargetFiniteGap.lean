module
public import KIP126.Main.SectionSeven.Predicates
public import KIP126.Def.Literature.Standard.Filtration
import all KIP126.Main.Internal.DetectionLabels
import all KIP126.Main.Internal.LambdaZero
import all KIP126.Main.Internal.QuotientCalculus
import all KIP126.Main.Internal.Selected.InfinityFrames
import all KIP126.Main.Internal.Selected.SphereDetection
import all KIP126.Main.SectionSeven.NuTargetWindows
public import KIP126.Def.Computation.Table
/-! Finite-window gaps and the h₀ error estimate from NuTargetHelpers.lean:
2277–2296,2388–2426,2732–2777, bbac1fc05843 (MIT). -/
@[expose] section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
namespace KIP126.Main.SectionSeven.Internal
open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence KIP126.AdamsSynthetic
open KIP126.Core.SpectralSequence KIP126.Kervaire.Route KIP126.Literature
open KIP126.AdamsSynthetic.Standard KIP126.Main.Internal KIP126.Main.Internal.Selected
open KIP126.ProofTools.Operations
noncomputable section

theorem finite_sphere_zero_of_classical_quotient (q : ℕ) (hq : 0<q) (s t w : ℤ)
    (hw : 0≤t-w ∧ t-w<q)
    (hc : Subsingleton (CycleQuotient model .sphere ((q:ℤ)-t+w) (1+t-w) (s,t))) :
    IsZero (((model.family.quotient (S_0_0 : SyntheticSpectrum) q).sequence.ssData (s,t,w)).eInfty) := by
  let e := KIP126.Literature.Standard.infinityFiniteWindow .sphere q hq (s,t) w hw
  haveI := hc
  haveI : Subsingleton (((model.family.quotient (model.nu.functor.obj SphereSpectrum) q).sequence.ssData (s,t,w)).eInfty) :=
    e.injective.subsingleton
  let hn := ModuleCat.isZero_of_subsingleton
    (((model.family.quotient (model.nu.functor.obj SphereSpectrum) q).sequence.ssData (s,t,w)).eInfty)
  let f := (model.family.map (XModLambdaN.map model.nu.unitIso.hom q)).eInftyMap (s,t,w)
  let g := (model.family.map (XModLambdaN.map model.nu.unitIso.inv q)).eInftyMap (s,t,w)
  have hfg : g ≫ f=𝟙 _ := by
    dsimp only [f,g]
    rw [←SpectralSequenceMorphism.eInftyMap_comp,←SyntheticAdamsFamily.map_comp,
      ←model.quotients.functoriality.map_comp,model.nu.unitIso.inv_hom_id,
      model.quotients.functoriality.map_id,SyntheticAdamsFamily.map_id,SpectralSequenceMorphism.eInftyMap_id]
  apply (CategoryTheory.Limits.IsZero.iff_id_eq_zero _).mpr
  exact hfg.symm.trans (by rw [hn.eq_of_src f 0,CategoryTheory.Limits.comp_zero])

theorem nu_target_finite_error_twice_zero
    (h0 : BiHom 0 1 (S_0_0 : SyntheticSpectrum))
    (hd : Detects (model.convergence .sphere) (1,1,1)
      (sphereLabel 1 1 0 KIP126.Computation.Standard.h0) h0)
    (hgap : cycles model .sphere 3 (12,137) ≤ boundaries model .sphere 7 (12,137))
    (hprod : ∀ x : model.classical.sphere.Page 2 (13,138),
      model.sphereAlgebra.product (1,1) (13,138) KIP126.Computation.Standard.h0 x ∈ boundaries model .sphere 2 (14,139))
    (a : BiHom 125 131 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9))
    (ha : FiltrationAtLeast model.syntheticTower 12 a) :
    lambdaMultiply 1 (sphereAction h0 a)=0 := by
  have hc : Subsingleton (CycleQuotient model .sphere 3 7 (12,137)) := by
    apply subsingleton_of_forall_eq 0
    intro z
    obtain ⟨z,rfl⟩ := Quotient.exists_rep z
    exact (subquotientClass_eq_zero_iff _ _ z).mpr (hgap z.property)
  have hg : FiltrationAtLeast model.syntheticTower 12 a ↔
      FiltrationAtLeast model.syntheticTower 13 a := by
    apply filtration_iff_of_infinity_zero (model.convergence (.quotient 9 .sphere)) 12 13 125 131 (by decide)
    intro j hj hj'
    have : j=12 := by omega
    subst j
    exact finite_sphere_zero_of_classical_quotient 9 (by decide) 12 137 131 (by norm_num) hc
  obtain ⟨x,_,hx⟩ := finite_sphere_filtration_has_cycle_label 9 7 (by decide) (by decide) 13 138 a (hg.mp ha)
  have hdprod := KIP126.Literature.Standard.finite_action 9 (by decide) 1 1 13 138 0 7
    KIP126.Computation.Standard.h0 x h0 a hd hx
  let z : model.classical.sphere.Page 2 (14,139) :=
    model.sphereAlgebra.product (1,1) (13,138) KIP126.Computation.Standard.h0 x
  have hb : z∈boundaries model .sphere 8 (14,139) :=
    boundaries_monotone model .sphere (14,139) (by decide : (2:ℤ)≤8) (hprod x)
  have hz := finite_sphere_boundary_detects_zero 9 7 (by decide) (by decide) 14 139 z hb
  have he : FiltrationAtLeast model.syntheticTower 15 (sphereAction h0 a) := by
    simpa only [sub_zero, homotopyRegrade, Int.reduceAdd, Int.reduceSub, SyntheticObject.obj] using
      detects_sub_filtration (model.convergence (.quotient 9 .sphere)) (14,139,132) hdprod hz
  have hf := lambda_filtration_preserved 1 15 (sphereAction h0 a) he
  exact sphere_quotient_high_filtration_zero 9 (by decide) 125 131 15 (by decide)
    (lambdaMultiply 1 (sphereAction h0 a)) hf

theorem nu_nine_h0x_gap
    (a : BiHom 122 127 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9)) :
    FiltrationAtLeast model.syntheticTower 9 a ↔ FiltrationAtLeast model.syntheticTower 11 a := by
  apply filtration_iff_of_infinity_zero (model.convergence (.quotient 9 .sphere)) 9 11 122 127 (by decide)
  intro j hj hj'
  have hc : Subsingleton (model.classical.sphere.Page 2 (j,122+j)) := by
    have hjs : j=9 ∨ j=10 := by omega
    rcases hjs with rfl|rfl
    · obtain ⟨e,_⟩ := KIP126.Computation.Table.basis_correct ⟨.sphere,9,131,[]⟩ (by
        exact List.mem_of_getElem? (l := KIP126.Computation.Table.Raw.degrees) (i := 170) rfl)
      change model.classical.sphere.Page 2 (9,131) ≃ₗ[ℤ] (Fin 0 →₀ ZMod 2) at e
      exact e.injective.subsingleton
    · obtain ⟨e,_⟩ := KIP126.Computation.Table.basis_correct ⟨.sphere,10,132,[]⟩ (by
        exact List.mem_of_getElem? (l := KIP126.Computation.Table.Raw.degrees) (i := 179) rfl)
      change model.classical.sphere.Page 2 (10,132) ≃ₗ[ℤ] (Fin 0 →₀ ZMod 2) at e
      exact e.injective.subsingleton
  haveI : Subsingleton ((model.classical.obj (ClassicalObject.sphere.obj model.auxiliary)).Page 2 (j,122+j)) := hc
  apply finite_sphere_zero_of_classical_quotient 9 (by decide) j (122+j) 127
    (by constructor <;> omega)
  infer_instance

theorem detected_filtration (O : SyntheticObject) (i : Tridegree)
    {x : (model.family.obj (O.obj model.nu model.auxiliary)).E₂ i}
    {a : BiHom (i.2.1-i.1) i.2.2 (O.obj model.nu model.auxiliary)}
    (ha : Detects (model.convergence O) i x a) :
    FiltrationAtLeast model.syntheticTower i.1 a := by
  obtain ⟨_,_,a',ha',_⟩ := ha
  have hm : ((model.syntheticTower.filtration (O.obj model.nu model.auxiliary)).F i.1 (i.2.1-i.1,i.2.2)).arrow a' ∈
      ModuleCat.subobjectModule _ ((model.syntheticTower.filtration (O.obj model.nu model.auxiliary)).F i.1 (i.2.1-i.1,i.2.2)) := ⟨a',rfl⟩
  rw [ha'] at hm
  simpa only [SyntheticTowerPresentation.filtration,OrderIso.apply_symm_apply,FiltrationAtLeast] using hm

theorem nu_target_h0x_filtration
    (h0 : BiHom 0 1 (S_0_0 : SyntheticSpectrum))
    (hd : Detects (model.convergence .sphere) (1,1,1)
      (sphereLabel 1 1 0 KIP126.Computation.Standard.h0) h0)
    (x : BiHom 122 126 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9))
    (hx : FiltrationAtLeast model.syntheticTower 8 x) :
    FiltrationAtLeast model.syntheticTower 11 (sphereAction h0 x) := by
  have hf0 := detected_filtration .sphere (1,1,1) hd
  exact (nu_nine_h0x_gap _).mp
    (KIP126.Literature.Standard.action_filtration (.quotient 9 .sphere) 0 1 122 126 1 8 h0 x hf0 hx)

end
end KIP126.Main.SectionSeven.Internal
