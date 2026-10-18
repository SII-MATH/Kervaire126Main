module
import all KIP126.Main.SectionSeven.Predicates
public import KIP126.Main.SectionSeven.AlphaOne
public import KIP126.ProofTools.Operations
public import KIP126.ProofTools.Representatives
public import KIP126.Literature.Standard.Filtration
import all KIP126.Main.Internal.AlphaOne.Detection
import all KIP126.Main.Internal.AlphaOne.Coherence
import all KIP126.Main.Internal.Selected.SphereDetection
import all KIP126.Main.Internal.Choice.Filtration

/-! The boundary comparison and finite-filtration error in
AlphaOne/Existence.lean:1434–1491,1679–1814, bbac1fc05843 (MIT). -/
@[expose] section
namespace KIP126.Main.Internal.AlphaOne
open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence KIP126.AdamsSynthetic
open KIP126.Core.SpectralSequence KIP126.Core.SpectralSequence.FinitePageCalculus
open KIP126.Main.SectionSeven KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard (model SyntheticSpectrum)
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald KIP126.Main.Internal
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
private theorem cycle_quotient_zero_of_page (r c b : ℤ) (p : ℤ×ℤ)
    (hr : 2≤r) (hc : r≤c+1) (hb : r-1≤b)
    (hz : Subsingleton (model.classical.sphere.Page r p)) :
    Subsingleton (KIP126.Literature.CycleQuotient model .sphere c b p) := by
  apply Choice.subquotient_subsingleton_of_le
  intro x hx
  obtain ⟨x',hx'⟩ := (KIP126.ProofTools.isCycle_iff_reaches model .sphere (c+1) (by omega) p x).mp
    ⟨by omega,by simpa using hx⟩
  obtain ⟨xr,hxr⟩ := represents_before hr hc hx'
  rw [hz.elim xr 0] at hxr
  exact KIP126.Literature.boundaries_monotone model .sphere p hb
    (represents_zero_mem_boundary model .sphere r p x hxr)
private theorem finite_boundary_detects_sub_filtration

    (x y : model.classical.sphere.Page 2 (10,134))
    (hx : x∈KIP126.Literature.cycles model .sphere 8 (10,134))
    (hy : y∈KIP126.Literature.cycles model .sphere 8 (10,134))
    (hxy : x-y∈KIP126.Literature.boundaries model .sphere 4 (10,134))
    (a b : BiHom 124 131 (XModLambdaN (S_0_0 : SyntheticSpectrum) 11))
    (ha : Detects (model.convergence (.quotient 11 .sphere)) (10,134,131)
      (quotientLabel 11 10 134 3 x) a)
    (hb : Detects (model.convergence (.quotient 11 .sphere)) (10,134,131)
      (quotientLabel 11 10 134 3 y) b) :
    FiltrationAtLeast model.syntheticTower 11 (a-b) := by
  classical
  obtain ⟨e,he,a',ha',hga⟩ := ha
  obtain ⟨f,hf,b',hb',hgb⟩ := hb
  let g := XModLambdaN.map model.nu.unitIso.inv 11
  have he' := family_infinity_representative_map g (10,134,131) _ _ he
  have hf' := family_infinity_representative_map g (10,134,131) _ _ hf
  have hlx := sphere_quotient_label_to_nu  11 3 10 134 x
  have hly := sphere_quotient_label_to_nu  11 3 10 134 y
  change familyPageMap model.family g 2 (10,134,131) (quotientLabel 11 10 134 3 x)=_ at hlx
  change familyPageMap model.family g 2 (10,134,131) (quotientLabel 11 10 134 3 y)=_ at hly
  rw [hlx] at he'
  rw [hly] at hf'
  let xx : KIP126.Literature.cycles model .sphere (11-134+(134-3)) (10,134) := ⟨x,hx⟩
  let yy : KIP126.Literature.cycles model .sphere (11-134+(134-3)) (10,134) := ⟨y,hy⟩
  have hxq := (finite_target_label_iff .sphere 11 (by decide) 10 134 3 (by decide) xx _).mp he'
  have hyq := (finite_target_label_iff .sphere 11 (by decide) 10 134 3 (by decide) yy _).mp hf'
  have hz : KIP126.Literature.subquotientClass _ (KIP126.Literature.boundaries model .sphere 4 (10,134)) (xx-yy)=0 :=
    (subquotientClass_eq_zero_iff _ _ (xx-yy)).mpr hxy
  rw [map_sub] at hz
  have heq := sub_eq_zero.mp hz
  have hge : (model.family.functor.map g).eInftyMap (10,134,131) e=
      (model.family.functor.map g).eInftyMap (10,134,131) f := by
    apply (KIP126.Literature.Standard.infinityFiniteWindow .sphere 11 (by decide) (10,134) 131 (by decide)).injective
    change KIP126.Literature.Standard.infinityFiniteWindow .sphere 11 (by decide) (10,134) 131 (by decide)
      ((model.family.functor.map g).eInftyMap (10,134,131) e) =
      KIP126.Literature.subquotientClass _ (KIP126.Literature.boundaries model .sphere 4 (10,134)) xx at hxq
    change KIP126.Literature.Standard.infinityFiniteWindow .sphere 11 (by decide) (10,134) 131 (by decide)
      ((model.family.functor.map g).eInftyMap (10,134,131) f) =
      KIP126.Literature.subquotientClass _ (KIP126.Literature.boundaries model .sphere 4 (10,134)) yy at hyq
    exact hxq.trans (heq.trans hyq.symm)
  let h := (model.family.functor.map (XModLambdaN.map model.nu.unitIso.hom 11)).eInftyMap (10,134,131)
  have hgh : (model.family.functor.map g).eInftyMap (10,134,131) ≫ h=𝟙 _ := by
    dsimp only [g,h]
    rw [←SpectralSequenceMorphism.eInftyMap_comp,←Functor.map_comp,
      ←model.quotients.functoriality.map_comp,model.nu.unitIso.inv_hom_id,
      model.quotients.functoriality.map_id,CategoryTheory.Functor.map_id,SpectralSequenceMorphism.eInftyMap_id]
  have hef : e=f := by
    have he0 := ConcreteCategory.congr_hom hgh e
    have hf0 := ConcreteCategory.congr_hom hgh f
    change h ((model.family.functor.map g).eInftyMap (10,134,131) e)=e at he0
    change h ((model.family.functor.map g).eInftyMap (10,134,131) f)=f at hf0
    exact he0.symm.trans ((congrArg h hge).trans hf0)
  apply detects_sub_filtration (model.convergence (.quotient 11 .sphere)) (10,134,131)
    (show Detects _ _ (quotientLabel 11 10 134 3 x) a from ⟨e,he,a',ha',hga⟩)
  exact ⟨e,he,b',hb',hef ▸ hgb⟩



private theorem alpha_error_filtration_gap

    (h11 : Subsingleton ((model.classical.sphere).Page 5 (11,135)))
    (h12 : Subsingleton ((model.classical.sphere).Page 4 (12,136)))
    (a : BiHom 124 131 (XModLambdaN (S_0_0 : SyntheticSpectrum) 11)) :
    FiltrationAtLeast model.syntheticTower 11 a ↔
      FiltrationAtLeast model.syntheticTower 13 a := by
  classical
  apply filtration_iff_of_infinity_zero (model.convergence (.quotient 11 .sphere))
    11 13 124 131 (by decide)
  intro j hj hj'
  haveI : Subsingleton (KIP126.Literature.CycleQuotient model .sphere
      (11-(124+j)+131) (1+(124+j)-131) (j,124+j)) := by
    rw [show (11:ℤ)-(124+j)+131=18-j by omega,
      show (1:ℤ)+(124+j)-131=j-6 by omega,add_comm 124 j]
    have hjcases : j=11 ∨ j=12 := by omega
    rcases hjcases with rfl|rfl
    · exact cycle_quotient_zero_of_page 5 7 5 (11,135) (by decide) (by decide) (by decide) h11
    · exact cycle_quotient_zero_of_page 4 6 6 (12,136) (by decide) (by decide) (by decide) h12
  let e := KIP126.Literature.Standard.infinityFiniteWindow .sphere 11 (by decide) (j,124+j) 131
    (by constructor <;> omega)
  haveI : Subsingleton (((model.family.quotient (model.nu.functor.obj SphereSpectrum) 11).sequence.ssData (j,124+j,131)).eInfty) :=
    e.injective.subsingleton
  let hn := ModuleCat.isZero_of_subsingleton
    (((model.family.quotient (model.nu.functor.obj SphereSpectrum) 11).sequence.ssData (j,124+j,131)).eInfty)
  let f := (model.family.functor.map (XModLambdaN.map model.nu.unitIso.hom 11)).eInftyMap (j,124+j,131)
  let g := (model.family.functor.map (XModLambdaN.map model.nu.unitIso.inv 11)).eInftyMap (j,124+j,131)
  have hfg : g ≫ f=𝟙 _ := by
    dsimp only [f,g]
    rw [←SpectralSequenceMorphism.eInftyMap_comp,←Functor.map_comp,
      ←model.quotients.functoriality.map_comp,model.nu.unitIso.inv_hom_id,
      model.quotients.functoriality.map_id,CategoryTheory.Functor.map_id,SpectralSequenceMorphism.eInftyMap_id]
  apply (CategoryTheory.Limits.IsZero.iff_id_eq_zero _).mpr
  exact hfg.symm.trans (by rw [hn.eq_of_src f 0,CategoryTheory.Limits.comp_zero])


private theorem alpha_error_filtration_thirteen


    (U : model.classical.sphere.Page 2 (10,134)) (V : model.classical.sphere.Page 2 (9,132))
    (source : model.classical.sphere.Page 2 (8,133))
    (hU : U∈KIP126.Literature.cycles model .sphere 8 (10,134))
    (hd : HasDifferential (model.classical.sphere)
      2 (8,133) (10,134) source (KIP126.Computation.Standard.product (r := (10,134)) (KIP126.Computation.Standard.h1) V + U))
    (h11 : Subsingleton ((model.classical.sphere).Page 5 (11,135)))
    (h12 : Subsingleton ((model.classical.sphere).Page 4 (12,136)))
    (a : BiHom 123 132 (XModLambdaN (S_0_0 : SyntheticSpectrum) 11))
    (ha : FiniteDetected 11 (by decide) 9 132 0 V a)
    (u : BiHom 124 134 (S_0_0 : SyntheticSpectrum)) (hu : SphereDetected 10 134 0 U u) :
    FiltrationAtLeast model.syntheticTower 13
      ((show BiHom 124 131 (XModLambdaN (S_0_0 : SyntheticSpectrum) 11) from lambdaMultiply 3 (sphereAction KIP126.Literature.Standard.eta a))-
        (show BiHom 124 131 (XModLambdaN (S_0_0 : SyntheticSpectrum) 11) from lambdaMultiply 3 (quotientClass 11 u))) := by
  classical
  have hlabel := Selected.sphere_zero_weight_label_10_134 U u hu.1
  have he := model.sphereDetectionCompatible.homotopy_lambda 1 2 3 KIP126.Literature.Standard.eta
  have hη := KIP126.Literature.Standard.eta_label
  dsimp only [KIP126.Literature.sphereFirstQuotient] at hη
  rw [hη] at he
  have hp : Detects (model.convergence (.quotient 11 .sphere)) (10,134,131)
      (quotientLabel 11 10 134 3 (KIP126.Computation.Standard.product (r := (10,134)) (KIP126.Computation.Standard.h1) V))
      (sphereAction (lambdaMultiply 3 KIP126.Literature.Standard.eta) a) :=
    KIP126.Literature.Standard.finite_action 11 (by decide) 1 2 9 132 3 0
      (KIP126.Computation.Standard.h1) V (lambdaMultiply 3 KIP126.Literature.Standard.eta) a he ha.1
  rw [sphere_action_lambda_three KIP126.Literature.Standard.eta a] at hp
  have hu3 := model.sphereDetectionCompatible.homotopy_lambda 10 134 3 u
  dsimp only [KIP126.Literature.sphereFirstQuotient] at hlabel
  rw [hlabel] at hu3
  have huq := detects_map  .sphere (.quotient 11 .sphere)
    (XModLambdaN.incl (S_0_0 : SyntheticSpectrum) 11) (10,134,131) _ (lambdaMultiply 3 u) hu3
  have hcomm : lambdaMultiply 3 u≫XModLambdaN.incl (S_0_0 : SyntheticSpectrum) 11 =
      lambdaMultiply 3 (quotientClass 11 u) := by
    simp only [lambdaMultiply,quotientClass,Category.assoc]
  change Detects (model.convergence (.quotient 11 .sphere)) (10,134,131)
    (quotientLabel 11 10 134 3 U) (lambdaMultiply 3 u≫XModLambdaN.incl (S_0_0 : SyntheticSpectrum) 11) at huq
  rw [hcomm] at huq
  have hU2 : U+U=0 := by
    apply (KIP126.Computation.Standard.coordinates 10 134 (by decide)).injective
    rw [map_add,map_zero]
    ext i
    exact CharTwo.add_self_eq_zero _
  have hneg : -U=U := by
    apply neg_eq_iff_add_eq_zero.mpr
    exact hU2
  have hd0 := differential_target_later_zero (le_of_eq (model.classical.firstPage _))
    (show (2:ℤ)<3 from by decide) hd
  have hbound := represents_zero_mem_boundary model .sphere 3 (10,134) _ hd0
  have hbound4 : KIP126.Computation.Standard.product (r := (10,134)) (KIP126.Computation.Standard.h1) V-U∈
      KIP126.Literature.boundaries model .sphere 4 (10,134) := by
    rw [sub_eq_add_neg,hneg]
    exact KIP126.Literature.boundaries_monotone model .sphere (10,134) (by decide : (2:ℤ)≤4) hbound
  have hprod : KIP126.Computation.Standard.product (r := (10,134)) (KIP126.Computation.Standard.h1) V∈
      KIP126.Literature.cycles model .sphere 8 (10,134) := by
    have hb := KIP126.ProofTools.Internal.Mahowald.boundaries_le_cycles model .sphere (10,134) 4 8 hbound4
    have hh := (KIP126.Literature.cycles model .sphere 8 (10,134)).add_mem hb hU
    simpa only [sub_add_cancel] using hh
  apply (alpha_error_filtration_gap h11 h12 _).mp
  exact finite_boundary_detects_sub_filtration _ U hprod hU hbound4 _ _ hp huq



end
end KIP126.Main.Internal.AlphaOne
end
