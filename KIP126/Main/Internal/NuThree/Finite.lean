module
import all KIP126.Main.SectionSeven.Predicates
public import KIP126.E2Computation.Table.Values
public import KIP126.ProofTools.Operations
import all KIP126.Main.Internal.AlphaOne.Detection
import all KIP126.Main.Internal.DetectionLabels
import all KIP126.Main.Internal.QuotientCalculus
import all KIP126.Main.SectionSeven.NuTargetFiniteGap
import all KIP126.Main.SectionSeven.NuFifthAction
/-! NuFifth:1370–1744,1947–1956, bbac1fc05843 (MIT): the finite
filtration argument proving uniqueness of the nonzero class in π₁₂₂,₁₃₀(S/λ³).
Shared representative and quotient operations are the same proved operations. -/
@[expose] section
namespace KIP126.Main.Internal.NuThree
open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence KIP126.AdamsSynthetic
open KIP126.Core.SpectralSequence KIP126.Kervaire.Route KIP126.Literature
open KIP126.AdamsSynthetic.Standard (model SyntheticSpectrum)
open KIP126.ProofTools KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
open KIP126.Main.Internal KIP126.Main.SectionSeven KIP126.Main.SectionSeven.Internal
open KIP126.Computation.Table
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

private theorem nu_three_x_gap (a : BiHom 122 130 (XModLambdaN (S_0_0:SyntheticSpectrum) 3)) :
    FiltrationAtLeast model.syntheticTower 9 a ↔ FiltrationAtLeast model.syntheticTower 11 a := by
  apply filtration_iff_of_infinity_zero (model.convergence (.quotient 3 .sphere))
    9 11 122 130 (by decide)
  intro j hj hj'
  have hc : Subsingleton (model.classical.sphere.Page 2 (j,122+j)) := by
    have hjs : j=9 ∨ j=10 := by omega
    rcases hjs with rfl|rfl
    · obtain ⟨e,_⟩ := basis_correct ⟨.sphere,9,131,[]⟩ (by
        exact List.mem_of_getElem? (i:=170) (by rfl))
      change model.classical.sphere.Page 2 (9,131) ≃ₗ[ℤ] (Fin 0 →₀ ZMod 2) at e
      exact e.injective.subsingleton
    · obtain ⟨e,_⟩ := basis_correct ⟨.sphere,10,132,[]⟩ (by
        exact List.mem_of_getElem? (i:=179) (by rfl))
      change model.classical.sphere.Page 2 (10,132) ≃ₗ[ℤ] (Fin 0 →₀ ZMod 2) at e
      exact e.injective.subsingleton
  haveI := hc
  apply finite_sphere_zero_of_classical_quotient 3 (by decide) j (122+j) 130 (by omega)
  haveI : Subsingleton (cycles model .sphere ((3:ℤ)-(122+j)+130) (j,122+j)) := ⟨fun x y => Subtype.ext (hc.elim x.val y.val)⟩
  constructor
  intro x y
  obtain ⟨x,rfl⟩ := Quotient.exists_rep x
  obtain ⟨y,rfl⟩ := Quotient.exists_rep y
  exact congrArg (subquotientClass _ _) (Subsingleton.elim x y)

private theorem finite_sphere_filtration_floor (q : ℕ) (hq : 0<q) (s t : ℤ)
    (a : BiHom (t-s) t (XModLambdaN (S_0_0:SyntheticSpectrum) q)) :
    FiltrationAtLeast model.syntheticTower s a := by
  let f : XModLambdaN (S_0_0:SyntheticSpectrum) q ⟶ XModLambdaN (model.nu.functor.obj SphereSpectrum) q := XModLambdaN.map model.nu.unitIso.inv q
  let g : XModLambdaN (model.nu.functor.obj SphereSpectrum) q ⟶ XModLambdaN (S_0_0:SyntheticSpectrum) q := XModLambdaN.map model.nu.unitIso.hom q
  have hfg : f≫g=𝟙 (XModLambdaN (S_0_0:SyntheticSpectrum) q) := by
    dsimp only [f,g]
    rw [←model.quotients.functoriality.map_comp,Iso.inv_hom_id,model.quotients.functoriality.map_id]
    rfl
  have h := finite_bottom_filtration .sphere q hq s t (a≫f)
  have hh := map_preserves_filtration
    (model.convergentMap (.quotient q (.nu .sphere)) (.quotient q .sphere) g) (t-s,t) s (a≫f) h
  change FiltrationAtLeast model.syntheticTower s ((a≫f)≫g) at hh
  rw [Category.assoc,hfg,Category.comp_id] at hh
  exact hh

private theorem nu_x_label : basis .sphere 8 130 0 = KIP126.Computation.Standard.X := by
  have h := basis_value ⟨.mul (.named .h1) (.named .x_121_7),0⟩ (by decide)
  simpa only [Expression.value,Expression.degree,KIP126.Computation.Standard.X,
    KIP126.Computation.Standard.atom_h1] using h

private theorem nu_three_nonzero_detects_x
    (a : BiHom 122 130 (XModLambdaN (S_0_0:SyntheticSpectrum) 3)) (han : a≠0) :
    FiniteDetected 3 (by decide) 8 130 0 KIP126.Computation.Standard.X a := by
  classical
  obtain ⟨xr,hxr,hxn⟩ := KIP126.Computation.Standard.x_to_e6
  have hX5 : KIP126.Computation.Standard.X∈cycles model .sphere 5 (8,130) :=
    ((isCycle_iff_reaches model .sphere 6 (by decide) (8,130) _).mpr ⟨xr,hxr⟩).2
  have hX3 := cycles_antitone model .sphere (8,130) (by decide : (3:ℤ)≤5) hX5
  have hXn : KIP126.Computation.Standard.X≠0 := by
    intro h
    rw [h] at hxr
    exact hxn (RepresentsOnPage.unique hxr (RepresentsOnPage.zero (by decide : (2:ℤ)≤6)))
  obtain ⟨x3,hx3⟩ := AlphaOne.finite_sphere_detection_exists 3 (by decide) 8 130 _ hX3 hXn
  change BiHom 122 130 (XModLambdaN (S_0_0:SyntheticSpectrum) 3) at x3
  let c : cycles model .sphere ((3:ℤ)-130+(130-0)) (8,130) := ⟨KIP126.Computation.Standard.X,hX3⟩
  have frame : ∀z : CycleQuotient model .sphere 3 1 (8,130), z=0 ∨ z=subquotientClass _ _ c := by
    obtain ⟨e,he⟩ := basis_correct ⟨.sphere,8,130,["1,1,323,1"]⟩ (by
      exact List.mem_of_getElem? (i:=158) (by rfl))
    change model.classical.sphere.Page 2 (8,130) ≃ₗ[ℤ] (Fin 1 →₀ ZMod 2) at e
    have hb : e.symm (Finsupp.single (0:Fin 1) 1)=KIP126.Computation.Standard.X :=
      (he 0).trans nu_x_label
    intro z
    obtain ⟨z,rfl⟩ := Quotient.exists_rep z
    have hh : e z.val=Finsupp.single 0 (e z.val 0) := by
      apply Finsupp.ext
      intro i
      fin_cases i
      simp
    have hz : z.val=e.symm (Finsupp.single 0 (e z.val 0)) := by
      rw [←hh,LinearEquiv.symm_apply_apply]
    generalize hd : e z.val 0=d at hz
    fin_cases d
    · change z.val=e.symm (Finsupp.single 0 (0:ZMod 2)) at hz
      simp only [Finsupp.single_zero,map_zero] at hz
      left
      exact (subquotientClass_eq_zero_iff _ _ z).mpr (hz ▸ (boundaries model .sphere 1 (8,130)).zero_mem)
    · change z.val=e.symm (Finsupp.single 0 (1:ZMod 2)) at hz
      right
      have heq : z=c := Subtype.ext (hz.trans hb)
      exact congrArg (subquotientClass _ _) heq
  have hinf := finite_sphere_frame 3 0 (by decide) (by decide) 8 130 c frame
  have ha8 := finite_sphere_filtration_floor 3 (by decide) 8 130 a
  obtain ⟨b,hb⟩ := finite_detection_peel 3 (8,130,130)
    (quotientLabel 3 8 130 0 KIP126.Computation.Standard.X) hinf x3 hx3.1 a ha8
  have heq : a-(if b then x3 else 0)=0 := by
    apply sphere_quotient_high_filtration_zero 3 (by decide) 122 130 11 (by decide)
    exact (nu_three_x_gap _).mp hb
  cases b
  · simp only [Bool.false_eq_true,↓reduceIte,sub_zero] at heq
    exact (han heq).elim
  · simp only [↓reduceIte] at heq
    rw [sub_eq_zero.mp heq]
    exact hx3

private theorem nu_three_nonzero_unique :
    ∀u v:BiHom 122 130 (XModLambdaN (S_0_0:SyntheticSpectrum) 3),u≠0→v≠0→u=v := by
  intro u v hu hv
  apply sub_eq_zero.mp
  apply sphere_quotient_high_filtration_zero 3 (by decide) 122 130 11 (by decide)
  apply (nu_three_x_gap (u-v)).mp
  exact detects_sub_filtration (model.convergence (.quotient 3 .sphere)) (8,130,130)
    (nu_three_nonzero_detects_x u hu).1 (nu_three_nonzero_detects_x v hv).1

end
end KIP126.Main.Internal.NuThree
