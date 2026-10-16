module
public import KIP126.Main.Conditions
public import KIP126.Computation.Table.Archive
import all KIP126.Main.Internal.AlphaOne.Coherence
import all KIP126.Main.SectionSeven.NuTargetWindows
import all KIP126.Main.Internal.Selected.InfinityFrames
/-! Low-degree uniqueness from AnyYHelpers:2946–3011 and
Computation/LowDegrees:22–63, bbac1fc05843 (MIT). -/
@[expose] section
namespace KIP126.Main.Internal
open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence KIP126.AdamsSynthetic
open KIP126.Core.SpectralSequence KIP126.Kervaire.Route KIP126.Literature
open KIP126.AdamsSynthetic.Standard KIP126.ProofTools.Operations
open KIP126.Main.SectionSeven.Internal KIP126.Main.Internal.Selected
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

theorem low_eta_page_zero : Subsingleton (model.classical.sphere.Page 2 (2,3)) := by
  let e := KIP126.Computation.Standard.coordinates 2 3 (by decide)
  have hdim : KIP126.Computation.Standard.archive.basisCount 2 3=0 :=
    KIP126.Computation.Table.archive_dimension 2 3 (by decide)
  haveI : IsEmpty (Fin (KIP126.Computation.Standard.archive.basisCount 2 3)) := by
    rw [hdim]; infer_instance
  exact e.injective.subsingleton

theorem low_eta_page_unique : ∀x y:model.classical.sphere.Page 2 (1,2),x≠0→y≠0→x=y := by
  classical
  obtain ⟨e,_⟩ := KIP126.Computation.Table.basis_correct ⟨.sphere,1,2,["1,1"]⟩ (by
    unfold KIP126.Computation.Table.Raw.degrees
    iterate 80 apply List.mem_cons_of_mem
    exact List.mem_cons_self)
  change model.classical.sphere.Page 2 (1,2) ≃ₗ[ℤ] (Fin 1 →₀ ZMod 2) at e
  have hc (x:model.classical.sphere.Page 2 (1,2)) (hx:x≠0) : e x 0=1 := by
    generalize h:e x 0=c
    fin_cases c
    · exfalso; apply hx; apply e.injective; rw [map_zero]
      apply Finsupp.ext; intro i; fin_cases i; exact h
    · rfl
  intro x y hx hy
  apply e.injective; apply Finsupp.ext; intro i; fin_cases i
  exact (hc x hx).trans (hc y hy).symm

theorem sphere_one_three_zero (z : BiHom 1 3 (S_0_0 : SyntheticSpectrum)) : z=0 := by
  have hz (j:ℤ) (hj:0≤j) :
      IsZero (((model.family.obj (S_0_0:SyntheticSpectrum)).sequence.ssData (j,1+j,3)).eInfty) := by
    by_cases hw:3≤1+j
    · have hp : Subsingleton (model.classical.sphere.Page 2 (j,1+j)) := by
        by_cases he:j=2
        · subst j; exact low_eta_page_zero
        · exact KIP126.Literature.Standard.sphereVanishing _ _ (by omega) (by omega)
      exact sphere_infinity_zero_of_permanent_quotient j (1+j) 3 (by omega)
        (permanent_quotient_zero_of_page_zero .sphere 2 _ (by decide) (by omega) _ hp)
    · haveI : Subsingleton (nuEInftyModel model .sphere (j,1+j) 3) := by
        simp only [nuEInftyModel,hw,ite_false]; infer_instance
      haveI : Subsingleton (((model.family.nu model.nu SphereSpectrum).sequence.ssData (j,1+j,3)).eInfty) :=
        (KIP126.Literature.Standard.eInfinity_nu .sphere (j,1+j) 3).injective.subsingleton
      have hn := ModuleCat.isZero_of_subsingleton (((model.family.nu model.nu SphereSpectrum).sequence.ssData (j,1+j,3)).eInfty)
      let f := (model.family.map model.nu.unitIso.hom).eInftyMap (j,1+j,3)
      let g := (model.family.map model.nu.unitIso.inv).eInftyMap (j,1+j,3)
      have hgf:g≫f=𝟙 _ := by
        dsimp only [f,g]
        rw [←SpectralSequenceMorphism.eInftyMap_comp,←SyntheticAdamsFamily.map_comp,
          Iso.inv_hom_id,SyntheticAdamsFamily.map_id,SpectralSequenceMorphism.eInftyMap_id]
      apply (IsZero.iff_id_eq_zero _).mpr
      exact hgf.symm.trans (by
        have hf:f=0 := hn.eq_of_src f 0
        rw [hf,comp_zero])
  have h0 : FiltrationAtLeast model.syntheticTower 0 z := by
    refine ⟨z≫(model.syntheticTower.tower _).zeroIso.inv,?_⟩
    change (z≫(model.syntheticTower.tower _).zeroIso.inv)≫(model.syntheticTower.tower _).projection 0=z
    simp only [AbstractAdamsTower.projection,Int.toNat_zero,(model.syntheticTower.tower _).map_self]
    erw [Category.assoc,Category.id_comp,Iso.inv_hom_id,Category.comp_id]
  apply synthetic_homotopy_separated .sphere 1 3 z
  intro j
  exact (filtration_iff_of_infinity_zero (model.convergence .sphere) 0 j 1 3
    (by omega) (fun k hk _ => hz k hk) z).mp h0

theorem eta_first_quotient_injective :
    Function.Injective (fun z:BiHom 1 2 (S_0_0:SyntheticSpectrum) => quotientClass 1 z) := by
  intro x y h
  have hz:quotientClass 1 (x-y)=0 := by
    simp only [quotientClass,Preadditive.sub_comp] at h ⊢
    rw [h,sub_self]
  obtain ⟨b,hb⟩ := AlphaOne.lambda_one_division_of_quotient_zero 1 3 (x-y) hz
  rw [sphere_one_three_zero b] at hb
  simp only [lambdaMultiply,comp_zero] at hb
  exact sub_eq_zero.mp hb.symm

theorem eta_unique_from_low_degrees : ∀x y:BiHom 1 2 (S_0_0:SyntheticSpectrum),x≠0→y≠0→x=y := by
  let f:=fun z:BiHom 1 2 (S_0_0:SyntheticSpectrum) =>
    KIP126.Literature.sphereFirstQuotient model 1 2 (quotientClass 1 z)
  have hf:Function.Injective f :=
    (KIP126.Literature.sphereFirstQuotient model 1 2).injective.comp eta_first_quotient_injective
  intro x y hx hy
  have hn (z:BiHom 1 2 (S_0_0:SyntheticSpectrum)) (hz:z≠0) : f z≠0 := by
    intro hh; apply hz; apply hf
    simpa only [f,quotientClass,zero_comp,map_zero] using hh
  exact hf (low_eta_page_unique _ _ (hn x hx) (hn y hy))
end
end KIP126.Main.Internal
