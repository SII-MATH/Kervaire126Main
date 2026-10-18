module
public import KIP126.Main.Conditions
public import KIP126.AdamsCalculations.Table.Archive
import KIP126.Literature.Standard.QuotientAlgebra
import all KIP126.Main.Internal.AlphaOne.Coherence
import all KIP126.Main.SectionSeven.NuTargetWindows
import all KIP126.Main.Internal.Selected.InfinityFrames
/-! Low-degree calculations from AnyYHelpers:2946–3011 and
Computation/LowDegrees:22–63, bbac1fc05843 (MIT).
After restricting synthetic separatedness to finite λ quotients, the
calculations give uniqueness and invariance in those actual quotients.
They do not assert separatedness of the untruncated ordinary sphere. -/
@[expose] section
namespace KIP126.Main.Internal
open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence KIP126.AdamsSynthetic
open KIP126.Core.SpectralSequence KIP126.Kervaire.Route KIP126.Literature
open KIP126.AdamsSynthetic.Standard KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
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

theorem sphere_one_three_infinite_filtration (z : BiHom 1 3 (S_0_0 : SyntheticSpectrum)) :
    ∀ j : ℕ, FiltrationAtLeast model.syntheticTower j z := by
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
  intro j
  exact (filtration_iff_of_infinity_zero (model.convergence .sphere) 0 j 1 3
    (by omega) (fun k hk _ => hz k hk) z).mp h0

/-- The E∞ calculation is used only after mapping to an actual finite λ quotient. -/
theorem sphere_one_three_finite_quotient_zero
    (z : BiHom 1 3 (S_0_0 : SyntheticSpectrum)) (n : ℕ) : quotientClass n z = 0 := by
  apply synthetic_homotopy_separated .sphere n 1 3 (quotientClass n z)
  intro j
  exact map_preserves_filtration
    (model.convergentMap .sphere (.quotient n .sphere) (XModLambdaN.incl _ n))
    (1,3) j z (sphere_one_three_infinite_filtration z j)

theorem eta_finite_quotient_eq_of_first_quotient_eq
    (n : ℕ) (x y : BiHom 1 2 (S_0_0 : SyntheticSpectrum))
    (h : quotientClass 1 x = quotientClass 1 y) : quotientClass n x = quotientClass n y := by
  have hz : quotientClass 1 (x-y) = 0 := by
    simp only [quotientClass, Preadditive.sub_comp] at h ⊢
    rw [h, sub_self]
  obtain ⟨b,hb⟩ := AlphaOne.lambda_one_division_of_quotient_zero 1 3 (x-y) hz
  have hh := congrArg (fun u => quotientClass n u) hb
  have hbn := sphere_one_three_finite_quotient_zero b n
  have he : quotientClass n (lambdaMultiply 1 b) = 0 := by
    change b ≫ XModLambdaN.incl _ n = 0 at hbn
    simp only [quotientClass, lambdaMultiply, Category.assoc]
    rw [hbn]
    simp only [comp_zero]
  rw [he] at hh
  change 0 = (x-y) ≫ XModLambdaN.incl _ n at hh
  rw [Preadditive.sub_comp] at hh
  exact sub_eq_zero.mp hh.symm

/-- Source automorphisms act trivially on the image of η in each finite λ quotient. -/
theorem eta_source_iso_fixed_in_finite_quotient
    (n : ℕ) (eta : BiHom 1 2 (S_0_0 : SyntheticSpectrum))
    (a : Smn (Syn := SyntheticSpectrum) 1 2 ≅ Smn 1 2) :
    quotientClass n (a.hom ≫ eta) = quotientClass n eta := by
  apply eta_finite_quotient_eq_of_first_quotient_eq
  let e := KIP126.Literature.sphereFirstQuotient model 1 2
  by_cases h : quotientClass 1 eta = 0
  · change (a.hom ≫ eta) ≫ XModLambdaN.incl _ 1 = eta ≫ XModLambdaN.incl _ 1
    change eta ≫ XModLambdaN.incl _ 1 = 0 at h
    rw [Category.assoc, h, comp_zero]
  · apply e.injective
    apply low_eta_page_unique
    · intro he
      have hz : quotientClass 1 (a.hom ≫ eta) = 0 := e.injective (he.trans (map_zero e).symm)
      apply h
      have hh := congrArg (fun u => a.inv ≫ u) hz
      simpa only [quotientClass, Category.assoc, Iso.inv_hom_id_assoc, comp_zero] using hh
    · exact fun he => h (e.injective (he.trans (map_zero e).symm))

theorem eta_action_source_iso_fixed_in_finite_quotient
    (n : ℕ) (hn : 0 < n) (eta : BiHom 1 2 (S_0_0 : SyntheticSpectrum))
    {k l : ℤ} (x : BiHom k l (XModLambdaN (S_0_0 : SyntheticSpectrum) n))
    (a : Smn (Syn := SyntheticSpectrum) (1+k) (2+l) ≅ Smn (1+k) (2+l)) :
    a.hom ≫ sphereAction eta x = sphereAction eta x := by
  let F := SyntheticCategory.biShift (Syn := SyntheticSpectrum) (k,l)
  let ff := SyntheticCategory.biShift_fullyFaithful (Syn := SyntheticSpectrum) (k,l)
  let d : Smn (Syn := SyntheticSpectrum) (1+k) (2+l) ≅ F.obj (Smn 1 2) :=
    ((SyntheticCategory.biShift_comp (1,2) (k,l)).app (S_0_0 : SyntheticSpectrum)).symm
  let b := ff.preimageIso (d.symm ≪≫ a ≪≫ d)
  have hb : F.map b.hom = d.inv ≫ a.hom ≫ d.hom := ff.map_preimage _
  have hh : sphereAction (b.hom ≫ eta) x = sphereAction eta x := by
    rw [← KIP126.Literature.Standard.quotientAlgebra_sphere_action n hn 1 2 k l (b.hom ≫ eta) x,
      ← KIP126.Literature.Standard.quotientAlgebra_sphere_action n hn 1 2 k l eta x,
      eta_source_iso_fixed_in_finite_quotient n eta b]
  change d.hom ≫ F.map (b.hom ≫ eta) ≫ x = d.hom ≫ F.map eta ≫ x at hh
  rw [Functor.map_comp, hb] at hh
  change a.hom ≫ (d.hom ≫ F.map eta ≫ x) = d.hom ≫ F.map eta ≫ x
  simpa only [Category.assoc, d.hom_inv_id_assoc] using hh

end
end KIP126.Main.Internal
