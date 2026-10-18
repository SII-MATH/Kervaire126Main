module
import all KIP126.Main.SectionSeven.Predicates
public import KIP126.ProofTools.Operations
import all KIP126.Main.Internal.NuThree.Finite
import all KIP126.Main.Internal.QuotientCalculus
import all KIP126.Main.SectionSeven.WeakInitialNonzero
/-! The strict actual-map and nonzero target steps, NuFifth:1170–1418
at bbac1fc05843 (MIT), retaining the same normalized Cν map. -/
@[expose] section
namespace KIP126.Main.Internal.NuThree
open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence KIP126.AdamsSynthetic
open KIP126.Core.SpectralSequence KIP126.Core.SpectralSequence.FinitePageCalculus
open KIP126.Kervaire.Route KIP126.Literature KIP126.ProofTools
open KIP126.AdamsSynthetic.Standard (model Spectrum SyntheticSpectrum)
open KIP126.ProofTools.Operations KIP126.Main.Internal KIP126.Main.SectionSeven
open KIP126.Main.SectionSeven.Internal
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
private theorem nu_finite_extension_actual_relation
    (x : (model.classical.obj (Sphere 3)).Page 2 (8,133))
    (y : model.classical.sphere.Page 2 (11,136))
    (W : FiniteExtensionWitness model (.shift 3 .sphere) .sphere
      model.auxiliary.nuMap 4 3 8 133 x y) :
    ∃ (a : BiHom 125 (133+normalizedExponent model.classicalTower model.auxiliary.nuMap)
        (XModLambdaN ((extensionSourceObject model (.shift 3 .sphere) .sphere
          model.auxiliary.nuMap).obj model.nu model.auxiliary) 3))
      (b : BiHom 125 (133+normalizedExponent model.classicalTower model.auxiliary.nuMap)
        (XModLambdaN (model.nu.functor.obj SphereSpectrum) 3)),
      a≫finiteExtensionMap model (.shift 3 .sphere) .sphere model.auxiliary.nuMap 3=b ∧
      Detects (model.convergence (.quotient 3 (.nu .sphere)))
        (11,136,133+normalizedExponent model.classicalTower model.auxiliary.nuMap)
        (finiteTargetForExtension model (.shift 3 .sphere) .sphere model.auxiliary.nuMap
          3 3 8 133 W.length_lower y) b := by
  obtain ⟨_,a,b,hab,ha,hb⟩ := (tower_extension_iff _ _ _ _ _ _).mp W.equation
  refine ⟨_,_,hab,W.target,W.target_rep,b,rfl,?_⟩
  exact hb.symm

private theorem cycles_one_mem (X : ClassicalObject) (p : ℤ×ℤ)
    (x : Ambient model X p) : x∈cycles model X 1 p :=
  ((isCycle_iff_reaches model X 2 (by decide) p x).mpr ⟨x,represents_two_self x⟩).2

private theorem q3_target_boundary_congruent (y' y : model.classical.sphere.Page 2 (11,136))
    (hy : Congruent model .sphere 3 (11,136) y' y)
    (e : ((model.family.quotient (model.nu.functor.obj SphereSpectrum) 3).sequence.ssData (11,136,134)).eInfty) :
    HasInfinityRepresentative _ 2 (11,136,134) (finiteTargetLabel model .sphere 3 11 136 2 y') e ↔
      HasInfinityRepresentative _ 2 (11,136,134) (finiteTargetLabel model .sphere 3 11 136 2 y) e := by
  let c' : cycles model .sphere ((3:ℤ)-136+(136-(2:ℕ))) (11,136) :=
    ⟨y',cycles_one_mem .sphere (11,136) y'⟩
  let c : cycles model .sphere ((3:ℤ)-136+(136-(2:ℕ))) (11,136) :=
    ⟨y,cycles_one_mem .sphere (11,136) y⟩
  have heq : subquotientClass _ (boundaries model .sphere 3 (11,136)) c' =
      subquotientClass _ (boundaries model .sphere 3 (11,136)) c := by
    apply sub_eq_zero.mp
    rw [←map_sub]
    exact (subquotientClass_eq_zero_iff _ _ (c'-c)).mpr hy.2
  exact (finite_target_label_iff .sphere 3 (by decide) 11 136 2 (by decide) c' e).trans
    ((congrArg (fun z => KIP126.Literature.Standard.infinityFiniteWindow .sphere 3 (by decide)
      (11,136) 134 (by constructor <;> omega) e = z) heq).to_iff.trans
      (finite_target_label_iff .sphere 3 (by decide) 11 136 2 (by decide) c e).symm)

private theorem nu_three_y_nonzero (b : BiHom 125 134 (XModLambdaN (S_0_0:SyntheticSpectrum) 3))
    (hb : Detects (model.convergence (.quotient 3 .sphere)) (11,136,134)
      (quotientLabel 3 11 136 2 KIP126.Computation.Standard.Y) b) :
    FiniteDetected 3 (by decide) 11 136 2 KIP126.Computation.Standard.Y b := by
  apply sphere_finite_detection_nonzero 3 2 (by decide) (by decide) 11 136 _
    (cycles_one_mem .sphere (11,136) _) ?_ b hb
  intro hy
  have hy4 := boundaries_monotone model .sphere (11,136) (by decide : (3:ℤ)≤4) hy
  have hz : RepresentsOnPage model.classical.sphere 5 (11,136) KIP126.Computation.Standard.Y 0 :=
    representsOnPage_of_congruent model .sphere (by decide)
      (RepresentsOnPage.zero (by decide : (2:ℤ)≤5)) ⟨by decide,by change KIP126.Computation.Standard.Y - 0 ∈ boundaries model .sphere 4 (11,136); rw [sub_zero]; exact hy4⟩
  obtain ⟨z,hz',hzn⟩ := KIP126.Computation.Standard.y_to_e5
  exact hzn (represents_unique hz' hz)

private theorem q3_nu_map_normalization
    (he : normalizedExponent model.classicalTower model.auxiliary.nuMap = 1) :
    let A := (SyntheticCategory.biShift
      (0, (normalizedExponent model.classicalTower model.auxiliary.nuMap : ℤ))).obj
      (model.nu.functor.obj (Sphere (C:=Spectrum) 3))
    let e : A ≅ Smn (Syn:=SyntheticSpectrum) 3 4 := by
      dsimp only [A]
      rw [he]
      exact (SyntheticCategory.biShift (0,1)).mapIso (nuSphereThree model) ≪≫
        (SyntheticCategory.biShift_comp (3,3) (0,1)).app S_0_0
    let Q := model.quotients.functoriality.functor 3
    ∀ x : BiHom 125 134 (XModLambdaN A 3),
      x ≫ (finiteExtensionMap model (.shift 3 .sphere) .sphere model.auxiliary.nuMap 3) ≫
          (Q.mapIso model.nu.unitIso).hom =
        (x ≫ (Q.mapIso e).hom) ≫ XModLambdaN.map (normalizedNu model he) 3 := by
  dsimp only
  let e : (SyntheticCategory.biShift
      (0, (normalizedExponent model.classicalTower model.auxiliary.nuMap : ℤ))).obj
      (model.nu.functor.obj (Sphere (C:=Spectrum) 3)) ≅ Smn (Syn:=SyntheticSpectrum) 3 4 := by
    rw [he]
    exact (SyntheticCategory.biShift (0,1)).mapIso (nuSphereThree model) ≪≫
      (SyntheticCategory.biShift_comp (3,3) (0,1)).app S_0_0
  let Q := model.quotients.functoriality.functor 3
  intro x
  change x ≫ Q.map _ ≫ Q.map _ = (x ≫ Q.map e.hom) ≫
    Q.map (e.inv ≫ _ ≫ _)
  simp only [Functor.map_comp, Category.assoc]
  rw [← Q.map_comp_assoc, e.hom_inv_id, Q.map_id, Category.id_comp]
private theorem nu_relation_weight_transport
    (A : SyntheticSpectrum) (g : A ⟶ XModLambdaN (model.nu.functor.obj SphereSpectrum) 3)
    (n : ℕ) (hn : n=1) (hlower : (n:ℤ)≤3)
    (y : model.classical.sphere.Page 2 (11,136))
    (h : ∃ (a : BiHom 125 (133+n) A)
      (b : BiHom 125 (133+n) (XModLambdaN (model.nu.functor.obj SphereSpectrum) 3)),
      a≫g=b ∧ Detects (model.convergence (.quotient 3 (.nu .sphere))) (11,136,133+n)
        (regradeE2 (A:=model.family.obj (XModLambdaN (model.nu.functor.obj SphereSpectrum) 3))
          (i:=(11,136,136-(3-(n:ℤ)).toNat)) (j:=(11,136,133+n))
          (by ext <;> simp only [Int.toNat_of_nonneg (sub_nonneg.mpr hlower)]; omega)
          (finiteTargetLabel model .sphere 3 11 136 (3-(n:ℤ)).toNat y)) b) :
    ∃ (a : BiHom 125 134 A)
      (b : BiHom 125 134 (XModLambdaN (model.nu.functor.obj SphereSpectrum) 3)),
      a≫g=b ∧ Detects (model.convergence (.quotient 3 (.nu .sphere))) (11,136,134)
        (finiteTargetLabel model .sphere 3 11 136 2 y) b := by
  subst n
  exact h


end
end KIP126.Main.Internal.NuThree
