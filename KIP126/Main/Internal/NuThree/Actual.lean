module
public import KIP126.Def.ProofTools.Operations
import all KIP126.Main.Internal.NuThree.Mahowald
import all KIP126.Main.Internal.NuThree.ActualOperations
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
private theorem nu_three_actual_map_relation :
    ∃ (a : BiHom 125 134 (XModLambdaN (Smn (Syn:=SyntheticSpectrum) 3 4) 3))
      (b : BiHom 125 134 (XModLambdaN (S_0_0:SyntheticSpectrum) 3)),
      a≫XModLambdaN.map (normalizedNu model KIP126.Literature.Standard.nuCofiber_nu_exponent) 3=b ∧
      FiniteDetected 3 (by decide) 11 136 2 KIP126.Computation.Standard.Y b := by
  obtain ⟨x,y',⟨W⟩,hy'⟩ := cnu_mahowald_finite
  have hw := nu_finite_extension_actual_relation x y' W
  obtain ⟨a,b,hab,hb⟩ := nu_relation_weight_transport _ _ _
    KIP126.Literature.Standard.nuCofiber_nu_exponent W.length_lower y' hw
  obtain ⟨et,het,bt,hbt,hgr⟩ := hb
  have hbY : Detects (model.convergence (.quotient 3 (.nu .sphere))) (11,136,134)
      (finiteTargetLabel model .sphere 3 11 136 2 KIP126.Computation.Standard.Y) b :=
    ⟨et,(q3_target_boundary_congruent _ _ hy' et).mp het,bt,hbt,hgr⟩
  let S := (SyntheticCategory.biShift
      (0,(normalizedExponent model.classicalTower model.auxiliary.nuMap:ℤ))).obj
      (model.nu.functor.obj (Sphere (C:=Spectrum) 3))
  let e : S≅Smn (Syn:=SyntheticSpectrum) 3 4 := by
    dsimp only [S]
    rw [KIP126.Literature.Standard.nuCofiber_nu_exponent]
    exact (SyntheticCategory.biShift (0,1)).mapIso (nuSphereThree model) ≪≫
      (SyntheticCategory.biShift_comp (3,3) (0,1)).app S_0_0
  let Q := model.quotients.functoriality.functor 3
  refine ⟨a≫(Q.mapIso e).hom,b≫(Q.mapIso model.nu.unitIso).hom,?_,?_⟩
  · refine (q3_nu_map_normalization KIP126.Literature.Standard.nuCofiber_nu_exponent a).symm.trans ?_
    simpa only [Category.assoc] using
      (congrArg (fun z=>z≫(Q.mapIso model.nu.unitIso).hom) hab)
  · have hh := detects_map (.quotient 3 (.nu .sphere)) (.quotient 3 .sphere)
      (Q.mapIso model.nu.unitIso).hom (11,136,134) _ b hbY
    have hl := sphere_quotient_label_from_nu 3 2 11 136 KIP126.Computation.Standard.Y
    change familyPageMap model.family (Q.mapIso model.nu.unitIso).hom 2 (11,136,134) _=_ at hl
    have hfinal := (congrArg (fun z : (model.family.obj (XModLambdaN (S_0_0:SyntheticSpectrum) 3)).E₂ (11,136,134)=>
      Detects (model.convergence (.quotient 3 .sphere)) (11,136,134) z
        (b≫(Q.mapIso model.nu.unitIso).hom)) hl).mp hh
    exact nu_three_y_nonzero _ hfinal

end
end KIP126.Main.Internal.NuThree
