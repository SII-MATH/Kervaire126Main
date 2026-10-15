module

public import KIP126.Main.AdamsSynthetic.Context
public import KIP126.Main.Computation.LinCoordinates.Model.BasisCatalogue.FiniteCertificates
public import KIP126.Main.AdamsSynthetic.SphereConvergence
public import KIP126.Main.Literature.SourceComparisons.RealizationKernel

import all KIP126.Main.AdamsSynthetic.NuSource.FromSuspension
import all KIP126.Main.AdamsSynthetic.NuSource.Suspension

@[expose] public section

/-! Assemble the ν-cofiber comparison on the sole correlated ExternalHypotheses witness. -/

namespace KIP126.Main.AdamsSynthetic

open private nu_source_from_suspension_square from KIP126.Main.AdamsSynthetic.NuSource.FromSuspension
open private nu_suspension_square from KIP126.Main.AdamsSynthetic.NuSource.Suspension

section NuSourceBasis
open KIP126.LinE2
set_option maxRecDepth 100000
private theorem full_basis_nu_low :
    (∀ r ∈ basisRows, r.s=1 → r.t=4 → r.monomial="2,1") ∧
    (∀ r ∈ basisRows, r.s=2 → r.t=3 → False) := by
  have h := KIP126.LinE2.BasisCertificates.NuLow.nu_low
  exact h

end NuSourceBasis

set_option backward.isDefEq.respectTransparency false in
open CategoryTheory in
theorem nuSourceResults :
    KIP126.Literature.AdamsSynthetic.NuCofiberSourceResults adamsComparison
      literature.sources.sourceComparisons.nuSource := by
  let c := KIP126.AdamsSynthetic.Standard.classicalContext
  letI : KIP126.Foundation.TensorTriangulatedStructure c.stableContext := c.tensorStructure
  letI : (CategoryTheory.MonoidalCategory.tensorLeft
      KIP126.Classical.Adams.standardFoundation.hf2.HF2).CommShift ℤ :=
    c.tensorStructure.leftShift c.stableContext.hf2.HF2
  letI : (CategoryTheory.MonoidalCategory.tensorLeft
      KIP126.Classical.Adams.standardFoundation.hf2.HF2).IsTriangulated :=
    c.tensorStructure.leftExact c.stableContext.hf2.HF2
  have hs : adamsComparison.nu.functor.map
      ((CategoryTheory.shiftFunctor KIP126.Classical.Adams.standardFoundation.Spectrum (1 : ℤ)).map
        adamsComparison.hopfAndDetector.nuMap) ≫
      (adamsComparison.nu.suspensionIso KIP126.StableHomotopy.SphereSpectrum).hom =
    (adamsComparison.nu.suspensionIso (KIP126.StableHomotopy.Sphere
      (C := KIP126.Classical.Adams.standardFoundation.Spectrum) 3)).hom ≫
      (KIP126.Synthetic.Context.SyntheticCategory.biShift (1,1)).map
        (adamsComparison.nu.functor.map adamsComparison.hopfAndDetector.nuMap) := by
    letI : CategoryTheory.SymmetricCategory
        KIP126.Classical.Adams.standardFoundation.Spectrum := c.tensorStructure.symmetric
    letI : CategoryTheory.MonoidalPreadditive
        KIP126.Classical.Adams.standardFoundation.Spectrum := c.tensorStructure.monoidalPreadditive
    letI : ∀ Z : KIP126.Classical.Adams.standardFoundation.Spectrum,
        (CategoryTheory.MonoidalCategory.tensorRight Z).CommShift ℤ := c.tensorStructure.rightShift
    exact nu_suspension_square
      (C := KIP126.Classical.Adams.standardFoundation.Spectrum)
      (Syn := KIP126.Def.standardSyntheticContext.Syn)
      (H := KIP126.Classical.Adams.standardFoundation.hf2)
      (M := KIP126.Classical.Adams.standardMilnorCooperations) adamsComparison
      c.cooperationStructure.ring c.cooperationStructure.kunneth c.cooperationStructure.basis
      KIP126.Def.standardSphereSeparated literature.theorems.synthetic_triangle_lift
      (KIP126.Main.Literature.SourceComparisons.realizationKernel_of_source adamsComparison
        literature.sources.sourceComparisons.kernelSource literature.theorems.realizationKernel
        literature.sources.sourceComparisons.kernelComparison)
  exact @nu_source_from_suspension_square
    KIP126.Classical.Adams.standardFoundation.Spectrum inferInstance inferInstance
    KIP126.Def.standardSyntheticContext.Syn inferInstance inferInstance
    KIP126.Classical.Adams.standardFoundation.hf2
    KIP126.Classical.Adams.standardMilnorCooperations
    adamsComparison KIP126.Def.standardAdamsSyntheticComparisons
    literature.theorems.synthetic_e2_weight_vanishing etaClass
    literature.sources.sourceComparisons.classicalSource literature.sources.sourceComparisons.hopfComparison
    literature.theorems.classical_nu_detection literature.theorems.classical_nu_permanent
    c.cooperationStructure.ring
    (c.tensorStructure.leftShift c.stableContext.hf2.HF2)
    (c.tensorStructure.leftExact c.stableContext.hf2.HF2)
    literature.theorems.synthetic_triangle_lift
    literature.sources.sourceComparisons.nuSource
    (computation.interpretation.presentation.comparison 1 4 (by decide)).symm
    (computation.theorems.sphereBasis.coordinates 1 4 (by decide))
    (computation.theorems.sphereBasis.csv_values 1 4 (by decide)) full_basis_nu_low.1 hs

end KIP126.Main.AdamsSynthetic
