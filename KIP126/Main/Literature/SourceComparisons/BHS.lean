module

public import KIP126.Main.ExternalHypotheses.Data
public import KIP126.Main.Literature.AdamsSynthetic.Theorems
public import KIP126.Main.AdamsSynthetic.SphereConvergence

@[expose] public section

/-! BHS theorems and comparison with completed objects.

The statements retain the hypotheses of BHS A.1(2) and cor:tau-surj
(Source/BHS/source/SynRevBigraded.tex and SynRevAdams.tex). Completion maps
and their image, divisibility and realization comparisons transport the
source theorems. Specialization to the sphere uses Def's accepted
standard-sphere applicability hypothesis; source nilpotent completeness
and strong convergence remain explicit.
-/
namespace KIP126.Main.Literature.SourceComparisons
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.Synthetic.Context KIP126.AdamsSynthetic
open KIP126.Literature.AdamsSynthetic

/-- The actual selected ν cofiber has finite mod-two homology, by exact
tensoring of its sphere triangle. No Hopf detection or literature input is used. -/
theorem standard_nu_cofiber_finite_mod2_type :
    FiniteMod2Type standardFoundation.hf2
      (ClassicalObject.obj (C := standardFoundation.Spectrum)
        standardAdamsComparison.hopfAndDetector .nuCofiber) := by
  let c := KIP126.AdamsSynthetic.Standard.classicalContext
  letI : KIP126.Foundation.TensorTriangulatedStructure c.stableContext := c.tensorStructure
  letI : (tensorLeft standardFoundation.hf2.HF2).CommShift ℤ :=
    KIP126.Foundation.TensorTriangulatedStructure.leftShift (F := c.stableContext) _
  letI : (tensorLeft standardFoundation.hf2.HF2).IsTriangulated :=
    KIP126.Foundation.TensorTriangulatedStructure.leftExact (F := c.stableContext) _
  have hs : FiniteMod2Type standardFoundation.hf2 SphereSpectrum :=
    KIP126.Def.standardSphereFiniteMod2Type
  exact FiniteMod2Type.of_cofiber
    (HoCofiberSequence.ofMorphism (C := standardFoundation.Spectrum)
      standardAdamsComparison.hopfAndDetector.nuMap) (hs.shift 3) hs

/-- Apply BHS `cor:synth-ctau-ASS` (1),(3) on the same supplied synthetic
family and positive finite lambda quotient. This projection retains all
finite pages r >= 2 and both weight inequalities. It does not derive an
E3 or E7 zero region from an E-infinity-only comparison, and it supplies no
new computation result. The field is supplied with the other BHS literature
statements. -/
theorem bhs_finite_quotient_page_vanishing
    (syntheticContext : StandardSyntheticContext) (source : SyntheticSourceTheorems syntheticContext.adamsComparison) :
    FiniteQuotientPageVanishing syntheticContext.adamsComparison :=
  source.finite_quotient_page_vanishing

/-- Apply BHS A.1(2) to the specified synthetic context and source object,
with the source completeness and strong-convergence hypotheses explicit. -/
theorem bhs_permanent_lift_of_complete_source
    (syntheticContext : StandardSyntheticContext) (source : SyntheticSourceTheorems syntheticContext.adamsComparison)
    (X : standardFoundation.Spectrum)
    (products : HasProductsOfShape ℕ standardFoundation.Spectrum)
    (hX : BHSObjectApplicability products standardFoundation.hf2.unit X) :
    BHSPermanentLiftAt syntheticContext.adamsComparison X :=
  source.permanent_lift X products hX

/-- BHS cor:tau-surj on that same source. -/
theorem bhs_filtration_lambda_of_complete_source
    (syntheticContext : StandardSyntheticContext) (source : SyntheticSourceTheorems syntheticContext.adamsComparison)
    (X : standardFoundation.Spectrum)
    (products : HasProductsOfShape ℕ standardFoundation.Spectrum)
    (hX : BHSObjectApplicability products standardFoundation.hf2.unit X) :
    BHSFiltrationLambdaAt syntheticContext.adamsComparison X :=
  source.filtration_lambda X products hX

/-- Specialize the source theorem to the sphere using its fixed
completeness and strong-convergence hypotheses from Def. -/
theorem standard_sphere_permanent_lift
    (syntheticContext : StandardSyntheticContext) (source : SyntheticSourceTheorems syntheticContext.adamsComparison) :
    BHSPermanentLiftAt syntheticContext.adamsComparison SphereSpectrum :=
  bhs_permanent_lift_of_complete_source syntheticContext source _ _
    KIP126.Def.standardSphereApplicability

theorem standard_sphere_filtration_lambda
    (syntheticContext : StandardSyntheticContext) (source : SyntheticSourceTheorems syntheticContext.adamsComparison) :
    BHSFiltrationLambdaAt syntheticContext.adamsComparison SphereSpectrum :=
  bhs_filtration_lambda_of_complete_source syntheticContext source _ _
    KIP126.Def.standardSphereApplicability

/-- The remaining untruncated clauses of BHS A.1 on an applicable source.
The classical convergence is canonical for that SAME source object's tower. -/
theorem bhs_realization_of_complete_source
    (syntheticContext : StandardSyntheticContext)
    (R : RealizationCoordinates syntheticContext.adamsComparison)
    (source : BHSRealizationSourceResults syntheticContext.adamsComparison R)
    (X : standardFoundation.Spectrum)
    (products : HasProductsOfShape ℕ standardFoundation.Spectrum)
    (hX : BHSObjectApplicability products standardFoundation.hf2.unit X)
    (convergence : TowerDetection.Convergence standardFoundation.hf2.unit X) :
    BHSRealizationDetectionAt syntheticContext.adamsComparison R X convergence :=
  source X products hX convergence

section Transport
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H}

/-- Transport source lifetime/detection and the two existential lift clauses.
The hypotheses contain actual q/νq maps, canonical detection comparison,
realization naturality, and the precise prescribed/torsion image reflections.
The proof uses λ naturality and the source clauses; it never calls a paper
proposition, ExternalHypotheses, or a high125 conclusion. -/
theorem realization_detection_of_completed_sources
    (D : AdamsComparison H M Syn) (R : RealizationCoordinates D) (Q : BHSCompletionData D)
    (source : BHSRealizationSourceResults D R)
    (applicable : BHSCompletionApplicability D Q)
    (comparison : BHSCompletionComparison D Q)
    (realization : BHSRealizationComparison D R Q) : RealizationDetection D R := by
  constructor
  · intro X s t r hr x a hx hs ha
    have h := (source (Q.completed X) Q.products (applicable.source X)
      (Q.convergence X)).lifetime s t r hr
      (adamsInternalE2Induced H.unit (Q.map X) (s,t) x)
      (a ≫ (SyntheticCategory.biShift (0,0)).map (D.nu.functor.map (Q.map X)))
      ((comparison.permanent_cycles X s t x).mp hx)
      ((realization.survives_to X s t r x).mp hs)
      (realization.first_quotient_natural X s t x a ha)
    intro hz
    apply h
    simpa only [lambdaMultiply, Category.assoc, zero_comp] using
      congrArg (fun z => z ≫ (SyntheticCategory.biShift (0,0)).map
        (D.nu.functor.map (Q.map X))) hz
  · intro X s t x a hx ha
    apply (realization.detection X s t x (realizeNuZero D R X a)).mpr
    rw [realization.realization_natural]
    exact (source (Q.completed X) Q.products (applicable.source X)
      (Q.convergence X)).detection s t
      (adamsInternalE2Induced H.unit (Q.map X) (s,t) x)
      (a ≫ (SyntheticCategory.biShift (0,0)).map (D.nu.functor.map (Q.map X)))
      ((realization.nonzero_survival X s t x).mp hx)
      (realization.first_quotient_natural X s t x a ha)
  · intro X s t x α hx hα
    apply realization.prescribed_lift_reflection X s t x α
    exact (source (Q.completed X) Q.products (applicable.source X)
      (Q.convergence X)).prescribed_lift s t
      (adamsInternalE2Induced H.unit (Q.map X) (s,t) x) (α ≫ Q.map X)
      ((realization.nonzero_survival X s t x).mp hx)
      ((realization.detection X s t x α).mp hα)
  · intro X s t r hr y hy hh
    apply realization.torsion_lift_reflection X s t (r-1) y
    exact (source (Q.completed X) Q.products (applicable.source X)
      (Q.convergence X)).boundary_lift s t r hr
      (adamsInternalE2Induced H.unit (Q.map X) (s,t) y)
      ((comparison.permanent_cycles X s t y).mp hy)
      ((realization.hit_on_page X s t r y).mp hh)
end Transport

end KIP126.Main.Literature.SourceComparisons
