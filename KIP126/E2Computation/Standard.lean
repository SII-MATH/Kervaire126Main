module

public import KIP126.E2Computation.Basis
public import KIP126.AdamsSynthetic.Standard.Background
public import KIP126.Literature

/-! Fixed E₂ archive, actual-page comparisons, products and coordinate labels.
No later Adams differential, survival or extension result is imported here. -/

set_option backward.isDefEq.respectTransparency false

@[expose] section
namespace KIP126.Computation.Standard
open CategoryTheory KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.AdamsSynthetic.Standard

/-- The complete generator catalogue of the pinned sphere archive. -/
public noncomputable def generators : GeneratorCatalogue := by sorry
public noncomputable def atomIndex (a : Atom) : Fin generators.count := by sorry
public theorem atom_record (a : Atom) :
    ((atomIndex a).val, generators.record (atomIndex a)) = a.record := by sorry
public noncomputable def basisCount : ℕ → ℕ → ℕ := by sorry
public noncomputable def basisMonomial (s t : ℕ) (i : Fin (basisCount s t)) :
    SourceMonomial generators s t := by sorry

/-- The one fixed archive, retaining all generators and every bounded monomial. -/
public noncomputable def archive : SphereArchive where
  generators := generators
  atomIndex := atomIndex
  atom_record := atom_record
  basisCount := basisCount
  basisMonomial := basisMonomial

public noncomputable def sourceComponent : ℕ → ℕ → ModuleCat.{0} (ZMod 2) := by sorry
public noncomputable def sourceProduct (s t s' t' : ℕ) :
    sourceComponent s t →ₗ[ZMod 2] sourceComponent s' t' →ₗ[ZMod 2]
      sourceComponent (s+s') (t+t') := by sorry
public noncomputable def sourceUnit : sourceComponent 0 0 := by sorry
public noncomputable def sourceAtom (a : Atom) : sourceComponent a.degree.1 a.degree.2 := by sorry
public noncomputable def sourceData : ProgramData.{0} where
  component := sourceComponent
  product := sourceProduct
  unit := sourceUnit
  atom := sourceAtom
public noncomputable def sourceGenerator (i : Fin archive.generators.count) :
    sourceData.component (archive.generators.degree i).1 (archive.generators.degree i).2 := by sorry
public theorem sourceAtom_agrees (a : Atom) :
    (eqToHom (congrArg (fun d : ℕ × ℕ => sourceData.component d.1 d.2)
      (archive.atom_degree a))) (sourceGenerator (archive.atomIndex a)) = sourceData.atom a := by sorry
public noncomputable def sourceCoordinates (s t : ℕ) (ht : t ≤ 261) :
    sourceData.component s t ≃ₗ[ℤ] (Fin (archive.basisCount s t) →₀ ZMod 2) := by sorry
public theorem sourceBasis_values (s t : ℕ) (ht : t ≤ 261)
    (i : Fin (archive.basisCount s t)) :
    (sourceCoordinates s t ht).symm (Finsupp.single i 1) =
      (archive.basisMonomial s t i).value sourceData sourceGenerator := by sorry

private noncomputable def sourceBasis : SourceBasisSpecification sourceData archive where
  generator := sourceGenerator
  atom_agrees := sourceAtom_agrees
  coordinates := sourceCoordinates
  basis_values := sourceBasis_values

/-- Comparison with the actual project sphere; its bounded range is explicit. -/
public noncomputable def comparison (s t : ℕ) (ht : t ≤ 261) :
    sourceData.component s t ≃ₗ[ℤ] model.classical.sphere.Page 2 (s,t) := by sorry
public theorem comparison_product (s t s' t' : ℕ) (ht : t+t' ≤ 261)
    (x : sourceData.component s t) (y : sourceData.component s' t') :
    comparison (s+s') (t+t') ht (sourceData.product s t s' t' x y) =
      model.sphereAlgebra.product (s,t) (s',t')
        (comparison s t (by omega) x) (comparison s' t' (by omega) y) := by sorry
public theorem comparison_unit : comparison 0 0 (by decide) sourceData.unit =
    model.sphereAlgebra.unit := by sorry
public theorem comparison_h0 : comparison 1 1 (by decide) (sourceData.atom .h0) =
    model.standardClasses.standardHi 0 := by sorry
public theorem comparison_h1 : comparison 1 2 (by decide) (sourceData.atom .h1) =
    model.standardClasses.standardHi 1 := by sorry
public theorem comparison_h2 : comparison 1 4 (by decide) (sourceData.atom .h2) =
    model.standardClasses.standardHi 2 := by sorry
public theorem comparison_h4 : comparison 1 16 (by decide) (sourceData.atom .h4) =
    model.standardClasses.standardHi 4 := by sorry
public theorem comparison_h5 : comparison 1 32 (by decide) (sourceData.atom .h5) =
    model.standardClasses.standardHi 5 := by sorry
public theorem comparison_h6 : comparison 1 64 (by decide) (sourceData.atom .h6) =
    model.standardClasses.standardH6 := by sorry

private noncomputable def presentation : SpherePresentation model sourceData where
  comparison := comparison
  comparison_product := comparison_product
  comparison_unit := comparison_unit
  h0 := comparison_h0
  h1 := comparison_h1
  h2 := comparison_h2
  h4 := comparison_h4
  h5 := comparison_h5
  h6 := comparison_h6
public noncomputable def atom (a : Atom) :
    model.classical.sphere.Page 2 (a.degree.1,a.degree.2) :=
  comparison a.degree.1 a.degree.2 (by cases a <;> decide) (sourceData.atom a)

public noncomputable abbrev h0 : model.classical.sphere.Page 2 (1,1) := model.standardClasses.standardHi 0
public noncomputable abbrev h1 : model.classical.sphere.Page 2 (1,2) := model.standardClasses.standardHi 1
public noncomputable abbrev h2 : model.classical.sphere.Page 2 (1,4) := model.standardClasses.standardHi 2
public noncomputable abbrev h4 : model.classical.sphere.Page 2 (1,16) := model.standardClasses.standardHi 4
public noncomputable abbrev h5 : model.classical.sphere.Page 2 (1,32) := model.standardClasses.standardHi 5
public noncomputable abbrev h6 := model.standardClasses.standardH6
public noncomputable abbrev h6Square := model.standardClasses.standardH6Square

public noncomputable def product {p q r : Bidegree}
    (x : model.classical.sphere.Page 2 p) (y : model.classical.sphere.Page 2 q)
    (h : p + q = r := by decide) : model.classical.sphere.Page 2 r :=
  (eqToHom (congrArg (model.classical.sphere.Page 2) h))
    (model.sphereAlgebra.product p q x y)

public noncomputable def h0Square : model.classical.sphere.Page 2 (2,2) :=
  product h0 h0
public noncomputable def h0Six : model.classical.sphere.Page 2 (6,6) :=
  product (product (r := (4,4)) h0Square h0Square) h0Square
public noncomputable def h5Square : model.classical.sphere.Page 2 (2,64) :=
  product h5 h5
public noncomputable def W : model.classical.sphere.Page 2 (8,134) :=
  atom .x_126_8_4 + atom .x_126_8
public noncomputable def U : model.classical.sphere.Page 2 (10,134) :=
  product h0Square (atom .x_124_8)
public noncomputable def T : model.classical.sphere.Page 2 (14,139) :=
  product h1 (product (r := (13,137)) h4 (atom .x_109_12))
public noncomputable def V : model.classical.sphere.Page 2 (9,132) :=
  atom .x_123_9 + product (r := (9,132)) h0 (atom .x_123_8)
public noncomputable def Y : model.classical.sphere.Page 2 (11,136) :=
  product h0Square (atom .x_125_9_2)
public noncomputable def X : model.classical.sphere.Page 2 (8,130) :=
  product h1 (atom .x_121_7)
public noncomputable def P : model.classical.sphere.Page 2 (11,133) :=
  product h6 (atom .M_mul_d_0)
public noncomputable def Q : model.classical.sphere.Page 2 (12,134) :=
  product h5 (atom .x_91_11)
public noncomputable def correction : model.classical.sphere.Page 2 (13,137) :=
  product (atom .e0) (atom .delta_h_6_mul_g)
public noncomputable def highClass : model.classical.sphere.Page 2 (25,150) :=
  product (product (r := (16,96)) (product (r := (8,48)) (atom .g) (atom .g))
    (product (r := (8,48)) (atom .g) (atom .g))) (atom .delta_h_1_mul_g)
public noncomputable def d2Target : model.classical.sphere.Page 2 (10,134) :=
  product (r := (10,134)) h1 V + U
public noncomputable def d7Source : model.classical.sphere.Page 2 (11,134) :=
  atom .x_123_11_2 + atom .x_123_11 +
    product (r := (11,134)) (product (r := (2,65)) h0 h6) (atom .b4)
public noncomputable def d3Candidate : model.classical.sphere.Page 2 (9,134) :=
  product h5 (atom .x_94_8)
public noncomputable def d3OtherCandidate : model.classical.sphere.Page 2 (9,134) :=
  d3Candidate + product (r := (9,134)) h6 (atom .b)

public theorem atom_h0 : atom .h0 = h0  := presentation.h0
public theorem atom_h1 : atom .h1 = h1  := presentation.h1
public theorem atom_h2 : atom .h2 = h2  := presentation.h2
public theorem atom_h4 : atom .h4 = h4  := presentation.h4
public theorem atom_h5 : atom .h5 = h5  := presentation.h5
public theorem atom_h6 : atom .h6 = h6  := presentation.h6

/-- The complete actual-page coordinates, including spanning and independence. -/
public noncomputable def coordinates (s t : ℕ) (ht : t ≤ 261) :
    model.classical.sphere.Page 2 (s,t) ≃ₗ[ℤ] (Fin (archive.basisCount s t) →₀ ZMod 2) :=
  (comparison s t ht).symm.trans (sourceCoordinates s t ht)

public noncomputable def comparisonF2 (s t : ℕ) (ht : t ≤ 261) :
    letI := model.sphereAlgebra.scalar (s,t)
    sourceData.component s t ≃ₗ[ZMod 2] model.classical.sphere.Page 2 (s,t) :=
  by
  letI := model.sphereAlgebra.scalar (s,t)
  exact { (comparison s t ht).toAddEquiv with
    map_smul' := fun a x => ZMod.map_smul (comparison s t ht).toAddMonoidHom a x }

public theorem coordinates_basis (s t : ℕ) (ht : t ≤ 261)
    (i : Fin (archive.basisCount s t)) :
    (coordinates s t ht).symm (Finsupp.single i 1) =
      comparison s t ht ((archive.basisMonomial s t i).value sourceData sourceGenerator) :=
  presentation.coordinates_basis sourceBasis s t ht i

public theorem comparison_symm_coordinates_basis (s t : ℕ) (ht : t ≤ 261)
    (i : Fin (archive.basisCount s t)) :
    (comparison s t ht).symm ((coordinates s t ht).symm (Finsupp.single i 1)) =
      (archive.basisMonomial s t i).value sourceData sourceGenerator :=
  presentation.comparison_symm_coordinates_basis sourceBasis s t ht i

public theorem h6_square : comparison 2 128 (by decide)
    (sourceData.product 1 64 1 64 (sourceData.atom .h6) (sourceData.atom .h6)) =
    h6Square := presentation.h6_square

public theorem h5Square_b_zero : product (r := (10,134)) h5Square (atom .b) = 0 := by sorry

public theorem t_not_h0_multiple : ¬ ∃ a : model.classical.sphere.Page 2 (13,138),
    product (r := (14,139)) h0 a = T := by sorry

public theorem t_not_h2_multiple : ¬ ∃ a : model.classical.sphere.Page 2 (13,135),
    product (r := (14,139)) h2 a = T := by sorry

public theorem x_h2_zero : product (r := (9,134)) X h2 = 0 := by sorry

public theorem y_not_h2_multiple : ¬ ∃ a : model.classical.sphere.Page 2 (10,132),
    product (r := (11,136)) h2 a = Y := by sorry

public theorem h1_correction_zero : product (r := (14,139)) h1 correction = 0 := by sorry

public theorem e2_stem125_low : ∀ s : ℕ, s ≤ 4 →
    Subsingleton (model.classical.sphere.Page 2 (s,(s : ℤ)+125)) := by sorry

public theorem square_nonzero : h6Square ≠ 0 := by sorry
public theorem square_exhaustive (x : model.classical.sphere.Page 2 (2,128)) :
    x = 0 ∨ x = h6Square := by sorry

public abbrev nuCofiberSequence :=
  model.classical.obj (HasFunctorialCofiber.cofib model.auxiliary.nuMap)
public noncomputable def bottom (s t : ℤ) :
    model.classical.sphere.Page 2 (s,t) →ₗ[ℤ] nuCofiberSequence.Page 2 (s,t) :=
  (model.classical.pageMap (HasFunctorialCofiber.cofibι model.auxiliary.nuMap) 2 (s,t)).hom
public noncomputable def topCell : nuCofiberSequence.Page 2 (8,134) := by sorry
/-- The selected label is tied to the actual connecting arrow and four
specified sphere desuspensions. -/
public theorem top_comparison :
  ∃ (a3 : (model.classical.obj (Sphere 3)).Page 2 (8,133))
    (a2 : (model.classical.obj (Sphere 2)).Page 2 (8,132))
    (a1 : (model.classical.obj (Sphere 1)).Page 2 (8,131)),
    (model.classicalSuspension (.shift 3 .sphere)).DesuspendsClass 8 134
      (model.classical.pageMap (HasFunctorialCofiber.cofibδ model.auxiliary.nuMap) 2 (8,134) topCell) a3 ∧
    (model.classicalSuspension (.shift 2 .sphere)).DesuspendsClass 8 133
      (model.classical.pageMap
        ((shiftFunctorAdd' Spectrum (2 : ℤ) 1 3 (by decide)).hom.app SphereSpectrum)
        2 (8,133) a3) a2 ∧
    (model.classicalSuspension (.shift 1 .sphere)).DesuspendsClass 8 132
      (model.classical.pageMap
        ((shiftFunctorAdd' Spectrum (1 : ℤ) 1 2 (by decide)).hom.app SphereSpectrum)
        2 (8,132) a2) a1 ∧
    (model.classicalSuspension .sphere).DesuspendsClass 8 131 a1 X := by sorry
public noncomputable def cofiberSource : nuCofiberSequence.Page 2 (8,134) :=
  topCell + bottom 8 134 (atom .x_126_8_2) + bottom 8 134 (atom .x_126_8)
/-- The computation labels coincide with the same fixed literature labels. -/
public theorem g_agrees : atom .g = KIP126.Literature.Standard.g := by sorry
public theorem delta_agrees : atom .delta_h_1_mul_g = KIP126.Literature.Standard.deltaH1g := by sorry

/-- The pinned detector calculation, before comparison with the actual object. -/
public noncomputable def detectorComponent : ℕ → ℕ → ModuleCat.{0} (ZMod 2) := by sorry
public noncomputable def detectorV2Sixteen : detectorComponent 16 112 := by sorry
public noncomputable def detectorBetaGFour : detectorComponent 19 114 := by sorry
public noncomputable def detectorComparison (s t : ℕ) (ht : t ≤ 261) :
    detectorComponent s t ≃ₗ[ℤ] (model.classical.obj model.auxiliary.detector).Page 2 (s,t) := by sorry
public theorem detector_v2_agrees : detectorComparison 16 112 (by decide) detectorV2Sixteen =
    (model.classical.map KIP126.Literature.Standard.tmfIso.hom).pageMap 2 (16,112)
      KIP126.Literature.Standard.tmfV2Sixteen := by sorry
public theorem detector_beta_agrees : detectorComparison 19 114 (by decide) detectorBetaGFour =
    (model.classical.map KIP126.Literature.Standard.tmfIso.hom).pageMap 2 (19,114)
      KIP126.Literature.Standard.tmfBetaGFour := by sorry

end KIP126.Computation.Standard
