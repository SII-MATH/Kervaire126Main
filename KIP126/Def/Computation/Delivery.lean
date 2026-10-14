module

public import KIP126.Def.Computation.Cofiber
public import KIP126.Def.Literature

/-! Correlated computation delivery, adapted from the reviewed
Interface/Challenge/Computation/Delivery. Every result refers to the same model,
source comparison, named classes and literature delivery. Producer constructions
of the archived data presentations and their correctness are deferred. -/

@[expose] section
namespace KIP126.Computation
open CategoryTheory KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.Kervaire.Route KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.Literature
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w,v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  {D : Model C Syn}

/-- The two BR21 coordinates in the externally supplied tmf data algebra.
The producer constructs this from the fixed tmf source presentation. -/
public structure DetectorData where
  component : ℕ → ℕ → ModuleCat.{v} (ZMod 2)
  v2Sixteen : component 16 112
  betaGFour : component 19 114

/-- Bounded tmf coordinates identify the exact same two literature source
classes, transported by the actual source-to-detector isomorphism. -/
public structure DetectorPresentation (L : LiteratureInterface D) (P : DetectorData.{v}) where
  comparison : ∀ s t : ℕ, t ≤ 261 →
    P.component s t ≃ₗ[ℤ] (D.classical.obj D.auxiliary.detector).Page 2 (s,t)
  v2_agrees : comparison 16 112 (by decide) P.v2Sixteen =
    (D.classical.map L.bindings.tmf.sourceIso.hom).pageMap 2 (16,112)
      L.bindings.tmfSource.v2Sixteen
  beta_agrees : comparison 19 114 (by decide) P.betaGFour =
    (D.classical.map L.bindings.tmf.sourceIso.hom).pageMap 2 (19,114)
      L.bindings.tmfSource.betaGFour

/-- Binding uses the literature delivery as a genuine dependent parameter;
its g and Δh₁g labels cannot be replaced by a different source unnoticed. -/
public structure ComputationBindings (L : LiteratureInterface D) extends Bindings D where
  cofiber : CofiberBindings toBindings
  g_agrees : toBindings.atom .g = L.bindings.tmf.g
  delta_agrees : toBindings.atom .delta_h_1_mul_g = L.bindings.tmf.deltaH1g
  detectorData : DetectorData.{v}
  detectorPresentation : DetectorPresentation L detectorData

public structure ComputationResults (L : LiteratureInterface D)
    (B : ComputationBindings L) : Prop where
  route : RouteResults B.toBindings
  cofiber : CofiberResults B.toBindings B.cofiber
  /-- Actual E₂ exhaustion at the h₆² bidegree, independent of permanence. -/
  square_nonzero : D.standardClasses.standardH6Square ≠ 0
  square_exhaustive : ∀ x : D.classical.sphere.Page 2 (2,128),
    x = 0 ∨ x = D.standardClasses.standardH6Square

/-- One computation delivery on the same supplied literature/background. -/
public structure ComputationInterface (L : LiteratureInterface D) where
  bindings : ComputationBindings L
  results : ComputationResults L bindings

namespace ComputationInterface
variable {L : LiteratureInterface D} (I : ComputationInterface L)

/-- The old section-seven table package is a derived consumer view. -/
public theorem near126 : Near126Results I.bindings.toBindings :=
  I.results.route.toNear126Results

/-- This standard one-line differential comes from the same literature
input. It is derived here rather than requested again from the computation. -/
public theorem d2_h6 (L : LiteratureInterface D) :
    HasNonzeroDifferential D.classical.sphere 2 (1,64) (3,65)
      (Bindings.h6 (D := D))
      (Bindings.product (D := D) (Bindings.h0 (D := D)) (Bindings.h5Square (D := D))) := by
  have h := L.results.classicalRange.adamsOneLine_d2 6 (by decide)
  change HasNonzeroDifferential D.classical.sphere 2 (1,64) (3,65)
    (Bindings.h6 (D := D))
    (Bindings.product (D := D) (Bindings.h0 (D := D)) (Bindings.h5Square (D := D))) at h
  exact h

/-- The actual detector differential is transported from literature and then
rewritten using the chosen computation coordinates; it is not a new input. -/
public theorem detector_d3 :
    HasDifferential (D.classical.obj D.auxiliary.detector) 3 (16,112) (19,114)
      (I.bindings.detectorPresentation.comparison 16 112 (by decide)
        I.bindings.detectorData.v2Sixteen)
      (I.bindings.detectorPresentation.comparison 19 114 (by decide)
        I.bindings.detectorData.betaGFour) := by
  rw [I.bindings.detectorPresentation.v2_agrees, I.bindings.detectorPresentation.beta_agrees]
  exact L.results.tmf.detector_d3 D
end ComputationInterface
end KIP126.Computation
