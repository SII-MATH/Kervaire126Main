module

public import KIP126.Computation.LinCoordinates.Interpretation.SphereAndCofiber.Predicates
public import KIP126.Def.AdamsSynthetic.SphereClasses.Tmf.Data

@[expose] public section

/-! Computation theorems for one E₂ interpretation and its distinguished classes. -/

namespace KIP126.Computation.SphereAndCofiber
open CategoryTheory
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology KIP126.Classical.Adams
open KIP126.SpectralSequence KIP126.Synthetic.Context KIP126.AdamsSynthetic
open KIP126.LinE2
universe u v w
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H}

/-- Identification of the specified computation coordinates with the Milnor
classes and the distinguished sphere and tmf classes on E₂. -/
structure DistinguishedClassComparison {D : AdamsComparison H M Syn} (R : E2Interpretation D)
    (L : SphereAdamsClasses H) (G : KIP126.Literature.AdamsSynthetic.TmfDetectionClasses H) : Prop where
  h0 : R.sphere 1 1 dataH0 = Sphere.Internal.hi H M 0
  h1 : R.sphere 1 2 dataH1 = Sphere.Internal.hi H M 1
  h2 : R.sphere 1 4 (Near126.atom .h2) = Sphere.Internal.hi H M 2
  h4 : R.sphere 1 16 (Near126.atom .h4) = Sphere.Internal.hi H M 4
  h5 : R.sphere 1 32 (Near126.atom .h5) = Sphere.Internal.hi H M 5
  h6 : R.sphere 1 64 dataH6 = Sphere.Internal.hi H M 6
  h0_square : R.sphere 2 2 Near126.h0Sq = Sphere.Internal.hiSquare H M 0
  h5_square : R.sphere 2 64 Near126.h5Sq = Sphere.Internal.hiSquare H M 5
  h6_square : R.sphere 2 128 dataH6Sq = Sphere.Internal.hiSquare H M 6
  x_126_8_4 : R.sphere 8 134 (Near126.atom .x_126_8_4) = L.x_126_8_4
  x_126_8 : R.sphere 8 134 (Near126.atom .x_126_8) = L.x_126_8
  x_124_8 : R.sphere 8 132 (Near126.atom .x_124_8) = L.x_124_8
  x_109_12 : R.sphere 12 121 (Near126.atom .x_109_12) = L.x_109_12
  g : R.sphere 4 24 (Near126.atom .g) = G.g
  delta_h_1_mul_g : R.sphere 9 54 (Near126.atom .delta_h_1_mul_g) = G.delta_h_1_mul_g

/-- The finite sphere and Cν computations on one E₂ interpretation:
basis equivalences, monomials, products, distinguished classes, Adams
statements, and comparison with the cofiber inclusion and boundary maps. -/
structure AdamsComputationTheorems (D : AdamsComparison H M Syn) (L : SphereAdamsClasses H)
    (G : KIP126.Literature.AdamsSynthetic.TmfDetectionClasses H) where
  interpretation : E2Interpretation D
  basis : ∀ d ∈ Raw.degrees, BasisEquivalence interpretation d
  monomials : ∀ d ∈ Raw.degrees, SphereMonomialComparison interpretation d
  products : ∀ p ∈ Raw.products, SphereProductComparison interpretation p
  distinguishedClasses : DistinguishedClassComparison interpretation L G
  adamsStatements : ∀ c ∈ Raw.claims, AdamsStatement interpretation c
  cofiberInclusion : ∀ p ∈ Raw.bottomMaps, CofiberInclusionComparison interpretation p
  cofiberBoundary : CofiberBoundaryComparison interpretation

/-- The seven mathematical comparison and correctness conditions for the
specified E₂ interpretation, sphere classes and tmf classes. -/
structure E2InterpretationCorrect {D : AdamsComparison H M Syn} (R : E2Interpretation D)
    (L : SphereAdamsClasses H) (G : KIP126.Literature.AdamsSynthetic.TmfDetectionClasses H) : Prop where
  basis : ∀ d ∈ Raw.degrees, BasisEquivalence R d
  monomials : ∀ d ∈ Raw.degrees, SphereMonomialComparison R d
  products : ∀ p ∈ Raw.products, SphereProductComparison R p
  distinguishedClasses : DistinguishedClassComparison R L G
  adamsStatements : ∀ c ∈ Raw.claims, AdamsStatement R c
  cofiberInclusion : ∀ p ∈ Raw.bottomMaps, CofiberInclusionComparison R p
  cofiberBoundary : CofiberBoundaryComparison R

/-- Joint existence, not correctness for an arbitrary interpretation/label. -/
def E2InterpretationExists (D : AdamsComparison H M Syn) (G : KIP126.Literature.AdamsSynthetic.TmfDetectionClasses H) : Prop :=
  ∃ (R : E2Interpretation D) (L : SphereAdamsClasses H), E2InterpretationCorrect R L G

/-- The specified E₂ interpretation together with its computation theorems. -/
def E2InterpretationCorrect.toComputationTheorems {D : AdamsComparison H M Syn} {R : E2Interpretation D}
    {L : SphereAdamsClasses H} {G : KIP126.Literature.AdamsSynthetic.TmfDetectionClasses H}
    (h : E2InterpretationCorrect R L G) : AdamsComputationTheorems D L G where
  interpretation := R
  basis := h.basis
  monomials := h.monomials
  products := h.products
  distinguishedClasses := h.distinguishedClasses
  adamsStatements := h.adamsStatements
  cofiberInclusion := h.cofiberInclusion
  cofiberBoundary := h.cofiberBoundary

end
end KIP126.Computation.SphereAndCofiber
