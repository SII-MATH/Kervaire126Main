module

public import KIP126.Computation.LinCoordinates.Interpretation.SphereAndCofiber.Data
public import KIP126.Computation.LinCoordinates.Model.BasisCatalogue.Data
public import KIP126.Def.ClassicalAdams.TowerNaturality.Page.Data
public import KIP126.Def.SpectralSequence.Computation.CyclesAndBoundaries.Predicates

@[expose] public section

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

/-- Mathematical interpretation, including successful coordinate decoding.
Nonzero on E₂ is never substituted for nonzero on a later page. -/
def AdamsStatement {D : AdamsComparison H M Syn} (R : E2Interpretation D) (c : Raw.Claim) : Prop :=
  ∃ x, R.coordinateSum c.spectrum c.s c.t c.x = some x ∧
    match c.kind with
    | .reaches => ReachesPage (sequence D c.spectrum) c.r (c.s,c.t) x
    | .boundaryBy => IsBoundaryBy (sequence D c.spectrum) c.r (c.s,c.t) x
    | .equation => ∃ y, R.coordinateSum c.spectrum c.ts c.tt c.y = some y ∧
        HasDifferential (sequence D c.spectrum) c.r (c.s,c.t) (c.ts,c.tt) x y
    | .refutation => ∃ y, R.coordinateSum c.spectrum c.ts c.tt c.y = some y ∧
        ¬ HasDifferential (sequence D c.spectrum) c.r (c.s,c.t) (c.ts,c.tt) x y

/-- Explicit additive bases, including empty degrees and ALL linear combinations.
An integer-linear equivalence to F₂ coordinates uses the actual additive group;
it neither chooses a second group law nor postulates a new scalar action. -/
def BasisEquivalence {D : AdamsComparison H M Syn} (R : E2Interpretation D) (d : Raw.Degree) : Prop :=
  ∃ e : Page D d.spectrum d.s d.t ≃ₗ[ℤ]
      (Fin d.monomials.length →₀ KIP126.Algebra.F2),
    ∀ i, e.symm (Finsupp.single i 1) = R.basis d.spectrum d.s d.t i.val

/-- Each selected sphere basis value is the specified CSV monomial, interpreted
through the same comparison used for named elements and products. Homogeneity
is a required witness; no invalid monomial is silently mapped to zero. -/
def SphereMonomialComparison {D : AdamsComparison H M Syn} (R : E2Interpretation D)
    (d : Raw.Degree) : Prop :=
  d.spectrum = .sphere → ∀ i : Fin d.monomials.length,
    ∃ z : E2At d.s d.t,
      z.val = projection (monomialOfString d.monomials[i]) ∧
      R.sphere d.s d.t z = R.basis .sphere d.s d.t i.val

/-- Only the selected product degrees, using the relation quotient, not a stored
multiplication table. Both operations are fixed before this condition is stated. -/
def SphereProductComparison {D : AdamsComparison H M Syn} (R : E2Interpretation D) (p : Raw.Product) : Prop :=
  ∀ (x : E2At p.s p.t) (y : E2At p.sp p.tp),
    R.sphere (p.s+p.sp) (p.t+p.tp) (mulAt x y) =
      Sphere.Internal.product H M (R.sphere p.s p.t x) (R.sphere p.sp p.tp y)

/-- Bottom-cell labels are images under the actual inclusion of the same cofiber. -/
def CofiberInclusionComparison {D : AdamsComparison H M Syn} (R : E2Interpretation D) (p : Raw.BottomMap) : Prop :=
  ∃ x y, R.coordinateSum .sphere p.s p.t p.x = some x ∧
    R.coordinateSum .nuCofiber p.s p.t p.y = some y ∧
    adamsInternalE2Induced H.unit (HasFunctorialCofiber.cofibι D.hopfAndDetector.nuMap)
      (p.s,p.t) x = y

/-- The top-cell value is compared via D's actual tower suspension data, not
an arbitrary degree-shifted linear map. Two canonical shift-addition maps
and four one-fold desuspensions identify Σ(S³) with S⁰ in degree t-4. -/
def CofiberBoundaryComparison {D : AdamsComparison H M Syn} (R : E2Interpretation D) : Prop :=
  ∃ (x : Page D .nuCofiber 8 134) (y : Page D .sphere 8 130)
    (a3 : E2 H (Sphere 3) 8 133)
    (a2 : E2 H (Sphere 2) 8 132)
    (a1 : E2 H (Sphere 1) 8 131),
    R.coordinateSum .nuCofiber 8 134 [0] = some x ∧
    R.coordinateSum .sphere 8 130 [0] = some y ∧
    (D.classicalSuspension (.shift 3 .sphere)).DesuspendsClass 8 134
      (adamsInternalE2Induced H.unit (HasFunctorialCofiber.cofibδ D.hopfAndDetector.nuMap)
        (8,134) x) a3 ∧
    (D.classicalSuspension (.shift 2 .sphere)).DesuspendsClass 8 133
      (adamsInternalE2Induced H.unit
        ((shiftFunctorAdd' C (2 : ℤ) 1 3 (by decide)).hom.app SphereSpectrum)
        (8,133) a3) a2 ∧
    (D.classicalSuspension (.shift 1 .sphere)).DesuspendsClass 8 132
      (adamsInternalE2Induced H.unit
        ((shiftFunctorAdd' C (1 : ℤ) 1 2 (by decide)).hom.app SphereSpectrum)
        (8,132) a2) a1 ∧
    (D.classicalSuspension .sphere).DesuspendsClass 8 131 a1 y

end
end KIP126.Computation.SphereAndCofiber
