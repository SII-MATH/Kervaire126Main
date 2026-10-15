module

public import KIP126.Def.Kervaire.Theta5.Synthetic.Data
public import KIP126.Def.Synthetic.Sphere.Homotopy.Predicates
public import KIP126.Def.SpectralSequence.Computation.Predicates

@[expose] public section

/-! Precise source and paper-normalized conditions on actual objects.
Defining these predicates does not prove the literature inputs or the paper's
conversion. No record field can supply a replacement survival/zero predicate. -/
namespace KIP126.Kervaire
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Synthetic.Context KIP126.Comparison.ClassicalSynthetic
open KIP126.Classical.Adams KIP126.SpectralSequence
open SyntheticTheta5
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  (H : Mod2EilenbergMacLane (C := C)) (M : MilnorCooperations H)
  (comparison : SphereFirstQuotientComparison H Syn)

/-- A lift of the actual standard h₅² through the first λ quotient.
Constructing the canonical comparison, or proving uniqueness of lifts, is not
part of this definition. The degree (s,t)=(2,64) gives (t-s,t)=(62,64). -/
def SyntheticTheta5.DetectsTheta (θ : Theta Syn) : Prop :=
  comparison 2 64 (quotientClass 1 θ) = Sphere.Internal.hiSquare H M 5

/-- The same comparison detects the candidate η by the standard h₁.
This does not itself prove its identification with a chosen geometric Hopf map. -/
def SyntheticTheta5.DetectsEta (η : Eta Syn) : Prop :=
  comparison 1 2 (quotientClass 1 η) = Sphere.Internal.hi H M 1

/-- Original finite BX condition at a specified source choice, with its
order and detection hypotheses recorded explicitly. Source: Proposition 7.19,
local kervairev2.tex:587–600. It uses η / λ^r, not the LWX normalized formula.
Supplying a proof for this predicate is still an external mathematical input. -/
def BJMOriginalCriterion (η : Eta Syn) (θ : Theta Syn) : Prop :=
  SyntheticTheta5.DetectsEta H M comparison η ∧
  SyntheticTheta5.DetectsTheta H M comparison θ ∧ θ + θ = 0 ∧
  ∀ r : ℕ, 1 ≤ r →
    (SurvivesTo (adamsTowerInternalSpectralSequence H.unit SphereSpectrum)
        ((r : ℤ) + 3) (2, 128) (Sphere.Internal.hiSquare H M 6) ↔
      VanishesModLambda r (etaThetaSquare η θ))

/-- The paper's finite normalized conclusion on the actual synthetic sphere.
Its bidegrees are explicit, unlike the single-carrier abstraction `BJM_BXCriterion`.
LWX Remark 7.4 requires an additional torsion/comparison argument to prove it. -/
def BJMNormalizedFiniteCriterion (η : Eta Syn) (θ : Theta Syn) : Prop :=
  ∀ r : ℕ, 1 ≤ r →
    (SurvivesTo (adamsTowerInternalSpectralSequence H.unit SphereSpectrum)
        ((r : ℤ) + 3) (2, 128) (Sphere.Internal.hiSquare H M 6) ↔
      VanishesModLambda (r + 1) (lambdaEtaThetaSquare η θ))

/-- The total-differential identity for the actual cofiber boundary of h₆².
The right-hand side is the specified product ληθ₅² in the synthetic sphere. -/
def BJMDistinguishedThetaBoundaryIdentity (η : Eta Syn) (θ : Theta Syn) : Prop :=
  deltaH6Square H M comparison = lambdaEtaThetaSquare η θ

/-- The untruncated criterion uses precisely the standard internal T(M)
predicate. This is a proposed literature comparison obligation, not another
Final declaration and not a consequence claimed from the finite clauses. -/
def BJMUntruncatedCriterion (η : Eta Syn) (θ : Theta Syn) : Prop :=
  NonzeroSurvival (adamsTowerInternalSpectralSequence H.unit SphereSpectrum)
      (2, 128) (Sphere.Internal.hiSquare H M 6) ↔
    lambdaEtaThetaSquare η θ = 0

end KIP126.Kervaire
