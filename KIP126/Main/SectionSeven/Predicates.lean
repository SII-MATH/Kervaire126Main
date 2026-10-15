module

public import KIP126.Def.Computation
public import KIP126.Def.Literature

/-! Paper-specific language adapted from Kervaire126
`KIP126/Def/Kervaire/Route/Section7/Predicates.lean` at
bbac1fc05843bdf2d56057e6114a38839e939378 (MIT; see the retained source LICENSE).
All objects use the fixed public upstream system. These predicates assert
no paper result, and retain finite-quotient, nonzero and indeterminacy data. -/

@[expose] section
namespace KIP126.Main.SectionSeven
open CategoryTheory
open KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.AdamsSynthetic KIP126.AdamsSynthetic.Standard
open KIP126.Core.SpectralSequence KIP126.Literature.Route
noncomputable section

/-- Nonzero detection of lambda^k x in the specified finite quotient.
The E2 label is induced by the actual sphere quotient map, not chosen anew. -/
private def FiniteDetected (n : ℕ) (_hn : 0 < n) (s t : ℤ) (k : ℕ)
    (x : sphereSequence.Page 2 (s,t))
    (a : BiHom (t-s) (t-k) (XModLambdaN (S_0_0 : SyntheticSpectrum) n)) : Prop :=
  DetectsNonzero (model.convergence (.quotient n .sphere)) (s,t,t-k)
    ((family.quotientProjection syntheticSphere n).pageMap 2 (s,t,t-k) (comparison.sphereE2 s t k x)) a

/-- Nonzero detection in the untruncated synthetic sphere, with all
higher-filtration ambiguity still present. -/
private def SphereDetected (s t : ℤ) (k : ℕ) (x : sphereSequence.Page 2 (s,t))
    (a : BiHom (t-s) (t-k) (S_0_0 : SyntheticSpectrum)) : Prop :=
  DetectsNonzero (model.convergence .sphere) (s,t,t-k) (comparison.sphereE2 s t k x) a

/-- The right-module bracket <x,y,z>, for x in pi(X) and sphere classes
y,z. The actual arrow chain is z, then y, then x; only its LAST arrow
lands in X. This is essential: putting x first would instead allow
arbitrary endomorphisms of X in the indeterminacy.

For <lambda^3 alpha1,h0,eta>, the two indeterminacy images are
lambda^3 alpha1 * pi_(2,3)(sphere) and pi_(124,130)(Q9) * eta.
The source has degree (124,132), and its Toda suspension (1,0) gives
the required (125,132). All cofiber and extension choices are retained. -/
private def ModuleTripleToda {X : SyntheticSpectrum} {a aw b bw c cw : ℤ}
    (x : BiHom a aw X) (y : BiHom b bw (S_0_0 : SyntheticSpectrum))
    (z : BiHom c cw (S_0_0 : SyntheticSpectrum))
    (value : BiHom (a+(b+c)+1) (aw+(bw+cw)) X) : Prop :=
  Toda.Relation ((tripleTodaSource c cw b bw a aw).inv ≫
      homotopyRegrade (by omega) (by omega) value)
    ((SyntheticCategory.biShift (b+a,bw+aw)).map z)
    ((SyntheticCategory.biShift_comp (b,bw) (a,aw)).inv.app S_0_0 ≫
      (SyntheticCategory.biShift (a,aw)).map y) x

/-- Only the lambda^2 h0 image of the indeterminacy of <theta,2,b>
vanishes. The two summands have degree (125,134), and the image has
degree (125,133). This does not assert that the original bracket is a singleton. -/
private def ThetaBMultipliedIndeterminacy
    (h0 : BiHom 0 1 (S_0_0 : SyntheticSpectrum)) (theta : BiHom 62 64 (S_0_0 : SyntheticSpectrum))
    (b : BiHom 62 70 (S_0_0 : SyntheticSpectrum)) : Prop :=
  ∀ (a : BiHom 63 70 (S_0_0 : SyntheticSpectrum)) (c : BiHom 63 64 (S_0_0 : SyntheticSpectrum)),
    lambdaMultiply 2 (sphereProduct h0
      ((show BiHom 125 134 (S_0_0 : SyntheticSpectrum) from sphereProduct theta a) +
        (show BiHom 125 134 (S_0_0 : SyntheticSpectrum) from sphereProduct c b))) = 0

/-- Only the lambda-and-b image of the indeterminacy of <2,theta,2>
vanishes. Both unmultiplied summands lie in degree (63,64). -/
private def SymmetricTwoMultipliedIndeterminacy (b : BiHom 62 70 (S_0_0 : SyntheticSpectrum)) : Prop :=
  ∀ a c : BiHom 63 64 (S_0_0 : SyntheticSpectrum),
    lambdaMultiply 1 (sphereProduct
      ((show BiHom 63 64 (S_0_0 : SyntheticSpectrum) from sphereProduct syntheticTwo a) +
        (show BiHom 63 64 (S_0_0 : SyntheticSpectrum) from sphereProduct c syntheticTwo)) b) = 0

/-- The exact quotient relation in Lemma `lem:nuext125`, with existential
representatives. It is not an assertion about every representative of X. -/
private def NuExtension9 (X : sphereSequence.Page 2 (8,130))
    (Y : sphereSequence.Page 2 (11,136)) (h2 : BiHom 3 4 (S_0_0 : SyntheticSpectrum)) : Prop :=
  ∃ (x : BiHom 122 126 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9))
    (y : BiHom 125 131 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9)),
    FiniteDetected 9 (by decide) 8 130 4 X x ∧
    FiniteDetected 9 (by decide) 11 136 5 Y y ∧
    sphereAction h2 x = lambdaMultiply 1 y

/-- The Q3 relation must be lifted to actual Q5 representatives; existence
of an E4 extension alone does not provide this exact equality. -/
private def NuExtension5 (X : sphereSequence.Page 2 (8,130))
    (Y : sphereSequence.Page 2 (11,136)) (h2 : BiHom 3 4 (S_0_0 : SyntheticSpectrum)) : Prop :=
  ∃ (x : BiHom 122 130 (XModLambdaN (S_0_0 : SyntheticSpectrum) 5))
    (y : BiHom 125 134 (XModLambdaN (S_0_0 : SyntheticSpectrum) 5)),
    FiniteDetected 5 (by decide) 8 130 0 X x ∧
    FiniteDetected 5 (by decide) 11 136 2 Y y ∧
    sphereAction h2 x = y

/-- Corollary `cor:2ext125`: forall source representatives, there is a
target representative depending on that source. No fixed target is chosen.
Both representatives live in the same actual Q9, as in the corollary. -/
private def AnyYH0Extension (Y : sphereSequence.Page 2 (11,136))
    (T : sphereSequence.Page 2 (14,139)) (h0 : BiHom 0 1 (S_0_0 : SyntheticSpectrum)) : Prop :=
  ∀ y : BiHom 125 132 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9),
    FiniteDetected 9 (by decide) 11 136 4 Y y →
    ∃ t : BiHom 125 139 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9),
      FiniteDetected 9 (by decide) 14 139 0 T t ∧
      sphereAction h0 y = lambdaMultiply 6 t ∧ lambdaMultiply 6 t ≠ 0

/-- The common untruncated conclusion of the P and Q branches in
`prop:state5false`. The preimage and detected T representative must both
be produced. Their degrees explicitly express divisibility by lambda h2. -/
private def TargetNuDivisible (T : sphereSequence.Page 2 (14,139))
    (h2 : BiHom 3 4 (S_0_0 : SyntheticSpectrum)) : Prop :=
  ∃ (t : BiHom 125 139 (S_0_0 : SyntheticSpectrum)) (a : BiHom 122 132 (S_0_0 : SyntheticSpectrum)),
    SphereDetected 14 139 0 T t ∧
    sphereProduct (lambdaMultiply 1 h2) a = lambdaMultiply 4 t


end
end KIP126.Main.SectionSeven
