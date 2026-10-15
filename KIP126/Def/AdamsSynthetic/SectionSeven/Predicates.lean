module

public import KIP126.Def.AdamsSynthetic.ComparisonStatements

@[expose] public section

/-! Concrete language for the second half of LWX Section 7.

These definitions assert no local result. In particular, finite-quotient
detection retains the actual quotient projection and tower convergence;
Toda indeterminacy is removed only after the multiplications appearing in
`lem:toda2ext`, and no cancellation law for eta is introduced.
-/
namespace KIP126.AdamsSynthetic.SectionSeven
open CategoryTheory
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.SpectralSequence
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Literature.AdamsSynthetic
universe u v w
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H}
  (D : AdamsComparison H M Syn)

/-- Nonzero detection of lambda^k x in the specified finite quotient.
The E2 label is induced by the actual sphere quotient map, not chosen anew. -/
def FiniteDetected (n : ℕ) (hn : 0 < n) (s t : ℤ) (k : ℕ)
    (x : E2 H SphereSpectrum s t)
    (a : BiHom (t-s) (t-k) (XModLambdaN (S_0_0 : Syn) n)) : Prop :=
  DetectsNonzero (D.quotientConvergence n hn) (s,t,t-k)
    (D.quotientLabel n s t k x) a

/-- Nonzero detection in the untruncated synthetic sphere, with all
higher-filtration ambiguity still present. -/
def SphereDetected (s t : ℤ) (k : ℕ) (x : E2 H SphereSpectrum s t)
    (a : BiHom (t-s) (t-k) (S_0_0 : Syn)) : Prop :=
  DetectsNonzero D.sphereConvergence (s,t,t-k) (D.sphereE2 s t k x) a

/-- The right-module bracket <x,y,z>, for x in pi(X) and sphere classes
y,z. The actual arrow chain is z, then y, then x; only its LAST arrow
lands in X. This is essential: putting x first would instead allow
arbitrary endomorphisms of X in the indeterminacy.

For <lambda^3 alpha1,h0,eta>, the two indeterminacy images are
lambda^3 alpha1 * pi_(2,3)(sphere) and pi_(124,130)(Q9) * eta.
The source has degree (124,132), and its Toda suspension (1,0) gives
the required (125,132). All cofiber and extension choices are retained. -/
def ModuleTripleToda {X : Syn} {a aw b bw c cw : ℤ}
    (x : BiHom a aw X) (y : BiHom b bw (S_0_0 : Syn))
    (z : BiHom c cw (S_0_0 : Syn))
    (value : BiHom (a+(b+c)+1) (aw+(bw+cw)) X) : Prop :=
  Toda.Relation ((tripleTodaSource c cw b bw a aw).inv ≫
      homotopyRegrade (by omega) (by omega) value)
    ((SyntheticCategory.biShift (b+a,bw+aw)).map z)
    ((SyntheticCategory.biShift_comp (b,bw) (a,aw)).inv.app S_0_0 ≫
      (SyntheticCategory.biShift (a,aw)).map y) x

/-- Only the lambda^2 h0 image of the indeterminacy of <theta,2,b>
vanishes. The two summands have degree (125,134), and the image has
degree (125,133). This does not assert that the original bracket is a singleton. -/
def ThetaBMultipliedIndeterminacy
    (h0 : BiHom 0 1 (S_0_0 : Syn)) (theta : BiHom 62 64 (S_0_0 : Syn))
    (b : BiHom 62 70 (S_0_0 : Syn)) : Prop :=
  ∀ (a : BiHom 63 70 (S_0_0 : Syn)) (c : BiHom 63 64 (S_0_0 : Syn)),
    lambdaMultiply 2 (sphereProduct h0
      ((show BiHom 125 134 (S_0_0 : Syn) from sphereProduct theta a) +
        (show BiHom 125 134 (S_0_0 : Syn) from sphereProduct c b))) = 0

/-- Only the lambda-and-b image of the indeterminacy of <2,theta,2>
vanishes. Both unmultiplied summands lie in degree (63,64). -/
def SymmetricTwoMultipliedIndeterminacy (b : BiHom 62 70 (S_0_0 : Syn)) : Prop :=
  ∀ a c : BiHom 63 64 (S_0_0 : Syn),
    lambdaMultiply 1 (sphereProduct
      ((show BiHom 63 64 (S_0_0 : Syn) from sphereProduct syntheticTwo a) +
        (show BiHom 63 64 (S_0_0 : Syn) from sphereProduct c syntheticTwo)) b) = 0

/-- The exact quotient relation in Lemma `lem:nuext125`, with existential
representatives. It is not an assertion about every representative of X. -/
def NuExtension9 (X : E2 H SphereSpectrum 8 130)
    (Y : E2 H SphereSpectrum 11 136) (h2 : BiHom 3 4 (S_0_0 : Syn)) : Prop :=
  ∃ (x : BiHom 122 126 (XModLambdaN (S_0_0 : Syn) 9))
    (y : BiHom 125 131 (XModLambdaN (S_0_0 : Syn) 9)),
    FiniteDetected D 9 (by decide) 8 130 4 X x ∧
    FiniteDetected D 9 (by decide) 11 136 5 Y y ∧
    sphereAction h2 x = lambdaMultiply 1 y

/-- The direct Q₃ relation supplied by the generalized Mahowald argument.
The target is detected by λ²Y, so both sides of the h₂ action lie in
π₍₁₂₅,₁₃₄₎(Q₃). This is the E₄ extension output before the separate
Q₃-to-Q₅ correction analysis. -/
def NuExtension3 (X : E2 H SphereSpectrum 8 130)
    (Y : E2 H SphereSpectrum 11 136) (h2 : BiHom 3 4 (S_0_0 : Syn)) : Prop :=
  ∃ (x : BiHom 122 130 (XModLambdaN (S_0_0 : Syn) 3))
    (y : BiHom 125 134 (XModLambdaN (S_0_0 : Syn) 3)),
    FiniteDetected D 3 (by decide) 8 130 0 X x ∧
    FiniteDetected D 3 (by decide) 11 136 2 Y y ∧
    sphereAction h2 x = y

/-- The Q3 relation must be lifted to actual Q5 representatives; existence
of an E4 extension alone does not provide this exact equality. -/
def NuExtension5 (X : E2 H SphereSpectrum 8 130)
    (Y : E2 H SphereSpectrum 11 136) (h2 : BiHom 3 4 (S_0_0 : Syn)) : Prop :=
  ∃ (x : BiHom 122 130 (XModLambdaN (S_0_0 : Syn) 5))
    (y : BiHom 125 134 (XModLambdaN (S_0_0 : Syn) 5)),
    FiniteDetected D 5 (by decide) 8 130 0 X x ∧
    FiniteDetected D 5 (by decide) 11 136 2 Y y ∧
    sphereAction h2 x = y

/-- Corollary `cor:2ext125`: forall source representatives, there is a
target representative depending on that source. No fixed target is chosen.
Both representatives live in the same actual Q9, as in the corollary. -/
def AnyYH0Extension (Y : E2 H SphereSpectrum 11 136)
    (T : E2 H SphereSpectrum 14 139) (h0 : BiHom 0 1 (S_0_0 : Syn)) : Prop :=
  ∀ y : BiHom 125 132 (XModLambdaN (S_0_0 : Syn) 9),
    FiniteDetected D 9 (by decide) 11 136 4 Y y →
    ∃ t : BiHom 125 139 (XModLambdaN (S_0_0 : Syn) 9),
      FiniteDetected D 9 (by decide) 14 139 0 T t ∧
      sphereAction h0 y = lambdaMultiply 6 t ∧ lambdaMultiply 6 t ≠ 0

/-- The common untruncated conclusion of the P and Q branches in
`prop:state5false`. The preimage and detected T representative must both
be produced. Their degrees explicitly express divisibility by lambda h2. -/
def TargetNuDivisible (T : E2 H SphereSpectrum 14 139)
    (h2 : BiHom 3 4 (S_0_0 : Syn)) : Prop :=
  ∃ (t : BiHom 125 139 (S_0_0 : Syn)) (a : BiHom 122 132 (S_0_0 : Syn)),
    SphereDetected D 14 139 0 T t ∧
    sphereProduct (lambdaMultiply 1 h2) a = lambdaMultiply 4 t

end
end KIP126.AdamsSynthetic.SectionSeven
