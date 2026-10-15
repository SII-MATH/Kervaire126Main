module

public import KIP126.Def.AdamsSynthetic.Comparison.Data
public import KIP126.Def.Synthetic.AdamsSequence.TowerComparison.Data
public import KIP126.Def.Synthetic.QuotientRestrictions.Data
public import KIP126.Def.Synthetic.ExtensionSS.Data

@[expose] public section

namespace KIP126.AdamsSynthetic
open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} (D : AdamsComparisonData H Syn)

/-- Required agreement of named comparisons with the actual first quotient
and actual λ multiplication. These are structural comparison equations,
not any of the Section 7 differential or permanence conclusions. -/
structure ComparisonCompatible : Prop where
  quotient_restriction : ∀ (X : Syn) (i j : ℕ) (h : i ≤ j),
    (D.quotientTower X).rho i j h = XModLambdaN.restriction D.shiftCoherence X i j h
  quotient_naturality : ∀ {X Y : Syn} (f : X ⟶ Y),
    FiniteLambdaQuotientTower.Hom (D.quotientTower X) (D.quotientTower Y) f
  first_quotient : ∀ (s t : ℤ) (x : E2 H SphereSpectrum s t),
    Detects (D.quotientConvergence 1 (by decide)) (s, t, t)
      (by simpa [SyntheticObject.obj, SyntheticAdamsSS.E₂] using D.quotientLabel 1 s t 0 x) ((D.sphereFirstQuotient s t).symm x)
  homotopy_lambda : ∀ (s t : ℤ) (k : ℕ)
      (x : BiHom (t - s) t (S_0_0 : Syn)),
    Detects D.sphereConvergence (s, t, t - k)
      (D.sphereE2 s t k (D.sphereFirstQuotient s t (quotientClass 1 x)))
      (lambdaMultiply k x)
  /-- The ν-sphere label and the sphere label use the specified unit iso. -/
  sphere_nu : ∀ (s t : ℤ) (k : ℕ) (x : E2 H SphereSpectrum s t),
    familyPageMap D.family
        (SyntheticCategory.biShift_zero.hom.app _ ≫ D.nu.unitIso.hom)
        2 (s, t, t - k) (by simpa [ClassicalObject.obj, SyntheticAdamsSS.E₂] using D.nuE2 .sphere 0 s t k x) = D.sphereE2 s t k x
  nu_natural : ∀ (X Y : ClassicalObject) (f : X.obj D.hopfAndDetector ⟶ Y.obj D.hopfAndDetector)
      (a s t : ℤ) (k : ℕ) (x : E2 H (X.obj D.hopfAndDetector) s t),
    familyPageMap D.family ((SyntheticCategory.biShift (0, a)).map (D.nu.functor.map f))
        2 (s, t, t + a - k) (D.nuE2 X a s t k x) =
      D.nuE2 Y a s t k (KIP126.Classical.Adams.adamsInternalE2Induced H.unit f (s, t) x)
  nu_first_quotient : ∀ (X : ClassicalObject) (a s t : ℤ)
      (x : E2 H (X.obj D.hopfAndDetector) s t),
    Detects (D.convergence (.quotient 1 (.shift (0, a) (.nu X)))) (s, t, t + a)
      (familyPageMap D.family (XModLambdaN.incl _ 1) 2 (s, t, t + a)
        (by simpa [SyntheticObject.obj, SyntheticAdamsSS.E₂] using D.nuE2 X a s t 0 x)) ((D.firstQuotient (X.obj D.hopfAndDetector) a s t).symm x)
  /-- λ compatibility with its actual map. HEq only transports the identity
  (t-1)-k = t-(k+1); it never identifies different page objects implicitly. -/
  nu_lambda : ∀ (X : ClassicalObject) (s t : ℤ) (k : ℕ)
      (x : E2 H (X.obj D.hopfAndDetector) s t),
    HEq (familyPageMap D.family (SyntheticCategory.lam.app (D.nu.functor.obj (X.obj D.hopfAndDetector)))
      2 (s, t, t - 1 - k) (D.nuE2 X (-1) s t k x)) (D.nuE2 X 0 s t (k + 1) x)
  /-- Naturality on the entire selected object closure, including λ, ρ, δ,
  normalized maps, Cν cell maps, and the Hurewicz map. Both maps are fixed. -/
  convergence_natural : ∀ (X Y : SyntheticObject)
      (f : X.obj D.nu D.hopfAndDetector ⟶ Y.obj D.nu D.hopfAndDetector),
    ∃ c : KIP126.SpectralSequence.ConvergenceMorphism
        (D.convergence X).toSynthetic.toConvergence (D.convergence Y).toSynthetic.toConvergence,
      c.aMap = syntheticHomotopyMap f ∧ c.eMap = (D.family.functor.map f).eInftyMap

/-- Multiplicativity of the chosen labels and convergence, expressed using
the standard cup product and actual composition of sphere maps. Products
are allowed to have zero leading term; this asserts no particular product
value, differential, or survivor. -/
def MultiplicationCompatible (M : MilnorCooperations H) : Prop :=
  ∀ (s t s' t' k l : ℕ)
    (x : E2 H SphereSpectrum s t) (y : E2 H SphereSpectrum s' t')
    (α : BiHom ((t : ℤ) - s) ((t : ℤ) - k) (S_0_0 : Syn))
    (β : BiHom ((t' : ℤ) - s') ((t' : ℤ) - l) (S_0_0 : Syn)),
    Detects D.sphereConvergence (s, t, (t : ℤ) - k) (D.sphereE2 s t k x) α →
    Detects D.sphereConvergence (s', t', (t' : ℤ) - l) (D.sphereE2 s' t' l y) β →
    Detects D.sphereConvergence ((s + s' : ℕ), (t + t' : ℕ), (t + t' : ℕ) - (k + l : ℕ))
      (D.sphereE2 (s + s' : ℕ) (t + t' : ℕ) (k + l)
        (KIP126.Classical.Adams.Sphere.Internal.product H M x y))
      (homotopyRegrade (by simp only [Nat.cast_add]; omega) (by simp only [Nat.cast_add]; omega) (sphereProduct α β))

/-- Hausdorff convergence on the selected complete objects. This is a
structural convergence requirement, not a finite filtration bound or a
vanishing assertion in a specified stem. -/
def HomotopySeparated : Prop :=
  ∀ (X : SyntheticObject) (m w : ℤ) (α : BiHom m w (X.obj D.nu D.hopfAndDetector)),
    (∀ s : ℕ, FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) s α) → α = 0

/-- The graded commutativity law for the actual sphere composition product.
The sign uses the topological degrees; weights introduce no additional sign.
The equalities in `homotopyRegrade` transport only the sum of degrees. -/
def SphereProductCommutative : Prop :=
  ∀ (m n k l : ℤ) (x : BiHom m n (S_0_0 : Syn)) (y : BiHom k l (S_0_0 : Syn)),
    sphereProduct x y = ((-1 : ℤ) ^ (m * k).natAbs) •
      homotopyRegrade (add_comm k m) (add_comm l n) (sphereProduct y x)

end KIP126.AdamsSynthetic
