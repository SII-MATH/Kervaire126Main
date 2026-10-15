module

public import KIP126.Def.AdamsSynthetic.Comparison.Coherent.Data
public import KIP126.Def.AdamsSynthetic.Multiplication.Operations
public import KIP126.Def.Synthetic.Detection.Proofs

@[expose] public section

/-! Structural multiplication comparisons on the same finite lambda quotients.
These predicates specify no local product value, differential, or survivor.
The algebra parameter is a MonObj on the actual quotient, never a new carrier.
The associated-graded statements quantify all detected representatives and allow
zero leading terms; no compatible infinite lift of a finite class is assumed. -/
namespace KIP126.AdamsSynthetic
open CategoryTheory CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
universe u v w
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w,v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H}


variable (D : AdamsComparison H M Syn)

/-- The first-lambda-quotient comparison identifies its ACTUAL algebra product
with the fixed Milnor cobar product on the existing classical sphere E2.
This is a multiplicativity equation, not just an additive equivalence. -/
def FirstQuotientMultiplicationCompatible
    (Q : MonObj (XModLambdaN (S_0_0 : Syn) 1)) : Prop :=
  ∀ (s t s' t' : ℕ)
    (a : BiHom ((t : ℤ)-s) t (XModLambdaN (S_0_0 : Syn) 1))
    (b : BiHom ((t' : ℤ)-s') t' (XModLambdaN (S_0_0 : Syn) 1)),
    D.sphereFirstQuotient (s+s' : ℕ) (t+t' : ℕ)
      (homotopyRegrade (by simp only [Nat.cast_add]; omega)
        (by simp only [Nat.cast_add]) (algebraProduct Q a b)) =
      Sphere.Internal.product H M
        (D.sphereFirstQuotient s t a) (D.sphereFirstQuotient s' t' b)

/-- Multiplication of detected finite-quotient classes is detected by the
same cobar product. Either leading term and the product may be zero.
All weights are explicit; no premise requires a lift to the untruncated sphere. -/
def FiniteQuotientMultiplicationCompatible (q : ℕ) (hq : 0 < q)
    (Q : MonObj (XModLambdaN (S_0_0 : Syn) q)) : Prop :=
  ∀ (s t s' t' k l : ℕ)
    (x : E2 H SphereSpectrum s t) (y : E2 H SphereSpectrum s' t')
    (a : BiHom ((t : ℤ)-s) ((t : ℤ)-k) (XModLambdaN (S_0_0 : Syn) q))
    (b : BiHom ((t' : ℤ)-s') ((t' : ℤ)-l) (XModLambdaN (S_0_0 : Syn) q)),
    Detects (D.quotientConvergence q hq) (s,t,(t : ℤ)-k)
      (D.quotientLabel q s t k x) a →
    Detects (D.quotientConvergence q hq) (s',t',(t' : ℤ)-l)
      (D.quotientLabel q s' t' l y) b →
    Detects (D.quotientConvergence q hq)
      ((s+s' : ℕ),(t+t' : ℕ),(t+t' : ℕ)-(k+l : ℕ))
      (D.quotientLabel q (s+s' : ℕ) (t+t' : ℕ) (k+l)
        (Sphere.Internal.product H M x y))
      (homotopyRegrade (by simp only [Nat.cast_add]; omega)
        (by simp only [Nat.cast_add]; omega) (algebraProduct Q a b))

/-- The actual sphere action on a finite quotient, including classes which
exist only on that finite quotient, preserves the same leading product. -/
def FiniteQuotientSphereActionCompatible : Prop :=
  ∀ (q : ℕ) (hq : 0 < q) (s t s' t' k l : ℕ)
    (x : E2 H SphereSpectrum s t) (y : E2 H SphereSpectrum s' t')
    (a : BiHom ((t : ℤ)-s) ((t : ℤ)-k) (S_0_0 : Syn))
    (b : BiHom ((t' : ℤ)-s') ((t' : ℤ)-l) (XModLambdaN (S_0_0 : Syn) q)),
    Detects D.sphereConvergence (s,t,(t : ℤ)-k) (D.sphereE2 s t k x) a →
    Detects (D.quotientConvergence q hq) (s',t',(t' : ℤ)-l)
      (D.quotientLabel q s' t' l y) b →
    Detects (D.quotientConvergence q hq)
      ((s+s' : ℕ),(t+t' : ℕ),(t+t' : ℕ)-(k+l : ℕ))
      (D.quotientLabel q (s+s' : ℕ) (t+t' : ℕ) (k+l)
        (Sphere.Internal.product H M x y))
      (homotopyRegrade (by simp only [Nat.cast_add]; omega)
        (by simp only [Nat.cast_add]; omega) (sphereAction a b))

/-- Structural multiplicativity of the actual Adams tower filtration, on
all selected objects. It makes no finite upper bound or vanishing claim. -/
def SphereActionFiltrationCompatible : Prop :=
  ∀ (X : SyntheticObject) (m w m' w' s s' : ℤ)
    (a : BiHom m w (S_0_0 : Syn))
    (b : BiHom m' w' (X.obj D.nu D.hopfAndDetector)),
    FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) s a →
    FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) s' b →
    FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) (s+s') (sphereAction a b)

/-- The same filtration law for the actual finite-quotient algebra. -/
def FiniteQuotientFiltrationCompatible (q : ℕ)
    (Q : MonObj (XModLambdaN (S_0_0 : Syn) q)) : Prop :=
  ∀ (m w m' w' s s' : ℤ)
    (a : BiHom m w (XModLambdaN (S_0_0 : Syn) q))
    (b : BiHom m' w' (XModLambdaN (S_0_0 : Syn) q)),
    FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) s a →
    FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) s' b →
    FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) (s+s') (algebraProduct Q a b)
end
end KIP126.AdamsSynthetic
