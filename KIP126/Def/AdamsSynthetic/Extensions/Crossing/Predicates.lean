module

public import KIP126.Def.AdamsSynthetic.Extensions.Predicates

@[expose] public section

namespace KIP126.AdamsSynthetic
open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H}
  (D : AdamsComparison H M Syn) (X Y : ClassicalObject)
  (f : X.obj D.hopfAndDetector ⟶ Y.obj D.hopfAndDetector)

/-- A crossing in the finite page-extension position `(r,n,s,t)`.
The target degree is written as the actual shorter witness's target;
it is `(s+n-b,t+n-b)`. Its source and target cycle conditions are supplied
by that same witness, on page r-a and of length n-a-b. -/
def FiniteExtension.HasCrossing
    (r : ℕ) (n s t : ℤ) : Prop :=
  ∃ a b : ℕ, 0 < a ∧ a ≤ r - 2 ∧
    (b : ℤ) ≤ n - a - normalizedExponent H f ∧
    ∃ (x' : PageRepresentatives.Ambient H (X.obj D.hopfAndDetector) (s + a, t + a))
      (y' : PageRepresentatives.Ambient H (Y.obj D.hopfAndDetector)
        (s + a + (n - a - b), t + a + (n - a - b))),
      ∃ W' : FiniteExtensionWitness D X Y f (r - a) (n - a - b) (s + a) (t + a) x' y',
        W'.Essential ∧ y' ∉ PageRepresentatives.boundaries H (Y.obj D.hopfAndDetector)
          (1 + n - b - normalizedExponent H f)
          (s + a + (n - a - b), t + a + (n - a - b))

/-- Absence of crossings in this finite position. Applied to an actual
extension witness, its page and length validity are already supplied. -/
def FiniteExtension.NoCrossing
    (r : ℕ) (n s t : ℤ) : Prop :=
  ¬ FiniteExtension.HasCrossing D X Y f r n s t

/-- The infinite clause uses the same untruncated normalized map and actual
permanent representatives. The bound a≤n-e follows from the length range,
and is recorded explicitly; there is no finite-page upper bound on a. -/
def InfiniteExtension.HasCrossing
    (n s t : ℤ) : Prop :=
  ∃ a b : ℕ, 0 < a ∧ (a : ℤ) ≤ n - normalizedExponent H f ∧
    (b : ℤ) ≤ n - a - normalizedExponent H f ∧
    ∃ (x' : PageRepresentatives.Ambient H (X.obj D.hopfAndDetector) (s + a, t + a))
      (y' : PageRepresentatives.Ambient H (Y.obj D.hopfAndDetector)
        (s + a + (n - a - b), t + a + (n - a - b))),
      ∃ W' : InfiniteExtensionWitness D X Y f (n - a - b) (s + a) (t + a) x' y',
        W'.Essential ∧ y' ∉ PageRepresentatives.boundaries H (Y.obj D.hopfAndDetector)
          (1 + n - b - normalizedExponent H f)
          (s + a + (n - a - b), t + a + (n - a - b))

def InfiniteExtension.NoCrossing
    (n s t : ℤ) : Prop :=
  ¬ InfiniteExtension.HasCrossing D X Y f n s t

end KIP126.AdamsSynthetic
