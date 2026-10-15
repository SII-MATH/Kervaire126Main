module

public import KIP126.Def.Synthetic.PageExtension.Predicates

@[expose] public section

/-!
# Crossings of normalized page extensions

MainPaper Definition `def:41d51149` (lines 1437–1441) requires both an
essential shorter extension and exclusion from the larger ordinary Adams
boundary B_(1+n-b-e). The shorter extension's own essentiality does not
imply that second condition. The paragraph following `prop:cross-f-Er`
(line 1543) extends the definition to infinity; that clause uses an actual
untruncated extension with permanent representatives, not unrelated finite
candidates. These definitions do not prove the synthetic crossing comparison
or extend the bounded-convergence inputs of `NormalizedPageFamily`.
-/

namespace KIP126.Synthetic.PageExtension

open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams

universe u v u' v'
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type u'} [SyntheticCategory.{u', v'} Syn]
  [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {N : NuFunctorData C Syn}
  {F : SyntheticAdamsFamily Syn} {X Y : C} {f : X ⟶ Y}

/-- A crossing in the finite page-extension position `(r,n,s,t)`.
The target degree is written as the actual shorter witness's target;
it is `(s+n-b,t+n-b)`. Its source and target cycle conditions are supplied
by that same witness, on page r-a and of length n-a-b. -/
def FinitePageExtension.HasCrossing (P : NormalizedPageFamily H N F f)
    (r : ℕ) (n s t : ℤ) : Prop :=
  ∃ a b : ℕ, 0 < a ∧ a ≤ r - 2 ∧
    (b : ℤ) ≤ n - a - normalizedExponent H f ∧
    ∃ (x' : PageRepresentatives.Ambient H X (s + a, t + a))
      (y' : PageRepresentatives.Ambient H Y
        (s + a + (n - a - b), t + a + (n - a - b))),
      ∃ W' : FiniteExtensionWitness P (r - a) (n - a - b) (s + a) (t + a) x' y',
        W'.Essential ∧ y' ∉ PageRepresentatives.boundaries H Y
          (1 + n - b - normalizedExponent H f)
          (s + a + (n - a - b), t + a + (n - a - b))

/-- Absence of crossings in this finite position. Applied to an actual
extension witness, its page and length validity are already supplied. -/
def FinitePageExtension.NoCrossing (P : NormalizedPageFamily H N F f)
    (r : ℕ) (n s t : ℤ) : Prop :=
  ¬ FinitePageExtension.HasCrossing P r n s t

/-- The infinite clause uses the same untruncated normalized map and actual
permanent representatives. The bound a≤n-e follows from the length range,
and is recorded explicitly; there is no finite-page upper bound on a. -/
def InfinitePageExtension.HasCrossing (P : NormalizedPageFamily H N F f)
    (n s t : ℤ) : Prop :=
  ∃ a b : ℕ, 0 < a ∧ (a : ℤ) ≤ n - normalizedExponent H f ∧
    (b : ℤ) ≤ n - a - normalizedExponent H f ∧
    ∃ (x' : PageRepresentatives.Ambient H X (s + a, t + a))
      (y' : PageRepresentatives.Ambient H Y
        (s + a + (n - a - b), t + a + (n - a - b))),
      ∃ W' : InfiniteExtensionWitness P (n - a - b) (s + a) (t + a) x' y',
        W'.Essential ∧ y' ∉ PageRepresentatives.boundaries H Y
          (1 + n - b - normalizedExponent H f)
          (s + a + (n - a - b), t + a + (n - a - b))

def InfinitePageExtension.NoCrossing (P : NormalizedPageFamily H N F f)
    (n s t : ℤ) : Prop :=
  ¬ InfinitePageExtension.HasCrossing P n s t

def FiniteExtensionWitness.HasCrossing {P : NormalizedPageFamily H N F f}
    {r : ℕ} {n s t : ℤ} {x : PageRepresentatives.Ambient H X (s, t)}
    {y : PageRepresentatives.Ambient H Y (s + n, t + n)}
    (_W : FiniteExtensionWitness P r n s t x y) : Prop :=
  FinitePageExtension.HasCrossing P r n s t

def FiniteExtensionWitness.NoCrossing {P : NormalizedPageFamily H N F f}
    {r : ℕ} {n s t : ℤ} {x : PageRepresentatives.Ambient H X (s, t)}
    {y : PageRepresentatives.Ambient H Y (s + n, t + n)}
    (_W : FiniteExtensionWitness P r n s t x y) : Prop :=
  FinitePageExtension.NoCrossing P r n s t

def InfiniteExtensionWitness.HasCrossing {P : NormalizedPageFamily H N F f}
    {n s t : ℤ} {x : PageRepresentatives.Ambient H X (s, t)}
    {y : PageRepresentatives.Ambient H Y (s + n, t + n)}
    (_W : InfiniteExtensionWitness P n s t x y) : Prop :=
  InfinitePageExtension.HasCrossing P n s t

def InfiniteExtensionWitness.NoCrossing {P : NormalizedPageFamily H N F f}
    {n s t : ℤ} {x : PageRepresentatives.Ambient H X (s, t)}
    {y : PageRepresentatives.Ambient H Y (s + n, t + n)}
    (_W : InfiniteExtensionWitness P n s t x y) : Prop :=
  InfinitePageExtension.NoCrossing P n s t

end KIP126.Synthetic.PageExtension
