module

public import KIP126.Def.AdamsSynthetic.Extensions.Witness.Data
public import KIP126.Def.ClassicalAdams.PageRepresentatives.Predicates

@[expose] public section

/-! Finite and infinite extensions for the specified Adams comparison.
Their equations use the same normalized maps, filtrations and E∞ representatives. -/
namespace KIP126.AdamsSynthetic
open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H} (D : AdamsComparison H M Syn)
  (X Y : ClassicalObject) (f : X.obj D.hopfAndDetector ⟶ Y.obj D.hopfAndDetector)


def FiniteExtension (r : ℕ) (n s t : ℤ)
    (x : E2 H (X.obj D.hopfAndDetector) s t)
    (y : E2 H (Y.obj D.hopfAndDetector) (s + n) (t + n)) : Prop :=
  Nonempty (FiniteExtensionWitness D X Y f r n s t x y)

def FiniteExtensionWitness.Essential {r : ℕ} {n s t : ℤ} {x y}
    (W : FiniteExtensionWitness D X Y f r n s t x y) : Prop :=
  EssentialExtension (finiteExtensionMap D X Y f (r - 1))
    (D.convergence (.quotient (r - 1) (extensionSourceObject D X Y f)))
    (D.convergence (.quotient (r - 1) (.nu Y)))
    (t - s, t + normalizedExponent H f) s n W.source W.target


def InfiniteExtension (n s t : ℤ)
    (x : E2 H (X.obj D.hopfAndDetector) s t)
    (y : E2 H (Y.obj D.hopfAndDetector) (s + n) (t + n)) : Prop :=
  Nonempty (InfiniteExtensionWitness D X Y f n s t x y)

def InfiniteExtensionWitness.Essential {n s t : ℤ} {x y}
    (W : InfiniteExtensionWitness D X Y f n s t x y) : Prop :=
  EssentialExtension (D.normalizedMap X Y f).map
    (D.convergence (extensionSourceObject D X Y f)) (D.convergence (.nu Y))
    (t - s, t + normalizedExponent H f) s n W.source W.target
end KIP126.AdamsSynthetic
