module

public import KIP126.Def.Synthetic.PageExtension.Ambiguity.Data

@[expose] public section

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
  {P : NormalizedPageFamily H N F f}

namespace FiniteExtensionWitness
variable {r : ℕ} {n s t : ℤ} {x : PageRepresentatives.Ambient H X (s, t)}
  {y : PageRepresentatives.Ambient H Y (s + n, t + n)}
  (W : FiniteExtensionWitness P r n s t x y)

/-- The λ-scaled comparison kills exactly the ordinary Adams boundaries.
This is a specific kernel theorem to prove from model coherence, not a
consequence of choosing top-weight comparison isomorphisms. -/
def ClassicalBoundaryKernel : Prop :=
  LinearMap.ker W.scaledTargetMap = W.ordinaryBoundaries

/-- Actual shorter classical extension targets generate exactly the actual
ESS boundary after the fixed λ-scaled comparison. This compatibility is
separate from the kernel theorem and is not asserted automatically. -/
def ShorterImagesCompatible : Prop :=
  W.shorterImages.map W.scaledTargetMap = W.essBoundaries

end FiniteExtensionWitness

namespace InfiniteExtensionWitness
variable {n s t : ℤ} {x : PageRepresentatives.Ambient H X (s, t)}
  {y : PageRepresentatives.Ambient H Y (s + n, t + n)}
  (W : InfiniteExtensionWitness P n s t x y)

def ClassicalBoundaryKernel : Prop :=
  LinearMap.ker W.scaledTargetMap = W.ordinaryBoundaries

def ShorterImagesCompatible : Prop :=
  W.shorterImages.map W.scaledTargetMap = W.essBoundaries

end InfiniteExtensionWitness
end KIP126.Synthetic.PageExtension
