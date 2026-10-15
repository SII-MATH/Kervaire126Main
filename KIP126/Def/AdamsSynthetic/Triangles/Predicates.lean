module

public import KIP126.Def.AdamsSynthetic.Triangles.Data

@[expose] public section

namespace KIP126.AdamsSynthetic
open CategoryTheory CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology KIP126.Synthetic.Context
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} (D : AdamsComparisonData H Syn)

/-- The geometric compatibility required of the selected lifts in Mahowald.
Factorization through νf alone does not supply this property. This predicate
is a premise to the tool, not a field assuming a paper conclusion in M. -/
def NormalizedTriangleCompatible (T : ClassicalCofiberTriangle D.hopfAndDetector)
    (he : (normalizedExponent H T.f : ℤ) + normalizedExponent H T.g +
      normalizedExponent H T.h = 1) : Prop :=
  normalizedTriangle D T he ∈ distTriang Syn
end KIP126.AdamsSynthetic
