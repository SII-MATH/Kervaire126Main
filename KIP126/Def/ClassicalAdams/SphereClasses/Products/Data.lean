module

public import KIP126.Def.ClassicalAdams.SphereClasses.Product.Data
public import KIP126.Def.ClassicalAdams.SphereClasses.Hi.Internal.Data

@[expose] public section

/-! Specified products of the standard Milnor classes on the actual internal E₂.
The product is the existing cobar cup product followed by its canonical
comparison with the same Adams tower. No new page classes or products are chosen. -/

namespace KIP126.Classical.Adams.Sphere.Internal

noncomputable section
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  (H : Mod2EilenbergMacLane (C := C)) (M : MilnorCooperations H)

/-- The actual class `hᵢ hⱼ`, obtained from the specified cobar product. -/
def hiProduct (i j : ℕ) :
    (adamsTowerInternalSpectralSequence H.unit SphereSpectrum).Page 2
      (2, ((2 ^ i + 2 ^ j : ℕ) : ℤ)) :=
  MilnorCohomology.comparison H M 2 (2 ^ i + 2 ^ j)
    (MilnorCohomology.cup H M (MilnorCohomology.hi H M i) (MilnorCohomology.hi H M j))

/-- The actual one-line differential target `h₀ hᵢ²`, with no asserted nonvanishing. -/
def h0HiSquare (i : ℕ) :
    (adamsTowerInternalSpectralSequence H.unit SphereSpectrum).Page 2
      (3, ((1 + 2 ^ (i + 1) : ℕ) : ℤ)) :=
  MilnorCohomology.comparison H M 3 (1 + 2 ^ (i + 1))
    (MilnorCohomology.cup H M (MilnorCohomology.hi H M 0)
      (MilnorCohomology.hiSquare H M i))

end
end KIP126.Classical.Adams.Sphere.Internal
