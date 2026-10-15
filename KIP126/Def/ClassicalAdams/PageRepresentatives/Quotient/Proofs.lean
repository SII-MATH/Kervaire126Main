module

public import KIP126.Def.ClassicalAdams.PageRepresentatives.Quotient.Data
public import KIP126.Def.Algebra.NestedQuotient.Proofs

@[expose] public section

namespace KIP126.Classical.Adams.PageRepresentatives

open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology KIP126.Algebra

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  (H : Mod2EilenbergMacLane (C := C)) (X : C)

theorem quotientMap_cycle_injective {c c' : ℤ} (hc : c' ≤ c) (b : ℤ)
    (p : ℤ × ℤ) : Function.Injective (quotientMap H X hc (le_refl b) p) :=
  NestedQuotient.cycle_map_injective (cycles_antitone H X p hc)

end KIP126.Classical.Adams.PageRepresentatives
