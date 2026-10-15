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

theorem quotientMap_boundary_surjective (c : ℤ) {b b' : ℤ} (hb : b ≤ b')
    (p : ℤ × ℤ) : Function.Surjective (quotientMap H X (le_refl c) hb p) :=
  NestedQuotient.boundary_map_surjective (boundaries_monotone H X p hb)

/-- The same quotient surjection when equal cycle cutoffs have different
index expressions, as happens for the finite synthetic λ map. -/
theorem quotientMap_surjective_of_cycle_eq {c c' b b' : ℤ}
    (hc : c' ≤ c) (hb : b ≤ b') (heq : c = c') (p : ℤ × ℤ) :
    Function.Surjective (quotientMap H X hc hb p) := by
  subst c'
  exact quotientMap_boundary_surjective H X c hb p

theorem quotientMap_cycle_injective {c c' : ℤ} (hc : c' ≤ c) (b : ℤ)
    (p : ℤ × ℤ) : Function.Injective (quotientMap H X hc (le_refl b) p) :=
  NestedQuotient.cycle_map_injective (cycles_antitone H X p hc)

theorem permanentQuotientMap_surjective {b b' : ℤ} (hb : b ≤ b') (p : ℤ × ℤ) :
    Function.Surjective (permanentQuotientMap H X hb p) :=
  NestedQuotient.boundary_map_surjective (boundaries_monotone H X p hb)

theorem permanentToFinite_injective (c b : ℤ) (p : ℤ × ℤ) :
    Function.Injective (permanentToFinite H X c b p) :=
  NestedQuotient.cycle_map_injective (permanentCycles_le_cycles H X p c)

end KIP126.Classical.Adams.PageRepresentatives
