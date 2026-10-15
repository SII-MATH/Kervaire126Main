module

public import KIP126.Def.ClassicalAdams.MilnorCooperations.Data

@[expose] public section

/-!
# Transport of Milnor cocycles to the first Adams page
-/

namespace KIP126.Classical.Adams

noncomputable section

open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]

namespace Sphere

variable (H : Mod2EilenbergMacLane (C := C)) (M : MilnorCooperations H)

/-- A specified Milnor cocycle is a cycle in the actual first Adams page. -/
theorem milnorCocycle_d_zero (s t : ℕ) (x : KIP126.Steenrod.Milnor.cochains s t)
    (hx : KIP126.Steenrod.Milnor.differential s t x = 0) :
    sphereFirstDifferential H s t ((M.coordinates s t).symm x) = 0 := by
  apply (M.coordinates (s + 1) t).injective
  rw [M.differential_coordinates, LinearEquiv.apply_symm_apply, hx, map_zero]

end Sphere

variable (H : Mod2EilenbergMacLane (C := C)) (M : MilnorCooperations H)

/-- The first-page differential of the specified Adams tower squares to zero. -/
theorem sphereFirstDifferential_squared (s t : ℕ)
    (x : adamsPage H.unit SphereSpectrum 1 (by decide) s t) :
    sphereFirstDifferential H (s + 1) t (sphereFirstDifferential H s t x) = 0 := by
  have h := (adamsPageComplex H.unit SphereSpectrum 1 (by decide)).d_comp_d
    ((s : ℤ), (t : ℤ)) (((s + 1 : ℕ) : ℤ), (t : ℤ))
    ((((s + 1) + 1 : ℕ) : ℤ), (t : ℤ))
  exact congrArg (fun f => f x) h

include M in
/-- a04 consequence of a03: Milnor coordinates transport the already proved
square-zero law. This is conditional on the explicit cooperation comparison,
not a new cobar axiom or a claim to an independent polynomial proof. -/
theorem milnor_differential_squared (s t : ℕ) (x : Steenrod.Milnor.cochains s t) :
    Steenrod.Milnor.differential (s + 1) t
      (Steenrod.Milnor.differential s t x) = 0 := by
  obtain ⟨y, rfl⟩ := (M.coordinates s t).surjective x
  rw [← M.differential_coordinates, ← M.differential_coordinates,
    sphereFirstDifferential_squared, map_zero]


end

end KIP126.Classical.Adams
