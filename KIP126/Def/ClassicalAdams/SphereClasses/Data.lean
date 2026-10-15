module

public import KIP126.Def.ClassicalAdams.MilnorCooperations.Proofs
public import KIP126.Def.ClassicalAdams.TowerSequence.PageHomology.Data
public import KIP126.Def.Steenrod.MilnorCobar.Proofs
public import Mathlib.Algebra.Homology.ConcreteCategory

@[expose] public section

/-!
# Standard sphere Adams classes from specified Milnor cocycles

These classes lie in the quotient defining the second page of the specified
Adams tower. This is also the second-page carrier of its Mathlib spectral
sequence, by definitional equality.
-/

namespace KIP126.Classical.Adams

noncomputable section

open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]

namespace Sphere

variable (H : Mod2EilenbergMacLane (C := C)) (M : MilnorCooperations H)

/-- Send a specified normalized Milnor cocycle through the actual first-page
homology quotient and page-passage map to `E₂`. -/
def classOfMilnorCocycle (s t : ℕ) (x : KIP126.Steenrod.Milnor.cochains s t)
    (hx : KIP126.Steenrod.Milnor.differential s t x = 0) :
    adamsPage H.unit SphereSpectrum 2 (by decide) s t := by
  let K := adamsPageComplex H.unit SphereSpectrum 1 (by decide)
  let p : ℤ × ℤ := (s, t)
  let q : ℤ × ℤ := ((s + 1 : ℕ), t)
  let a : K.X p := (M.coordinates s t).symm x
  have hpq : (classicalAdamsShape 1).next p = q := by
    apply ComplexShape.next_eq'
    change p + ((1 : ℤ), 1 - 1) = q
    dsimp [p, q]
    apply Prod.ext <;> simp
  have ha : (K.d p q).hom a = 0 := milnorCocycle_d_zero H M s t x hx
  exact (adamsPageHomologyIso H.unit SphereSpectrum 1 (by decide) p).hom
    ((K.homologyπ p).hom (K.cyclesMk a q hpq ha))

end Sphere

end

end KIP126.Classical.Adams
