module

public import KIP126.Def.ClassicalAdams.MilnorCohomology.Data
public import KIP126.Def.ClassicalAdams.MilnorCooperations.Proofs
public import KIP126.Def.ClassicalAdams.TowerSequence.PageHomology.Data
public import KIP126.Def.ClassicalAdams.TowerSSData.Sequence.Data
public import Mathlib.Algebra.Homology.ConcreteCategory

@[expose] public section

/-!
# The canonical map from Milnor cocycles to the actual internal second page

The coordinate map and the first-page homology quotient belong to the same
Adams tower. These constructions do not select an unrelated page comparison.
-/

namespace KIP126.Classical.Adams.MilnorCohomology

open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Steenrod.Milnor

universe u v
noncomputable section

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  (H : Mod2EilenbergMacLane (C := C)) (M : MilnorCooperations H)

/-- Actual cobar cycles, sent through the inverse coordinates into cycles
of the actual first-page differential. -/
def cyclesToFirstPageCycles (s t : ℕ) :
    cycles s t →ₗ[ℤ]
      (adamsPageComplex H.unit SphereSpectrum 1 (by decide)).cycles ((s : ℤ), (t : ℤ)) := by
  let K := adamsPageComplex H.unit SphereSpectrum 1 (by decide)
  let p : ℤ × ℤ := (s, t)
  let q : ℤ × ℤ := ((s + 1 : ℕ), t)
  have hpq : (classicalAdamsShape 1).next p = q := by
    apply ComplexShape.next_eq'
    change p + ((1 : ℤ), 1 - 1) = q
    dsimp [p, q]
    apply Prod.ext <;> simp
  have hi (a : K.X p) (ha : (K.d p q).hom a = 0) :
      (K.iCycles p).hom (K.cyclesMk a q hpq ha) = a := K.i_cyclesMk a q hpq ha
  let f : cycles s t →+ K.cycles p := by
    refine
      { toFun := fun x => K.cyclesMk ((M.coordinates s t).symm x.val) q hpq
          (Sphere.milnorCocycle_d_zero H M s t x.val x.property)
        map_zero' := ?_
        map_add' := ?_ }
    · apply (ModuleCat.mono_iff_injective (K.iCycles p)).1 inferInstance
      change (K.iCycles p).hom _ = (K.iCycles p).hom _
      rw [hi, map_zero]
      exact (M.coordinates s t).symm.map_zero
    · intro x y
      apply (ModuleCat.mono_iff_injective (K.iCycles p)).1 inferInstance
      change (K.iCycles p).hom _ = (K.iCycles p).hom _
      rw [map_add, hi, hi, hi]
      exact (M.coordinates s t).symm.map_add _ _
  exact
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun n x => map_intCast_smul f ℤ ℤ n x }

/-- The linear class map to the actual internal E₂ page. -/
def cycleClassMap (s t : ℕ) : cycles s t →ₗ[ℤ]
    (adamsTowerInternalSpectralSequence H.unit SphereSpectrum).Page 2
      ((s : ℤ), (t : ℤ)) :=
  ((adamsTowerSSDataPageIso H.unit SphereSpectrum s t 0).inv.hom).comp
    (((adamsPageHomologyIso H.unit SphereSpectrum 1 (by decide) (s, t)).hom.hom).comp
      (((adamsPageComplex H.unit SphereSpectrum 1 (by decide)).homologyπ (s, t)).hom.comp
        (cyclesToFirstPageCycles H M s t)))

/-- The canonical internal class of this specified Milnor cocycle. -/
def internalClassOfCocycle {s t : ℕ} (x : cochains s t)
    (hx : differential s t x = 0) :
    (adamsTowerInternalSpectralSequence H.unit SphereSpectrum).Page 2
      ((s : ℤ), (t : ℤ)) :=
  cycleClassMap H M s t ⟨x, hx⟩

end
end KIP126.Classical.Adams.MilnorCohomology
