module

public import KIP126.Def.ClassicalAdams.SphereClasses.Data
public import KIP126.Def.Steenrod.MilnorCobar.Data
public import Mathlib.Algebra.MvPolynomial.Coeff
public import KIP126.Def.Algebra.Coefficients.Data
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Choose.Lucas
public import KIP126.Def.Steenrod.MilnorCobar.Polynomial.Detection.Projection.Monomials.Proofs
public import KIP126.Def.Steenrod.MilnorCobar.Polynomial.Monomials.Basis.Proofs
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

@[expose] public section

/-! Zero detection for the specified standard classes uses the actual
first-page homology quotient, not the Lin comparison. -/

namespace KIP126.Classical.Adams

noncomputable section

open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Steenrod.Milnor

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]

namespace Sphere

variable (H : Mod2EilenbergMacLane (C := C)) (M : MilnorCooperations H)

/-- In positive filtration, a specified Milnor cocycle represents zero on
the constructed second page exactly when it is a cobar boundary. -/
theorem classOfMilnorCocycle_eq_zero_iff (s t : ℕ) (x : cochains (s + 1) t)
    (hx : differential (s + 1) t x = 0) :
    classOfMilnorCocycle H M (s + 1) t x hx = 0 ↔
      ∃ b : cochains s t, differential s t b = x := by
  let K := adamsPageComplex H.unit SphereSpectrum 1 (by decide)
  let p : ℤ × ℤ := ((s + 1 : ℕ), t)
  let q : ℤ × ℤ := ((s + 1 + 1 : ℕ), t)
  let a : K.X p := (M.coordinates (s + 1) t).symm x
  have hpq : (classicalAdamsShape 1).next p = q := by
    apply ComplexShape.next_eq'
    change p + ((1 : ℤ), 1 - 1) = q
    dsimp [p, q]
    apply Prod.ext <;> simp
  have hprev : (classicalAdamsShape 1).prev p = ((s : ℤ), (t : ℤ)) := by
    apply ComplexShape.prev_eq'
    change ((s : ℤ), (t : ℤ)) + ((1 : ℤ), 1 - 1) = p
    dsimp [p]
    apply Prod.ext <;> simp
  have ha : (K.d p q).hom a = 0 := milnorCocycle_d_zero H M (s + 1) t x hx
  let z := K.cyclesMk a q hpq ha
  have hz : (K.iCycles p).hom z = a := K.i_cyclesMk a q hpq ha
  have hπ : (K.homologyπ p).hom z = 0 ↔ (K.pOpcycles p).hom a = 0 := by
    have he := congrArg (fun f : K.cycles p ⟶ K.opcycles p => f.hom z)
      (K.homology_π_ι p)
    change (K.homologyι p).hom ((K.homologyπ p).hom z) =
      (K.pOpcycles p).hom ((K.iCycles p).hom z) at he
    rw [hz] at he
    constructor
    · intro h
      simpa only [h, map_zero] using he.symm
    · intro h
      apply (ModuleCat.mono_iff_injective (K.homologyι p)).1 inferInstance
      rw [map_zero, he, h]
  have hboundary : (K.pOpcycles p).hom a = 0 ↔
      ∃ b : K.X ((s : ℤ), (t : ℤ)),
        (K.d ((s : ℤ), (t : ℤ)) p).hom b = a := by
    have h := (K.sc p).moduleCat_pOpcycles_eq_zero_iff a
    change (K.pOpcycles p).hom a = 0 ↔
      ∃ b : K.X ((classicalAdamsShape 1).prev p),
        (K.d ((classicalAdamsShape 1).prev p) p).hom b = a at h
    erw [hprev] at h
    exact h
  have hclass : classOfMilnorCocycle H M (s + 1) t x hx =
      (adamsPageHomologyIso H.unit SphereSpectrum 1 (by decide) p).hom
        ((K.homologyπ p).hom z) := rfl
  have hinj := (ModuleCat.mono_iff_injective
    (adamsPageHomologyIso H.unit SphereSpectrum 1 (by decide) p).hom).1 inferInstance
  have hezero : classOfMilnorCocycle H M (s + 1) t x hx = 0 ↔
      (K.homologyπ p).hom z = 0 := by
    constructor
    · intro h
      apply hinj
      exact (hclass.symm.trans h).trans (map_zero _).symm
    · intro h
      exact hclass.trans ((congrArg
        (adamsPageHomologyIso H.unit SphereSpectrum 1 (Nat.le_refl 1) p).hom.hom h).trans
          (map_zero _))
  refine hezero.trans (hπ.trans (hboundary.trans ?_))
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨M.coordinates s t b, ?_⟩
    rw [← M.differential_coordinates]
    change M.coordinates (s + 1) t ((K.d ((s : ℤ), (t : ℤ)) p).hom b) = x
    rw [hb]
    exact (M.coordinates (s + 1) t).apply_symm_apply x
  · rintro ⟨b, hb⟩
    refine ⟨(M.coordinates s t).symm b, ?_⟩
    apply (M.coordinates (s + 1) t).injective
    change M.coordinates (s + 1) t
      (sphereFirstDifferential H s t ((M.coordinates s t).symm b)) =
        M.coordinates (s + 1) t ((M.coordinates (s + 1) t).symm x)
    rw [M.differential_coordinates, LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply, hb]

end Sphere

end

end KIP126.Classical.Adams
