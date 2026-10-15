module

public import KIP126.Def.ClassicalAdams.MilnorCohomology.Comparison.CycleMap.Data
public import KIP126.Def.ClassicalAdams.MilnorCohomology.Proofs
public import KIP126.Def.ClassicalAdams.SphereClasses.Proofs
public import KIP126.Def.ClassicalAdams.TowerVanishing.Proofs

@[expose] public section
namespace KIP126.Classical.Adams.Sphere
noncomputable section
open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Steenrod.Milnor
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  (H : Mod2EilenbergMacLane (C := C)) (M : MilnorCooperations H)
theorem classOfMilnorCocycle_zero_iff (t : ℕ) (x : cochains 0 t)
    (hx : differential 0 t x = 0) :
    classOfMilnorCocycle H M 0 t x hx = 0 ↔ x = 0 := by
  let K := adamsPageComplex H.unit SphereSpectrum 1 (by decide)
  let p : ℤ × ℤ := ((0 : ℕ), t)
  let q : ℤ × ℤ := ((1 : ℕ), t)
  let a : K.X p := (M.coordinates 0 t).symm x
  have hpq : (classicalAdamsShape 1).next p = q := by
    apply ComplexShape.next_eq'
    change p + ((1 : ℤ), 1 - 1) = q
    dsimp [p, q]
    apply Prod.ext <;> norm_num
  have hprev : (classicalAdamsShape 1).prev p = ((-1 : ℤ), (t : ℤ)) := by
    apply ComplexShape.prev_eq'
    change ((-1 : ℤ), (t : ℤ)) + ((1 : ℤ), 1 - 1) = p
    dsimp [p]
    apply Prod.ext <;> norm_num
  have ha : (K.d p q).hom a = 0 := milnorCocycle_d_zero H M 0 t x hx
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
      ∃ b : K.X ((-1 : ℤ), (t : ℤ)),
        (K.d ((-1 : ℤ), (t : ℤ)) p).hom b = a := by
    have h := (K.sc p).moduleCat_pOpcycles_eq_zero_iff a
    change (K.pOpcycles p).hom a = 0 ↔
      ∃ b : K.X ((classicalAdamsShape 1).prev p),
        (K.d ((classicalAdamsShape 1).prev p) p).hom b = a at h
    erw [hprev] at h
    exact h
  have hclass : classOfMilnorCocycle H M 0 t x hx =
      (adamsPageHomologyIso H.unit SphereSpectrum 1 (by decide) p).hom
        ((K.homologyπ p).hom z) := rfl
  have hinj := (ModuleCat.mono_iff_injective
    (adamsPageHomologyIso H.unit SphereSpectrum 1 (by decide) p).hom).1 inferInstance
  have hezero : classOfMilnorCocycle H M 0 t x hx = 0 ↔
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
  haveI : Subsingleton (K.X ((-1 : ℤ), (t : ℤ))) :=
    adamsPage_subsingleton_of_negative H.unit SphereSpectrum 1 (by decide) (-1) t (by omega)
  constructor
  · rintro ⟨b, hb⟩
    have hb0 : b = 0 := Subsingleton.elim _ _
    have ha0 : a = 0 := by simpa only [hb0, map_zero] using hb.symm
    have hh := (congrArg (M.coordinates 0 t) ha0).trans ((M.coordinates 0 t).map_zero)
    simpa only [a, LinearEquiv.apply_symm_apply] using hh
  · intro hx0
    refine ⟨0, ?_⟩
    change (K.d ((-1 : ℤ), (t : ℤ)) p).hom 0 = (M.coordinates 0 t).symm x
    rw [hx0]
    exact (map_zero _).trans ((M.coordinates 0 t).symm.map_zero).symm

end
end KIP126.Classical.Adams.Sphere

namespace KIP126.Classical.Adams.MilnorCohomology

open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Steenrod.Milnor
universe u v
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  (H : Mod2EilenbergMacLane (C := C)) (M : MilnorCooperations H)

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem iCycles_cyclesToFirstPageCycles (s t : ℕ) (x : cycles s t) :
    ((adamsPageComplex H.unit SphereSpectrum 1 (by decide)).iCycles
      ((s : ℤ), (t : ℤ))).hom (cyclesToFirstPageCycles H M s t x) =
      (M.coordinates s t).symm x.val := by
  let K := adamsPageComplex H.unit SphereSpectrum 1 (by decide)
  let p : ℤ × ℤ := (s, t)
  let q : ℤ × ℤ := ((s + 1 : ℕ), t)
  have hpq : (classicalAdamsShape 1).next p = q := by
    apply ComplexShape.next_eq'
    change p + ((1 : ℤ), 1 - 1) = q
    dsimp [p, q]
    apply Prod.ext <;> simp
  have ha := Sphere.milnorCocycle_d_zero H M s t x.val x.property
  have hi : (K.iCycles p).hom
      (K.cyclesMk ((M.coordinates s t).symm x.val) q hpq ha) =
      (M.coordinates s t).symm x.val := K.i_cyclesMk _ q hpq ha
  exact hi

/-- The canonical class agrees with the existing class of the same actual
first-page cocycle, transported through the actual tower's quotient-page iso. -/
theorem internalClassOfCocycle_eq {s t : ℕ} (x : cochains s t)
    (hx : differential s t x = 0) :
    internalClassOfCocycle H M x hx =
      (adamsTowerSSDataPageIso H.unit SphereSpectrum s t 0).inv
        (Sphere.classOfMilnorCocycle H M s t x hx) := rfl

theorem cyclesToFirstPageCycles_surjective (s t : ℕ) :
    Function.Surjective (cyclesToFirstPageCycles H M s t) := by
  intro z
  let K := adamsPageComplex H.unit SphereSpectrum 1 (by decide)
  let p : ℤ × ℤ := (s, t)
  let q : ℤ × ℤ := ((s + 1 : ℕ), t)
  let x := M.coordinates s t ((K.iCycles p).hom z)
  have hx : differential s t x = 0 := by
    rw [← M.differential_coordinates]
    change M.coordinates (s + 1) t ((K.d p q).hom ((K.iCycles p).hom z)) = 0
    have hz := congrArg (fun f : K.cycles p ⟶ K.X q => f.hom z) (K.iCycles_d p q)
    change (K.d p q).hom ((K.iCycles p).hom z) = 0 at hz
    rw [hz]
    exact (M.coordinates (s + 1) t).map_zero
  refine ⟨⟨x, hx⟩, ?_⟩
  apply (ModuleCat.mono_iff_injective (K.iCycles p)).1 inferInstance
  change (K.iCycles p).hom (cyclesToFirstPageCycles H M s t ⟨x, hx⟩) = _
  rw [iCycles_cyclesToFirstPageCycles]
  exact (M.coordinates s t).symm_apply_apply _

theorem cycleClassMap_surjective (s t : ℕ) :
    Function.Surjective (cycleClassMap H M s t) := by
  intro y
  let e := adamsTowerSSDataPageIso H.unit SphereSpectrum s t 0
  let h := adamsPageHomologyIso H.unit SphereSpectrum 1 (by decide) (s, t)
  let K := adamsPageComplex H.unit SphereSpectrum 1 (by decide)
  obtain ⟨z, hz⟩ := ((ModuleCat.epi_iff_surjective (K.homologyπ (s, t))).1
    inferInstance) (h.inv.hom (e.hom.hom y))
  obtain ⟨x, hx⟩ := cyclesToFirstPageCycles_surjective H M s t z
  refine ⟨x, ?_⟩
  change e.inv.hom (h.hom.hom ((K.homologyπ (s, t)).hom
    (cyclesToFirstPageCycles H M s t x))) = y
  rw [hx, hz]
  change e.toLinearEquiv.symm (h.toLinearEquiv
    (h.toLinearEquiv.symm (e.toLinearEquiv y))) = y
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]

theorem cycleClassMap_eq_zero_iff {s t : ℕ} (x : cycles s t) :
    cycleClassMap H M s t x = 0 ↔ x.val ∈ boundaries s t := by
  have hi := (ModuleCat.mono_iff_injective
    (adamsTowerSSDataPageIso H.unit SphereSpectrum s t 0).inv).1 inferInstance
  have he : cycleClassMap H M s t x = 0 ↔
      Sphere.classOfMilnorCocycle H M s t x.val x.property = 0 := by
    change (adamsTowerSSDataPageIso H.unit SphereSpectrum s t 0).inv
      (Sphere.classOfMilnorCocycle H M s t x.val x.property) = 0 ↔ _
    constructor
    · intro h
      exact hi (h.trans (map_zero _).symm)
    · intro h
      rw [h]
      exact (adamsTowerSSDataPageIso H.unit SphereSpectrum s t 0).inv.hom.map_zero
  cases s with
  | zero =>
      exact he.trans ((Sphere.classOfMilnorCocycle_zero_iff H M t x.val x.property).trans
        (by simp only [boundaries_zero, Submodule.mem_bot]))
  | succ s =>
      exact he.trans (Sphere.classOfMilnorCocycle_eq_zero_iff H M s t x.val x.property)

theorem boundariesInCycles_restrictScalars_eq_ker (s t : ℕ) :
    (boundariesInCycles H M s t).restrictScalars ℤ = LinearMap.ker (cycleClassMap H M s t) := by
  ext x
  exact (mem_boundariesInCycles H M x).trans (cycleClassMap_eq_zero_iff H M x).symm

end
end KIP126.Classical.Adams.MilnorCohomology
