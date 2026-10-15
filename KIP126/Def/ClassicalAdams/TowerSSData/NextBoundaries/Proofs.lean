module

public import KIP126.Def.ClassicalAdams.TowerSSData.NextCycles.Proofs
public import KIP126.Def.ClassicalAdams.TowerSequence.NextHomology.Proofs

@[expose] public section

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  KIP126.StableHomotopy KIP126.SpectralSequence
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : 𝟙_ C ⟶ H) (X : C)

/-- On the actual tower quotient, differential images are precisely next boundaries. -/
theorem adamsDifferential_range_iff (r : ℕ) (hr : 1 ≤ r) (s t : ℤ)
    (x : adamsCycles unit X r hr (s + r) (t + r - 1)) :
    (∃ y : adamsPage unit X r hr s t, adamsDifferential unit X r hr s t y =
      (adamsCycleBoundaries unit X r hr (s + r) (t + r - 1)).mkQ x) ↔
    x.val ∈ adamsBoundaries unit X (r + 1) (by omega) (s + r) (t + r - 1) := by
  constructor
  · rintro ⟨y, hy⟩
    induction y using Submodule.Quotient.induction_on with
    | H y =>
      have he : adamsJ unit X (s + r) (t + r - 1)
          (adamsDifferentialLift unit X r hr s t y) - x.val ∈
          adamsBoundaries unit X r hr (s + r) (t + r - 1) :=
        (Submodule.Quotient.eq (adamsCycleBoundaries unit X r hr (s + r) (t + r - 1))).mp hy
      have hm := (adamsBoundaries unit X (r + 1) (by omega) (s + r) (t + r - 1)).sub_mem
        (adamsDifferentialLift_boundary unit X r hr s t y)
        (adamsBoundaries_le_succ unit X r hr (s + r) (t + r - 1) he)
      simpa only [sub_sub_cancel] using hm
  · intro hx
    exact adamsNextBoundary_is_differential unit X r hr s t
      ⟨x.val, adamsBoundaries_le_cycles unit X (r + 1) (by omega)
        (s + r) (t + r - 1) hx⟩ hx

/-- Transporting the differential preserves its range element by element. -/
theorem adamsTowerInternalD_range_iff (n : ℕ) (s t : ℤ)
    (z : (adamsTowerSSData unit X (s + (n + 2 : ℕ))
      (t + (n + 2 : ℕ) - 1)).page (n : WithTop ℕ)) :
    (∃ y, adamsTowerInternalD unit X n s t y = z) ↔
      ∃ y : adamsPage unit X (n + 2) (by omega) s t,
        adamsDifferential unit X (n + 2) (by omega) s t y =
        (adamsTowerSSDataPageIso unit X (s + (n + 2 : ℕ))
          (t + (n + 2 : ℕ) - 1) n).hom z := by
  let e := (adamsTowerSSDataPageIso unit X s t n).toLinearEquiv
  let f := (adamsTowerSSDataPageIso unit X (s + (n + 2 : ℕ))
    (t + (n + 2 : ℕ) - 1) n).toLinearEquiv
  change (∃ y, f.symm (adamsDifferential unit X (n + 2) (by omega) s t (e y)) = z) ↔
    ∃ y : adamsPage unit X (n + 2) (by omega) s t,
      adamsDifferential unit X (n + 2) (by omega) s t y = f z
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨e y, (f.symm_apply_eq.mp hy)⟩
  · rintro ⟨y, hy⟩
    refine ⟨e.symm y, ?_⟩
    rw [e.apply_symm_apply, hy, f.symm_apply_apply]

/-- A specified internal representative is hit precisely when it is a next boundary. -/
theorem adamsTowerInternalD_π_range_iff (n : ℕ) (s t : ℤ)
    (x : adamsFiniteCycleSubmodule unit X (s + (n + 2 : ℕ))
      (t + (n + 2 : ℕ) - 1) n) :
    (∃ y, adamsTowerInternalD unit X n s t y =
      (adamsTowerSSData unit X (s + (n + 2 : ℕ)) (t + (n + 2 : ℕ) - 1)).pageπ
        (n : WithTop ℕ)
        ((submoduleUnderlyingIso (M := ModuleCat.of ℤ (adamsCycleAmbient unit X
          (s + (n + 2 : ℕ)) (t + (n + 2 : ℕ) - 1)))
          (adamsFiniteCycleSubmodule unit X (s + (n + 2 : ℕ))
            (t + (n + 2 : ℕ) - 1) n)).inv x)) ↔
    x.val ∈ adamsFiniteBoundarySubmodule unit X (s + (n + 2 : ℕ))
      (t + (n + 2 : ℕ) - 1) (n + 1) := by
  rw [adamsTowerInternalD_range_iff]
  have hp := congrArg (fun f => f.hom x) (adamsTowerSSDataPageIso_π unit X
    (s + (n + 2 : ℕ)) (t + (n + 2 : ℕ) - 1) n)
  change (adamsTowerSSDataPageIso unit X (s + (n + 2 : ℕ))
    (t + (n + 2 : ℕ) - 1) n).hom _ =
      (adamsCycleBoundaries unit X (n + 2) (by omega)
        (s + (n + 2 : ℕ)) (t + (n + 2 : ℕ) - 1)).mkQ
        (adamsFiniteCycleEquiv unit X (s + (n + 2 : ℕ))
          (t + (n + 2 : ℕ) - 1) n x) at hp
  have h := adamsDifferential_range_iff unit X (n + 2) (by omega) s t
    (adamsFiniteCycleEquiv unit X (s + (n + 2 : ℕ))
      (t + (n + 2 : ℕ) - 1) n x)
  constructor
  · rintro ⟨y, hy⟩
    exact h.mp ⟨y, hy.trans hp⟩
  · intro hx
    obtain ⟨y, hy⟩ := h.mpr hx
    exact ⟨y, hy.trans hp.symm⟩

/-- The internal next-boundary axiom is a theorem of the constructed tower. -/
theorem adamsTowerInternalD_image (s t : ℤ) (n : ℕ) :
    imageSubobject (adamsTowerInternalD unit X n s t) =
      imageSubobject (Subobject.ofLE
        ((adamsTowerSSData unit X (s + (n + 2 : ℕ))
          (t + (n + 2 : ℕ) - 1)).B ((n + 1 : ℕ) : WithTop ℕ))
        ((adamsTowerSSData unit X (s + (n + 2 : ℕ))
          (t + (n + 2 : ℕ) - 1)).Z (n : WithTop ℕ))
        (le_trans ((adamsTowerSSData unit X (s + (n + 2 : ℕ))
          (t + (n + 2 : ℕ) - 1)).B_le_Z ((n + 1 : ℕ) : WithTop ℕ))
          ((adamsTowerSSData unit X (s + (n + 2 : ℕ))
            (t + (n + 2 : ℕ) - 1)).Z_anti (by exact_mod_cast Nat.le_succ n))) ≫
        (adamsTowerSSData unit X (s + (n + 2 : ℕ))
          (t + (n + 2 : ℕ) - 1)).pageπ (n : WithTop ℕ)) := by
  let a : ℤ := s + (n + 2 : ℕ)
  let b : ℤ := t + (n + 2 : ℕ) - 1
  let eB := submoduleUnderlyingIso (M := ModuleCat.of ℤ (adamsCycleAmbient unit X a b))
    (adamsFiniteBoundarySubmodule unit X a b (n + 1))
  let eZ := submoduleUnderlyingIso (M := ModuleCat.of ℤ (adamsCycleAmbient unit X a b))
    (adamsFiniteCycleSubmodule unit X a b n)
  have hB := adamsFiniteBoundarySubmodule_le_cycle unit X a b (n + 1) n
  let j := Subobject.ofLE
    ((adamsTowerSSData unit X a b).B ((n + 1 : ℕ) : WithTop ℕ))
    ((adamsTowerSSData unit X a b).Z (n : WithTop ℕ))
    (le_trans ((adamsTowerSSData unit X a b).B_le_Z ((n + 1 : ℕ) : WithTop ℕ))
      ((adamsTowerSSData unit X a b).Z_anti (by exact_mod_cast Nat.le_succ n)))
  have hi (w : adamsFiniteBoundarySubmodule unit X a b (n + 1)) :
      j (eB.inv w) = eZ.inv ⟨w.val, hB w.property⟩ := by
    exact congrArg (fun f => f.hom w) (submoduleUnderlyingIso_inv_ofLE
      (M := ModuleCat.of ℤ (adamsCycleAmbient unit X a b))
      (adamsFiniteBoundarySubmodule unit X a b (n + 1))
      (adamsFiniteCycleSubmodule unit X a b n) hB)
  apply (ModuleCat.subobjectModule _).injective
  rw [subobjectModule_image, subobjectModule_image]
  ext z
  change (∃ y, adamsTowerInternalD unit X n s t y = z) ↔
    ∃ y, (adamsTowerSSData unit X a b).pageπ (n : WithTop ℕ) (j y) = z
  constructor
  · intro hz
    obtain ⟨w, rfl⟩ := adamsTowerSSData_projection_surjective unit X a b n z
    have hw := (adamsTowerInternalD_π_range_iff unit X n s t w).mp hz
    refine ⟨eB.inv ⟨w.val, hw⟩, ?_⟩
    exact congrArg (fun y => (adamsTowerSSData unit X a b).pageπ (n : WithTop ℕ) y)
      (hi ⟨w.val, hw⟩)
  · rintro ⟨y, rfl⟩
    obtain ⟨w, rfl⟩ := (ModuleCat.epi_iff_surjective eB.inv).mp inferInstance y
    obtain ⟨y, hy⟩ := (adamsTowerInternalD_π_range_iff unit X n s t
      ⟨w.val, hB w.property⟩).mpr w.property
    refine ⟨y, hy.trans ?_⟩
    exact (congrArg (fun x => (adamsTowerSSData unit X a b).pageπ (n : WithTop ℕ) x)
      (hi w)).symm

end
end KIP126.Classical.Adams
