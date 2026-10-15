module

public import KIP126.Def.ClassicalAdams.TowerSSData.Differential.Proofs
public import KIP126.Def.ClassicalAdams.TowerSSData.Page.Proofs
public import KIP126.Def.ClassicalAdams.TowerSequence.NextCycles.Proofs

@[expose] public section

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  KIP126.StableHomotopy KIP126.SpectralSequence
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : 𝟙_ C ⟶ H) (X : C)

/-- A cycle represents an internal differential cycle exactly when it lifts
one stage farther in the actual tower. -/
theorem adamsTowerInternalD_π_eq_zero_iff (s t : ℤ) (n : ℕ)
    (x : adamsFiniteCycleSubmodule unit X s t n) :
    adamsTowerInternalD unit X n s t
      ((adamsTowerSSData unit X s t).pageπ (n : WithTop ℕ)
        ((submoduleUnderlyingIso (M := ModuleCat.of ℤ (adamsCycleAmbient unit X s t))
          (adamsFiniteCycleSubmodule unit X s t n)).inv x)) = 0 ↔
      x.val ∈ adamsFiniteCycleSubmodule unit X s t (n + 1) := by
  let z := (adamsTowerSSData unit X s t).pageπ (n : WithTop ℕ)
    ((submoduleUnderlyingIso (M := ModuleCat.of ℤ (adamsCycleAmbient unit X s t))
      (adamsFiniteCycleSubmodule unit X s t n)).inv x)
  have hp := congrArg (fun f => f.hom x) (adamsTowerSSDataPageIso_π unit X s t n)
  change (adamsTowerSSDataPageIso unit X s t n).hom z =
    (adamsCycleBoundaries unit X (n + 2) (by omega) s t).mkQ
      (adamsFiniteCycleEquiv unit X s t n x) at hp
  have hd := congrArg (fun f => f.hom z) (adamsTowerInternalD_comparison unit X n s t)
  change (adamsTowerSSDataPageIso unit X (s + (n + 2 : ℕ))
    (t + (n + 2 : ℕ) - 1) n).hom (adamsTowerInternalD unit X n s t z) =
      adamsDifferential unit X (n + 2) (by omega) s t
        ((adamsTowerSSDataPageIso unit X s t n).hom z) at hd
  rw [hp, adamsDifferential_mk] at hd
  have hz := adamsDifferentialValue_eq_zero_iff unit X (n + 2) (by omega) s t
    (adamsFiniteCycleEquiv unit X s t n x)
  constructor
  · intro h
    change adamsTowerInternalD unit X n s t z = 0 at h
    rw [h, map_zero] at hd
    exact hz.mp hd.symm
  · intro h
    apply (ModuleCat.mono_iff_injective
      (adamsTowerSSDataPageIso unit X (s + (n + 2 : ℕ))
        (t + (n + 2 : ℕ) - 1) n).hom).mp inferInstance
    rw [map_zero, hd]
    exact hz.mpr h

/-- The internal next-cycle axiom follows from the actual tower lifting criterion. -/
theorem adamsTowerInternalD_kernel (s t : ℤ) (n : ℕ) :
    kernelSubobject (adamsTowerInternalD unit X n s t) =
      imageSubobject (Subobject.ofLE
        ((adamsTowerSSData unit X s t).Z ((n + 1 : ℕ) : WithTop ℕ))
        ((adamsTowerSSData unit X s t).Z (n : WithTop ℕ))
        ((adamsTowerSSData unit X s t).Z_anti (by exact_mod_cast Nat.le_succ n)) ≫
        (adamsTowerSSData unit X s t).pageπ (n : WithTop ℕ)) := by
  let e (m : ℕ) := submoduleUnderlyingIso
    (M := ModuleCat.of ℤ (adamsCycleAmbient unit X s t))
    (adamsFiniteCycleSubmodule unit X s t m)
  have hZ : adamsFiniteCycleSubmodule unit X s t (n + 1) ≤
      adamsFiniteCycleSubmodule unit X s t n :=
    adamsFiniteCycleSubmodule_antitone unit X s t (Nat.le_succ n)
  have hi (w : adamsFiniteCycleSubmodule unit X s t (n + 1)) :
      Subobject.ofLE
        ((adamsTowerSSData unit X s t).Z ((n + 1 : ℕ) : WithTop ℕ))
        ((adamsTowerSSData unit X s t).Z (n : WithTop ℕ))
        ((adamsTowerSSData unit X s t).Z_anti (by exact_mod_cast Nat.le_succ n))
        ((e (n + 1)).inv w) = (e n).inv ⟨w.val, hZ w.property⟩ := by
    exact congrArg (fun f => f.hom w) (submoduleUnderlyingIso_inv_ofLE
      (M := ModuleCat.of ℤ (adamsCycleAmbient unit X s t))
      (adamsFiniteCycleSubmodule unit X s t (n + 1))
      (adamsFiniteCycleSubmodule unit X s t n) hZ)
  apply (ModuleCat.subobjectModule _).injective
  rw [subobjectModule_kernel, subobjectModule_image]
  ext z
  change adamsTowerInternalD unit X n s t z = 0 ↔ ∃ y, _ = z
  constructor
  · intro hz
    obtain ⟨w, rfl⟩ := adamsTowerSSData_projection_surjective unit X s t n z
    have hw := (adamsTowerInternalD_π_eq_zero_iff unit X s t n w).mp hz
    refine ⟨(e (n + 1)).inv ⟨w.val, hw⟩, ?_⟩
    change (adamsTowerSSData unit X s t).pageπ (n : WithTop ℕ) _ = _
    exact congrArg (fun y => (adamsTowerSSData unit X s t).pageπ (n : WithTop ℕ) y)
      (hi ⟨w.val, hw⟩)
  · rintro ⟨y, rfl⟩
    obtain ⟨w, rfl⟩ := (ModuleCat.epi_iff_surjective (e (n + 1)).inv).mp inferInstance y
    change adamsTowerInternalD unit X n s t
      ((adamsTowerSSData unit X s t).pageπ (n : WithTop ℕ) _) = 0
    exact (congrArg (fun y => adamsTowerInternalD unit X n s t
      ((adamsTowerSSData unit X s t).pageπ (n : WithTop ℕ) y)) (hi w)).trans
        ((adamsTowerInternalD_π_eq_zero_iff unit X s t n _).mpr w.property)

end
end KIP126.Classical.Adams
