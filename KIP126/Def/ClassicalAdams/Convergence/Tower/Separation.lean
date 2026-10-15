module

public import KIP126.Def.ClassicalAdams.Convergence.Tower.Predicates
public import KIP126.Def.ClassicalAdams.SphereVanishing.Predicates

@[expose] public section

/-! The elementwise form of the separatedness condition in strong Adams
convergence. The tower, filtration and homotopy groups are unchanged. -/
namespace KIP126.Classical.Adams

open CategoryTheory MonoidalCategory KIP126.StableHomotopy

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} {unit : 𝟙_ C ⟶ H} {X : C}

set_option backward.isDefEq.respectTransparency false in
/-- Hausdorffness of the specified Adams filtration forces an element lying
in every nonnegative filtration level to vanish. -/
theorem IsAdamsTowerStronglyConvergent.eq_zero_of_mem_filtration
    (convergence : IsAdamsTowerStronglyConvergent unit X)
    (n : ℤ) (a : HomotopyGroup n X)
    (ha : ∀ s : ℕ, a ∈ TowerDetection.filtrationSubmodule unit X s n) : a = 0 := by
  let V := towerAbutment X n
  let S : Submodule ℤ V := Submodule.span ℤ {a}
  have hs : (ModuleCat.subobjectModule V).symm S = ⊥ := by
    apply convergence.separated n
    intro s
    apply (ModuleCat.subobjectModule V).symm.monotone
    apply Submodule.span_le.mpr
    intro x hx
    have hxa := Set.mem_singleton_iff.mp hx
    rw [hxa]
    change a ∈ TowerDetection.filtrationSubmodule unit X s n
    have hh := ha s.toNat
    simpa only [TowerDetection.filtrationSubmodule, Int.toNat_natCast] using hh
  have hz : S = ⊥ := by
    have hh := congrArg (ModuleCat.subobjectModule V) hs
    simpa only [OrderIso.apply_symm_apply, OrderIso.map_bot] using hh
  have ham : a ∈ S := Submodule.subset_span (Set.mem_singleton a)
  rw [hz] at ham
  exact (Submodule.mem_bot ℤ).mp ham

/-- The sphere-separation predicate is the elementwise separatedness of its
same Adams tower; completeness and associated-graded data are not replaced. -/
theorem classicalSphereSeparated_of_strongConvergence
    (H : Cohomology.Mod2EilenbergMacLane (C := C))
    (convergence : IsAdamsTowerStronglyConvergent H.unit SphereSpectrum) :
    ClassicalSphereSeparated H :=
  convergence.eq_zero_of_mem_filtration

end KIP126.Classical.Adams
