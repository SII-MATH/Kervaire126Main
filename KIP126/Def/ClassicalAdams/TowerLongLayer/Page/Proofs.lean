module

public import KIP126.Def.ClassicalAdams.TowerLongLayer.Page.Data

@[expose] public section

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : 𝟙_ C ⟶ H) (X : C)

theorem adamsLongLayerToCycles_surjective (r : ℕ) (hr : 1 ≤ r) (s t : ℤ) :
    Function.Surjective (adamsLongLayerToCycles unit X r hr s t) := by
  intro x
  obtain ⟨z, hz⟩ := (adamsCycles_mem_iff_longLayer unit X r hr s t x.val).mp x.property
  exact ⟨z, Subtype.ext hz⟩

theorem adamsLongLayerToPage_surjective (r : ℕ) (hr : 1 ≤ r) (s t : ℤ) :
    Function.Surjective (adamsLongLayerToPage unit X r hr s t) :=
  (Submodule.mkQ_surjective (adamsCycleBoundaries unit X r hr s t)).comp
    (adamsLongLayerToCycles_surjective unit X r hr s t)

/-- Long-layer boundary followed by the target projection computes the
actual differential on every page class, since this source map is surjective. -/
theorem adamsDifferential_longLayerToPage (r : ℕ) (hr : 1 ≤ r) (s t : ℤ)
    (z : HomotopyGroup (t - s) (adamsLongLayer unit X r hr s)) :
    adamsDifferential unit X r hr s t (adamsLongLayerToPage unit X r hr s t z) =
      adamsJToPage unit X r hr (s + r) (t + r - 1)
        (Eq.mp (congrArg (fun n => HomotopyGroup n (adamsTowerAt unit X (s + r)))
          (by omega : t - s - 1 = (t + r - 1) - (s + r)))
            (adamsLongLayerK unit X r hr s t z)) :=
  adamsDifferential_of_longLayer unit X r hr s t
    (adamsLongLayerToCycles unit X r hr s t z) z rfl

end
end KIP126.Classical.Adams
