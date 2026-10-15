module

public import KIP126.Def.ClassicalAdams.Moss.Mapping.Data

@[expose] public section

namespace KIP126.Classical.Adams.Moss

open CategoryTheory CategoryTheory.MonoidalCategory KIP126.StableHomotopy

universe u v
noncomputable section

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] [MonoidalClosed C]
  {H : C} (unit : 𝟙_ C ⟶ H) (X Y : C)

@[simp] theorem mappingRestrict_self (s : ℕ) :
    mappingRestrict unit X Y s s le_rfl = 𝟙 _ :=
  adamsTowerMap_self unit _ s

theorem mappingRestrict_comp (s t z : ℕ) (hst : s ≤ t) (htz : t ≤ z) :
    mappingRestrict unit X Y t z htz ≫ mappingRestrict unit X Y s t hst =
      mappingRestrict unit X Y s z (hst.trans htz) :=
  adamsTowerMap_comp unit _ s t z hst htz

theorem mappingToTarget_compatible (s t : ℕ) (hst : s ≤ t) :
    mappingRestrict unit X Y s t hst ≫ mappingToTarget unit X Y s =
      mappingToTarget unit X Y t :=
  adamsTowerMap_comp unit _ 0 s t (Nat.zero_le s) hst

/-- Filtration membership means precisely a lift in this actual tower. -/
theorem mem_mappingFiltrationSubmodule (s n : ℤ) (f : mappingAbutment X Y n) :
    f ∈ mappingFiltrationSubmodule unit X Y s n ↔
      ∃ g : HomotopyGroup n (mappingStage unit X Y s.toNat),
        g ≫ mappingToTarget unit X Y s.toNat = f := Iff.rfl

theorem mappingFiltrationSubmodule_antitone (n : ℤ) :
    Antitone (fun s => mappingFiltrationSubmodule unit X Y s n) := by
  intro s t hst f hf
  obtain ⟨g, hg⟩ := hf
  refine ⟨g ≫ mappingRestrict unit X Y s.toNat t.toNat (by omega), ?_⟩
  change (g ≫ mappingRestrict unit X Y s.toNat t.toNat _) ≫
    mappingToTarget unit X Y s.toNat = f
  rw [Category.assoc, mappingToTarget_compatible]
  exact hg

theorem mappingSequence_firstPage : (mappingSequence unit X Y).r₀ = 2 := rfl

theorem mappingSequence_differentialDegree (r : ℤ) :
    (mappingSequence unit X Y).diffDeg r = (r, r - 1) := rfl

end
end KIP126.Classical.Adams.Moss
