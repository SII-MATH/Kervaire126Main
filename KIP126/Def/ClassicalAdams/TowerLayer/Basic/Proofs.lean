module

public import KIP126.Def.ClassicalAdams.TowerLayer.Basic.Data
public import KIP126.Def.ClassicalAdams.TowerPages.Proofs

@[expose] public section

namespace KIP126.Classical.Adams

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Pretriangulated
open KIP126.StableHomotopy

universe u v

set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]

theorem adamsFiberTriangle_distinguished {X Y : C} (f : X ⟶ Y) :
    adamsFiberTriangle f ∈ distTriang C :=
  inv_rot_of_distTriang _ (HasFunctorialCofiber.cofib_distinguished f)

/-- Keep track of the sign rather than identifying two different conventions. -/
theorem adamsFiberTriangle_mor₁ {X Y : C} (f : X ⟶ Y) :
    (adamsFiberTriangle f).mor₁ = -fiberι f := by
  simp only [adamsFiberTriangle, Triangle.invRotate, Triangle.mk, fiberι]
  rfl

theorem fiberι_comp_eq_zero {X Y : C} (f : X ⟶ Y) : fiberι f ≫ f = 0 := by
  have h := comp_distTriang_mor_zero₁₂ _ (adamsFiberTriangle_distinguished f)
  rw [adamsFiberTriangle_mor₁] at h
  change (-fiberι f) ≫ f = 0 at h
  simpa only [Preadditive.neg_comp, neg_eq_zero] using h

variable {H : C} (unit : 𝟙_ C ⟶ H) (X : C)

theorem adamsLayerTriangle_distinguished (s : ℤ) :
    adamsLayerTriangle unit X s ∈ distTriang C :=
  HasFunctorialCofiber.cofib_distinguished _

theorem adamsTowerMapAt_nat_succ (s : ℕ) :
    adamsTowerMapAt unit X (s : ℤ) ((s : ℤ) + 1) (by omega) =
      adamsTowerStep unit X s := by
  change adamsTowerMap unit X s (s + 1) _ = _
  rw [adamsTowerMap_succ unit X s s le_rfl, adamsTowerMap_self, Category.comp_id]

theorem adamsCycles_one (s t : ℤ) : adamsCycles unit X 1 (by decide) s t = ⊤ := by
  simp [adamsCycles, adamsI_self]

theorem adamsBoundaries_one (s t : ℤ) : adamsBoundaries unit X 1 (by decide) s t = ⊥ := by
  have hker (a : ℤ) (ha : a ≤ s) (he : a = s) :
      LinearMap.ker (adamsI unit X (t - s) a s ha) = ⊥ := by
    subst a
    rw [adamsI_self, LinearMap.ker_id]
  rw [adamsBoundaries, hker _ _ (by omega), Submodule.map_bot]

theorem adamsCycleBoundaries_one (s t : ℤ) :
    adamsCycleBoundaries unit X 1 (by decide) s t = ⊥ := by
  rw [adamsCycleBoundaries, adamsBoundaries_one, Submodule.comap_bot, Submodule.ker_subtype]

end KIP126.Classical.Adams
