module

public import KIP126.Def.ClassicalAdams.TowerSmash.Pairing.Data

@[expose] public section

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : 𝟙_ C ⟶ H)

theorem adamsSmashSpherePairingIso_zero (t : ℕ) :
    (adamsSmashSpherePairingIso unit 0 t).hom =
      (λ_ (adamsSmashTower unit (𝟙_ C) t)).hom := by
  simp only [adamsSmashSpherePairingIso, adamsSmashSphereTensorIso,
    adamsSmashTowerNestingIso, Iso.trans_hom, Iso.refl_hom]
  exact Category.comp_id _

/-- The successor formula is precisely reassociation followed by tensoring
the previous pairing, not a new chosen multiplication at each stage. -/
theorem adamsSmashSpherePairingIso_succ (s t : ℕ) :
    (adamsSmashSpherePairingIso unit (s + 1) t).hom =
      (α_ (fiber unit) (adamsSmashTower unit (𝟙_ C) s)
        (adamsSmashTower unit (𝟙_ C) t)).hom ≫
        (fiber unit ◁ (adamsSmashSpherePairingIso unit s t).hom) := by
  simp only [adamsSmashSpherePairingIso, adamsSmashSphereTensorIso,
    adamsSmashTowerNestingIso, Iso.trans_hom, Functor.mapIso_hom,
    Category.assoc, MonoidalCategory.whiskerLeft_comp]
  rfl

private theorem unitFiberPairing_step (U V W : C) (f : U ⊗ V ⟶ W) :
    ((α_ (fiber unit) U V).hom ≫ fiber unit ◁ f) ≫
        ((fiberι unit ▷ W) ≫ (λ_ W).hom) =
      (((fiberι unit ▷ U) ≫ (λ_ U).hom) ▷ V) ≫ f := by
  simp only [Category.assoc]
  rw [whisker_exchange_assoc, leftUnitor_naturality]
  rw [← associator_naturality_left_assoc, leftUnitor_tensor_hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, comp_whiskerRight]

/-- Concatenation commutes with dropping a fiber factor from the first
input. No second-input compatibility or Leibniz assertion is implicit here. -/
theorem adamsSmashSpherePairingIso_step_left (s t : ℕ) :
    (adamsSmashSpherePairingIso unit (s + 1) t).hom ≫
        adamsSmashTowerStep unit (𝟙_ C) (t + s) =
      (adamsSmashTowerStep unit (𝟙_ C) s ▷ adamsSmashTower unit (𝟙_ C) t) ≫
        (adamsSmashSpherePairingIso unit s t).hom := by
  rw [adamsSmashSpherePairingIso_succ]
  exact unitFiberPairing_step unit _ _ _ (adamsSmashSpherePairingIso unit s t).hom

end
end KIP126.Classical.Adams
