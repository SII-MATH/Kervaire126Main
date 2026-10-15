module

public import KIP126.Def.ClassicalAdams.TowerSmash.Pairing.Transport.Data

@[expose] public section

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : 𝟙_ C ⟶ H)
  [∀ Y : C, (tensorRight Y).CommShift ℤ]
  [∀ Y : C, (tensorRight Y).IsTriangulated]

/-- The pairing is transported through the already constructed tower maps. -/
theorem adamsTowerSpherePairingIso_comparison (s t : ℕ) :
    (adamsTowerSpherePairingIso unit s t).hom ≫
        (adamsTowerSmashIso unit (𝟙_ C) (t + s)).hom =
      ((adamsTowerSmashIso unit (𝟙_ C) s).hom ⊗ₘ
        (adamsTowerSmashIso unit (𝟙_ C) t).hom) ≫
        (adamsSmashSpherePairingIso unit s t).hom := by
  simp only [adamsTowerSpherePairingIso, Iso.trans_hom, Iso.symm_hom,
    tensorIso_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]

variable [MonoidalPreadditive C]

/-- The existing sphere tower pairing commutes with its actual first-input
successor map. This does not assert the second-input transition law. -/
theorem adamsTowerSpherePairingIso_step_left (s t : ℕ) :
    (adamsTowerSpherePairingIso unit (s + 1) t).hom ≫
        adamsTowerStep unit (𝟙_ C) (t + s) =
      (adamsTowerStep unit (𝟙_ C) s ▷ adamsTower unit (𝟙_ C) t) ≫
        (adamsTowerSpherePairingIso unit s t).hom := by
  have htensor :
      ((adamsTowerSmashIso unit (𝟙_ C) (s + 1)).hom ⊗ₘ
          (adamsTowerSmashIso unit (𝟙_ C) t).hom) ≫
          (adamsSmashTowerStep unit (𝟙_ C) s ▷ adamsSmashTower unit (𝟙_ C) t) =
        (adamsTowerStep unit (𝟙_ C) s ▷ adamsTower unit (𝟙_ C) t) ≫
          ((adamsTowerSmashIso unit (𝟙_ C) s).hom ⊗ₘ
            (adamsTowerSmashIso unit (𝟙_ C) t).hom) := by
    simp only [← tensorHom_id, tensorHom_comp_tensorHom, Category.comp_id,
      Category.id_comp, adamsTowerSmashIso_step]
  apply (cancel_mono (adamsTowerSmashIso unit (𝟙_ C) (t + s)).hom).mp
  have hcomparison := adamsTowerSpherePairingIso_comparison unit (s + 1) t
  simp only [Nat.add_succ, Nat.add_zero] at hcomparison
  simp only [Category.assoc, ← adamsTowerSmashIso_step]
  rw [← Category.assoc, hcomparison]
  simp only [Category.assoc]
  rw [adamsSmashSpherePairingIso_step_left]
  rw [← Category.assoc, htensor, Category.assoc, ← adamsTowerSpherePairingIso_comparison]

end
end KIP126.Classical.Adams
