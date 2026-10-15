module

public import KIP126.Def.ClassicalAdams.TowerSmash.Data

@[expose] public section

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] [MonoidalPreadditive C]
  {H : C} (unit : 𝟙_ C ⟶ H) (X : C)
  [∀ Y : C, (tensorRight Y).CommShift ℤ]
  [∀ Y : C, (tensorRight Y).IsTriangulated]

/-- The recursive comparisons preserve the actual tower's successor maps. -/
theorem adamsTowerSmashIso_step (s : ℕ) :
    (adamsTowerSmashIso unit X (s + 1)).hom ≫ adamsSmashTowerStep unit X s =
      adamsTowerStep unit X s ≫ (adamsTowerSmashIso unit X s).hom := by
  change ((adamsFiberTensorIso unit (adamsTower unit X s)).hom ≫
      (fiber unit ◁ (adamsTowerSmashIso unit X s).hom)) ≫
        ((fiberι unit ▷ adamsSmashTower unit X s) ≫ (λ_ _).hom) = _
  simp only [Category.assoc]
  rw [whisker_exchange_assoc, leftUnitor_naturality]
  rw [← Category.assoc (fiberι unit ▷ adamsTower unit X s)
    (λ_ (adamsTower unit X s)).hom (adamsTowerSmashIso unit X s).hom]
  rw [← Category.assoc, adamsFiberTensorIso_hom_ι]
  rfl

/-- The comparison respects every finite composite, not only the objects. -/
theorem adamsTowerSmashIso_composite (s length : ℕ) :
    (adamsTowerSmashIso unit X (s + length)).hom ≫
        adamsSmashTowerComposite unit X s length =
      adamsTowerComposite unit X s length ≫ (adamsTowerSmashIso unit X s).hom := by
  induction length with
  | zero => simp only [Nat.add_zero, adamsSmashTowerComposite, adamsTowerComposite,
      Category.comp_id, Category.id_comp]
  | succ n ih =>
      change (adamsTowerSmashIso unit X (s + n + 1)).hom ≫
        (adamsSmashTowerStep unit X (s + n) ≫ adamsSmashTowerComposite unit X s n) =
        (adamsTowerStep unit X (s + n) ≫ adamsTowerComposite unit X s n) ≫ _
      rw [← Category.assoc, adamsTowerSmashIso_step, Category.assoc, ih, Category.assoc]

/-- Actual homotopy-group liftability is unchanged in the smash comparison
model. This transports the finite-stage obstructions used to define Z_r. -/
theorem adamsTowerSmashIso_lift_iff (n : ℤ) (s length : ℕ)
    (x : HomotopyGroup n (adamsTower unit X s)) :
    (∃ y : HomotopyGroup n (adamsTower unit X (s + length)),
      y ≫ adamsTowerComposite unit X s length = x) ↔
    ∃ z : HomotopyGroup n (adamsSmashTower unit X (s + length)),
      z ≫ adamsSmashTowerComposite unit X s length =
        x ≫ (adamsTowerSmashIso unit X s).hom := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y ≫ (adamsTowerSmashIso unit X (s + length)).hom, ?_⟩
    rw [Category.assoc, adamsTowerSmashIso_composite, ← Category.assoc, hy]
  · rintro ⟨z, hz⟩
    refine ⟨z ≫ (adamsTowerSmashIso unit X (s + length)).inv, ?_⟩
    apply (cancel_mono (adamsTowerSmashIso unit X s).hom).mp
    calc
      ((z ≫ (adamsTowerSmashIso unit X (s + length)).inv) ≫
          adamsTowerComposite unit X s length) ≫ (adamsTowerSmashIso unit X s).hom =
          z ≫ adamsSmashTowerComposite unit X s length := by
        simp only [Category.assoc, ← adamsTowerSmashIso_composite, Iso.inv_hom_id_assoc]
      _ = x ≫ (adamsTowerSmashIso unit X s).hom := hz

end
end KIP126.Classical.Adams
