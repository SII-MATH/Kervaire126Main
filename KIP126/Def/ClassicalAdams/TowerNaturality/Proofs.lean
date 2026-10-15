module

public import KIP126.Def.ClassicalAdams.TowerNaturality.Data
public import KIP126.Def.ClassicalAdams.Tower.Proofs

@[expose] public section

namespace KIP126.Classical.Adams
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
universe u v
set_option backward.isDefEq.respectTransparency false
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : 𝟙_ C ⟶ H)

theorem fiberMap_ι {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y')
    (a : X ⟶ X') (b : Y ⟶ Y') (h : a ≫ g = f ≫ b) :
    fiberMap f g a b h ≫ fiberι g = fiberι f ≫ a := by
  dsimp [fiberMap, fiberι]
  rw [← Functor.map_comp_assoc, HasFunctorialCofiber.cofibMap_δ]
  simp only [Functor.map_comp, Category.assoc]
  exact congrArg (fun k => (HasFunctorialCofiber.cofibδ f)⟦(-1 : ℤ)⟧' ≫ k)
    ((shiftFunctorCompIsoId C (1 : ℤ) (-1 : ℤ) (by omega)).hom.naturality a)

/-- The induced maps commute with the actual tower bonding maps. -/
theorem adamsTowerInduced_step {X Y : C} (f : X ⟶ Y) (s : ℕ) :
    adamsTowerInduced unit f (s + 1) ≫ adamsTowerStep unit Y s =
      adamsTowerStep unit X s ≫ adamsTowerInduced unit f s :=
  fiberMap_ι _ _ _ _ _

theorem adamsTowerInduced_composite {X Y : C} (f : X ⟶ Y) (s l : ℕ) :
    adamsTowerInduced unit f (s + l) ≫ adamsTowerComposite unit Y s l =
      adamsTowerComposite unit X s l ≫ adamsTowerInduced unit f s := by
  induction l with
  | zero => simp [adamsTowerComposite]
  | succ l ih =>
    change adamsTowerInduced unit f (s + l + 1) ≫
        (adamsTowerStep unit Y (s + l) ≫ adamsTowerComposite unit Y s l) =
      (adamsTowerStep unit X (s + l) ≫ adamsTowerComposite unit X s l) ≫ _
    rw [← Category.assoc, adamsTowerInduced_step, Category.assoc, ih, ← Category.assoc]

theorem adamsTowerInduced_map {X Y : C} (f : X ⟶ Y) (s t : ℕ) (h : s ≤ t) :
    adamsTowerInduced unit f t ≫ adamsTowerMap unit Y s t h =
      adamsTowerMap unit X s t h ≫ adamsTowerInduced unit f s := by
  induction t, h using Nat.le_induction with
  | base => simp
  | succ t ht ih =>
    rw [adamsTowerMap_succ unit Y s t ht, adamsTowerMap_succ unit X s t ht,
      ← Category.assoc, adamsTowerInduced_step, Category.assoc, ih, ← Category.assoc]

theorem adamsTowerInduced_mapAt {X Y : C} (f : X ⟶ Y) (s t : ℤ) (h : s ≤ t) :
    adamsTowerInduced unit f t.toNat ≫ adamsTowerMapAt unit Y s t h =
      adamsTowerMapAt unit X s t h ≫ adamsTowerInduced unit f s.toNat :=
  adamsTowerInduced_map unit f _ _ _

end KIP126.Classical.Adams
