module

public import KIP126.Def.ClassicalAdams.TowerLayer.Basic.Data
public import KIP126.Def.ClassicalAdams.PageRepresentatives.Data
public import KIP126.Def.StableHomotopy.Context.Suspension.Data

@[expose] public section

/-!
# Suspension comparison for the actual Adams tower

This is explicit comparison data between the two constructed towers, with
the augmentation, every tower map and the actual cofiber-layer maps fixed.
No E₂ equivalence or freely chosen operation is a field. Constructing this
comparison from a concrete tensor/shift model remains a separate obligation.
-/

namespace KIP126.Classical.Adams.Suspension
open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology

universe u v
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]

/-- Actual tower and layer suspension isomorphisms. The connecting-square
sign is the usual sign of a suspended distinguished triangle with its first
two arrows kept positive. -/
structure TowerComparison (H : Mod2EilenbergMacLane (C := C)) (X : C) where
  tower : ∀ s : ℤ, adamsTowerAt H.unit (X⟦(1 : ℤ)⟧) s ≅
    (adamsTowerAt H.unit X s)⟦(1 : ℤ)⟧
  tower_zero : tower 0 = Iso.refl (X⟦(1 : ℤ)⟧)
  tower_comm : ∀ (s t : ℤ) (hst : s ≤ t),
    (tower t).hom ≫ (adamsTowerMapAt H.unit X s t hst)⟦(1 : ℤ)⟧' =
      adamsTowerMapAt H.unit (X⟦(1 : ℤ)⟧) s t hst ≫ (tower s).hom
  layer : ∀ s : ℤ, adamsLayerAt H.unit (X⟦(1 : ℤ)⟧) s ≅
    (adamsLayerAt H.unit X s)⟦(1 : ℤ)⟧
  layer_inclusion : ∀ s : ℤ,
    HasFunctorialCofiber.cofibι
        (adamsTowerMapAt H.unit (X⟦(1 : ℤ)⟧) s (s + 1) (by omega)) ≫
        (layer s).hom =
      (tower s).hom ≫ (HasFunctorialCofiber.cofibι
        (adamsTowerMapAt H.unit X s (s + 1) (by omega)))⟦(1 : ℤ)⟧'
  layer_connecting : ∀ s : ℤ,
    (layer s).hom ≫ (HasFunctorialCofiber.cofibδ
        (adamsTowerMapAt H.unit X s (s + 1) (by omega)))⟦(1 : ℤ)⟧' ≫
        (shiftFunctorComm C (1 : ℤ) (1 : ℤ)).hom.app
          (adamsTowerAt H.unit X (s + 1)) =
      -(HasFunctorialCofiber.cofibδ
        (adamsTowerMapAt H.unit (X⟦(1 : ℤ)⟧) s (s + 1) (by omega)) ≫
          (tower (s + 1)).hom⟦(1 : ℤ)⟧')

/-- The actual E₂ class of a raw second-cycle representative. -/
def classOfSecondCycle (H : Mod2EilenbergMacLane (C := C)) (X : C)
    (s t : ℤ) (z : adamsCycles H.unit X 2 (by decide) s t) :
    PageRepresentatives.Ambient H X (s, t) :=
  (adamsTowerSSDataPageIso H.unit X s t 0).inv
    ((adamsCycleBoundaries H.unit X 2 (by decide) s t).mkQ z)

/-- Desuspend actual first-page maps through the specified layer comparison;
the domain sphere is reindexed by its genuine integer equality. -/
def TowerComparison.desuspendFirstPage {H : Mod2EilenbergMacLane (C := C)} {X : C}
    (S : TowerComparison H X) (s t : ℤ) :
    adamsE1 H.unit (X⟦(1 : ℤ)⟧) s t →+ adamsE1 H.unit X s (t - 1) where
  toFun z :=
    eqToHom (congrArg (Sphere (C := C))
      (show (t - 1) - s = (t - s) - 1 by omega)) ≫
      homotopyDesuspend (adamsLayerAt H.unit X s) (t - s) (z ≫ (S.layer s).hom)
  map_zero' := by simp
  map_add' a b := by
    simp only [Preadditive.add_comp, map_add, Preadditive.comp_add]

end
end KIP126.Classical.Adams.Suspension
