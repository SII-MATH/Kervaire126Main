module

public import KIP126.Def.ClassicalAdams.Moss.Composition.Layer.Data
public import KIP126.Def.ClassicalAdams.TowerLongLayer.Data

@[expose] public section

namespace KIP126.Classical.Adams.Moss

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] [MonoidalClosed C] [BraidedCategory C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)
  [∀ A : C, (tensorRight A).CommShift ℤ]
  [∀ A : C, (tensorRight A).IsTriangulated]

/-- The prescribed mixed long-layer pairing projected to the actual one-step
output layer. This is constructed for every length, before a long-layer lift. -/
def longLayerProjectedComposition (X Y Z : C) (r : ℕ) (hr : 1 ≤ r) (s t : ℕ) :
    adamsLongLayer H.unit (mappingObject X Y) r hr s ⊗
      adamsLongLayer H.unit (mappingObject Y Z) r hr t ⟶
        adamsLayerAt H.unit (mappingObject X Z) ((s : ℤ) + (t : ℤ)) :=
  (adamsLongLayerProjection H.unit (mappingObject X Y) r hr s ⊗ₘ
    adamsLongLayerProjection H.unit (mappingObject Y Z) r hr t) ≫
      layerCompositionOrdered H R X Y Z s t

/-- The specific connecting morphism whose lift to the r-deeper target tower
is the obstruction to constructing the desired long-layer composition. -/
def longLayerCompositionBoundary (X Y Z : C) (r : ℕ) (hr : 1 ≤ r) (s t : ℕ) :
    adamsLongLayer H.unit (mappingObject X Y) r hr s ⊗
      adamsLongLayer H.unit (mappingObject Y Z) r hr t ⟶
        (adamsTowerAt H.unit (mappingObject X Z) (((s : ℤ) + (t : ℤ)) + 1))⟦(1 : ℤ)⟧ :=
  longLayerProjectedComposition H R X Y Z r hr s t ≫
    HasFunctorialCofiber.cofibδ (adamsTowerMapAt H.unit (mappingObject X Z)
      ((s : ℤ) + (t : ℤ)) (((s : ℤ) + (t : ℤ)) + 1) (by omega))

end
end KIP126.Classical.Adams.Moss
