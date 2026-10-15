module

public import KIP126.Def.ClassicalAdams.Moss.Composition.Data
public import KIP126.Def.ClassicalAdams.TowerLayer.Proofs
public import KIP126.Def.StableHomotopy.Cohomology.Multiplication.Pairing.Data
public import KIP126.Def.StableHomotopy.Context.TensorPairing.Data

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

/-- Multiply the HF₂ coefficients and compose the actual mapping-tower stages,
using the three existing layer comparisons. No layer operation is an input. -/
def layerComposition (X Y Z : C) (s t : ℕ) :
    adamsLayerAt H.unit (mappingObject X Y) s ⊗
      adamsLayerAt H.unit (mappingObject Y Z) t ⟶
        adamsLayerAt H.unit (mappingObject X Z) ((t + s : ℕ) : ℤ) :=
  ((adamsLayerIso H.unit (mappingObject X Y) s).hom ⊗ₘ
    (adamsLayerIso H.unit (mappingObject Y Z) t).hom) ≫
      mod2CoefficientPairing H R (stageComposition H.unit X Y Z s t) ≫
        (adamsLayerIso H.unit (mappingObject X Z) (t + s)).inv

/-- The same layer map, with the mixed-pairing target's additive indexing. -/
def layerCompositionOrdered (X Y Z : C) (s t : ℕ) :
    adamsLayerAt H.unit (mappingObject X Y) s ⊗
      adamsLayerAt H.unit (mappingObject Y Z) t ⟶
        adamsLayerAt H.unit (mappingObject X Z) ((s : ℤ) + (t : ℤ)) :=
  layerComposition H R X Y Z s t ≫
    eqToHom (congrArg (adamsLayerAt H.unit (mappingObject X Z)) (by omega))

/-- Integer-bilinear first-group composition induced by the actual layer map
and the selected sphere tensor comparison. No internal E₂ multiplication is
asserted by this first-group construction. -/
def firstComposition [MonoidalPreadditive C] (X Y Z : C) (s t : ℕ) (u v : ℤ) :
    adamsE1 H.unit (mappingObject X Y) s u →ₗ[ℤ]
      adamsE1 H.unit (mappingObject Y Z) t v →ₗ[ℤ]
        adamsE1 H.unit (mappingObject X Z) ((s : ℤ) + (t : ℤ)) (u + v) :=
  homotopyTensorPairing (u - s) (v - t) ((u + v) - ((s : ℤ) + (t : ℤ)))
    (by omega) (layerCompositionOrdered H R X Y Z s t)

end
end KIP126.Classical.Adams.Moss
