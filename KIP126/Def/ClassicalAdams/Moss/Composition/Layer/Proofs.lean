module

public import KIP126.Def.ClassicalAdams.Moss.Composition.Layer.Data
public import KIP126.Def.StableHomotopy.Cohomology.Multiplication.Pairing.Proofs

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

/-- The layer map is the coefficient product paired with the same stage map. -/
theorem layerComposition_comparison (X Y Z : C) (s t : ℕ) :
    layerComposition H R X Y Z s t ≫
        (adamsLayerIso H.unit (mappingObject X Z) (t + s)).hom =
      ((adamsLayerIso H.unit (mappingObject X Y) s).hom ⊗ₘ
        (adamsLayerIso H.unit (mappingObject Y Z) t).hom) ≫
        mod2CoefficientPairing H R (stageComposition H.unit X Y Z s t) := by
  simp only [layerComposition, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- On actual tower-to-layer images, the constructed layer map recovers
stage composition followed by the actual target layer projection. -/
theorem layerComposition_ι (X Y Z : C) (s t : ℕ) :
    ((adamsLayerTriangle H.unit (mappingObject X Y) s).mor₂ ⊗ₘ
        (adamsLayerTriangle H.unit (mappingObject Y Z) t).mor₂) ≫
        layerComposition H R X Y Z s t =
      stageComposition H.unit X Y Z s t ≫
        (adamsLayerTriangle H.unit (mappingObject X Z) ((t + s : ℕ) : ℤ)).mor₂ := by
  have hι (A : C) (k : ℕ) : (adamsLayerTriangle H.unit A k).mor₂ ≫
      (adamsLayerIso H.unit A k).hom = adamsUnit H.unit (adamsTower H.unit A k) :=
    adamsLayerIso_ι H.unit A k
  apply (cancel_mono (adamsLayerIso H.unit (mappingObject X Z) (t + s)).hom).mp
  erw [Category.assoc, layerComposition_comparison, ← Category.assoc,
    tensorHom_comp_tensorHom, hι, hι, mod2CoefficientPairing_unit]
  change stageComposition H.unit X Y Z s t ≫
      adamsUnit H.unit (adamsTower H.unit (mappingObject X Z) (t + s)) =
    (stageComposition H.unit X Y Z s t ≫
      (adamsLayerTriangle H.unit (mappingObject X Z) ((t + s : ℕ) : ℤ)).mor₂) ≫
      (adamsLayerIso H.unit (mappingObject X Z) (t + s)).hom
  exact (congrArg (fun f => stageComposition H.unit X Y Z s t ≫ f)
    (hι (mappingObject X Z) (t + s))).symm.trans (Category.assoc _ _ _).symm

end
end KIP126.Classical.Adams.Moss
