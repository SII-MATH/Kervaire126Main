module

public import KIP126.Def.ClassicalAdams.TowerSmash.Pairing.Layer.Multiplication.Data
public import KIP126.Def.StableHomotopy.Context.TensorPairing.Data

@[expose] public section

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] [BraidedCategory C] [MonoidalPreadditive C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)
  [∀ Y : C, (tensorRight Y).CommShift ℤ]
  [∀ Y : C, (tensorRight Y).IsTriangulated]

/-- The existing coefficient-induced layer product, with its target ordered
as required by the internal additive bidegree convention. -/
def adamsSphereLayerProductOrdered (s t : ℕ) :
    adamsLayerAt H.unit (𝟙_ C) s ⊗ adamsLayerAt H.unit (𝟙_ C) t ⟶
      adamsLayerAt H.unit (𝟙_ C) ((s : ℤ) + (t : ℤ)) :=
  adamsSphereLayerProduct H R s t ≫
    eqToHom (congrArg (adamsLayerAt H.unit (𝟙_ C))
      (by omega : ((t + s : ℕ) : ℤ) = (s : ℤ) + (t : ℤ)))

/-- A fixed first-page product obtained from the actual coefficient-induced
layer map and the given sphere shift comparisons; no arbitrary bilinear map
is supplied as a new input. Compatibility with Lin's product remains open. -/
def adamsSphereE1Product (s t : ℕ) (u v : ℤ) :
    adamsE1 H.unit (𝟙_ C) s u →ₗ[ℤ] adamsE1 H.unit (𝟙_ C) t v →ₗ[ℤ]
      adamsE1 H.unit (𝟙_ C) ((s : ℤ) + (t : ℤ)) (u + v) :=
  homotopyTensorPairing (u - s) (v - t) ((u + v) - ((s : ℤ) + (t : ℤ)))
    (by omega) (adamsSphereLayerProductOrdered H R s t)

end
end KIP126.Classical.Adams
