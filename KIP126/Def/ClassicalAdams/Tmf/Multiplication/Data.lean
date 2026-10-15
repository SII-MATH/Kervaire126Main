module

public import KIP126.Def.ClassicalAdams.TowerSmash.Pairing.Data
public import KIP126.Def.ClassicalAdams.TowerLayer.Data
public import KIP126.Def.StableHomotopy.Cohomology.Multiplication.Pairing.Data
public import KIP126.Def.StableHomotopy.Context.TensorPairing.Data
public import Mathlib.CategoryTheory.Monoidal.Mon

@[expose] public section

/-!
# Multiplication on the actual Adams stages and first groups

These maps use the same sphere-smash and layer comparisons as the Moss
composition maps, with the supplied algebra object's `MonObj.mul` in place
of internal mapping-spectrum composition. No page multiplication is input.
-/

namespace KIP126.Classical.Adams.Tmf

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] [BraidedCategory C]
  (H : Mod2EilenbergMacLane (C := C)) (T : Mon C)

/-- Concatenate the actual unit-fiber words and apply the given multiplication
of `T`. The order `s' + s` is the existing smash concatenation convention. -/
def smashMultiplication (s s' : ℕ) :
    adamsSmashTower H.unit T.X s ⊗ adamsSmashTower H.unit T.X s' ⟶
      adamsSmashTower H.unit T.X (s' + s) :=
  ((adamsSmashSphereTensorIso H.unit T.X s).inv ⊗ₘ
      (adamsSmashSphereTensorIso H.unit T.X s').inv) ≫
    tensorμ (adamsSmashTower H.unit (𝟙_ C) s) T.X
      (adamsSmashTower H.unit (𝟙_ C) s') T.X ≫
    ((adamsSmashSpherePairingIso H.unit s s').hom ⊗ₘ MonObj.mul) ≫
    (adamsSmashSphereTensorIso H.unit T.X (s' + s)).hom

variable [∀ A : C, (tensorRight A).CommShift ℤ]
  [∀ A : C, (tensorRight A).IsTriangulated]

/-- Transport the prescribed smash multiplication to the actual iterated-fiber
Adams stages, using the existing stage comparisons. -/
def stageMultiplication (s s' : ℕ) :
    adamsTower H.unit T.X s ⊗ adamsTower H.unit T.X s' ⟶
      adamsTower H.unit T.X (s' + s) :=
  ((adamsTowerSmashIso H.unit T.X s).hom ⊗ₘ
      (adamsTowerSmashIso H.unit T.X s').hom) ≫
    smashMultiplication H T s s' ≫
    (adamsTowerSmashIso H.unit T.X (s' + s)).inv

variable (R : Mod2RingStructure H)

/-- Multiply the actual HF₂ coefficients and the actual tower stages, then
return through the chosen cofiber-layer comparison. -/
def layerMultiplication (s s' : ℕ) :
    adamsLayerAt H.unit T.X s ⊗ adamsLayerAt H.unit T.X s' ⟶
      adamsLayerAt H.unit T.X ((s + s' : ℕ) : ℤ) :=
  ((adamsLayerIso H.unit T.X s).hom ⊗ₘ
      (adamsLayerIso H.unit T.X s').hom) ≫
    mod2CoefficientPairing H R (stageMultiplication H T s s') ≫
    (adamsLayerIso H.unit T.X (s' + s)).inv ≫
    eqToHom (congrArg (adamsLayerAt H.unit T.X) (by omega))

/-- The integer-bilinear first-group pairing induced by the fixed layer map
and the existing sphere tensor comparison. This is not a free E₂ operation. -/
def firstMultiplication [MonoidalPreadditive C] (s t s' t' : ℕ) :
    adamsE1 H.unit T.X s t →ₗ[ℤ] adamsE1 H.unit T.X s' t' →ₗ[ℤ]
      adamsE1 H.unit T.X ((s + s' : ℕ) : ℤ) ((t + t' : ℕ) : ℤ) :=
  homotopyTensorPairing ((t : ℤ) - s) ((t' : ℤ) - s')
    (((t + t' : ℕ) : ℤ) - ((s + s' : ℕ) : ℤ)) (by omega)
    (layerMultiplication H T R s s')

end
end KIP126.Classical.Adams.Tmf
