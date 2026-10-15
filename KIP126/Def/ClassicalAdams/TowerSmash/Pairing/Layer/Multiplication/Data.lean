module

public import KIP126.Def.ClassicalAdams.TowerSmash.Pairing.Transport.Proofs
public import KIP126.Def.ClassicalAdams.TowerLayer.Proofs
public import KIP126.Def.StableHomotopy.Cohomology.Multiplication.Pairing.Data

@[expose] public section

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] [BraidedCategory C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)
  [∀ Y : C, (tensorRight Y).CommShift ℤ]
  [∀ Y : C, (tensorRight Y).IsTriangulated]

/-- Multiply actual Adams layers through their existing comparisons with
HF2 smashed with a tower stage. This uses the supplied coefficient ring
multiplication, not either independently chosen mixed triangle completion.
No boundary formula, associativity on layers, or Lin comparison is asserted. -/
def adamsSphereLayerProduct (s t : ℕ) :
    adamsLayerAt H.unit (𝟙_ C) s ⊗ adamsLayerAt H.unit (𝟙_ C) t ⟶
      adamsLayerAt H.unit (𝟙_ C) ((t + s : ℕ) : ℤ) :=
  ((adamsLayerIso H.unit (𝟙_ C) s).hom ⊗ₘ
      (adamsLayerIso H.unit (𝟙_ C) t).hom) ≫
    mod2CoefficientPairing H R (adamsTowerSpherePairingIso H.unit s t).hom ≫
    (adamsLayerIso H.unit (𝟙_ C) (t + s)).inv

end
end KIP126.Classical.Adams
