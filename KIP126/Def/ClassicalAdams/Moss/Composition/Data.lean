module

public import KIP126.Def.ClassicalAdams.Moss.Mapping.Data
public import KIP126.Def.ClassicalAdams.TowerSmash.Pairing.Data
public import KIP126.Def.StableHomotopy.Context.Mapping.Composition.Data

@[expose] public section

/-!
Actual maps between the stages of the three mapping-object Adams towers.
The two unit-fiber words are concatenated and the remaining internal-hom
factors are composed by the selected closed structure. Nothing here chooses
a second spectral sequence or an independent multiplication on its pages.

These are stage maps. Transition, layer-boundary, and page-quotient
compatibility must still be proved before they give a multiplicative mapping
spectral sequence or a Massey relation.
-/

namespace KIP126.Classical.Adams.Moss

open CategoryTheory MonoidalCategory KIP126.StableHomotopy

universe u v
noncomputable section

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] [MonoidalClosed C] [BraidedCategory C]
  {H : C} (unit : 𝟙_ C ⟶ H)

/-- Factor out the actual sphere smash stages, braid the middle factors,
concatenate the unit-fiber words, and apply actual internal composition.
The target degree is `t+s`, the order used by the existing concatenation. -/
def smashComposition (X Y Z : C) (s t : ℕ) :
    adamsSmashTower unit (mappingObject X Y) s ⊗
        adamsSmashTower unit (mappingObject Y Z) t ⟶
      adamsSmashTower unit (mappingObject X Z) (t + s) :=
  ((adamsSmashSphereTensorIso unit (mappingObject X Y) s).inv ⊗ₘ
      (adamsSmashSphereTensorIso unit (mappingObject Y Z) t).inv) ≫
    tensorμ (adamsSmashTower unit (𝟙_ C) s) (mappingObject X Y)
      (adamsSmashTower unit (𝟙_ C) t) (mappingObject Y Z) ≫
    ((adamsSmashSpherePairingIso unit s t).hom ⊗ₘ Mapping.composition X Y Z) ≫
    (adamsSmashSphereTensorIso unit (mappingObject X Z) (t + s)).hom

variable [∀ A : C, (tensorRight A).CommShift ℤ]
  [∀ A : C, (tensorRight A).IsTriangulated]

/-- Transfer the concrete smash map to the existing iterated-fiber Adams
towers. The shift and exactness instances are selected for each tensor-right
functor; there is no quantification over arbitrary shift structures. -/
def stageComposition (X Y Z : C) (s t : ℕ) :
    mappingStage unit X Y s ⊗ mappingStage unit Y Z t ⟶
      mappingStage unit X Z (t + s) :=
  ((adamsTowerSmashIso unit (mappingObject X Y) s).hom ⊗ₘ
      (adamsTowerSmashIso unit (mappingObject Y Z) t).hom) ≫
    smashComposition unit X Y Z s t ≫
    (adamsTowerSmashIso unit (mappingObject X Z) (t + s)).inv

end
end KIP126.Classical.Adams.Moss
