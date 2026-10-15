module

public import KIP126.Def.ClassicalAdams.Moss.Composition.CoefficientCycles.Proofs
public import KIP126.Def.ClassicalAdams.TowerSSData.Sequence.Data
public import KIP126.Def.ClassicalAdams.Tower.Proofs
public import Mathlib.Algebra.Category.ModuleCat.Subobject
public import KIP126.Def.ClassicalAdams.TowerSmash.Pairing.Data
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import KIP126.Def.ClassicalAdams.TowerLayer.Proofs
public import KIP126.Def.StableHomotopy.Cohomology.Multiplication.Pairing.Data
public import KIP126.Def.StableHomotopy.Context.TensorPairing.Data
public import KIP126.Def.StableHomotopy.Cohomology.Multiplication.Pairing.Proofs
public import KIP126.Def.ClassicalAdams.TowerLongLayer.Proofs

@[expose] public section

namespace KIP126.Classical.Adams.Moss

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory MonoidalCategory Pretriangulated KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  (H : Mod2EilenbergMacLane (C := C))

/-- The actual layer boundary agrees, through the specified layer comparisons,
with the boundary of the unit resolution. The shift and sign conventions are
those already fixed by the two distinguished triangles. -/
theorem layerFirstBoundary_comparison (A : C) (s : ℕ) :
    HasFunctorialCofiber.cofibδ
        (adamsTowerMapAt H.unit A (s : ℤ) ((s : ℤ) + 1) (by omega)) ≫
      (HasFunctorialCofiber.cofibι
        (adamsTowerMapAt H.unit A ((s : ℤ) + 1) (((s : ℤ) + 1) + 1)
          (by omega)))⟦(1 : ℤ)⟧' ≫
      (adamsLayerIso H.unit A (s + 1)).hom⟦(1 : ℤ)⟧' =
    (adamsLayerIso H.unit A s).hom ≫
      (adamsResolutionSequence H (adamsTower H.unit A s)).h ≫
      (adamsUnit H.unit (fiber (adamsUnit H.unit (adamsTower H.unit A s))))⟦(1 : ℤ)⟧' := by
  rw [← Functor.map_comp]
  erw [adamsLayerIso_ι H.unit A (s + 1)]
  rw [adamsLayerIso_δ]
  simp only [adamsResolutionSequence, adamsResolutionConnecting,
    adamsTower, Preadditive.neg_comp, Preadditive.comp_neg, Category.assoc]

/-- A length-two long-layer projection has zero first boundary as an actual
morphism. This does not rely on homotopy groups detecting maps. -/
theorem longLayerTwoProjection_firstBoundary_eq_zero (A : C) (s : ℕ) :
    adamsLongLayerProjection H.unit A 2 (by decide) s ≫
      HasFunctorialCofiber.cofibδ
        (adamsTowerMapAt H.unit A (s : ℤ) ((s : ℤ) + 1) (by omega)) ≫
      (HasFunctorialCofiber.cofibι
        (adamsTowerMapAt H.unit A ((s : ℤ) + 1) (((s : ℤ) + 1) + 1)
          (by omega)))⟦(1 : ℤ)⟧' = 0 := by
  rw [← Category.assoc]
  unfold adamsLongLayerProjection
  rw [cofiberFactorizationMap_δ, Category.assoc, ← Functor.map_comp]
  have hz : adamsTowerMapAt H.unit A ((s : ℤ) + 1) (((s : ℤ) + 1) + 1)
      (by omega) ≫ HasFunctorialCofiber.cofibι
        (adamsTowerMapAt H.unit A ((s : ℤ) + 1) (((s : ℤ) + 1) + 1)
          (by omega)) = 0 :=
    comp_distTriang_mor_zero₁₂ (adamsLayerTriangle H.unit A ((s : ℤ) + 1))
      (adamsLayerTriangle_distinguished H.unit A ((s : ℤ) + 1))
  erw [hz]
  rw [Functor.map_zero, Limits.comp_zero]

variable (R : Mod2RingStructure H)
  [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]
  [(mod2UnitNatTrans H).CommShift ℤ]

include R in
/-- The unit-equalizer criterion for the actual first layer differential,
tested on an arbitrary source object. -/
theorem layerFirstBoundary_eq_zero_iff_unit_equalizer {U : C} (A : C) (s : ℕ)
    (a : U ⟶ adamsLayerAt H.unit A s) :
    a ≫ HasFunctorialCofiber.cofibδ
        (adamsTowerMapAt H.unit A (s : ℤ) ((s : ℤ) + 1) (by omega)) ≫
      (HasFunctorialCofiber.cofibι
        (adamsTowerMapAt H.unit A ((s : ℤ) + 1) (((s : ℤ) + 1) + 1)
          (by omega)))⟦(1 : ℤ)⟧' = 0 ↔
    (a ≫ (adamsLayerIso H.unit A s).hom) ≫
      adamsUnit H.unit (H.HF2 ⊗ adamsTower H.unit A s) =
    (a ≫ (adamsLayerIso H.unit A s).hom) ≫
      H.HF2 ◁ adamsUnit H.unit (adamsTower H.unit A s) := by
  rw [← firstBoundary_eq_zero_iff_unit_equalizer H R]
  rw [← cancel_mono ((adamsLayerIso H.unit A (s + 1)).hom⟦(1 : ℤ)⟧'),
    Limits.zero_comp]
  simp only [Category.assoc, layerFirstBoundary_comparison]

variable [MonoidalClosed C] [BraidedCategory C]
  [∀ A : C, (tensorRight A).CommShift ℤ]
  [∀ A : C, (tensorRight A).IsTriangulated]

end
end KIP126.Classical.Adams.Moss
