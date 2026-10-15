module

public import KIP126.Def.ClassicalAdams.TowerHomology.FirstDifferential.Proofs
public import KIP126.Def.StableHomotopy.Cohomology.Multiplication.Pairing.Proofs
public import KIP126.Def.StableHomotopy.Cohomology.Multiplication.Action.Basic.Proofs

@[expose] public section

/-!
The kernel of the first Adams boundary is the equalizer of the two actual unit insertions.
This holds on maps from every test object, not just on sphere homotopy groups.
The specified coefficient pairing preserves that equalizer.  The proofs use
the ring unit splitting and the actual smashed unit triangle; no pagewise
Leibniz law or long-layer multiplication is supplied as an input.
-/

namespace KIP126.Classical.Adams.Moss

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory MonoidalCategory Pretriangulated KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)

section Pairing
variable [BraidedCategory C]

/-- Naturality in both non-coefficient inputs of the actual coefficient pairing. -/
theorem coefficientPairing_precomp {A B A' B' D : C}
    (a : A ⟶ A') (b : B ⟶ B') (f : A' ⊗ B' ⟶ D) :
    ((H.HF2 ◁ a) ⊗ₘ (H.HF2 ◁ b)) ≫ mod2CoefficientPairing H R f =
      mod2CoefficientPairing H R ((a ⊗ₘ b) ≫ f) := by
  unfold mod2CoefficientPairing
  rw [← id_tensorHom, ← id_tensorHom, tensorμ_natural_assoc]
  simp only [tensorHom_comp_tensorHom, tensorHom_id, id_whiskerRight,
    Category.id_comp]

/-- Naturality in the non-coefficient output of the actual coefficient pairing. -/
theorem coefficientPairing_postcomp {A B D D' : C}
    (f : A ⊗ B ⟶ D) (g : D ⟶ D') :
    mod2CoefficientPairing H R f ≫ H.HF2 ◁ g =
      mod2CoefficientPairing H R (f ≫ g) := by
  unfold mod2CoefficientPairing
  rw [Category.assoc, ← id_tensorHom, tensorHom_comp_tensorHom]
  simp only [Category.comp_id]

/-- The inner unit insertion respects coefficient multiplication. -/
theorem coefficientPairing_innerUnit {A B D : C} (f : A ⊗ B ⟶ D) :
    ((H.HF2 ◁ adamsUnit H.unit A) ⊗ₘ (H.HF2 ◁ adamsUnit H.unit B)) ≫
        mod2CoefficientPairing H R (mod2CoefficientPairing H R f) =
      mod2CoefficientPairing H R f ≫ H.HF2 ◁ adamsUnit H.unit D := by
  rw [coefficientPairing_precomp, mod2CoefficientPairing_unit,
    coefficientPairing_postcomp]

/-- The two unit insertions agree on the coefficient product whenever they
agree on its two actual inputs. No boundary formula is assumed. -/
theorem coefficientPairing_preserves_unit_equalizer {A B D U V : C}
    (f : A ⊗ B ⟶ D) (a : U ⟶ H.HF2 ⊗ A) (b : V ⟶ H.HF2 ⊗ B)
    (ha : a ≫ adamsUnit H.unit (H.HF2 ⊗ A) = a ≫ H.HF2 ◁ adamsUnit H.unit A)
    (hb : b ≫ adamsUnit H.unit (H.HF2 ⊗ B) = b ≫ H.HF2 ◁ adamsUnit H.unit B) :
    ((a ⊗ₘ b) ≫ mod2CoefficientPairing H R f) ≫
        adamsUnit H.unit (H.HF2 ⊗ D) =
      ((a ⊗ₘ b) ≫ mod2CoefficientPairing H R f) ≫
        H.HF2 ◁ adamsUnit H.unit D := by
  rw [Category.assoc, ← mod2CoefficientPairing_unit,
    ← Category.assoc, tensorHom_comp_tensorHom, ha, hb,
    ← tensorHom_comp_tensorHom, Category.assoc, coefficientPairing_innerUnit,
    ← Category.assoc]

end Pairing

variable [HasFunctorialCofiber (C := C)]
  [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]
  [(mod2UnitNatTrans H).CommShift ℤ]

include R in
/-- The actual first boundary vanishes precisely on the equalizer of outer
and inner unit insertion.  Exactness is tested on the same arbitrary source
object, so this statement does not require homotopy-group detection. -/
theorem firstBoundary_eq_zero_iff_unit_equalizer {A U : C} (a : U ⟶ H.HF2 ⊗ A) :
    a ≫ (adamsResolutionSequence H A).h ≫
        (adamsUnit H.unit (fiber (adamsUnit H.unit A)))⟦(1 : ℤ)⟧' = 0 ↔
      a ≫ adamsUnit H.unit (H.HF2 ⊗ A) = a ≫ H.HF2 ◁ adamsUnit H.unit A := by
  rw [← adamsResolutionSequence_unit_last_square, ← Category.assoc]
  let T := adamsHomologySequence H A
  have hT := T.distinguished
  constructor
  · intro hz
    obtain ⟨b, hb⟩ := Triangle.coyoneda_exact₃
      (Triangle.mk T.f T.g T.h) hT (a ≫ adamsUnit H.unit (H.HF2 ⊗ A)) hz
    have hb' : a ≫ adamsUnit H.unit (H.HF2 ⊗ A) =
        b ≫ H.HF2 ◁ adamsUnit H.unit A := hb
    have hba : b = a := by
      have h := congrArg (fun k => k ≫ mod2FreeAction H R A) hb'
      have hb0 : b ≫ 𝟙 (H.HF2 ⊗ A) = a := by
        simpa [Category.assoc, mod2FreeAction_outerUnit,
          mod2FreeAction_unit] using h.symm
      exact (Category.comp_id b).symm.trans hb0
    simpa only [hba] using hb'
  · intro he
    rw [he, Category.assoc]
    change a ≫ T.g ≫ T.h = 0
    have hz : T.g ≫ T.h = 0 :=
      comp_distTriang_mor_zero₂₃ (Triangle.mk T.f T.g T.h) hT
    exact (congrArg (fun k => a ≫ k) hz).trans Limits.comp_zero

/-- The actual coefficient product preserves first-boundary cycles on maps
from arbitrary test objects. This uses the specified ring multiplication and
unit triangle, without assuming a Leibniz rule for Adams pages. -/
theorem coefficientPairing_firstBoundary_eq_zero [BraidedCategory C]
    {A B D U V : C} (f : A ⊗ B ⟶ D)
    (a : U ⟶ H.HF2 ⊗ A) (b : V ⟶ H.HF2 ⊗ B)
    (ha : a ≫ (adamsResolutionSequence H A).h ≫
      (adamsUnit H.unit (fiber (adamsUnit H.unit A)))⟦(1 : ℤ)⟧' = 0)
    (hb : b ≫ (adamsResolutionSequence H B).h ≫
      (adamsUnit H.unit (fiber (adamsUnit H.unit B)))⟦(1 : ℤ)⟧' = 0) :
    ((a ⊗ₘ b) ≫ mod2CoefficientPairing H R f) ≫
        (adamsResolutionSequence H D).h ≫
          (adamsUnit H.unit (fiber (adamsUnit H.unit D)))⟦(1 : ℤ)⟧' = 0 := by
  apply (firstBoundary_eq_zero_iff_unit_equalizer H R _).mpr
  exact coefficientPairing_preserves_unit_equalizer H R f a b
    ((firstBoundary_eq_zero_iff_unit_equalizer H R a).mp ha)
    ((firstBoundary_eq_zero_iff_unit_equalizer H R b).mp hb)

end
end KIP126.Classical.Adams.Moss
