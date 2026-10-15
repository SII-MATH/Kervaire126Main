module

public import KIP126.Def.Topology.SmallObject.Sequence.Functorial.Data

@[expose] public section

namespace KIP126.Topology.SmallObject

open CategoryTheory CategoryTheory.Limits

universe u v w

variable {C : Type u} [Category.{v} C] {I : Type w} {A B : I → C}
  (f : ∀ i, A i ⟶ B i) [HasPushouts C]
  [∀ {X S : C} (π : X ⟶ S), HasColimitsOfShape
    (Discrete (CategoryTheory.SmallObject.FunctorObjIndex f π)) C]

set_option backward.isDefEq.respectTransparency false

@[simp] theorem cellularStageArrowMap_right {X Y : Arrow C} (τ : X ⟶ Y) (n : ℕ) :
    (cellularStageArrowMap f τ n).right = τ.right := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

@[simp] theorem cellularStageArrowMap_id (X : Arrow C) (n : ℕ) :
    cellularStageArrowMap f (𝟙 X) n = 𝟙 _ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (CategoryTheory.SmallObject.functor f).map _ = _
    rw [ih]
    exact (CategoryTheory.SmallObject.functor f).map_id _

@[simp] theorem cellularStageArrowMap_comp {X Y Z : Arrow C} (τ : X ⟶ Y) (σ : Y ⟶ Z)
    (n : ℕ) : cellularStageArrowMap f (τ ≫ σ) n =
      cellularStageArrowMap f τ n ≫ cellularStageArrowMap f σ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (CategoryTheory.SmallObject.functor f).map _ = _
    rw [ih,Functor.map_comp]
    rfl

@[reassoc] theorem cellularReplacementMap_stage {X Y : Arrow C} (τ : X ⟶ Y)
    [HasColimit (cellularSequence f (Over.mk X.hom))]
    [HasColimit (cellularSequence f (Over.mk Y.hom))] (n : ℕ) :
    colimit.ι (cellularSequence f (Over.mk X.hom)) n ≫ cellularReplacementMap f τ =
      (cellularStageArrowMap f τ n).left ≫ colimit.ι (cellularSequence f (Over.mk Y.hom)) n :=
  ι_colimMap _ _

/-- Naturality of the actual comparison to the original target holds
strictly, before passage to any homotopy or localization. -/
@[reassoc] theorem cellularReplacementMap_comparison {X Y : Arrow C} (τ : X ⟶ Y)
    [HasColimit (cellularSequence f (Over.mk X.hom))]
    [HasColimit (cellularSequence f (Over.mk Y.hom))] :
    cellularReplacementMap f τ ≫ cellularComparison f (Over.mk Y.hom) =
      cellularComparison f (Over.mk X.hom) ≫ τ.right := by
  apply colimit.hom_ext
  intro n
  rw [cellularReplacementMap_stage_assoc,cellularComparison_stage,
    cellularComparison_stage_assoc]
  exact (cellularStageArrowMap f τ n).w.trans
    (by rw [cellularStageArrowMap_right]; rfl)

@[simp] theorem cellularReplacementMap_id (X : Arrow C)
    [HasColimit (cellularSequence f (Over.mk X.hom))] :
    cellularReplacementMap f (𝟙 X) = 𝟙 _ := by
  apply colimit.hom_ext
  intro n
  rw [cellularReplacementMap_stage,cellularStageArrowMap_id]
  simp

@[simp] theorem cellularReplacementMap_comp {X Y Z : Arrow C} (τ : X ⟶ Y) (σ : Y ⟶ Z)
    [HasColimit (cellularSequence f (Over.mk X.hom))]
    [HasColimit (cellularSequence f (Over.mk Y.hom))]
    [HasColimit (cellularSequence f (Over.mk Z.hom))] :
    cellularReplacementMap f (τ ≫ σ) = cellularReplacementMap f τ ≫ cellularReplacementMap f σ := by
  apply colimit.hom_ext
  intro n
  rw [cellularReplacementMap_stage,cellularReplacementMap_stage_assoc,
    cellularReplacementMap_stage,cellularStageArrowMap_comp]
  exact Category.assoc _ _ _

end KIP126.Topology.SmallObject
