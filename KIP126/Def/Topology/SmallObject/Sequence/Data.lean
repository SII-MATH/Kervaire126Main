module

public import Mathlib.CategoryTheory.SmallObject.Construction
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Comma.Over.Basic

@[expose] public section

namespace KIP126.Topology.SmallObject

open CategoryTheory CategoryTheory.Limits

universe u v w

variable {C : Type u} [Category.{v} C] {I : Type w} {A B : I → C}
  (f : ∀ i, A i ⟶ B i) [HasPushouts C]
  [∀ {X S : C} (π : X ⟶ S), HasColimitsOfShape
    (Discrete (CategoryTheory.SmallObject.FunctorObjIndex f π)) C]
  {S : C} (X : Over S)

/-- The actual finite stages of attaching every specified lifting problem,
starting with a given map to the fixed target. -/
noncomputable def cellularStage : ℕ → Over S
  | 0 => X
  | n+1 => Over.mk (CategoryTheory.SmallObject.πFunctorObj f (cellularStage n).hom)

/-- The actual pushout inclusion at each finite attachment stage. -/
noncomputable def cellularStageMap (n : ℕ) :
    (cellularStage f X n).left ⟶ (cellularStage f X (n+1)).left :=
  CategoryTheory.SmallObject.ιFunctorObj f (cellularStage f X n).hom

/-- The countable sequence of actual simultaneous cell attachments. -/
noncomputable def cellularSequence : ℕ ⥤ C :=
  Functor.ofSequence (cellularStageMap f X)

/-- The canonical compatible projections of every actual attachment
stage to the specified target. -/
noncomputable def cellularTargetCocone : Cocone (cellularSequence f X) where
  pt := S
  ι := NatTrans.ofSequence (fun n => (cellularStage f X n).hom) (by
    intro n
    change (Functor.ofSequence (cellularStageMap f X)).map
      (homOfLE (Nat.le_succ n)) ≫ (cellularStage f X (n+1)).hom =
      (cellularStage f X n).hom ≫ 𝟙 S
    rw [Functor.ofSequence_map_homOfLE_succ,Category.comp_id]
    exact CategoryTheory.SmallObject.ιFunctorObj_πFunctorObj f (cellularStage f X n).hom)

/-- The actual countable cell attachment object. -/
noncomputable abbrev cellularReplacement [HasColimit (cellularSequence f X)] : C :=
  colimit (cellularSequence f X)

/-- The comparison induced from the genuine compatible stage projections. -/
noncomputable def cellularComparison [HasColimit (cellularSequence f X)] :
    cellularReplacement f X ⟶ S :=
  colimit.desc (cellularSequence f X) (cellularTargetCocone f X)

end KIP126.Topology.SmallObject
