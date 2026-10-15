module

public import KIP126.Def.Topology.SmallObject.Sequence.Proofs

@[expose] public section

namespace KIP126.Topology.SmallObject

open CategoryTheory CategoryTheory.Limits

universe u v w

variable {C : Type u} [Category.{v} C] {I : Type w} {A B : I → C}
  (f : ∀ i, A i ⟶ B i) [HasPushouts C]
  [∀ {X S : C} (π : X ⟶ S), HasColimitsOfShape
    (Discrete (CategoryTheory.SmallObject.FunctorObjIndex f π)) C]

set_option backward.isDefEq.respectTransparency false

/-- Every actual square induces actual maps of all simultaneous
attachment stages by sending each lifting problem to its composite. -/
noncomputable def cellularStageArrowMap {X Y : Arrow C} (τ : X ⟶ Y) :
    ∀ n, Arrow.mk (cellularStage f (Over.mk X.hom) n).hom ⟶
      Arrow.mk (cellularStage f (Over.mk Y.hom) n).hom
  | 0 => τ
  | n+1 => (CategoryTheory.SmallObject.functor f).map (cellularStageArrowMap τ n)

/-- The induced strict natural transformation of the actual stage
sequences, including all transition maps. -/
noncomputable def cellularSequenceMap {X Y : Arrow C} (τ : X ⟶ Y) :
    cellularSequence f (Over.mk X.hom) ⟶ cellularSequence f (Over.mk Y.hom) :=
  NatTrans.ofSequence (fun n => (cellularStageArrowMap f τ n).left) (by
    intro n
    dsimp only [cellularSequence]
    simp only [Functor.ofSequence_map_homOfLE_succ]
    exact CategoryTheory.SmallObject.ιFunctorObj_naturality f (cellularStageArrowMap f τ n))

/-- The actual map of countable attachment objects induced by a square. -/
noncomputable def cellularReplacementMap {X Y : Arrow C} (τ : X ⟶ Y)
    [HasColimit (cellularSequence f (Over.mk X.hom))]
    [HasColimit (cellularSequence f (Over.mk Y.hom))] :
    cellularReplacement f (Over.mk X.hom) ⟶ cellularReplacement f (Over.mk Y.hom) :=
  colimMap (cellularSequenceMap f τ)

end KIP126.Topology.SmallObject
