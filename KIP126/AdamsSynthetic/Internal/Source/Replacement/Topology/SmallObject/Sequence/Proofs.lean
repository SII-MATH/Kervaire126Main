module

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SmallObject.Sequence.Data
import Mathlib.CategoryTheory.LiftingProperties.Basic

@[expose] section

namespace KIP126.Topology.SmallObject

open CategoryTheory CategoryTheory.Limits

universe u v w

variable {C : Type u} [Category.{v} C] {I : Type w} {A B : I → C}
  (f : ∀ i, A i ⟶ B i) [HasPushouts C]
  [∀ {X S : C} (π : X ⟶ S), HasColimitsOfShape
    (Discrete (CategoryTheory.SmallObject.FunctorObjIndex f π)) C]
  {S : C} (X : Over S)

set_option backward.isDefEq.respectTransparency false

@[reassoc (attr := simp)] theorem cellularStageMap_projection (n : ℕ) :
    cellularStageMap f X n ≫ (cellularStage f X (n+1)).hom =
      (cellularStage f X n).hom :=
  CategoryTheory.SmallObject.ιFunctorObj_πFunctorObj f _

/-- Every actual lifting problem at one stage has its tautological solution
at the next stage, retaining both boundary and target values exactly. -/
theorem cellularStage_extension (n : ℕ) (i : I)
    (t : A i ⟶ (cellularStage f X n).left) (b : B i ⟶ S)
    (h : t ≫ (cellularStage f X n).hom = f i ≫ b) :
    ∃ l : B i ⟶ (cellularStage f X (n+1)).left,
      f i ≫ l = t ≫ cellularStageMap f X n ∧
      l ≫ (cellularStage f X (n+1)).hom = b :=
  CategoryTheory.SmallObject.ιFunctorObj_extension f t b ⟨h⟩

variable [HasColimit (cellularSequence f X)]

@[reassoc (attr := simp)] theorem cellularComparison_stage (n : ℕ) :
    colimit.ι (cellularSequence f X) n ≫ cellularComparison f X =
      (cellularStage f X n).hom :=
  colimit.ι_desc _ _

/-- A finite-stage factorization of an actual boundary lifting problem
gives an exact solution in the countable attachment object. -/
theorem cellularComparison_extension (i : I)
    (t : A i ⟶ cellularReplacement f X) (b : B i ⟶ S)
    (h : t ≫ cellularComparison f X = f i ≫ b)
    (n : ℕ) (g : A i ⟶ (cellularSequence f X).obj n)
    (hg : g ≫ colimit.ι (cellularSequence f X) n = t) :
    ∃ l : B i ⟶ cellularReplacement f X, f i ≫ l = t ∧
      l ≫ cellularComparison f X = b := by
  obtain ⟨l,hl,hπ⟩ := cellularStage_extension f X n i g b (by
    rw [← cellularComparison_stage f X n, ← Category.assoc, hg, h])
  refine ⟨l ≫ colimit.ι (cellularSequence f X) (n+1),?_,?_⟩
  · rw [← Category.assoc,hl,Category.assoc]
    have hn : cellularStageMap f X n ≫ colimit.ι (cellularSequence f X) (n+1) =
        colimit.ι (cellularSequence f X) n := by
      simpa only [cellularSequence,Functor.ofSequence_map_homOfLE_succ] using
        colimit.w (cellularSequence f X) (homOfLE (Nat.le_succ n))
    rw [hn,hg]
  · rw [Category.assoc,cellularComparison_stage,hπ]

end KIP126.Topology.SmallObject
