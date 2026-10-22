module

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Sigma.Attachment.Cubical.Sequence.Model
import Mathlib.CategoryTheory.Functor.OfSequence

@[expose] section

namespace KIP126.Topology.SimplicialRealization
open CategoryTheory HomotopicalAlgebra
open KIP126.Topology.HomotopyLifting
universe u
set_option backward.isDefEq.respectTransparency false

/-- Choose all parts of an actual attachment-model extension together. -/
noncomputable def orderCubeAttachmentExtension
    {X Y : TopCat.{u}} {f : X ⟶ Y}
    (hc : Nonempty (AttachCells.{u} cubeBoundaryInclusion.{u} f))
    (M : OrderRealizationModel X) : OrderRealizationExtension f M :=
  Classical.choice (nonempty_orderRealizationExtension_of_cube_attachCells hc M)

variable (F : ℕ ⥤ TopCat.{u})
  (hc : ∀ n, Nonempty (AttachCells.{u} cubeBoundaryInclusion.{u}
    (F.map (homOfLE (Nat.le_succ n)))))
  (M₀ : OrderRealizationModel (F.obj 0))

/-- Models of the original attachment stages, recursively extending the
specified initial model through the original transition maps. -/
noncomputable def cubicalOrderStageModel : ∀ n, OrderRealizationModel (F.obj n)
  | 0 => M₀
  | n+1 => (orderCubeAttachmentExtension (hc n) (cubicalOrderStageModel n)).model

/-- The actual order embedding chosen at each attachment stage. -/
noncomputable def cubicalOrderStageEmbedding (n : ℕ) :
    (cubicalOrderStageModel F hc M₀ n).order ↪o
      (cubicalOrderStageModel F hc M₀ (n+1)).order :=
  (orderCubeAttachmentExtension (hc n) (cubicalOrderStageModel F hc M₀ n)).embedding

/-- The actual sequence of partial orders with embedding transitions. -/
noncomputable def cubicalOrderSequence : ℕ ⥤ PartOrd.{u} :=
  Functor.ofSequence (fun n => PartOrd.ofHom (cubicalOrderStageEmbedding F hc M₀ n).toOrderHom)

/-- The realized sequence of the chosen order models. -/
noncomputable def cubicalOrderRealizationSequence : ℕ ⥤ TopCat.{u} :=
  cubicalOrderSequence F hc M₀ ⋙ PartOrd.nerveFunctor ⋙ SSet.toTop

/-- All forward model comparisons are a strictly natural map to the
original sequence of spaces. -/
noncomputable def cubicalOrderSequenceComparison :
    cubicalOrderRealizationSequence F hc M₀ ⟶ F :=
  NatTrans.ofSequence
    (fun n => TopCat.ofHom (cubicalOrderStageModel F hc M₀ n).equivalence.toFun) (by
      intro n
      apply TopCat.hom_ext
      apply ContinuousMap.ext
      intro x
      change (cubicalOrderStageModel F hc M₀ (n+1)).equivalence
        ((PartOrd.nerveFunctor ⋙ SSet.toTop).map
          ((cubicalOrderSequence F hc M₀).map (homOfLE (Nat.le_succ n))) x) = _
      have hs : (cubicalOrderSequence F hc M₀).map (homOfLE (Nat.le_succ n)) =
          PartOrd.ofHom (cubicalOrderStageEmbedding F hc M₀ n).toOrderHom :=
        Functor.ofSequence_map_homOfLE_succ _ n
      rw [hs]
      exact (orderCubeAttachmentExtension (hc n)
        (cubicalOrderStageModel F hc M₀ n)).forward x)

/-- All reverse comparisons are strictly natural as well; the same
choice of an extension supplies both directions. -/
noncomputable def cubicalOrderSequenceInverseComparison :
    F ⟶ cubicalOrderRealizationSequence F hc M₀ :=
  NatTrans.ofSequence
    (fun n => TopCat.ofHom (cubicalOrderStageModel F hc M₀ n).equivalence.invFun) (by
      intro n
      apply TopCat.hom_ext
      apply ContinuousMap.ext
      intro x
      change _ = (PartOrd.nerveFunctor ⋙ SSet.toTop).map
        ((cubicalOrderSequence F hc M₀).map (homOfLE (Nat.le_succ n)))
          ((cubicalOrderStageModel F hc M₀ n).equivalence.invFun x)
      have hs : (cubicalOrderSequence F hc M₀).map (homOfLE (Nat.le_succ n)) =
          PartOrd.ofHom (cubicalOrderStageEmbedding F hc M₀ n).toOrderHom :=
        Functor.ofSequence_map_homOfLE_succ _ n
      rw [hs]
      exact (orderCubeAttachmentExtension (hc n)
        (cubicalOrderStageModel F hc M₀ n)).backward x)

end KIP126.Topology.SimplicialRealization
