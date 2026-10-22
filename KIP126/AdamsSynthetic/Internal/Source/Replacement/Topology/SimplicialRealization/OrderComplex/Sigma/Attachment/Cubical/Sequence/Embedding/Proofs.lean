module

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Sigma.Attachment.Cubical.Sequence.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.Relative.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.MappingCylinder.Proofs

@[expose] section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory HomotopicalAlgebra
open KIP126.Topology.HomotopyLifting

universe u

set_option backward.isDefEq.respectTransparency false

variable (F : ℕ ⥤ TopCat.{u})
  (hc : ∀ n, Nonempty (AttachCells.{u} cubeBoundaryInclusion.{u}
    (F.map (homOfLE (Nat.le_succ n)))))
  (M₀ : OrderRealizationModel (F.obj 0))

/-- Every transition in the actual recursive order model is injective,
including every composite of the specified successor embeddings. -/
theorem cubicalOrderSequence_map_injective {n m : ℕ} (h : n ≤ m) :
    Function.Injective ((cubicalOrderSequence F hc M₀).map (homOfLE h)) := by
  have hs (k : ℕ) :
      Function.Injective ((cubicalOrderSequence F hc M₀).map (homOfLE (Nat.le_succ k))) := by
    rw [cubicalOrderSequence,Functor.ofSequence_map_homOfLE_succ]
    exact (cubicalOrderStageEmbedding F hc M₀ k).injective
  induction m, h using Nat.le_induction with
  | base => simpa using (Function.injective_id : Function.Injective (id :
      (cubicalOrderSequence F hc M₀).obj n → (cubicalOrderSequence F hc M₀).obj n))
  | succ m h ih =>
    have he : homOfLE (by omega : n ≤ m+1) = homOfLE h ≫ homOfLE (Nat.le_succ m) := rfl
    rw [he,Functor.map_comp]
    exact (hs m).comp ih

/-- Every realized transition of the original recursive order model is
an actual closed embedding, in particular every successor inclusion. -/
theorem cubicalOrderRealizationSequence_map_isClosedEmbedding {n m : ℕ} (h : n ≤ m) :
    _root_.Topology.IsClosedEmbedding
      ((cubicalOrderRealizationSequence F hc M₀).map (homOfLE h)) := by
  let a := (cubicalOrderSequence F hc M₀).map (homOfLE h)
  letI : Mono (PartOrd.nerveFunctor.map a) :=
    nerveMap_mono_of_injective_orderHom a.hom (cubicalOrderSequence_map_injective F hc M₀ h)
  exact realization_mono_isClosedEmbedding (PartOrd.nerveFunctor.map a)

/-- The same actual realized transitions have full homotopy extension;
no extension property is added to the original attachment-model inputs. -/
theorem cubicalOrderRealizationSequence_map_hasHomotopyExtension {n m : ℕ} (h : n ≤ m) :
    HomotopyExtension.HasHomotopyExtension
      ((cubicalOrderRealizationSequence F hc M₀).map (homOfLE h)) := by
  let a := (cubicalOrderSequence F hc M₀).map (homOfLE h)
  letI : Mono (PartOrd.nerveFunctor.map a) :=
    nerveMap_mono_of_injective_orderHom a.hom (cubicalOrderSequence_map_injective F hc M₀ h)
  exact realization_mono_hasHomotopyExtension (PartOrd.nerveFunctor.map a)

end KIP126.Topology.SimplicialRealization
