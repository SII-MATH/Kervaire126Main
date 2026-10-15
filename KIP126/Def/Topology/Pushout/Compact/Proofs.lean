module

public import Mathlib.Topology.Maps.Proper.Basic

@[expose] public section

namespace KIP126.Topology
open _root_.Topology Function Set
universe u v w
variable {A : Type u} {B : Type v} {F : Type w}
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace F]

/-- Pulling a compact-source map back along an arbitrary continuous map
gives a proper map on the literal topological fiber product. -/
theorem compact_pullback_snd_isProperMap [CompactSpace A] [T2Space B]
    (f : A → B) (hf : Continuous f) (g : F → B) (hg : Continuous g) :
    IsProperMap (fun z : {az : A × F // f az.1 = g az.2} => z.val.2) := by
  have hc : IsClosed {az : A × F | f az.1 = g az.2} :=
    isClosed_eq (hf.comp continuous_fst) (hg.comp continuous_snd)
  exact (isProperMap_snd_of_compactSpace (X := A) (Y := F)).comp
    hc.isClosedEmbedding_subtypeVal.isProperMap

end KIP126.Topology
