module

public import Mathlib.Topology.Maps.Proper.Basic

@[expose] public section

namespace KIP126.Topology
open _root_.Topology Function Set
universe u v w
variable {A : Type u} {B : Type v} {F : Type w}
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace F]

/-- A quotient from a compact space to a Hausdorff space remains a quotient
after taking its product with an arbitrary space, without local compactness of that factor. -/
theorem compact_surjection_prodMap_isQuotientMap [CompactSpace A] [T2Space B]
    (f : A → B) (hf : Continuous f) (hs : Function.Surjective f) :
    IsQuotientMap (Prod.map f (id : F → F)) := by
  have hp := hf.isProperMap.prodMap (isProperMap_id (X := F))
  exact hp.isClosedMap.isQuotientMap hp.continuous (by
    rintro ⟨b,x⟩
    obtain ⟨a,ha⟩ := hs b
    exact ⟨(a,x),Prod.ext ha rfl⟩)

/-- The same product-stability statement, with the arbitrary factor on the left. -/
theorem compact_surjection_prodMap_left_isQuotientMap [CompactSpace A] [T2Space B]
    (f : A → B) (hf : Continuous f) (hs : Function.Surjective f) :
    IsQuotientMap (Prod.map (id : F → F) f) := by
  have hp := (isProperMap_id (X := F)).prodMap hf.isProperMap
  exact hp.isClosedMap.isQuotientMap hp.continuous (by
    rintro ⟨x,b⟩
    obtain ⟨a,ha⟩ := hs b
    exact ⟨(x,a),Prod.ext rfl ha⟩)

/-- Pulling a compact-source map back along an arbitrary continuous map
gives a proper map on the literal topological fiber product. -/
theorem compact_pullback_snd_isProperMap [CompactSpace A] [T2Space B]
    (f : A → B) (hf : Continuous f) (g : F → B) (hg : Continuous g) :
    IsProperMap (fun z : {az : A × F // f az.1 = g az.2} => z.val.2) := by
  have hc : IsClosed {az : A × F | f az.1 = g az.2} :=
    isClosed_eq (hf.comp continuous_fst) (hg.comp continuous_snd)
  exact (isProperMap_snd_of_compactSpace (X := A) (Y := F)).comp
    hc.isClosedEmbedding_subtypeVal.isProperMap

/-- Every pullback of a compact-source continuous surjection to a Hausdorff
space is a genuine quotient map, with the actual subspace fiber product. -/
theorem compact_surjection_pullback_snd_isQuotientMap [CompactSpace A] [T2Space B]
    (f : A → B) (hf : Continuous f) (hs : Function.Surjective f)
    (g : F → B) (hg : Continuous g) :
    IsQuotientMap (fun z : {az : A × F // f az.1 = g az.2} => z.val.2) := by
  have hp := compact_pullback_snd_isProperMap f hf g hg
  exact hp.isClosedMap.isQuotientMap hp.continuous (by
    intro x
    obtain ⟨a,ha⟩ := hs (g x)
    exact ⟨⟨(a,x),ha⟩,rfl⟩)


end KIP126.Topology
