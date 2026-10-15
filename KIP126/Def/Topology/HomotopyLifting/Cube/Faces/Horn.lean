module

public import KIP126.Def.Topology.HomotopyLifting.Cube.Faces.Retraction.Proofs
public import KIP126.Def.Topology.HomotopyLifting.Trivialization.Proofs

@[expose] public section

section

namespace KIP126.Topology.HomotopyLifting
open Metric Set
open scoped unitInterval
set_option backward.isDefEq.respectTransparency false

noncomputable def cubeFacesHornRetraction {n : ℕ} (faces : Set (Fin n × Bool)) :
    C(I × (Fin n → I), CylinderHorn (Fin n → I) (cubeFacesBoundary n faces)) :=
  ⟨fun z => ⟨cubeFacesRetractionFunction faces z,cubeFacesRetractionFunction_range faces z⟩,
    (cubeFacesRetractionFunction_continuous faces).subtype_mk _⟩


end KIP126.Topology.HomotopyLifting

end

section

namespace KIP126.Topology.HomotopyLifting
open Metric Set
open scoped unitInterval
set_option backward.isDefEq.respectTransparency false

theorem cubeFacesHornRetraction_restrict {n : ℕ} (faces : Set (Fin n × Bool))
    (z : CylinderHorn (Fin n → I) (cubeFacesBoundary n faces)) :
    cubeFacesHornRetraction faces z.val = z :=
  Subtype.ext (cubeFacesRetractionFunction_restrict faces z.val z.property)

/-- One actual chart extends a lift already given on the bottom and any
selected side faces. This is the local operation used by finite grid gluing. -/
theorem exists_relativeLift_faces_in_trivialization
    {E B F : Type*} [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace F]
    (f : C(E,B)) (T : Bundle.Trivialization F f) {n : ℕ} (faces : Set (Fin n × Bool))
    (g : C(CylinderHorn (Fin n → I) (cubeFacesBoundary n faces),E))
    (H : C(I × (Fin n → I),B)) (hH : ∀ z, H z ∈ T.baseSet)
    (hcomm : ∀ z, f (g z) = H z.val) :
    ∃ L : C(I × (Fin n → I),E), (∀ z, f (L z) = H z) ∧
      (∀ z, L z.val = g z) :=
  exists_relativeLift_of_retraction f T (cubeFacesBoundary n faces)
    (cubeFacesHornRetraction faces) (cubeFacesHornRetraction_restrict faces) g H hH hcomm


end KIP126.Topology.HomotopyLifting

end
