module

public import KIP126.Def.Topology.HomotopyExtension.CylinderCorner.Data
public import KIP126.Def.Topology.HomotopyExtension.NDR.Proofs
public import KIP126.Def.Topology.HomotopyExtension.NDR.Product.Proofs
public import KIP126.Def.Topology.HomotopyExtension.NDR.Retraction.Proofs

@[expose] public section

namespace KIP126.Topology.HomotopyExtension

open CategoryTheory Set _root_.Topology
open scoped unitInterval

universe u
set_option backward.isDefEq.respectTransparency false

private theorem ndr_of_extension {A B : TopCat.{u}} {i : A ⟶ B}
    (hi : HasHomotopyExtension i) (he : IsClosedEmbedding i) :
    ∃ u : C(B,I), ∃ h : C(B × I,B), IsNDRData (range i) u h := by
  obtain ⟨u,h,hu,hz,h0,hfix,h1⟩ := hi.exists_ndr he
  refine ⟨u,h,?_,h0,?_,h1⟩
  · intro b
    exact ⟨hz b,by rintro ⟨a,rfl⟩; exact hu a⟩
  · rintro b ⟨a,rfl⟩ t
    exact hfix a t

private theorem interval_ndr :
    ∃ u : C(I,I), ∃ h : C(I × I,I), IsNDRData {t : I | t = 0 ∨ t = 1} u h := by
  let E := TopCat.of {t : I // t = 0 ∨ t = 1}
  let j : E ⟶ TopCat.of I := TopCat.ofHom ⟨Subtype.val,continuous_subtype_val⟩
  have hclosed : IsClosed {t : I | t = 0 ∨ t = 1} :=
    (isClosed_eq continuous_id continuous_const).union (isClosed_eq continuous_id continuous_const)
  have hj : IsClosedEmbedding j := hclosed.isClosedEmbedding_subtypeVal
  obtain ⟨r,h0,hl,hr,himage⟩ := exists_interval_boundary_retraction
  have hH : HasHomotopyExtension j := hasHomotopyExtension_of_cylinder_retraction j hj r h0
    (by
      intro a t
      change r ((a : I),t) = ((a : I),t)
      rcases a.property with ha | ha
      · rw [ha]; exact hl t
      · rw [ha]; exact hr t)
    (by
      intro q
      rcases himage q with hz | hl | hr
      · exact Or.inl hz
      · exact Or.inr ⟨⟨(r q).1,Or.inl hl⟩,rfl⟩
      · exact Or.inr ⟨⟨(r q).1,Or.inr hr⟩,rfl⟩)
  obtain ⟨u,h,hn⟩ := ndr_of_extension hH hj
  refine ⟨u,h,?_⟩
  have heq : range j = {t : I | t = 0 ∨ t = 1} := by
    change range (Subtype.val : {t : I // t = 0 ∨ t = 1} → I) = _
    exact Subtype.range_val
  rwa [heq] at hn

/-- The actual cylinder corner of a closed embedding is a closed embedding. -/
theorem cylinderCornerMap_isClosedEmbedding {A B : TopCat.{u}} (i : A ⟶ B)
    (hi : IsClosedEmbedding i) : IsClosedEmbedding (cylinderCornerMap i) := by
  apply IsClosed.isClosedEmbedding_subtypeVal
  exact (hi.isClosed_range.preimage continuous_fst).union
    ((isClosed_eq continuous_snd continuous_const).union (isClosed_eq continuous_snd continuous_const))

/-- Closed homotopy extension is preserved by the actual full cylinder
corner, retaining both endpoints and the entire original image cylinder. -/
theorem HasHomotopyExtension.cylinderCorner {A B : TopCat.{u}} {i : A ⟶ B}
    (hi : HasHomotopyExtension i) (he : IsClosedEmbedding i) :
    HasHomotopyExtension (cylinderCornerMap i) := by
  obtain ⟨u,h,hN⟩ := ndr_of_extension hi he
  obtain ⟨v,k,kN⟩ := interval_ndr
  obtain ⟨w,H,hW⟩ := hN.exists_product kN
  apply IsNDRData.hasHomotopyExtension (cylinderCornerMap i) (cylinderCornerMap_isClosedEmbedding i he)
    (u := w) (h := H)
  have hrange : range (cylinderCornerMap i) =
      {q : B × I | q.1 ∈ range i ∨ q.2 = 0 ∨ q.2 = 1} := by
    change range (Subtype.val : {q : B × I // q.1 ∈ range i ∨ q.2 = 0 ∨ q.2 = 1} → B × I) = _
    exact Subtype.range_val
  rw [hrange]
  exact hW

end KIP126.Topology.HomotopyExtension
