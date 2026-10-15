module

public import KIP126.Def.Topology.HomotopyExtension.HomotopyEquivalence.Proofs

@[expose] public section

namespace KIP126.Topology.HomotopyExtension
open CategoryTheory Set _root_.Topology
open scoped unitInterval
universe u
set_option backward.isDefEq.respectTransparency false

/-- The full cylinder corner of a closed HEP homotopy equivalence is again
an actual homotopy equivalence, with its literal inclusion as forward map. -/
theorem HasHomotopyExtension.exists_cylinderCorner_homotopyEquiv
    {A B : TopCat.{u}} {i : A ⟶ B} (hi : HasHomotopyExtension i)
    (he : IsClosedEmbedding i) (e : ContinuousMap.HomotopyEquiv A B)
    (hei : e.toFun = i.hom) :
    ∃ E : ContinuousMap.HomotopyEquiv (HomotopyExtension.cylinderCorner i) (B × I),
      E.toFun = (cylinderCornerMap i).hom := by
  obtain ⟨r,hr,H,hH⟩ := hi.exists_strong_deformation_retraction he e hei
  let R : C(B × I,HomotopyExtension.cylinderCorner i) := ⟨fun z => ⟨(i (r z.1),z.2),Or.inl ⟨r z.1,rfl⟩⟩,
    ((i.hom.continuous.comp (r.continuous.comp continuous_fst)).prodMk continuous_snd).subtype_mk _⟩
  have hmem (s : I) (z : HomotopyExtension.cylinderCorner i) :
      H (s,z.val.1) ∈ range i ∨ z.val.2 = 0 ∨ z.val.2 = 1 := by
    rcases z.property with ⟨a,ha⟩ | hz
    · left
      refine ⟨a,?_⟩
      rw [← ha,hH]
    · exact Or.inr hz
  let L : (ContinuousMap.id (HomotopyExtension.cylinderCorner i)).Homotopy
      (R.comp (cylinderCornerMap i).hom) := {
    toFun := fun z => ⟨(H (z.1,z.2.val.1),z.2.val.2),hmem z.1 z.2⟩
    continuous_toFun := ((H.continuous.comp
      (continuous_fst.prodMk continuous_snd.subtype_val.fst)).prodMk
      continuous_snd.subtype_val.snd).subtype_mk _
    map_zero_left := fun z => Subtype.ext (Prod.ext (H.apply_zero z.val.1) rfl)
    map_one_left := fun z => Subtype.ext (Prod.ext (H.apply_one z.val.1) rfl) }
  let K : (ContinuousMap.id (B × I)).Homotopy
      ((cylinderCornerMap i).hom.comp R) := {
    toFun := fun z => (H (z.1,z.2.1),z.2.2)
    continuous_toFun := (H.continuous.comp (continuous_fst.prodMk continuous_snd.fst)).prodMk
      continuous_snd.snd
    map_zero_left := fun z => Prod.ext (H.apply_zero z.1) rfl
    map_one_left := fun z => Prod.ext (H.apply_one z.1) rfl }
  exact ⟨⟨(cylinderCornerMap i).hom,R,⟨L.symm⟩,⟨K.symm⟩⟩,rfl⟩

end KIP126.Topology.HomotopyExtension
