module

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.HomotopyExtension.CylinderCorner.HomotopyEquivalence.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.HomotopyExtension.CylinderCorner.Gluing.Proofs

@[expose] section

namespace KIP126.Topology.HomotopyExtension
open CategoryTheory Set _root_.Topology
open scoped unitInterval
universe u
set_option backward.isDefEq.respectTransparency false

/-- An actual homotopy on a closed HEP homotopy-equivalent subspace extends
between two specified ambient endpoint maps, preserving every original
homotopy value exactly. -/
theorem HasHomotopyExtension.exists_homotopy_extension_of_homotopyEquiv
    {A B : TopCat.{u}} {i : A ⟶ B} (hi : HasHomotopyExtension i)
    (he : IsClosedEmbedding i) (e : ContinuousMap.HomotopyEquiv A B)
    (hei : e.toFun = i.hom) {Y : TopCat.{u}} (f g : C(B,Y))
    (H : (f.comp i.hom).Homotopy (g.comp i.hom)) :
    ∃ K : f.Homotopy g, ∀ (t : I) (a : A), K (t,i a) = H (t,a) := by
  obtain ⟨E,hE⟩ := hi.exists_cylinderCorner_homotopyEquiv he e hei
  obtain ⟨r,hr,_,_⟩ := (hi.cylinderCorner he).exists_strong_deformation_retraction
    (cylinderCornerMap_isClosedEmbedding i he) E hE
  obtain ⟨d,hd,hd0,hd1⟩ := exists_cylinderCorner_desc i he
    (H.toContinuousMap.comp ContinuousMap.prodSwap) f g
    (fun a => H.apply_zero a) (fun a => H.apply_one a)
  have hri (a : HomotopyExtension.cylinderCorner i) : r a.val = a :=
    ContinuousMap.congr_fun hr a
  refine ⟨{
    toContinuousMap := (d.comp r).comp ContinuousMap.prodSwap
    map_zero_left := ?_
    map_one_left := ?_ },?_⟩
  · intro b
    change d (r (b,0)) = f b
    rw [hri ⟨(b,0),Or.inr (Or.inl rfl)⟩]
    exact hd0 b
  · intro b
    change d (r (b,1)) = g b
    rw [hri ⟨(b,1),Or.inr (Or.inr rfl)⟩]
    exact hd1 b
  · intro t a
    change d (r (i a,t)) = H (t,a)
    rw [hri ⟨(i a,t),Or.inl ⟨a,rfl⟩⟩]
    exact hd a t

end KIP126.Topology.HomotopyExtension
