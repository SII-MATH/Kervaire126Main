module

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.Pushout.Equivalence.General.Proofs

@[expose] section

namespace KIP126.Topology

open CategoryTheory CategoryTheory.Limits

universe u

set_option backward.isDefEq.respectTransparency false

/-- Actual cofibration attachments are invariant under replacement of
the old space by an actual homotopy equivalence and an attaching square
commuting through a specified continuous homotopy. Both directions
retain the given old-space maps exactly. -/
theorem exists_homotopyEquiv_of_cofibration_pushout_homotopy_square
    {S A B P A' P' : TopCat.{u}} {a : S ⟶ A} {a' : S ⟶ A'} {i : S ⟶ B}
    {u : A ⟶ P} {v : B ⟶ P} {u' : A' ⟶ P'} {v' : B ⟶ P'}
    (hp : IsPushout a i u v) (hp' : IsPushout a' i u' v')
    (hi : HomotopyExtension.HasHomotopyExtension i)
    (e : ContinuousMap.HomotopyEquiv A A')
    (H : (e.toFun.comp a.hom).Homotopy a'.hom) :
    ∃ E : ContinuousMap.HomotopyEquiv P P',
      (∀ x : A, E (u x) = u' (e x)) ∧
      ∀ x : A', E.invFun (u' x) = u (e.invFun x) := by
  let q : A ⟶ A' := TopCat.ofHom e.toFun
  let a2 := a ≫ q
  let P2 := pushout a2 i
  let u2 : A' ⟶ P2 := pushout.inl a2 i
  let v2 : B ⟶ P2 := pushout.inr a2 i
  have hp2 : IsPushout a2 i u2 v2 := IsPushout.of_hasPushout a2 i
  have hw : a ≫ (q ≫ u2) = i ≫ v2 := by
    rw [← Category.assoc]
    exact hp2.w
  let F : P ⟶ P2 := hp.desc (q ≫ u2) v2 hw
  obtain ⟨E0,hE0,hE0inv⟩ := exists_homotopyEquiv_of_cofibration_pushout hp hp2 hi e rfl
    F (hp.inl_desc _ _ _) (hp.inr_desc _ _ _)
  obtain ⟨E1,hE1,hE1inv⟩ := exists_homotopyEquiv_of_homotopic_attaching_maps hp2 hp' hi H
  refine ⟨E0.trans E1,?_,?_⟩
  · intro x
    change E1.toFun (E0.toFun (u x)) = u' (e x)
    rw [hE0]
    change E1 (F (u x)) = _
    rw [show F (u x) = u2 (e x) from ConcreteCategory.congr_hom (hp.inl_desc _ _ _) x]
    exact hE1 (e x)
  · intro x
    change E0.invFun (E1.invFun (u' x)) = _
    rw [hE1inv]
    exact hE0inv x

end KIP126.Topology
