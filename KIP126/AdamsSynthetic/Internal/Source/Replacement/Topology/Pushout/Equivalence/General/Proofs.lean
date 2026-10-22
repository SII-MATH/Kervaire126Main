module

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.Pushout.Equivalence.HomotopicAttachment.Proofs

@[expose] section

namespace KIP126.Topology

open CategoryTheory CategoryTheory.Limits
open scoped unitInterval

universe u

set_option backward.isDefEq.respectTransparency false

/-- A strict pushout comparison induced by a self-map homotopic to the
identity is an actual homotopy equivalence. Its inverse fixes the old
space strictly. -/
theorem exists_homotopyEquiv_of_cofibration_pushout_homotopic_identity
    {S A B P P' : TopCat.{u}} {a a' : S ⟶ A} {i : S ⟶ B}
    {u : A ⟶ P} {v : B ⟶ P} {u' : A ⟶ P'} {v' : B ⟶ P'}
    (hp : IsPushout a i u v) (hp' : IsPushout a' i u' v')
    (hi : HomotopyExtension.HasHomotopyExtension i)
    (e : A ⟶ A) (he : a ≫ e = a')
    (H : e.hom.Homotopy (ContinuousMap.id A))
    (F : P ⟶ P') (hFu : u ≫ F = e ≫ u') (hFv : v ≫ F = v') :
    ∃ E : ContinuousMap.HomotopyEquiv P P', E.toFun = F.hom ∧
      ∀ x : A, E.invFun (u' x) = u x := by
  have ha : e.hom.comp a.hom = a'.hom := congrArg TopCat.Hom.hom he
  let Ha := (H.compContinuousMap a.hom).cast ha rfl
  let L := (ContinuousMap.Homotopy.refl u.hom).comp Ha.symm
  let L' := (ContinuousMap.Homotopy.refl u'.hom).comp Ha
  have hL : u.hom.comp a.hom = v.hom.comp i.hom := congrArg TopCat.Hom.hom hp.w
  have hL' : u'.hom.comp a'.hom = v'.hom.comp i.hom := congrArg TopCat.Hom.hom hp'.w
  obtain ⟨D,hD,E',hE'⟩ := exists_map_of_cofibration_attachment_with_homotopy hp hi
    u' v' (L'.cast hL' rfl)
  obtain ⟨G,hG,E,hE⟩ := exists_map_of_cofibration_attachment_with_homotopy hp' hi
    u v (L.cast hL rfl)
  have hE'' : ∀ (t : I) (s : S), E' (t,i s) = u' (Ha.symm.symm (t,s)) := by
    intro t s
    rw [ContinuousMap.Homotopy.symm_symm]
    exact hE' t s
  have hleft := cofibration_attachment_composite_homotopic hp hi Ha.symm D G hD hG E E' hE hE''
  have hright := cofibration_attachment_composite_homotopic hp' hi Ha G D hG hD E' E hE' hE
  have hA₀ : u'.hom.comp e.hom = F.hom.comp u.hom :=
    (congrArg TopCat.Hom.hom hFu).symm
  have hA₁ : u'.hom.comp (ContinuousMap.id A) = D.hom.comp u.hom :=
    (congrArg TopCat.Hom.hom hD).symm
  have hB₀ : v'.hom = F.hom.comp v.hom := (congrArg TopCat.Hom.hom hFv).symm
  obtain ⟨K,_,_⟩ := exists_homotopy_of_topological_pushout hp F.hom D.hom
    (((ContinuousMap.Homotopy.refl u'.hom).comp H).cast hA₀ hA₁)
    (E'.cast hB₀ rfl) (fun t s => (hE' t s).symm)
  have hl : (G.hom.comp F.hom).Homotopic (ContinuousMap.id P) :=
    ((ContinuousMap.Homotopic.refl G.hom).comp ⟨K⟩).trans hleft
  have hr : (F.hom.comp G.hom).Homotopic (ContinuousMap.id P') :=
    ((show F.hom.Homotopic D.hom from ⟨K⟩).comp (ContinuousMap.Homotopic.refl G.hom)).trans hright
  exact ⟨⟨F.hom,G.hom,hl,hr⟩,rfl,fun x => ConcreteCategory.congr_hom hG x⟩

/-- Replacing the old space by an arbitrary actual homotopy equivalent
space preserves the actual pushout along a cofibration. The forward
map is the specified strict pushout comparison. The inverse restricts
exactly to the specified old-space homotopy inverse. -/
theorem exists_homotopyEquiv_of_cofibration_pushout
    {S A B P A' P' : TopCat.{u}} {a : S ⟶ A} {a' : S ⟶ A'} {i : S ⟶ B}
    {u : A ⟶ P} {v : B ⟶ P} {u' : A' ⟶ P'} {v' : B ⟶ P'}
    (hp : IsPushout a i u v) (hp' : IsPushout a' i u' v')
    (hi : HomotopyExtension.HasHomotopyExtension i)
    (e : ContinuousMap.HomotopyEquiv A A')
    (he : a ≫ TopCat.ofHom e.toFun = a')
    (F : P ⟶ P') (hFu : u ≫ F = TopCat.ofHom e.toFun ≫ u')
    (hFv : v ≫ F = v') :
    ∃ E : ContinuousMap.HomotopyEquiv P P', E.toFun = F.hom ∧
      ∀ x : A', E.invFun (u' x) = u (e.invFun x) := by
  let q : A ⟶ A' := TopCat.ofHom e.toFun
  let r : A' ⟶ A := TopCat.ofHom e.invFun
  let a2 := a' ≫ r
  let a3 := a2 ≫ q
  let P2 := pushout a2 i
  let P3 := pushout a3 i
  let u2 : A ⟶ P2 := pushout.inl a2 i
  let v2 : B ⟶ P2 := pushout.inr a2 i
  let u3 : A' ⟶ P3 := pushout.inl a3 i
  let v3 : B ⟶ P3 := pushout.inr a3 i
  have hp2 : IsPushout a2 i u2 v2 := IsPushout.of_hasPushout a2 i
  have hp3 : IsPushout a3 i u3 v3 := IsPushout.of_hasPushout a3 i
  have hwG : a' ≫ (r ≫ u2) = i ≫ v2 := by
    rw [← Category.assoc]
    exact hp2.w
  let G : P' ⟶ P2 := hp'.desc (r ≫ u2) v2 hwG
  have hGu : u' ≫ G = r ≫ u2 := hp'.inl_desc _ _ _
  have hGv : v' ≫ G = v2 := hp'.inr_desc _ _ _
  have hwJ : a2 ≫ (q ≫ u3) = i ≫ v3 := by
    rw [← Category.assoc]
    exact hp3.w
  let J : P2 ⟶ P3 := hp2.desc (q ≫ u3) v3 hwJ
  have hJu : u2 ≫ J = q ≫ u3 := hp2.inl_desc _ _ _
  have hJv : v2 ≫ J = v3 := hp2.inr_desc _ _ _
  obtain ⟨H0⟩ := e.left_inv
  obtain ⟨H1⟩ := e.right_inv
  have he0 : a ≫ (q ≫ r) = a2 := by rw [← Category.assoc,he]
  have hFu0 : u ≫ (F ≫ G) = (q ≫ r) ≫ u2 := by
    rw [← Category.assoc,hFu,Category.assoc,hGu,← Category.assoc]
  have hFv0 : v ≫ (F ≫ G) = v2 := by rw [← Category.assoc,hFv,hGv]
  obtain ⟨E0,hE0,hE0inv⟩ := exists_homotopyEquiv_of_cofibration_pushout_homotopic_identity
    hp hp2 hi (q ≫ r) he0 H0 (F ≫ G) hFu0 hFv0
  have he1 : a' ≫ (r ≫ q) = a3 := (Category.assoc a' r q).symm
  have hFu1 : u' ≫ (G ≫ J) = (r ≫ q) ≫ u3 := by
    rw [← Category.assoc,hGu,Category.assoc,hJu,← Category.assoc]
  have hFv1 : v' ≫ (G ≫ J) = v3 := by rw [← Category.assoc,hGv,hJv]
  obtain ⟨E1,hE1,_⟩ := exists_homotopyEquiv_of_cofibration_pushout_homotopic_identity
    hp' hp3 hi (r ≫ q) he1 H1 (G ≫ J) hFu1 hFv1
  let R : C(P',P) := E0.invFun.comp G.hom
  let Q : C(P2,P') := E1.invFun.comp J.hom
  have hleft : (R.comp F.hom).Homotopic (ContinuousMap.id P) := by
    have h := E0.left_inv
    rw [hE0] at h
    exact h
  have hQG : (Q.comp G.hom).Homotopic (ContinuousMap.id P') := by
    have h := E1.left_inv
    rw [hE1] at h
    exact h
  have hGR : (G.hom.comp (F.hom.comp R)).Homotopic G.hom := by
    have h := E0.right_inv
    rw [hE0] at h
    exact h.comp (ContinuousMap.Homotopic.refl G.hom)
  have hright : (F.hom.comp R).Homotopic (ContinuousMap.id P') :=
    (hQG.comp (ContinuousMap.Homotopic.refl (F.hom.comp R))).symm.trans
      (((ContinuousMap.Homotopic.refl Q).comp hGR).trans hQG)
  refine ⟨⟨F.hom,R,hleft,hright⟩,rfl,?_⟩
  intro x
  change E0.invFun (G (u' x)) = u (e.invFun x)
  rw [show G (u' x) = u2 (r x) from ConcreteCategory.congr_hom hGu x]
  exact hE0inv (r x)

end KIP126.Topology
