module

public import KIP126.Def.Topology.Pushout.Equivalence.Proofs
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic

@[expose] public section

namespace KIP126.Topology

open CategoryTheory CategoryTheory.Limits
open scoped unitInterval

universe u

set_option backward.isDefEq.respectTransparency false

/-- A homotopy on the attached piece whose boundary traverses one
specified homotopy and its reverse can be straightened and glued to the
constant old-space homotopy. The contraction is performed in the actual
compact-open path space using the cofibration's homotopy extension. -/
theorem homotopic_of_cofibration_pushout_canceling_boundary
    {S A B P Y : TopCat.{u}} {a : S ⟶ A} {i : S ⟶ B}
    {u : A ⟶ P} {v : B ⟶ P}
    (hp : IsPushout a i u v) (hi : HomotopyExtension.HasHomotopyExtension i)
    (F G : C(P,Y)) (hFG : F.comp u.hom = G.comp u.hom)
    {b : C(S,Y)} (L : ((F.comp u.hom).comp a.hom).Homotopy b)
    (K : (F.comp v.hom).Homotopy (G.comp v.hom))
    (hK : ∀ (t : I) (x : S), K (t,i x) = (L.trans L.symm) (t,x)) :
    F.Homotopic G := by
  let γ (x : S) : Path (F (u (a x))) (b x) :=
    { toFun := fun t => L (t,x)
      continuous_toFun := L.continuous.comp (continuous_id.prodMk continuous_const)
      source' := L.apply_zero x
      target' := L.apply_one x }
  let p : C(S × I,C(I,Y)) := (⟨fun z : (S × I) × I =>
    (Path.Homotopy.reflTransSymm (γ z.1.1)).symm (z.1.2,z.2),by
      change Continuous (fun z : (S × I) × I =>
        L (⟨Path.Homotopy.reflTransSymmAux (unitInterval.symm z.1.2,z.2),_⟩,z.1.1))
      fun_prop⟩ : C((S × I) × I,Y)).curry
  have hp₀ (x : S) (t : I) : p (x,0) t = K (t,i x) := by
    change (Path.Homotopy.reflTransSymm (γ x)).symm (0,t) = _
    exact ((Path.Homotopy.reflTransSymm (γ x)).symm.apply_zero t).trans (hK t x).symm
  have hp₁ (x : S) (t : I) : p (x,1) t = F (u (a x)) := by
    exact (Path.Homotopy.reflTransSymm (γ x)).symm.apply_one t
  have hp0 (x : S) (s : I) : p (x,s) 0 = F (u (a x)) := by
    exact ((Path.Homotopy.reflTransSymm (γ x)).symm.eval s).source
  have hp1 (x : S) (s : I) : p (x,s) 1 = F (u (a x)) := by
    exact ((Path.Homotopy.reflTransSymm (γ x)).symm.eval s).target
  let k : C(B,C(I,Y)) := (K.toContinuousMap.comp ContinuousMap.prodSwap).curry
  obtain ⟨E,hE₀,hEi⟩ := hi (TopCat.of C(I,Y)) k p (by
    intro x
    ext t
    exact hp₀ x t)
  let e0 : C(B,Y) := ⟨fun x => E (x,1) 0,by fun_prop⟩
  let e1 : C(B,Y) := ⟨fun x => E (x,1) 1,by fun_prop⟩
  let M0 : (F.comp v.hom).Homotopy e0 := {
    toFun := fun z => E (z.2,z.1) 0
    continuous_toFun := by fun_prop
    map_zero_left := fun x => (ContinuousMap.congr_fun (hE₀ x) 0).trans (K.apply_zero x)
    map_one_left := fun _ => rfl }
  let M1 : (G.comp v.hom).Homotopy e1 := {
    toFun := fun z => E (z.2,z.1) 1
    continuous_toFun := by fun_prop
    map_zero_left := fun x => (ContinuousMap.congr_fun (hE₀ x) 1).trans (K.apply_one x)
    map_one_left := fun _ => rfl }
  let M : e0.Homotopy e1 := {
    toFun := fun z => E (z.2,1) z.1
    continuous_toFun := by fun_prop
    map_zero_left := fun _ => rfl
    map_one_left := fun _ => rfl }
  have hM0 (t : I) (x : S) : M0 (t,i x) = F (u (a x)) :=
    (ContinuousMap.congr_fun (hEi x t) 0).trans (hp0 x t)
  have hM1 (t : I) (x : S) : M1 (t,i x) = F (u (a x)) :=
    (ContinuousMap.congr_fun (hEi x t) 1).trans (hp1 x t)
  have hM (t : I) (x : S) : M (t,i x) = F (u (a x)) :=
    (ContinuousMap.congr_fun (hEi x 1) t).trans (hp₁ x t)
  let N := (M0.trans M).trans M1.symm
  have hN (t : I) (x : S) : N (t,i x) = F (u (a x)) := by
    dsimp only [N]
    rw [ContinuousMap.Homotopy.trans_apply]
    split_ifs
    · rw [ContinuousMap.Homotopy.trans_apply]
      split_ifs
      · exact hM0 _ x
      · exact hM _ x
    · exact hM1 _ x
  obtain ⟨T,_,_⟩ := exists_homotopy_of_topological_pushout hp F G
    ((ContinuousMap.Homotopy.refl (F.comp u.hom)).cast rfl hFG) N
    (fun t x => (hN t x).symm)
  exact ⟨T⟩

/-- The two attachment extensions associated to opposite boundary
homotopies compose to the identity up to a genuine continuous homotopy. -/
theorem cofibration_attachment_composite_homotopic
    {S A B P P' : TopCat.{u}} {a a' : S ⟶ A} {i : S ⟶ B}
    {u : A ⟶ P} {v : B ⟶ P} {u' : A ⟶ P'} {v' : B ⟶ P'}
    (hp : IsPushout a i u v) (hi : HomotopyExtension.HasHomotopyExtension i)
    (H : a.hom.Homotopy a'.hom)
    (F : P ⟶ P') (G : P' ⟶ P) (hF : u ≫ F = u') (hG : u' ≫ G = u)
    (E : v.hom.Homotopy (v' ≫ G).hom)
    (E' : v'.hom.Homotopy (v ≫ F).hom)
    (hE : ∀ (t : I) (s : S), E (t,i s) = u (H (t,s)))
    (hE' : ∀ (t : I) (s : S), E' (t,i s) = u' (H.symm (t,s))) :
    (F ≫ G).hom.Homotopic (ContinuousMap.id P) := by
  have hFG : (ContinuousMap.id P).comp u.hom = (F ≫ G).hom.comp u.hom := by
    ext x
    exact (ConcreteCategory.congr_hom hG x).symm.trans
      (congrArg G (ConcreteCategory.congr_hom hF x).symm)
  let L := (ContinuousMap.Homotopy.refl u.hom).comp H
  let K := E.trans ((ContinuousMap.Homotopy.refl G.hom).comp E')
  apply (homotopic_of_cofibration_pushout_canceling_boundary hp hi
    (ContinuousMap.id P) (F ≫ G).hom hFG L K ?_).symm
  intro t s
  dsimp only [K]
  simp only [ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · exact hE _ s
  · change G (E' (_,i s)) = u (H.symm (_,s))
    rw [hE']
    exact ConcreteCategory.congr_hom hG _

/-- Changing an attaching map by a specified actual homotopy preserves
the homotopy type of the actual pushout along a cofibration. Both
directions retain the old space strictly. -/
theorem exists_homotopyEquiv_of_homotopic_attaching_maps
    {S A B P P' : TopCat.{u}} {a a' : S ⟶ A} {i : S ⟶ B}
    {u : A ⟶ P} {v : B ⟶ P} {u' : A ⟶ P'} {v' : B ⟶ P'}
    (hp : IsPushout a i u v) (hp' : IsPushout a' i u' v')
    (hi : HomotopyExtension.HasHomotopyExtension i)
    (H : a.hom.Homotopy a'.hom) :
    ∃ E : ContinuousMap.HomotopyEquiv P P',
      (∀ x : A, E (u x) = u' x) ∧
      (∀ x : A, E.invFun (u' x) = u x) := by
  let L := (ContinuousMap.Homotopy.refl u.hom).comp H
  let L' := (ContinuousMap.Homotopy.refl u'.hom).comp H.symm
  have hL : u.hom.comp a.hom = v.hom.comp i.hom :=
    congrArg TopCat.Hom.hom hp.w
  have hL' : u'.hom.comp a'.hom = v'.hom.comp i.hom :=
    congrArg TopCat.Hom.hom hp'.w
  obtain ⟨F,hF,E',hE'⟩ := exists_map_of_cofibration_attachment_with_homotopy hp hi
    u' v' (L'.cast hL' rfl)
  obtain ⟨G,hG,E,hE⟩ := exists_map_of_cofibration_attachment_with_homotopy hp' hi
    u v (L.cast hL rfl)
  have hleft := cofibration_attachment_composite_homotopic hp hi H F G hF hG E E' hE hE'
  have hright := cofibration_attachment_composite_homotopic hp' hi H.symm G F hG hF E' E
    hE' (by intro t s; rw [ContinuousMap.Homotopy.symm_symm]; exact hE t s)
  exact ⟨⟨F.hom,G.hom,hleft,hright⟩,
    fun x => ConcreteCategory.congr_hom hF x,
    fun x => ConcreteCategory.congr_hom hG x⟩

end KIP126.Topology
