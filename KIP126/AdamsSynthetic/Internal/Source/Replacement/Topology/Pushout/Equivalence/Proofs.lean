module

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.Pushout.Homotopy.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.HomotopyExtension.Predicates
import Mathlib.Topology.Homotopy.Equiv

@[expose] section

namespace KIP126.Topology

open CategoryTheory CategoryTheory.Limits
open scoped unitInterval

universe u

set_option backward.isDefEq.respectTransparency false

/-- Homotopy-compatible maps glue over a genuine cofibration attachment.
The map on the old space and the entire prescribed boundary homotopy
are retained exactly. -/
theorem exists_map_of_cofibration_attachment_with_homotopy
    {S A B P Y : TopCat.{u}} {a : S ⟶ A} {i : S ⟶ B}
    {u : A ⟶ P} {v : B ⟶ P}
    (hp : IsPushout a i u v) (hi : HomotopyExtension.HasHomotopyExtension i)
    (b : A ⟶ Y) (d : B ⟶ Y)
    (H : (d.hom.comp i.hom).Homotopy (b.hom.comp a.hom)) :
    ∃ r : P ⟶ Y, u ≫ r = b ∧
      ∃ H' : d.hom.Homotopy (v ≫ r).hom,
        ∀ (t : I) (x : S), H' (t,i x) = H (t,x) := by
  let p : C(S × I,Y) := H.toContinuousMap.comp ContinuousMap.prodSwap
  obtain ⟨E,hE₀,hEi⟩ := hi Y d.hom p (fun x => H.apply_zero x)
  let e₁ : B ⟶ Y :=
    TopCat.ofHom (E.comp ((ContinuousMap.id _).prodMk (ContinuousMap.const _ 1)))
  have he : a ≫ b = i ≫ e₁ := by
    ext x
    exact ((hEi x 1).trans (H.apply_one x)).symm
  let r := hp.desc b e₁ he
  have hv : v ≫ r = e₁ := hp.inr_desc _ _ _
  refine ⟨r,hp.inl_desc _ _ _,?_,?_⟩
  · exact {
      toFun := fun z => E (z.2,z.1)
      continuous_toFun := E.continuous.comp (continuous_snd.prodMk continuous_fst)
      map_zero_left := hE₀
      map_one_left := fun x => (ConcreteCategory.congr_hom hv x).symm }
  · intro t x
    exact hEi x t

/-- A specified left inverse homotopy on the old space extends across
an actual cofibration attachment to a left inverse of the induced
pushout map. The resulting inverse strictly retains its old-space map. -/
theorem exists_left_homotopy_inverse_of_cofibration_pushout
    {S A B P A' P' : TopCat.{u}} {a : S ⟶ A} {a' : S ⟶ A'} {i : S ⟶ B}
    {u : A ⟶ P} {v : B ⟶ P} {u' : A' ⟶ P'} {v' : B ⟶ P'}
    (hp : IsPushout a i u v) (hp' : IsPushout a' i u' v')
    (hi : HomotopyExtension.HasHomotopyExtension i)
    (e : A ⟶ A') (r : A' ⟶ A) (he : a ≫ e = a')
    (H : (ContinuousMap.id A).Homotopy (r.hom.comp e.hom))
    (F : P ⟶ P') (hFu : u ≫ F = e ≫ u') (hFv : v ≫ F = v') :
    ∃ R : P' ⟶ P, u' ≫ R = r ≫ u ∧
      ∃ E : v.hom.Homotopy (v' ≫ R).hom,
        (∀ (t : I) (s : S), E (t,i s) = u (H (t,a s))) ∧
        ∃ K : (ContinuousMap.id P).Homotopy (F ≫ R).hom,
          ∀ (t : I) (x : A), K (t,u x) = u (H (t,x)) := by
  let J := (ContinuousMap.Homotopy.refl u.hom).comp
    (H.compContinuousMap a.hom)
  have hJ₀ : u.hom.comp ((ContinuousMap.id A).comp a.hom) = v.hom.comp i.hom := by
    exact congrArg TopCat.Hom.hom hp.w
  have hJ₁ : u.hom.comp ((r.hom.comp e.hom).comp a.hom) =
      (r ≫ u).hom.comp a'.hom := by
    ext s
    exact congrArg (fun y => u (r y)) (ConcreteCategory.congr_hom he s)
  obtain ⟨R,hR,E,hE⟩ := exists_map_of_cofibration_attachment_with_homotopy hp' hi
    (r ≫ u) v (J.cast hJ₀ hJ₁)
  have hK₀ : u.hom.comp (ContinuousMap.id A) = (ContinuousMap.id P).comp u.hom := rfl
  have hK₁ : u.hom.comp (r.hom.comp e.hom) = (F ≫ R).hom.comp u.hom := by
    ext x
    exact (ConcreteCategory.congr_hom hR (e x)).symm.trans
      (congrArg R (ConcreteCategory.congr_hom hFu x).symm)
  let HA := ((ContinuousMap.Homotopy.refl u.hom).comp H).cast hK₀ hK₁
  have hB₁ : (v' ≫ R).hom = (F ≫ R).hom.comp v.hom := by
    change (v' ≫ R).hom = (v ≫ F ≫ R).hom
    rw [← Category.assoc,hFv]
  let HB := E.cast rfl hB₁
  obtain ⟨K,hK,_⟩ := exists_homotopy_of_topological_pushout hp
    (ContinuousMap.id P) (F ≫ R).hom HA HB (fun t s => (hE t s).symm)
  exact ⟨R,hR,E,hE,K,hK⟩

/-- A retraction with an actual deformation inside its fibers remains a
homotopy equivalence after a cofibration attachment. The forward map is
the specified strict pushout comparison, and its actual inverse retains
the specified section on the old space. -/
theorem exists_homotopyEquiv_of_cofibration_pushout_fiber_deformation
    {S A B P A' P' : TopCat.{u}} {a : S ⟶ A} {a' : S ⟶ A'} {i : S ⟶ B}
    {u : A ⟶ P} {v : B ⟶ P} {u' : A' ⟶ P'} {v' : B ⟶ P'}
    (hp : IsPushout a i u v) (hp' : IsPushout a' i u' v')
    (hi : HomotopyExtension.HasHomotopyExtension i)
    (e : A ⟶ A') (r : A' ⟶ A) (he : a ≫ e = a')
    (hr : r ≫ e = 𝟙 A')
    (H : (ContinuousMap.id A).Homotopy (r.hom.comp e.hom))
    (hH : ∀ (t : I) (x : A), e (H (t,x)) = e x)
    (F : P ⟶ P') (hFu : u ≫ F = e ≫ u') (hFv : v ≫ F = v') :
    ∃ E : ContinuousMap.HomotopyEquiv P P', E.toFun = F.hom ∧
      ∀ x : A', E.invFun (u' x) = u (r x) := by
  obtain ⟨R,hR,E,hE,K,_⟩ := exists_left_homotopy_inverse_of_cofibration_pushout
    hp hp' hi e r he H F hFu hFv
  have hA₁ : u'.hom = (R ≫ F).hom.comp u'.hom := by
    change u'.hom = (u' ≫ R ≫ F).hom
    rw [← Category.assoc,hR,Category.assoc,hFu,← Category.assoc,hr,Category.id_comp]
  let HA := (ContinuousMap.Homotopy.refl u'.hom).cast rfl hA₁
  have hB₀ : F.hom.comp v.hom = (ContinuousMap.id P').comp v'.hom := by
    exact congrArg TopCat.Hom.hom hFv
  let HB := ((ContinuousMap.Homotopy.refl F.hom).comp E).cast hB₀ rfl
  obtain ⟨L,_,_⟩ := exists_homotopy_of_topological_pushout hp'
    (ContinuousMap.id P') (R ≫ F).hom HA HB (by
      intro t s
      change u' (a' s) = F (E (t,i s))
      rw [hE]
      rw [show F (u (H (t,a s))) = u' (e (H (t,a s))) from
        ConcreteCategory.congr_hom hFu _,hH]
      exact congrArg u' (ConcreteCategory.congr_hom he s).symm)
  exact ⟨⟨F.hom,R.hom,⟨K.symm⟩,⟨L.symm⟩⟩,rfl,
    fun x => ConcreteCategory.congr_hom hR x⟩

end KIP126.Topology
