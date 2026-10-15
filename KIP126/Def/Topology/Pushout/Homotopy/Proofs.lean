module

public import KIP126.Def.Topology.Pushout.Proofs
public import Mathlib.Topology.Homotopy.Basic

@[expose] public section

namespace KIP126.Topology

open CategoryTheory CategoryTheory.Limits
open scoped unitInterval

universe u

set_option backward.isDefEq.respectTransparency false

/-- Compatible homotopies on the two pieces of an actual topological
pushout glue to a continuous homotopy, retaining their exact values
on both pieces. -/
theorem exists_homotopy_of_topological_pushout
    {S A B P Y : TopCat.{u}} {i : S ⟶ A} {f : S ⟶ B} {a : A ⟶ P} {b : B ⟶ P}
    (h : IsPushout i f a b) (F G : C(P,Y))
    (HA : (F.comp a.hom).Homotopy (G.comp a.hom))
    (HB : (F.comp b.hom).Homotopy (G.comp b.hom))
    (hH : ∀ (t : I) (s : S), HA (t,i s) = HB (t,f s)) :
    ∃ H : F.Homotopy G,
      (∀ (t : I) (x : A), H (t,a x) = HA (t,x)) ∧
      (∀ (t : I) (x : B), H (t,b x) = HB (t,x)) := by
  let cA : A ⟶ TopCat.of C(I,Y) :=
    TopCat.ofHom (HA.toContinuousMap.comp ContinuousMap.prodSwap).curry
  let cB : B ⟶ TopCat.of C(I,Y) :=
    TopCat.ofHom (HB.toContinuousMap.comp ContinuousMap.prodSwap).curry
  have hc : i ≫ cA = f ≫ cB := by
    ext s t
    exact hH t s
  let d := h.desc cA cB hc
  let E : C(P × I,Y) := d.hom.uncurry
  have hA (t : I) (x : A) : E (a x,t) = HA (t,x) :=
    congrArg (fun p : C(I,Y) => p t) (ConcreteCategory.congr_hom (h.inl_desc cA cB hc) x)
  have hB (t : I) (x : B) : E (b x,t) = HB (t,x) :=
    congrArg (fun p : C(I,Y) => p t) (ConcreteCategory.congr_hom (h.inr_desc cA cB hc) x)
  refine ⟨{
    toFun := fun z => E (z.2,z.1)
    continuous_toFun := E.continuous.comp (continuous_snd.prodMk continuous_fst)
    map_zero_left := ?_
    map_one_left := ?_ },hA,hB⟩
  · intro x
    obtain ⟨y,rfl⟩ | ⟨y,rfl⟩ := Types.eq_or_eq_of_isPushout (h.map (forget TopCat)) x
    · exact (hA 0 y).trans (HA.apply_zero y)
    · exact (hB 0 y).trans (HB.apply_zero y)
  · intro x
    obtain ⟨y,rfl⟩ | ⟨y,rfl⟩ := Types.eq_or_eq_of_isPushout (h.map (forget TopCat)) x
    · exact (hA 1 y).trans (HA.apply_one y)
    · exact (hB 1 y).trans (HB.apply_one y)

/-- If both component homotopies fix the preimages of a specified
region, their glued homotopy is relative to that entire region. -/
theorem homotopicRel_of_topological_pushout
    {S A B P Y : TopCat.{u}} {i : S ⟶ A} {f : S ⟶ B} {a : A ⟶ P} {b : B ⟶ P}
    (h : IsPushout i f a b) (F G : C(P,Y)) (T : Set P)
    (HA : (F.comp a.hom).HomotopyRel (G.comp a.hom) (a ⁻¹' T))
    (HB : (F.comp b.hom).HomotopyRel (G.comp b.hom) (b ⁻¹' T))
    (hH : ∀ (t : I) (s : S), HA (t,i s) = HB (t,f s)) : F.HomotopicRel G T := by
  obtain ⟨H,hA,hB⟩ := exists_homotopy_of_topological_pushout h F G
    HA.toHomotopy HB.toHomotopy hH
  refine ⟨⟨H,?_⟩⟩
  intro t x hx
  obtain ⟨y,rfl⟩ | ⟨y,rfl⟩ := Types.eq_or_eq_of_isPushout (h.map (forget TopCat)) x
  · exact (hA t y).trans (HA.eq_fst t hx)
  · exact (hB t y).trans (HB.eq_fst t hx)

end KIP126.Topology
