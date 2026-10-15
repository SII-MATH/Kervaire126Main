module

public import KIP126.Def.Topology.HomotopyExtension.Proofs
public import KIP126.Def.Topology.Pushout.Homotopy.Proofs

@[expose] public section

namespace KIP126.Topology.HomotopyExtension
open CategoryTheory CategoryTheory.Limits
open scoped unitInterval
universe u
set_option backward.isDefEq.respectTransparency false

/-- Actual homotopy extension is closed under composition. -/
theorem HasHomotopyExtension.comp {A B C : TopCat.{u}} {i : A ⟶ B} {j : B ⟶ C}
    (hi : HasHomotopyExtension i) (hj : HasHomotopyExtension j) : HasHomotopyExtension (i ≫ j) := by
  intro Y f p hp
  obtain ⟨E,hE,hEi⟩ := hi Y (f.comp j.hom) p hp
  obtain ⟨H,hH,hHj⟩ := hj Y f E hE
  exact ⟨H,hH,fun a t => (hHj (i a) t).trans (hEi a t)⟩

/-- Actual homotopy extension is preserved by every topological pushout. -/
theorem HasHomotopyExtension.of_isPushout
    {S A B P : TopCat.{u}} {i : S ⟶ A} {a : S ⟶ B} {u : A ⟶ P} {v : B ⟶ P}
    (hi : HasHomotopyExtension i) (h : IsPushout i a u v) : HasHomotopyExtension v := by
  intro Y f p hp
  let q : C(S × I,Y) := p.comp (a.hom.prodMap (ContinuousMap.id I))
  obtain ⟨E,hE,hEi⟩ := hi Y (f.comp u.hom) q (fun s =>
    (hp (a s)).trans (congrArg f (ConcreteCategory.congr_hom h.w s).symm))
  let A' : A ⟶ TopCat.of C(I,Y) := TopCat.ofHom E.curry
  let B' : B ⟶ TopCat.of C(I,Y) := TopCat.ofHom p.curry
  have hw : i ≫ A' = a ≫ B' := by ext s t; exact hEi s t
  let D := h.desc A' B' hw
  have hDA (a : A) (t : I) : D.hom.uncurry (u a,t) = E (a,t) :=
    congrArg (fun q : C(I,Y) => q t) (ConcreteCategory.congr_hom (h.inl_desc A' B' hw) a)
  have hDB (b : B) (t : I) : D.hom.uncurry (v b,t) = p (b,t) :=
    congrArg (fun q : C(I,Y) => q t) (ConcreteCategory.congr_hom (h.inr_desc A' B' hw) b)
  refine ⟨D.hom.uncurry,?_,hDB⟩
  intro x
  obtain ⟨a,rfl⟩ | ⟨b,rfl⟩ := Types.eq_or_eq_of_isPushout (h.map (forget TopCat)) x
  · exact (hDA a 0).trans (hE a)
  · exact (hDB b 0).trans (hp b)

/-- The inclusion of a summand has actual homotopy extension for arbitrary spaces. -/
theorem inl_hasHomotopyExtension (A B : TopCat.{u}) :
    HasHomotopyExtension (TopCat.ofHom (⟨Sum.inl,continuous_inl⟩ : C(A,A ⊕ B))) := by
  intro Y f p hp
  let q : C(B × I,Y) := f.comp ⟨fun z => Sum.inr z.1,continuous_inr.comp continuous_fst⟩
  let d : C(A ⊕ B,C(I,Y)) := ⟨Sum.elim p.curry q.curry,p.curry.continuous.sumElim q.curry.continuous⟩
  refine ⟨d.uncurry,?_,fun _ _ => rfl⟩
  intro x
  cases x with
  | inl a => exact hp a
  | inr b => rfl

end KIP126.Topology.HomotopyExtension
