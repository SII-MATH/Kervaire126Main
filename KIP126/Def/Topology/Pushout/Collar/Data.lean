module

public import Mathlib.Topology.Category.TopCat.Limits.Pullbacks

@[expose] public section

namespace KIP126.Topology

open CategoryTheory CategoryTheory.Limits Set

universe u v

/-- A concrete collar of an attachment, including its descended open
neighborhood and its actual continuous retraction to the old space. -/
structure AttachmentCollar {S A B P : TopCat.{u}}
    (i : S ⟶ A) (f : S ⟶ B) (a : A ⟶ P) (b : B ⟶ P) where
  W : Set A
  open_W : IsOpen W
  mem_W : ∀ s, i s ∈ W
  r : C(W,S)
  r_i : ∀ s, r ⟨i s,mem_W s⟩ = s
  V : Set P
  open_V : IsOpen V
  preimage_a : a ⁻¹' V = W
  preimage_b : b ⁻¹' V = Set.univ
  g : C(V,B)
  g_a : ∀ (x : A) (hx : a x ∈ V),
    g ⟨a x,hx⟩ = f (r ⟨x,by rw [← preimage_a]; exact hx⟩)
  g_b : ∀ (y : B) (hy : b y ∈ V), g ⟨b y,hy⟩ = y

namespace AttachmentCollar

variable {S A B P : TopCat.{u}} {i : S ⟶ A} {f : S ⟶ B} {a : A ⟶ P} {b : B ⟶ P}

/-- The actual bundle restricted to the collar neighborhood. -/
abbrev Source (c : AttachmentCollar i f a b) {E : Type v} [TopologicalSpace E] (p : C(E,P)) :=
  {z : E × c.V // p z.1 = z.2.1}

/-- The old bundle pulled back along the concrete collar retraction. -/
abbrev Target (c : AttachmentCollar i f a b) {E : Type v} [TopologicalSpace E] (p : C(E,P)) :=
  {z : E × c.V // p z.1 = b (c.g z.2)}

end AttachmentCollar

end KIP126.Topology
