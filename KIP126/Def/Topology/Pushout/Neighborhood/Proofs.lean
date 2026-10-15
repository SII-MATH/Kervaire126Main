module

public import KIP126.Def.Topology.Pushout.Cells.Proofs

@[expose] public section

namespace KIP126.Topology

open CategoryTheory CategoryTheory.Limits _root_.Topology Set

universe u v

set_option backward.isDefEq.respectTransparency false

/-- Continuity on an open portion of an actual pushout is detected on
its two restricted constituent spaces. -/
theorem continuous_on_open_pushout
    {S A B P : TopCat.{u}} {i : S ⟶ A} {f : S ⟶ B} {a : A ⟶ P} {b : B ⟶ P}
    (h : IsPushout i f a b) {V : Set P} (hV : IsOpen V)
    {T : Type v} [TopologicalSpace T] (g : V → T)
    (ha : Continuous (fun x : a ⁻¹' V => g ⟨a x.1,x.2⟩))
    (hb : Continuous (fun x : b ⁻¹' V => g ⟨b x.1,x.2⟩)) : Continuous g := by
  apply continuous_def.mpr
  intro U hU
  let Q : Set P := Subtype.val '' (g ⁻¹' U)
  have hQa : a ⁻¹' Q = Subtype.val ''
      ((fun x : a ⁻¹' V => g ⟨a x.1,x.2⟩) ⁻¹' U) := by
    ext x
    constructor
    · rintro ⟨y,hy,hxy⟩
      have hx : a x ∈ V := hxy ▸ y.2
      exact ⟨⟨x,hx⟩,by simpa [Q,show (⟨a x,hx⟩ : V) = y from Subtype.ext hxy.symm] using hy,rfl⟩
    · rintro ⟨y,hy,rfl⟩
      exact ⟨⟨a y.1,y.2⟩,hy,rfl⟩
  have hQb : b ⁻¹' Q = Subtype.val ''
      ((fun x : b ⁻¹' V => g ⟨b x.1,x.2⟩) ⁻¹' U) := by
    ext x
    constructor
    · rintro ⟨y,hy,hxy⟩
      have hx : b x ∈ V := hxy ▸ y.2
      exact ⟨⟨x,hx⟩,by simpa [Q,show (⟨b x,hx⟩ : V) = y from Subtype.ext hxy.symm] using hy,rfl⟩
    · rintro ⟨y,hy,rfl⟩
      exact ⟨⟨b y.1,y.2⟩,hy,rfl⟩
  have hQ : IsOpen Q := (isOpen_iff_of_topological_pushout h Q).mpr ⟨by
    rw [hQa]
    exact (hV.preimage a.hom.continuous).isOpenMap_subtype_val _ (hU.preimage ha),by
    rw [hQb]
    exact (hV.preimage b.hom.continuous).isOpenMap_subtype_val _ (hU.preimage hb)⟩
  have he : g ⁻¹' U = Subtype.val ⁻¹' Q := by
    simp only [Q,Set.preimage_image_eq _ Subtype.val_injective]
  rw [he]
  exact hQ.preimage continuous_subtype_val

/-- A retraction of an open boundary neighborhood in the attached cell
extends to a genuine retraction of an open neighborhood of the old space
in the pushout. This is the collar step for local bundle charts. -/
theorem exists_open_pushout_retraction_with_preimages
    {S A B P : TopCat.{u}} [NormalSpace A] [T1Space A]
    {i : S ⟶ A} {f : S ⟶ B} {a : A ⟶ P} {b : B ⟶ P}
    (h : IsPushout i f a b) (hi : IsClosedEmbedding i)
    (W : Set A) (hW : IsOpen W) (hiW : Set.range i ⊆ W)
    (r : A → B) (hr : ContinuousOn r W) (hri : ∀ s, r (i s) = f s) :
    ∃ V : Set P, IsOpen V ∧ a ⁻¹' V = W ∧ b ⁻¹' V = Set.univ ∧
      ∃ g : C(V,B), (∀ y (hy : b y ∈ V), g ⟨b y,hy⟩ = y) ∧
        (∀ x (hx : a x ∈ V), g ⟨a x,hx⟩ = r x) := by
  let ht := h.map (forget TopCat)
  let c : PushoutCocone ((forget TopCat).map i) ((forget TopCat).map f) :=
    PushoutCocone.mk (TypeCat.ofHom r) (𝟙 _) (by
      apply ConcreteCategory.hom_ext
      exact hri)
  let g : P → B := ht.isColimit.desc c
  have hga (x : A) : g (a x) = r x :=
    ConcreteCategory.congr_hom (ht.isColimit.fac c .left) x
  have hgb (y : B) : g (b y) = y :=
    ConcreteCategory.congr_hom (ht.isColimit.fac c .right) y
  let V : Set P := (a '' Wᶜ)ᶜ
  have haV : a ⁻¹' V = W := by
    ext x
    constructor
    · intro hx
      by_contra hxW
      exact hx ⟨x,hxW,rfl⟩
    · intro hxW
      rintro ⟨y,hy,hyx⟩
      have hyi : y ∉ Set.range i := fun h => hy (hiW h)
      exact hy ((pushout_cell_eq_of_outside_boundary h hi hyi hyx) ▸ hxW)
  have hbV : b ⁻¹' V = Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    rintro ⟨x,hx,hxy⟩
    obtain ⟨s,hs,_⟩ :=
      (Types.pushoutCocone_inl_eq_inr_iff_of_isColimit ht.isColimit hi.injective x y).mp hxy
    exact hx (hiW ⟨s,hs⟩)
  have hV : IsOpen V := (isOpen_iff_of_topological_pushout h V).mpr (by
    rw [haV,hbV]
    exact ⟨hW,isOpen_univ⟩)
  have hgc : Continuous (fun x : V => g x.1) := by
    apply continuous_on_open_pushout h hV
    · change Continuous (fun x : a ⁻¹' V => g (a x.1))
      simp only [hga]
      have he : a ⁻¹' V = W := haV
      exact continuousOn_iff_continuous_restrict.mp (he ▸ hr)
    · change Continuous (fun x : b ⁻¹' V => g (b x.1))
      simp only [hgb]
      exact continuous_subtype_val
  refine ⟨V,hV,haV,hbV,⟨fun x => g x.1,hgc⟩,?_,?_⟩
  · exact fun y _ => hgb y
  · exact fun x _ => hga x

end KIP126.Topology
