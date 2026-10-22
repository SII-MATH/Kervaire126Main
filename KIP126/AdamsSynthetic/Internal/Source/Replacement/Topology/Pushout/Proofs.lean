module

import Mathlib.Topology.Category.TopCat.Limits.Products
import Mathlib.CategoryTheory.Limits.Types.Pushouts
import Mathlib.Topology.Maps.Basic
import Mathlib.AlgebraicTopology.RelativeCellComplex.AttachCells

@[expose] section

namespace KIP126.Topology

open CategoryTheory CategoryTheory.Limits _root_.Topology Set

universe u

set_option backward.isDefEq.respectTransparency false

/-- Closed subsets of an actual topological pushout are detected on its
two attaching pieces. -/
theorem isClosed_iff_of_topological_pushout
    {S A B P : TopCat.{u}} {i : S ⟶ A} {f : S ⟶ B} {a : A ⟶ P} {b : B ⟶ P}
    (h : IsPushout i f a b) (K : Set P) :
    IsClosed K ↔ IsClosed (a ⁻¹' K) ∧ IsClosed (b ⁻¹' K) := by
  rw [TopCat.isClosed_iff_of_isColimit _ h.isColimit]
  constructor
  · intro hK
    exact ⟨hK .left,hK .right⟩
  · rintro ⟨ha,hb⟩ (_ | _ | _)
    · exact ha.preimage i.hom.continuous
    · exact ha
    · exact hb

/-- Attaching along a closed embedding preserves the old space as an
actual closed subspace of the pushout. -/
theorem isClosedEmbedding_of_topological_pushout
    {S A B P : TopCat.{u}} {i : S ⟶ A} {f : S ⟶ B} {a : A ⟶ P} {b : B ⟶ P}
    (h : IsPushout i f a b) (hi : IsClosedEmbedding i) : IsClosedEmbedding b := by
  have ht := h.map (forget TopCat)
  have hb : Function.Injective b :=
    Types.pushoutCocone_inr_injective_of_isColimit ht.isColimit hi.injective
  apply IsClosedEmbedding.of_continuous_injective_isClosedMap b.hom.continuous hb
  intro K hK
  apply (isClosed_iff_of_topological_pushout h _).mpr
  constructor
  · have he : a ⁻¹' (b '' K) = i '' (f ⁻¹' K) := by
      ext x
      constructor
      · rintro ⟨y,hy,hxy⟩
        obtain ⟨s,hs,hs'⟩ :=
          (Types.pushoutCocone_inl_eq_inr_iff_of_isColimit ht.isColimit hi.injective x y).mp hxy.symm
        exact ⟨s,by change f s ∈ K; change f s = y at hs'; rw [hs']; exact hy,hs⟩
      · rintro ⟨s,hs,rfl⟩
        exact ⟨f s,hs,(ConcreteCategory.congr_hom h.w s).symm⟩
    rw [he]
    exact hi.isClosedMap _ (hK.preimage f.hom.continuous)
  · rw [Set.preimage_image_eq _ hb]
    exact hK

/-- A disjoint union of closed embeddings is a closed embedding, with
no finiteness assumption on the family of attaching cells. -/
theorem isClosedEmbedding_sigma_map {ι : Type*} {A B : ι → Type*}
    [∀ i, TopologicalSpace (A i)] [∀ i, TopologicalSpace (B i)]
    (f : ∀ i, A i → B i) (hf : ∀ i, IsClosedEmbedding (f i)) :
    IsClosedEmbedding (Sigma.map id f) := by
  refine IsClosedEmbedding.of_continuous_injective_isClosedMap ?_
    (Function.injective_id.sigma_map (fun i => (hf i).injective)) ?_
  · apply continuous_sigma
    intro i
    exact (@continuous_sigmaMk ι B _ i).comp (hf i).continuous
  intro K hK
  apply isClosed_sigma_iff.mpr
  intro i
  have he : Sigma.mk i ⁻¹' (Sigma.map id f '' K) = f i '' (Sigma.mk i ⁻¹' K) := by
    ext y
    constructor
    · rintro ⟨⟨j,x⟩,hx,hxy⟩
      have hj : j = i := congrArg Sigma.fst hxy
      subst j
      exact ⟨x,hx,sigma_mk_injective hxy⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨⟨i,x⟩,hx,rfl⟩
  rw [he]
  exact (hf i).isClosedMap _ ((isClosed_sigma_iff.mp hK) i)

/-- Any categorical coproduct of closed embeddings has an actual closed
embedding as its comparison map. -/
theorem isClosedEmbedding_of_coproduct
    {ι : Type u} {A B : ι → TopCat.{u}} (f : ∀ i, A i ⟶ B i)
    (hf : ∀ i, IsClosedEmbedding (f i))
    (cA : Cofan A) (cB : Cofan B) (hA : IsColimit cA) (hB : IsColimit cB)
    (m : cA.pt ⟶ cB.pt) (hm : ∀ i, cA.inj i ≫ m = f i ≫ cB.inj i) :
    IsClosedEmbedding m := by
  let eA := hA.coconePointUniqueUpToIso (TopCat.sigmaCofanIsColimit A)
  let eB := hB.coconePointUniqueUpToIso (TopCat.sigmaCofanIsColimit B)
  let F : TopCat.of (Σ i, A i) ⟶ TopCat.of (Σ i, B i) := TopCat.ofHom
    ⟨Sigma.map id (fun i => (f i : A i → B i)),
      (isClosedEmbedding_sigma_map (fun i => (f i : A i → B i)) hf).continuous⟩
  have hcomp : m ≫ eB.hom = eA.hom ≫ F := by
    apply hA.hom_ext
    rintro ⟨i⟩
    change cA.inj i ≫ (m ≫ eB.hom) = cA.inj i ≫ (eA.hom ≫ F)
    rw [← Category.assoc, hm i, Category.assoc]
    simp only [eA,eB,Cofan.inj,IsColimit.comp_coconePointUniqueUpToIso_hom_assoc,
      IsColimit.comp_coconePointUniqueUpToIso_hom]
    rfl
  have hfunc : (m : cA.pt → cB.pt) =
      (TopCat.homeoOfIso eB).symm ∘ (Sigma.map id (fun i => (f i : A i → B i))) ∘
        (TopCat.homeoOfIso eA) := by
    funext x
    apply (TopCat.homeoOfIso eB).injective
    exact (ConcreteCategory.congr_hom hcomp x).trans
      ((TopCat.homeoOfIso eB).apply_symm_apply _).symm
  rw [hfunc]
  exact (TopCat.homeoOfIso eB).symm.isClosedEmbedding.comp
    ((isClosedEmbedding_sigma_map (fun i => (f i : A i → B i)) hf).comp
      (TopCat.homeoOfIso eA).isClosedEmbedding)

/-- Attaching any family of cells whose boundary maps are closed embeddings
preserves the old space as a closed subspace. -/
theorem isClosedEmbedding_of_attachCells {α : Type*} {A B : α → TopCat.{u}}
    {g : ∀ i, A i ⟶ B i} {X Y : TopCat.{u}} {f : X ⟶ Y}
    (c : HomotopicalAlgebra.AttachCells.{u} g f)
    (hg : ∀ i, IsClosedEmbedding (g i)) : IsClosedEmbedding f :=
  isClosedEmbedding_of_topological_pushout c.isPushout.flip
    (isClosedEmbedding_of_coproduct (fun i => g (c.π i)) (fun i => hg (c.π i))
      c.cofan₁ c.cofan₂ c.isColimit₁ c.isColimit₂ c.m c.hm)

end KIP126.Topology
