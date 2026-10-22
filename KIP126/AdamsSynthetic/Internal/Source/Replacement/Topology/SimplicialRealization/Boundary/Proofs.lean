module

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.Proofs
import Mathlib.AlgebraicTopology.SimplicialSet.Nonsingular
import Mathlib.Data.Finset.Sort
import Mathlib.Topology.Homeomorph.Lemmas

@[expose] section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

universe u

set_option backward.isDefEq.respectTransparency false

/-- An injective simplex map retains each of its original barycentric coordinates. -/
theorem simplex_map_apply_injective {A B : Type*} [Fintype A] [Fintype B]
    (f : A → B) (hf : Function.Injective f) (x : stdSimplex ℝ A) (a : A) :
    stdSimplex.map f x (f a) = x a := by
  classical
  change FunOnFinite.linearMap ℝ ℝ f x (f a) = x a
  rw [FunOnFinite.linearMap_apply_apply]
  apply Finset.sum_eq_single a
  · intro b hb hba
    exact (hba (hf (Finset.mem_filter.mp hb).2)).elim
  · intro ha
    exact (ha (Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩)).elim

/-- Barycentric coordinates outside the image of a simplex map vanish. -/
theorem simplex_map_apply_not_range {A B : Type*} [Fintype A] [Fintype B]
    (f : A → B) (x : stdSimplex ℝ A) (b : B) (hb : b ∉ Set.range f) :
    stdSimplex.map f x b = 0 := by
  classical
  change FunOnFinite.linearMap ℝ ℝ f x b = 0
  rw [FunOnFinite.linearMap_apply_apply]
  apply Finset.sum_eq_zero
  intro a ha
  exact (hb ⟨a,(Finset.mem_filter.mp ha).2⟩).elim

/-- Injective vertex maps induce injective maps of actual topological simplices. -/
theorem simplex_map_injective {A B : Type*} [Fintype A] [Fintype B]
    (f : A → B) (hf : Function.Injective f) :
    Function.Injective (stdSimplex.map (S := ℝ) f) := by
  intro x y h
  apply stdSimplex.ext
  funext a
  have hh := congrArg (fun z : stdSimplex ℝ B => z (f a)) h
  simpa only [simplex_map_apply_injective f hf] using hh

/-- The image of an injective simplex map consists exactly of barycentric
points supported on its image vertices. -/
theorem simplex_map_range_iff {A B : Type*} [Fintype A] [Fintype B]
    (f : A → B) (hf : Function.Injective f) (y : stdSimplex ℝ B) :
    y ∈ Set.range (stdSimplex.map (S := ℝ) f) ↔
      ∀ b, b ∉ Set.range f → y b = 0 := by
  classical
  constructor
  · rintro ⟨x,rfl⟩ b hb
    exact simplex_map_apply_not_range f x b hb
  · intro hy
    have hsum : ∑ a, y (f a) = 1 := by
      rw [← Finset.sum_image hf.injOn]
      calc
        ∑ b ∈ Finset.image f Finset.univ, y b = ∑ b, y b := by
          apply Finset.sum_subset (Finset.subset_univ _)
          intro b _ hb
          exact hy b (by simpa only [Finset.mem_image, Finset.mem_univ, true_and,
            Set.mem_range] using hb)
        _ = 1 := stdSimplex.sum_eq_one y
    let x : stdSimplex ℝ A := ⟨fun a => y (f a),fun a => stdSimplex.zero_le y _,hsum⟩
    refine ⟨x,?_⟩
    apply stdSimplex.ext
    funext b
    by_cases hb : b ∈ Set.range f
    · obtain ⟨a,rfl⟩ := hb
      exact simplex_map_apply_injective f hf x a
    · exact (simplex_map_apply_not_range f x b hb).trans (hy b hb).symm

/-- A nonzero-sum barycentric point always has a positive coordinate. -/
theorem simplex_exists_positive {A : Type*} [Fintype A] (x : stdSimplex ℝ A) :
    ∃ a, 0 < x a := by
  by_contra! h
  have hz (a : A) : x a = 0 := le_antisymm (h a) (stdSimplex.zero_le x a)
  have := stdSimplex.sum_eq_one x
  simp only [hz,Finset.sum_const_zero] at this
  norm_num at this

/-- The realization of a representable face maps injectively into the
topological simplex, with its actual barycentric face inclusion. -/
theorem face_realization_injective_of_orderIso {n m : ℕ}
    (S : Finset (Fin (n+1))) (e : Fin (m+1) ≃o S) :
    Function.Injective (fun x : |(SSet.stdSimplex.face.{u} S).toSSet| =>
      SimplexCategory.toTopHomeo ⦋n⦌ (SSet.toTop.map (SSet.stdSimplex.face S).ι x)) := by
  let f : ⦋m⦌ ⟶ ⦋n⦌ := SimplexCategory.Hom.mk
    ((OrderHom.Subtype.val _).comp e.toOrderEmbedding.toOrderHom)
  let E := SSet.stdSimplex.isoOfRepresentableBy (SSet.stdSimplex.faceRepresentableBy S m e)
  have hE : E.hom ≫ (SSet.stdSimplex.face S).ι = SSet.stdSimplex.map f := rfl
  have hf : Function.Injective f := Subtype.val_injective.comp e.injective
  intro x y h
  obtain ⟨a,rfl⟩ := ((TopCat.epi_iff_surjective (SSet.toTop.map E.hom)).mp inferInstance) x
  obtain ⟨b,rfl⟩ := ((TopCat.epi_iff_surjective (SSet.toTop.map E.hom)).mp inferInstance) y
  have hmap (a : |(Δ[m] : SSet.{u})|) :
      SimplexCategory.toTopHomeo ⦋n⦌
        (SSet.toTop.map (SSet.stdSimplex.face S).ι (SSet.toTop.map E.hom a)) =
      stdSimplex.map f (SimplexCategory.toTopHomeo ⦋m⦌ a) := by
    rw [← TopCat.comp_app, ← Functor.map_comp, hE]
    exact SimplexCategory.toTopHomeo_naturality_apply f a
  change SimplexCategory.toTopHomeo ⦋n⦌
      (SSet.toTop.map (SSet.stdSimplex.face S).ι (SSet.toTop.map E.hom a)) =
    SimplexCategory.toTopHomeo ⦋n⦌
      (SSet.toTop.map (SSet.stdSimplex.face S).ι (SSet.toTop.map E.hom b)) at h
  rw [hmap,hmap] at h
  exact congrArg (SSet.toTop.map E.hom)
    ((SimplexCategory.toTopHomeo ⦋m⦌).injective ((simplex_map_injective f hf) h))

/-- The image of the realized representable face is exactly its expected
barycentric support subset. -/
theorem face_realization_range_of_orderIso {n m : ℕ}
    (S : Finset (Fin (n+1))) (e : Fin (m+1) ≃o S)
    (y : stdSimplex ℝ (Fin (n+1))) :
    y ∈ Set.range (fun x : |(SSet.stdSimplex.face.{u} S).toSSet| =>
      SimplexCategory.toTopHomeo ⦋n⦌ (SSet.toTop.map (SSet.stdSimplex.face S).ι x)) ↔
      ∀ i, i ∉ S → y i = 0 := by
  let f : ⦋m⦌ ⟶ ⦋n⦌ := SimplexCategory.Hom.mk
    ((OrderHom.Subtype.val _).comp e.toOrderEmbedding.toOrderHom)
  let E := SSet.stdSimplex.isoOfRepresentableBy (SSet.stdSimplex.faceRepresentableBy S m e)
  have hE : E.hom ≫ (SSet.stdSimplex.face S).ι = SSet.stdSimplex.map f := rfl
  have hf : Function.Injective f := Subtype.val_injective.comp e.injective
  have hr (i : Fin (n+1)) : i ∈ Set.range f ↔ i ∈ S := by
    constructor
    · rintro ⟨j,rfl⟩
      exact (e j).2
    · intro hi
      obtain ⟨j,hj⟩ := e.surjective ⟨i,hi⟩
      exact ⟨j,congrArg Subtype.val hj⟩
  have hmap (a : |(Δ[m] : SSet.{u})|) :
      SimplexCategory.toTopHomeo ⦋n⦌
        (SSet.toTop.map (SSet.stdSimplex.face S).ι (SSet.toTop.map E.hom a)) =
      stdSimplex.map f (SimplexCategory.toTopHomeo ⦋m⦌ a) := by
    rw [← TopCat.comp_app, ← Functor.map_comp, hE]
    exact SimplexCategory.toTopHomeo_naturality_apply f a
  constructor
  · rintro ⟨x,rfl⟩ i hi
    obtain ⟨a,rfl⟩ := ((TopCat.epi_iff_surjective (SSet.toTop.map E.hom)).mp inferInstance) x
    change (SimplexCategory.toTopHomeo ⦋n⦌
      (SSet.toTop.map (SSet.stdSimplex.face S).ι (SSet.toTop.map E.hom a))) i = 0
    rw [hmap]
    exact simplex_map_apply_not_range f _ i (fun h => hi ((hr i).mp h))
  · intro hy
    obtain ⟨x,hx⟩ := (simplex_map_range_iff f hf y).mpr
      (fun i hi => hy i (fun h => hi ((hr i).mpr h)))
    refine ⟨SSet.toTop.map E.hom ((SimplexCategory.toTopHomeo ⦋m⦌).symm x),?_⟩
    change SimplexCategory.toTopHomeo ⦋n⦌
      (SSet.toTop.map (SSet.stdSimplex.face S).ι
        (SSet.toTop.map E.hom ((SimplexCategory.toTopHomeo ⦋m⦌).symm x))) = y
    rw [hmap,(SimplexCategory.toTopHomeo ⦋m⦌).apply_symm_apply]
    exact hx

/-- Every nonempty face has an injective actual realization map. -/
theorem face_realization_injective {n : ℕ} (S : Finset (Fin (n+1))) (hS : S.Nonempty) :
    Function.Injective (fun x : |(SSet.stdSimplex.face.{u} S).toSSet| =>
      SimplexCategory.toTopHomeo ⦋n⦌ (SSet.toTop.map (SSet.stdSimplex.face S).ι x)) := by
  have hc : S.card = (S.card - 1) + 1 := by have := hS.card_pos; omega
  exact face_realization_injective_of_orderIso S (S.orderIsoOfFin hc)

/-- Every nonempty realized face is the closed geometric face with the
specified zero coordinates. -/
theorem face_realization_range {n : ℕ} (S : Finset (Fin (n+1))) (hS : S.Nonempty)
    (y : stdSimplex ℝ (Fin (n+1))) :
    y ∈ Set.range (fun x : |(SSet.stdSimplex.face.{u} S).toSSet| =>
      SimplexCategory.toTopHomeo ⦋n⦌ (SSet.toTop.map (SSet.stdSimplex.face S).ι x)) ↔
      ∀ i, i ∉ S → y i = 0 := by
  have hc : S.card = (S.card - 1) + 1 := by have := hS.card_pos; omega
  exact face_realization_range_of_orderIso S (S.orderIsoOfFin hc) y

/-- Every realization point of a simplicial subcomplex of a standard simplex
comes from one of its nonempty representable faces. -/
theorem subcomplex_point_lies_in_face {n : ℕ}
    (A : (Δ[n] : SSet.{u}).Subcomplex) (x : |A.toSSet|) :
    ∃ (S : Finset (Fin (n+1))) (_ : S.Nonempty)
      (hSA : SSet.stdSimplex.face S ≤ A)
      (a : |(SSet.stdSimplex.face S).toSSet|),
      SSet.toTop.map (SSet.Subcomplex.homOfLE hSA) a = x := by
  obtain ⟨s,t,ht⟩ := exists_nondegenerate_simplex A.toSSet x
  let z : (Δ[n] : SSet.{u}).nonDegenerate s.dim :=
    ⟨s.simplex.1, (A.mem_nonDegenerate_iff s.simplex).mp s.nonDegenerate⟩
  let S := (SSet.stdSimplex.nonDegenerateEquiv' z).1
  have hS : S.Nonempty := Finset.card_pos.mp (by
    change 0 < (SSet.stdSimplex.nonDegenerateEquiv' z).1.card
    rw [(SSet.stdSimplex.nonDegenerateEquiv' z).2]
    omega)
  have hface : SSet.stdSimplex.face S = SSet.Subcomplex.ofSimplex s.simplex.1 :=
    SSet.stdSimplex.face_nonDegenerateEquiv' z
  have hSA : SSet.stdSimplex.face S ≤ A := by
    rw [hface,SSet.Subcomplex.ofSimplex_le_iff]
    exact s.simplex.2
  let q : (SSet.stdSimplex.face S).obj (op ⦋s.dim⦌) :=
    ⟨s.simplex.1, by rw [hface]; exact SSet.Subcomplex.mem_ofSimplex_obj _⟩
  let g : (Δ[s.dim] : SSet.{u}) ⟶ (SSet.stdSimplex.face S).toSSet :=
    SSet.yonedaEquiv.symm q
  have hg : g ≫ SSet.Subcomplex.homOfLE hSA = SSet.yonedaEquiv.symm s.simplex := by
    change SSet.yonedaEquiv.symm q ≫ SSet.Subcomplex.homOfLE hSA = _
    rw [SSet.yonedaEquiv_symm_comp]
    rfl
  refine ⟨S,hS,hSA,SSet.toTop.map g t,?_⟩
  rw [← TopCat.comp_app, ← Functor.map_comp,hg]
  exact ht

/-- The barycentric inclusion agrees with each actual subcomplex inclusion. -/
theorem subcomplex_realization_inclusion_apply {n : ℕ}
    {A B : (Δ[n] : SSet.{u}).Subcomplex} (h : A ≤ B) (x : |A.toSSet|) :
    SimplexCategory.toTopHomeo ⦋n⦌
      (SSet.toTop.map B.ι (SSet.toTop.map (SSet.Subcomplex.homOfLE h) x)) =
    SimplexCategory.toTopHomeo ⦋n⦌ (SSet.toTop.map A.ι x) := by
  rw [← TopCat.comp_app, ← Functor.map_comp,SSet.Subcomplex.homOfLE_ι]

/-- Realizing a subcomplex of a standard simplex gives an actual injective
map into its barycentric simplex. Overlapping face representatives are
identified through their common face. -/
theorem subcomplex_realization_injective {n : ℕ}
    (A : (Δ[n] : SSet.{u}).Subcomplex) :
    Function.Injective (fun x : |A.toSSet| =>
      SimplexCategory.toTopHomeo ⦋n⦌ (SSet.toTop.map A.ι x)) := by
  classical
  intro x y hxy
  obtain ⟨S,hS,hSA,a,rfl⟩ := subcomplex_point_lies_in_face A x
  obtain ⟨T,hT,hTA,b,rfl⟩ := subcomplex_point_lies_in_face A y
  change SimplexCategory.toTopHomeo ⦋n⦌
      (SSet.toTop.map A.ι (SSet.toTop.map (SSet.Subcomplex.homOfLE hSA) a)) =
    SimplexCategory.toTopHomeo ⦋n⦌
      (SSet.toTop.map A.ι (SSet.toTop.map (SSet.Subcomplex.homOfLE hTA) b)) at hxy
  rw [subcomplex_realization_inclusion_apply,subcomplex_realization_inclusion_apply] at hxy
  let p := SimplexCategory.toTopHomeo ⦋n⦌ (SSet.toTop.map (SSet.stdSimplex.face S).ι a)
  have hpS : ∀ i, i ∉ S → p i = 0 := (face_realization_range S hS p).mp ⟨a,rfl⟩
  have hpT : ∀ i, i ∉ T → p i = 0 := (face_realization_range T hT p).mp ⟨b,hxy.symm⟩
  have hST : (S ∩ T).Nonempty := by
    obtain ⟨i,hi⟩ := simplex_exists_positive p
    refine ⟨i,Finset.mem_inter.mpr ⟨?_,?_⟩⟩
    · by_contra h; exact (ne_of_gt hi) (hpS i h)
    · by_contra h; exact (ne_of_gt hi) (hpT i h)
  have hpST : ∀ i, i ∉ S ∩ T → p i = 0 := by
    intro i hi
    by_cases hS : i ∈ S
    · exact hpT i (fun hT => hi (Finset.mem_inter.mpr ⟨hS,hT⟩))
    · exact hpS i hS
  obtain ⟨c,hc⟩ := (face_realization_range (S ∩ T) hST p).mpr hpST
  have hKS : SSet.stdSimplex.face.{u} (S ∩ T) ≤ SSet.stdSimplex.face S :=
    (SSet.stdSimplex.face_le_face_iff _ _).mpr Finset.inter_subset_left
  have hKT : SSet.stdSimplex.face.{u} (S ∩ T) ≤ SSet.stdSimplex.face T :=
    (SSet.stdSimplex.face_le_face_iff _ _).mpr Finset.inter_subset_right
  have ha : SSet.toTop.map (SSet.Subcomplex.homOfLE hKS) c = a := by
    apply face_realization_injective S hS
    exact (subcomplex_realization_inclusion_apply hKS c).trans hc
  have hb : SSet.toTop.map (SSet.Subcomplex.homOfLE hKT) c = b := by
    apply face_realization_injective T hT
    exact (subcomplex_realization_inclusion_apply hKT c).trans (hc.trans hxy)
  rw [← ha, ← hb, ← TopCat.comp_app, ← TopCat.comp_app,
    ← Functor.map_comp, ← Functor.map_comp]
  rfl

/-- The actual realized boundary is exactly the barycentric points having
a zero coordinate, including the empty boundary in dimension zero. -/
theorem boundary_realization_range (n : ℕ) (p : stdSimplex ℝ (Fin (n+1))) :
    p ∈ Set.range (fun x : |(∂Δ[n] : SSet.{u})| =>
      SimplexCategory.toTopHomeo ⦋n⦌ (SSet.toTop.map (∂Δ[n]).ι x)) ↔
      ∃ i, p i = 0 := by
  classical
  constructor
  · rintro ⟨x,rfl⟩
    obtain ⟨S,hS,hSA,a,rfl⟩ := subcomplex_point_lies_in_face (∂Δ[n]) x
    have hproper : ∃ i, i ∉ S := by
      by_contra! h
      have hfull : S = Finset.univ := Finset.eq_univ_iff_forall.mpr h
      rw [hfull,SSet.stdSimplex.face_univ] at hSA
      exact (SSet.boundary_lt_top n).not_ge hSA
    obtain ⟨i,hi⟩ := hproper
    refine ⟨i,?_⟩
    change (SimplexCategory.toTopHomeo ⦋n⦌
      (SSet.toTop.map (∂Δ[n]).ι (SSet.toTop.map (SSet.Subcomplex.homOfLE hSA) a))) i = 0
    rw [subcomplex_realization_inclusion_apply]
    exact (face_realization_range S hS _).mp ⟨a,rfl⟩ i hi
  · rintro ⟨i,hi⟩
    have hS : ({i}ᶜ : Finset (Fin (n+1))).Nonempty := by
      obtain ⟨j,hj⟩ := simplex_exists_positive p
      refine ⟨j,Finset.mem_compl.mpr ?_⟩
      simp only [Finset.mem_singleton]
      intro h; subst j
      exact (ne_of_gt hj) hi
    have hsupport : ∀ j, j ∉ ({i}ᶜ : Finset (Fin (n+1))) → p j = 0 := by
      intro j hj
      have : j = i := by simpa only [Finset.mem_compl,not_not,Finset.mem_singleton] using hj
      simpa only [this] using hi
    obtain ⟨a,ha⟩ := (face_realization_range {i}ᶜ hS p).mpr hsupport
    refine ⟨SSet.toTop.map
      (SSet.Subcomplex.homOfLE (SSet.face_singleton_compl_le_boundary i)) a,?_⟩
    exact (subcomplex_realization_inclusion_apply
      (SSet.face_singleton_compl_le_boundary i) a).trans ha

/-- The actual realization of the simplicial boundary is homeomorphic to
the geometric zero-coordinate boundary, compatibly with its inclusion. -/
theorem exists_boundary_realization_homeomorph (n : ℕ) :
    ∃ e : |(∂Δ[n] : SSet.{u})| ≃ₜ
      {p : stdSimplex ℝ (Fin (n+1)) // ∃ i, p i = 0},
      ∀ x, (e x).1 = SimplexCategory.toTopHomeo ⦋n⦌
        (SSet.toTop.map (∂Δ[n]).ι x) := by
  letI : SSet.Finite (∂Δ[n] : SSet.{u}) := SSet.finite_of_mono (∂Δ[n]).ι
  letI : CompactSpace |(∂Δ[n] : SSet.{u})| := compactSpace_of_finite _
  let f : |(∂Δ[n] : SSet.{u})| →
      {p : stdSimplex ℝ (Fin (n+1)) // ∃ i, p i = 0} := fun x =>
    ⟨SimplexCategory.toTopHomeo ⦋n⦌ (SSet.toTop.map (∂Δ[n]).ι x),
      (boundary_realization_range n _).mp ⟨x,rfl⟩⟩
  have hf : Continuous f := ((SimplexCategory.toTopHomeo ⦋n⦌).continuous.comp
    (SSet.toTop.map (∂Δ[n]).ι).hom.continuous).subtype_mk _
  have hb : Function.Bijective f := by
    constructor
    · intro x y h
      exact subcomplex_realization_injective (∂Δ[n]) (congrArg Subtype.val h)
    · intro y
      obtain ⟨x,hx⟩ := (boundary_realization_range n y.1).mpr y.2
      exact ⟨x,Subtype.ext hx⟩
  let e : |(∂Δ[n] : SSet.{u})| ≃ _ := Equiv.ofBijective f hb
  exact ⟨hf.homeoOfEquivCompactToT2 (f := e),fun _ => rfl⟩

end KIP126.Topology.SimplicialRealization
