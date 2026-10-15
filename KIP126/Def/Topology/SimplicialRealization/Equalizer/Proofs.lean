module

public import KIP126.Def.Topology.SimplicialRealization.Equalizer.Data
public import KIP126.Def.Topology.SimplicialRealization.Classical.Proofs

@[expose] public section

namespace KIP126.Topology.SimplicialRealization
open CategoryTheory CategoryTheory.Limits Opposite Simplicial
universe u
set_option backward.isDefEq.respectTransparency false

theorem simplexPoint_naturality (A : SSet.{u}) {a b : SimplexCategory}
    (f : a ⟶ b) (x : A.obj (op b)) (u : stdSimplex ℝ (Fin (a.len + 1))) :
    simplexPoint A (A.map f.op x) u = simplexPoint A x (stdSimplex.map f.toOrderHom u) := by
  have h := ConcreteCategory.congr_hom ((sSetTopAdj.unit.app A).naturality f.op) x
  exact congrArg (fun y => (SSet.toTop.obj A).toSSetObjEquiv (op a) y u) h

theorem simplexPoint_map {A B : SSet.{u}} (f : A ⟶ B)
    (a : SimplexCategoryᵒᵖ) (x : A.obj a)
    (u : stdSimplex ℝ (Fin (a.unop.len + 1))) :
    SSet.toTop.map f (simplexPoint A x u) = simplexPoint B (f.app a x) u := by
  have h := congrArg (fun g : A ⟶ TopCat.toSSet.obj (SSet.toTop.obj B) =>
    (SSet.toTop.obj B).toSSetObjEquiv a (g.app a x) u)
    (sSetTopAdj.unit.naturality f)
  exact h.symm

/-- A surjective map of vertices carries strictly positive barycentric
coordinates to strictly positive barycentric coordinates. -/
theorem simplex_map_positive {A B : Type*} [Fintype A] [Fintype B]
    (f : A → B) (hf : Function.Surjective f) (u : stdSimplex ℝ A)
    (hu : ∀ a, 0 < u a) (b : B) : 0 < stdSimplex.map f u b := by
  classical
  obtain ⟨a, rfl⟩ := hf b
  change 0 < FunOnFinite.linearMap ℝ ℝ f u (f a)
  rw [FunOnFinite.linearMap_apply_apply]
  exact lt_of_lt_of_le (hu a) (Finset.single_le_sum
    (fun j hj => stdSimplex.zero_le u j) (by simp))

/-- The adjunction's characteristic map is the same actual map as the
realized Yoneda simplex in the CW construction. -/
theorem simplexPoint_eq_yoneda (X : SSet.{u}) (n : ℕ) (x : X.obj (op ⦋n⦌))
    (u : stdSimplex ℝ (Fin (n + 1))) :
    simplexPoint X x u = SSet.toTop.map (SSet.yonedaEquiv.symm x)
      ((SimplexCategory.toTopHomeo ⦋n⦌).symm u) := by
  have h := sSetTopAdj_unit_app_app_down X (op ⦋n⦌) x
  exact congrArg (fun f : SimplexCategory.toTop.obj ⦋n⦌ ⟶ SSet.toTop.obj X => f (ULift.up u)) h

/-- The actual simplex interior is precisely the set of positive barycentric
coordinates, in the characteristic-map parametrization. -/
theorem simplex_interior_iff_positive (n : ℕ) (u : stdSimplex ℝ (Fin (n + 1))) :
    (SimplexCategory.toTopHomeo ⦋n⦌).symm u ∉ Set.range (SSet.toTop.map ∂Δ[n].ι) ↔
      ∀ i, 0 < u i := by
  have hr : (SimplexCategory.toTopHomeo ⦋n⦌).symm u ∈
      Set.range (SSet.toTop.map ∂Δ[n].ι) ↔ ∃ i, u i = 0 := by
    rw [← KIP126.Topology.SimplicialRealization.boundary_realization_range n u]
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨x, (congrArg (SimplexCategory.toTopHomeo ⦋n⦌) hx).trans
        ((SimplexCategory.toTopHomeo ⦋n⦌).apply_symm_apply u)⟩
    · rintro ⟨x, hx⟩
      exact ⟨x, (SimplexCategory.toTopHomeo ⦋n⦌).injective
        (hx.trans ((SimplexCategory.toTopHomeo ⦋n⦌).apply_symm_apply u).symm)⟩
  rw [hr, not_exists]
  constructor
  · intro h i
    exact lt_of_le_of_ne (stdSimplex.zero_le u i) (Ne.symm (h i))
  · intro h i
    exact ne_of_gt (h i)

/-- A positive weight at a preimage contributes positively to its pushforward. -/
theorem positive_weight_le_pushforward {n m : ℕ} (w : Fin n → ℝ)
    (hw : ∀ i, 0 ≤ w i) (f : Fin n → Fin m) (i : Fin n) :
    w i ≤ FunOnFinite.linearMap ℝ ℝ f w (f i) := by
  classical
  rw [FunOnFinite.linearMap_apply_apply]
  exact Finset.single_le_sum (fun j hj => hw j) (by simp)

/-- A monotone map has no mass below the image of its first vertex. -/
theorem monotone_pushforward_eq_zero_below {n m : ℕ} (w : Fin (n + 1) → ℝ)
    (f : Fin (n + 1) →o Fin m) (j : Fin m) (hj : j < f 0) :
    FunOnFinite.linearMap ℝ ℝ f w j = 0 := by
  classical
  rw [FunOnFinite.linearMap_apply_apply]
  apply Finset.sum_eq_zero
  intro i hi
  have hfi : f i = j := (Finset.mem_filter.mp hi).2
  have h0i := f.monotone (Fin.zero_le i)
  rw [hfi] at h0i
  exact False.elim (not_lt_of_ge h0i hj)

/-- Strictly positive source weights determine a monotone vertex map from
its barycentric pushforward, including all of its degeneracy positions. -/
theorem monotone_weight_pushforward_injective {n m : ℕ} (w : Fin n → ℝ)
    (hw : ∀ i, 0 < w i) (f g : Fin n →o Fin m)
    (h : FunOnFinite.linearMap ℝ ℝ f w = FunOnFinite.linearMap ℝ ℝ g w) : f = g := by
  induction n with
  | zero =>
    apply OrderHom.ext
    funext i
    exact Fin.elim0 i
  | succ n ih =>
    have h0 : f 0 = g 0 := by
      rcases lt_trichotomy (f 0) (g 0) with hfg | he | hgf
      · have hp := lt_of_lt_of_le (hw 0) (positive_weight_le_pushforward w (fun i => (hw i).le) f 0)
        rw [h, monotone_pushforward_eq_zero_below w g (f 0) hfg] at hp
        exact False.elim (lt_irrefl _ hp)
      · exact he
      · have hp := lt_of_lt_of_le (hw 0) (positive_weight_le_pushforward w (fun i => (hw i).le) g 0)
        rw [← h, monotone_pushforward_eq_zero_below w f (g 0) hgf] at hp
        exact False.elim (lt_irrefl _ hp)
    let f' : Fin n →o Fin m := ⟨fun i => f i.succ,
      fun i j hij => f.monotone (Fin.succ_le_succ_iff.mpr hij)⟩
    let g' : Fin n →o Fin m := ⟨fun i => g i.succ,
      fun i j hij => g.monotone (Fin.succ_le_succ_iff.mpr hij)⟩
    have ht : FunOnFinite.linearMap ℝ ℝ f' (fun i => w i.succ) =
        FunOnFinite.linearMap ℝ ℝ g' (fun i => w i.succ) := by
      classical
      funext j
      have he := congrFun h j
      simp only [FunOnFinite.linearMap_apply_apply, Finset.sum_filter, Fin.sum_univ_succ, h0] at he
      have he' := add_left_cancel he
      simpa only [FunOnFinite.linearMap_apply_apply, Finset.sum_filter, f', g', OrderHom.coe_mk] using he'
    have he := ih (fun i => w i.succ) (fun i => hw i.succ) f' g' ht
    apply OrderHom.ext
    funext i
    induction i using Fin.cases with
    | zero => exact h0
    | succ i => exact DFunLike.congr_fun he i

/-- At strictly positive fixed barycentric coordinates, distinct simplices
have distinct realization points, even when those simplices are degenerate. -/
theorem simplexPoint_injective_of_positive (X : SSet.{u}) (n : ℕ)
    (u : stdSimplex ℝ (Fin (n + 1))) (hu : ∀ i, 0 < u i) :
    Function.Injective (fun x : X.obj (op ⦋n⦌) => simplexPoint X x u) := by
  intro x x' hxx'
  obtain ⟨m, f, hf, y, hy⟩ := X.exists_nonDegenerate x
  obtain ⟨l, g, hg, z, hz⟩ := X.exists_nonDegenerate x'
  let v := stdSimplex.map f.toOrderHom u
  let w := stdSimplex.map g.toOrderHom u
  have hv : ∀ i, 0 < v i := simplex_map_positive f.toOrderHom
    (SimplexCategory.epi_iff_surjective.mp hf) u hu
  have hw : ∀ i, 0 < w i := simplex_map_positive g.toOrderHom
    (SimplexCategory.epi_iff_surjective.mp hg) u hu
  have ht := (simplex_interior_iff_positive m v).mpr hv
  have ht' := (simplex_interior_iff_positive l w).mpr hw
  have he : SSet.toTop.map (SSet.yonedaEquiv.symm y.val)
      ((SimplexCategory.toTopHomeo ⦋m⦌).symm v) =
      SSet.toTop.map (SSet.yonedaEquiv.symm z.val)
        ((SimplexCategory.toTopHomeo ⦋l⦌).symm w) := by
    rw [← simplexPoint_eq_yoneda, ← simplexPoint_eq_yoneda]
    change simplexPoint X y.val (stdSimplex.map f.toOrderHom u) =
      simplexPoint X z.val (stdSimplex.map g.toOrderHom u)
    rw [← simplexPoint_naturality, ← simplexPoint_naturality, ← hy, ← hz]
    exact hxx'
  obtain ⟨hml, hyz, hvw⟩ := KIP126.Topology.SimplicialRealization.nondegenerate_interior_unique X
    y z _ _ ht ht' he
  subst l
  have hyz' : y = z := eq_of_heq hyz
  have hvw' : v = w := (SimplexCategory.toTopHomeo ⦋m⦌).symm.injective (eq_of_heq hvw)
  have hfg : f = g := by
    apply SimplexCategory.Hom.ext
    exact monotone_weight_pushforward_injective u hu f.toOrderHom g.toOrderHom
      (congrArg Subtype.val hvw')
  rw [hy, hz, hfg, hyz']

/-- The realized inclusion equalizes the actual maps pointwise. -/
theorem equalitySubcomplex_realization_eq {X Y : SSet.{u}} (f g : X ⟶ Y)
    (x : |(equalitySubcomplex f g).toSSet|) :
    SSet.toTop.map f (SSet.toTop.map (equalitySubcomplex f g).ι x) =
      SSet.toTop.map g (SSet.toTop.map (equalitySubcomplex f g).ι x) := by
  have he : (equalitySubcomplex f g).ι ≫ f = (equalitySubcomplex f g).ι ≫ g := by
    ext a z
    exact z.property
  have h := congrArg SSet.toTop.map he
  rw [Functor.map_comp, Functor.map_comp] at h
  exact ConcreteCategory.congr_hom h x

/-- Equality of the actual realized maps is detected in a positive simplex,
so every point of their topological equalizer comes from the actual
simplicial equalizer. -/
theorem equalitySubcomplex_realization_range {X Y : SSet.{u}} (f g : X ⟶ Y) (x : |X|) :
    x ∈ Set.range (SSet.toTop.map (equalitySubcomplex f g).ι) ↔
      SSet.toTop.map f x = SSet.toTop.map g x := by
  constructor
  · rintro ⟨y, rfl⟩
    exact equalitySubcomplex_realization_eq f g y
  · intro hx
    obtain ⟨n,s,t,ht,he⟩ := exists_nondegenerate_interior X x
    let u := SimplexCategory.toTopHomeo ⦋n⦌ t
    have htu : (SimplexCategory.toTopHomeo ⦋n⦌).symm u = t :=
      (SimplexCategory.toTopHomeo ⦋n⦌).symm_apply_apply t
    have hu : ∀ i, 0 < u i := (simplex_interior_iff_positive n u).mp (by rw [htu]; exact ht)
    have hs : simplexPoint X s.val u = x := by rw [simplexPoint_eq_yoneda,htu]; exact he
    have hfg : f.app (op ⦋n⦌) s.val = g.app (op ⦋n⦌) s.val := by
      apply simplexPoint_injective_of_positive Y n u hu
      dsimp only
      rw [← simplexPoint_map,← simplexPoint_map,hs]
      exact hx
    let z : (equalitySubcomplex f g).toSSet.obj (op ⦋n⦌) := ⟨s.val,hfg⟩
    refine ⟨simplexPoint (equalitySubcomplex f g).toSSet z u,?_⟩
    rw [simplexPoint_map]
    exact hs

theorem equalityComparison_isClosedEmbedding {X Y : SSet.{u}} (f g : X ⟶ Y) :
    _root_.Topology.IsClosedEmbedding (equalityComparison f g) := by
  exact (realization_mono_isClosedEmbedding (equalitySubcomplex f g).ι).of_comp
    _root_.Topology.IsEmbedding.subtypeVal

theorem equalityComparison_surjective {X Y : SSet.{u}} (f g : X ⟶ Y) :
    Function.Surjective (equalityComparison f g) := by
  intro x
  obtain ⟨y,hy⟩ := (equalitySubcomplex_realization_range f g x.val).mpr x.property
  exact ⟨y,Subtype.ext hy⟩

end KIP126.Topology.SimplicialRealization
