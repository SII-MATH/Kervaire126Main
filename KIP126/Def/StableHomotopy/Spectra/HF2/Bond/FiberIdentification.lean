module

public import KIP126.Def.StableHomotopy.Spectra.HF2.Bond.Fiber
public import KIP126.Def.Topology.SimplicialRealization.Classical.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Spectra.HF2Bond
open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open scoped unitInterval
set_option backward.isDefEq.respectTransparency false

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


/-- A simplex with strictly positive barycentric coordinates realizes to the
zero vertex only when the whole simplex is the zero simplex. -/
theorem realizeSimplex_eq_zero_of_positive
    (A : SimplicialObject (ModuleCat.{0} (ZMod 2))) (n : ℕ)
    (z : A.obj (op ⦋n⦌)) (u : stdSimplex ℝ (Fin (n + 1)))
    (hu : ∀ i, 0 < u i)
    (hz : realizeSimplex (A ⋙ forget (ModuleCat (ZMod 2))) z u = moduleRealizationPoint A) : z = 0 := by
  let B : SSet.{0} := A ⋙ forget (ModuleCat (ZMod 2))
  obtain ⟨m, f, hf, y, hy⟩ := B.exists_nonDegenerate z
  let v := stdSimplex.map f.toOrderHom u
  have hv : ∀ i, 0 < v i := simplex_map_positive f.toOrderHom
    (SimplexCategory.epi_iff_surjective.mp hf) u hu
  have ht := (simplex_interior_iff_positive m v).mpr hv
  let v0 : stdSimplex ℝ (Fin 1) := stdSimplex.vertex 0
  have hv0 : ∀ i, 0 < v0 i := by
    intro i
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    norm_num [v0, stdSimplex.vertex]
  have ht0 := (simplex_interior_iff_positive 0 v0).mpr hv0
  let y0 : B.nonDegenerate 0 := ⟨0, by simp⟩
  have he : SSet.toTop.map (SSet.yonedaEquiv.symm y.val)
      ((SimplexCategory.toTopHomeo ⦋m⦌).symm v) =
      SSet.toTop.map (SSet.yonedaEquiv.symm y0.val)
        ((SimplexCategory.toTopHomeo ⦋0⦌).symm v0) := by
    rw [← realizeSimplex_eq_yoneda, ← realizeSimplex_eq_yoneda]
    change realizeSimplex B y.val (stdSimplex.map f.toOrderHom u) = realizeSimplex B (a := op ⦋0⦌) 0 v0
    rw [← realizeSimplex_naturality, ← hy]
    exact hz.trans (realizeSimplex_zero A (op ⦋0⦌) v0).symm
  obtain ⟨hm, hy0, _⟩ := KIP126.Topology.SimplicialRealization.nondegenerate_interior_unique B
    y y0 _ _ ht ht0 he
  subst m
  have hyz : y.val = (0 : A.obj (op ⦋0⦌)) := congrArg Subtype.val (eq_of_heq hy0)
  rw [hy, hyz]
  exact (A.map f.op).hom.map_zero

/-- Every point of the actual endpoint fiber is represented by a simplex of
the actual simplicial kernel; this uses the positive nondegenerate normal form. -/
theorem loopFiberComparison_surjective (n : ℕ) : Function.Surjective (loopFiberComparison n) := by
  intro x
  let A := hf2SimplicialModule (n + 1)
  let D := decalage (hf2SimplicialSet (n + 1))
  obtain ⟨r, z, t, ht, he⟩ :=
    KIP126.Topology.SimplicialRealization.exists_nondegenerate_interior D x.val
  let u := SimplexCategory.toTopHomeo ⦋r⦌ t
  have htu : (SimplexCategory.toTopHomeo ⦋r⦌).symm u = t :=
    (SimplexCategory.toTopHomeo ⦋r⦌).symm_apply_apply t
  have hu : ∀ i, 0 < u i := (simplex_interior_iff_positive r u).mp (by rw [htu]; exact ht)
  have hx : realizeSimplex D z.val u = x.val := by
    rw [realizeSimplex_eq_yoneda, htu]
    exact he
  have hz : (decalageProjection A).app (op ⦋r⦌) z.val = 0 := by
    apply realizeSimplex_eq_zero_of_positive A r _ u hu
    have h := (congrArg (SSet.toTop.map (decalageProjection (hf2SimplicialSet (n + 1))))) hx
    have h' := h.trans x.property
    rw [realizeSimplex_map] at h'
    exact h'
  obtain ⟨w, hw⟩ := (loopInclusion_range_iff n (op ⦋r⦌) z.val).mpr hz
  refine ⟨realizeSimplex (loopSet n) w u, ?_⟩
  apply Subtype.ext
  change SSet.toTop.map (loopSetInclusion n) (realizeSimplex (loopSet n) w u) = x.val
  rw [realizeSimplex_map]
  change realizeSimplex D ((loopInclusion n).app (op ⦋r⦌) w) u = x.val
  rw [hw]
  exact hx

/-- The realized simplicial loop kernel is homeomorphic to the actual
endpoint fiber, by the displayed kernel inclusion itself. -/
noncomputable def loopFiberHomeomorph (n : ℕ) :
    loopRealizationLevel n ≃ₜ pathProjectionFiber n :=
  (loopFiberComparison_isClosedEmbedding n).isEmbedding.toHomeomorphOfSurjective
    (loopFiberComparison_surjective n)

@[simp] theorem loopFiberHomeomorph_apply (n : ℕ) (x : loopRealizationLevel n) :
    loopFiberHomeomorph n x = loopFiberComparison n x := rfl

/-- With the actual fiber homeomorphism, the simplicial comparison is exactly
the topological connecting-loop map of the realized path projection. -/
theorem loopComparison_eq_fiberLoopComparison (n : ℕ) :
    loopComparison n = (fiberLoopComparison n).comp
      ⟨loopFiberHomeomorph n, (loopFiberHomeomorph n).continuous⟩ := by
  ext x t
  rfl


/-- The specified zero point of the actual topological endpoint fiber. -/
noncomputable def pathProjectionFiberPoint (n : ℕ) : pathProjectionFiber n :=
  ⟨(pathRealizationLevel (hf2SimplicialModule (n + 1))).point, by
    have h := loopRealizationInclusion_projection n (loopRealizationLevel n).point
    rwa [loopRealizationInclusion_point] at h⟩

/-- The actual fiber homeomorphism preserves the specified zero vertices. -/
@[simp] theorem loopFiberHomeomorph_point (n : ℕ) :
    loopFiberHomeomorph n (loopRealizationLevel n).point = pathProjectionFiberPoint n := by
  apply Subtype.ext
  exact loopRealizationInclusion_point n

/-- The topological connecting map preserves the specified basepoint. -/
@[simp] theorem fiberLoopComparison_point (n : ℕ) :
    fiberLoopComparison n (pathProjectionFiberPoint n) =
      Path.refl (hf2RealizationLevel (n + 1)).point := by
  rw [← loopFiberHomeomorph_point]
  exact (fiberLoopComparison_loopFiberComparison n _).trans (loopComparison_point n)

end KIP126.StableHomotopy.Spectra.HF2Bond
