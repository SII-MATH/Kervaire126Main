module

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.Product.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.Simplex.MonotoneCoupling.Representation.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.Simplex.MonotoneCoupling.Uniqueness

@[expose] section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory MonoidalCategory Simplicial Opposite

universe u

set_option backward.isDefEq.respectTransparency false

/-- The realized Yoneda map of a standard simplex is its barycentric
vertex map, with the exact naturality of the actual realization. -/
theorem realized_standard_yoneda_apply {n p : ℕ}
    (z : (Δ[p] : SSet.{u}).obj (op ⦋n⦌)) (t : |(Δ[n] : SSet.{u})|) :
    SimplexCategory.toTopHomeo ⦋p⦌ (SSet.toTop.map (SSet.yonedaEquiv.symm z) t) =
      stdSimplex.map (SSet.stdSimplex.objEquiv z) (SimplexCategory.toTopHomeo ⦋n⦌ t) := by
  have he : SSet.yonedaEquiv.symm z = SSet.stdSimplex.map (SSet.stdSimplex.objEquiv z) := by
    apply SSet.yonedaEquiv.injective
    rw [Equiv.apply_symm_apply,SSet.yonedaEquiv_map,Equiv.symm_apply_apply]
  rw [he]
  exact SimplexCategory.toTopHomeo_naturality_apply _ _

/-- On each actual simplex of the product, the comparison is given by
the two barycentric marginal maps. -/
theorem stdSimplexProductComparison_simplex {p q n : ℕ}
    (z : (Δ[p] ⊗ Δ[q] : SSet.{u}).obj (op ⦋n⦌)) (t : |(Δ[n] : SSet.{u})|) :
    stdSimplexProductComparison p q (SSet.toTop.map (SSet.yonedaEquiv.symm z) t) =
      (stdSimplex.map (fun i => (SSet.prodStdSimplex.objEquiv z i).1)
        (SimplexCategory.toTopHomeo ⦋n⦌ t),
       stdSimplex.map (fun i => (SSet.prodStdSimplex.objEquiv z i).2)
        (SimplexCategory.toTopHomeo ⦋n⦌ t)) := by
  apply Prod.ext
  · change SimplexCategory.toTopHomeo ⦋p⦌
      ((SSet.toTop.map (SSet.yonedaEquiv.symm z) ≫ SSet.toTop.map (fst Δ[p] Δ[q])) t) = _
    rw [← Functor.map_comp,SSet.yonedaEquiv_symm_comp]
    exact realized_standard_yoneda_apply z.1 t
  · change SimplexCategory.toTopHomeo ⦋q⦌
      ((SSet.toTop.map (SSet.yonedaEquiv.symm z) ≫ SSet.toTop.map (snd Δ[p] Δ[q])) t) = _
    rw [← Functor.map_comp,SSet.yonedaEquiv_symm_comp]
    exact realized_standard_yoneda_apply z.2 t

/-- Every pair of points in two geometric simplices is realized by an
actual simplex of their simplicial product. -/
theorem stdSimplexProductComparison_surjective (p q : ℕ) :
    Function.Surjective (stdSimplexProductComparison.{u} p q) := by
  rintro ⟨x,y⟩
  obtain ⟨w,hw₁,hw₂,hw⟩ := Simplex.exists_chain_coupling x y
  obtain ⟨n,f,hf,v,hv,hfv⟩ := Simplex.exists_ordered_simplex_representation w hw
  let z : (Δ[p] ⊗ Δ[q] : SSet.{u}).obj (op ⦋n⦌) := SSet.prodStdSimplex.objEquiv.symm f
  let t := (SimplexCategory.toTopHomeo ⦋n⦌).symm v
  refine ⟨SSet.toTop.map (SSet.yonedaEquiv.symm z) t,?_⟩
  rw [stdSimplexProductComparison_simplex]
  change (stdSimplex.map (fun i => (SSet.prodStdSimplex.objEquiv z i).1)
      ((SimplexCategory.toTopHomeo ⦋n⦌) ((SimplexCategory.toTopHomeo ⦋n⦌).symm v)),
    stdSimplex.map (fun i => (SSet.prodStdSimplex.objEquiv z i).2)
      ((SimplexCategory.toTopHomeo ⦋n⦌) ((SimplexCategory.toTopHomeo ⦋n⦌).symm v))) = _
  rw [Homeomorph.apply_symm_apply]
  have hz : SSet.prodStdSimplex.objEquiv z = f := Equiv.apply_symm_apply _ f
  rw [hz]
  apply Prod.ext
  · exact (stdSimplex.map_comp_apply f Prod.fst v).symm.trans ((congrArg (stdSimplex.map Prod.fst) hfv).trans hw₁)
  · exact (stdSimplex.map_comp_apply f Prod.snd v).symm.trans ((congrArg (stdSimplex.map Prod.snd) hfv).trans hw₂)

/-- The positive coordinates of a nondegenerate interior point are its
actual barycentric coordinates in the standard simplex homeomorphism. -/
theorem simplex_coordinates_pos_of_interior {n : ℕ} (t : |(Δ[n] : SSet.{u})|)
    (ht : t ∉ Set.range (SSet.toTop.map ∂Δ[n].ι)) :
    ∀ i, 0 < (SimplexCategory.toTopHomeo ⦋n⦌ t) i := by
  intro i
  have hn : (SimplexCategory.toTopHomeo ⦋n⦌ t) i ≠ 0 := fun h =>
    ht ((simplex_mem_boundary_iff n t).mpr ⟨i,h⟩)
  exact lt_of_le_of_ne (stdSimplex.zero_le _ _) hn.symm

/-- The actual comparison for two standard simplices is injective:
a point determines its unique chain-supported joint barycentric distribution. -/
theorem stdSimplexProductComparison_injective (p q : ℕ) :
    Function.Injective (stdSimplexProductComparison.{u} p q) := by
  intro x y hxy
  obtain ⟨n,s,t,ht,hsx⟩ := exists_nondegenerate_interior (Δ[p] ⊗ Δ[q]) x
  obtain ⟨m,s',t',ht',hsy⟩ := exists_nondegenerate_interior (Δ[p] ⊗ Δ[q]) y
  let f := SSet.prodStdSimplex.objEquiv s.1
  let g := SSet.prodStdSimplex.objEquiv s'.1
  have hf : Function.Injective f :=
    (SSet.prodStdSimplex.nonDegenerate_iff_injective_objEquiv s.1).mp s.2
  have hg : Function.Injective g :=
    (SSet.prodStdSimplex.nonDegenerate_iff_injective_objEquiv s'.1).mp s'.2
  let v := SimplexCategory.toTopHomeo ⦋n⦌ t
  let v' := SimplexCategory.toTopHomeo ⦋m⦌ t'
  have hv : ∀ i, 0 < v i := simplex_coordinates_pos_of_interior t ht
  have hv' : ∀ i, 0 < v' i := simplex_coordinates_pos_of_interior t' ht'
  let w := stdSimplex.map f v
  let w' := stdSimplex.map g v'
  have hw : IsChain (· ≤ ·) {a | 0 < w a} := by
    rw [show {a | 0 < w a} = Set.range f from Simplex.positive_support_map_of_injective f hf v hv]
    exact f.monotone.isChain_range
  have hw' : IsChain (· ≤ ·) {a | 0 < w' a} := by
    rw [show {a | 0 < w' a} = Set.range g from Simplex.positive_support_map_of_injective g hg v' hv']
    exact g.monotone.isChain_range
  have hx : stdSimplexProductComparison p q x =
      (stdSimplex.map Prod.fst w,stdSimplex.map Prod.snd w) := by
    rw [← hsx,stdSimplexProductComparison_simplex]
    change (stdSimplex.map (Prod.fst ∘ f) v,stdSimplex.map (Prod.snd ∘ f) v) = _
    rw [← stdSimplex.map_comp_apply,← stdSimplex.map_comp_apply]
  have hy : stdSimplexProductComparison p q y =
      (stdSimplex.map Prod.fst w',stdSimplex.map Prod.snd w') := by
    rw [← hsy,stdSimplexProductComparison_simplex]
    change (stdSimplex.map (Prod.fst ∘ g) v',stdSimplex.map (Prod.snd ∘ g) v') = _
    rw [← stdSimplex.map_comp_apply,← stdSimplex.map_comp_apply]
  rw [hx,hy] at hxy
  have hww : w = w' := Simplex.chain_coupling_unique w w' hw hw'
    (congrArg Prod.fst hxy) (congrArg Prod.snd hxy)
  obtain ⟨hn,hfg,hvv⟩ := Simplex.ordered_simplex_representation_unique f g hf hg v v' hv hv' hww
  subst m
  have hss : s = s' := Subtype.ext (SSet.prodStdSimplex.objEquiv.injective (eq_of_heq hfg))
  have htt : t = t' := (SimplexCategory.toTopHomeo ⦋n⦌).injective (eq_of_heq hvv)
  exact hsx.symm.trans (by rw [hss,htt]; exact hsy)

/-- The standard-simplex product comparison is a genuine homeomorphism:
its actual continuous bijection has compact source and Hausdorff target. -/
theorem nonempty_stdSimplexProductHomeomorph (p q : ℕ) :
    ∃ e : |(Δ[p] ⊗ Δ[q] : SSet.{u})| ≃ₜ
      (stdSimplex ℝ (Fin (p+1)) × stdSimplex ℝ (Fin (q+1))),
      ∀ x, e x = stdSimplexProductComparison p q x := by
  letI := compactSpace_of_finite (Δ[p] ⊗ Δ[q] : SSet.{u})
  let e := Equiv.ofBijective _ ⟨stdSimplexProductComparison_injective.{u} p q,
      stdSimplexProductComparison_surjective p q⟩
  exact ⟨(stdSimplexProductComparison.{u} p q).continuous.homeoOfEquivCompactToT2 (f := e),
    fun _ => rfl⟩

end KIP126.Topology.SimplicialRealization
