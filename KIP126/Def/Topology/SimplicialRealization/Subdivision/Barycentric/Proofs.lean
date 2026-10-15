module

public import KIP126.Def.Topology.SimplicialRealization.Subdivision.Barycentric.Data
public import KIP126.Def.Topology.SimplicialRealization.Equalizer.Proofs
public import KIP126.Def.Topology.SimplicialRealization.Boundary.Proofs
public import KIP126.Def.Topology.SimplicialRealization.Subdivision.Proofs

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory Simplicial Opposite
open scoped unitInterval

universe u

set_option backward.isDefEq.respectTransparency false

/-- The actual adjunction extension evaluates a characteristic simplex
by its prescribed singular simplex. -/
theorem adjunction_symm_simplex {K : SSet.{u}} (B : TopCat.{u})
    (f : K ⟶ TopCat.toSSet.obj B) {d : SimplexCategoryᵒᵖ} (s : K.obj d)
    (t : stdSimplex ℝ (Fin (d.unop.len+1))) :
    (sSetTopAdj.homEquiv K B).symm f (simplexPoint K s t) =
      B.toSSetObjEquiv d (f.app d s) t := by
  have h := (sSetTopAdj.homEquiv K B).apply_symm_apply f
  rw [Adjunction.homEquiv_unit] at h
  exact congrArg (fun z => B.toSSetObjEquiv d z t)
    (ConcreteCategory.congr_hom (NatTrans.congr_app h d) s)

/-- Barycentric projection on each actual flag simplex is precisely the
weighted sum of its face barycenters. -/
theorem simplexSubdivisionBarycentric_simplex (n : SimplexCategory)
    {d : SimplexCategoryᵒᵖ} (s : (SimplexCategory.sd.{u}.obj n).obj d)
    (t : stdSimplex ℝ (Fin (d.unop.len+1))) :
    simplexSubdivisionBarycentric n (simplexPoint _ s t) =
      simplexCombination (fun k => finiteChainBarycenter n (s.obj k)) t := by
  exact congrArg ULift.down
    (adjunction_symm_simplex _ (simplexSubdivisionBarycentricAdjoint n) s t)

/-- A face barycenter has constant positive mass on that face and zero
mass elsewhere. -/
theorem finiteChainBarycenter_apply (n : SimplexCategory)
    (c : PartialOrder.NonemptyFiniteChains (ULift.{u} (Fin (n.len+1))))
    (j : Fin (n.len+1)) :
    finiteChainBarycenter n c j =
      if ULift.up j ∈ c.finset then (c.finset.card : ℝ)⁻¹ else 0 := by
  classical
  letI : Nonempty c.finset := c.nonempty.to_subtype
  let f : c.finset → Fin (n.len+1) := fun x => x.val.down
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    exact ULift.down_injective hab
  by_cases hj : ULift.up j ∈ c.finset
  · rw [if_pos hj]
    have h := simplex_map_apply_injective f hf
      (stdSimplex.barycenter : stdSimplex ℝ c.finset) ⟨ULift.up j,hj⟩
    change finiteChainBarycenter n c j = _ at h
    exact h.trans (by
      change ((Fintype.card c.finset : ℝ)⁻¹) = _
      rw [Fintype.card_coe])
  · rw [if_neg hj]
    apply simplex_map_apply_not_range f
    rintro ⟨a,ha⟩
    exact hj (by simpa only [← ha,ULift.up_down] using a.property)

/-- Injective vertex maps preserve uniform face barycenters. This is the
face-naturality needed for geometric subdivision; no degeneracy claim
is made for these barycenters. -/
theorem finiteChainBarycenter_map_injective {n m : SimplexCategory}
    (f : n ⟶ m) (hf : Function.Injective f)
    (c : PartialOrder.NonemptyFiniteChains (ULift.{u} (Fin (n.len+1)))) :
    stdSimplex.map f (finiteChainBarycenter n c) =
      finiteChainBarycenter m (c.map (SimplexCategory.toPartOrd.map f).hom) := by
  classical
  letI : DecidableEq (ULift.{u} (Fin (m.len+1))) := Classical.decEq _
  let g : ULift.{u} (Fin (n.len+1)) →o ULift.{u} (Fin (m.len+1)) := {
    toFun := fun x => ULift.up (f x.down)
    monotone' := fun _ _ h => f.toOrderHom.monotone h }
  have hg : Function.Injective g := by
    intro a b h
    exact ULift.down_injective (hf (congrArg ULift.down h))
  have hc : (c.map g).finset.card = c.finset.card := by
    exact Finset.card_image_of_injective c.finset hg
  have hmem (k : Fin (n.len+1)) :
      ULift.up (f k) ∈ (c.map g).finset ↔ ULift.up k ∈ c.finset := by
    rw [PartialOrder.NonemptyFiniteChains.mem_map_iff]
    constructor
    · rintro ⟨a,ha,he⟩
      have he' : a = ULift.up k := hg he
      simpa only [he'] using ha
    · intro h
      exact ⟨ULift.up k,h,rfl⟩
  apply stdSimplex.ext
  funext j
  change stdSimplex.map f (finiteChainBarycenter n c) j = finiteChainBarycenter m (c.map g) j
  by_cases hj : j ∈ Set.range f
  · obtain ⟨k,rfl⟩ := hj
    rw [simplex_map_apply_injective f hf,finiteChainBarycenter_apply,
      finiteChainBarycenter_apply,hc]
    simp only [hmem]
  · rw [simplex_map_apply_not_range f _ j hj,finiteChainBarycenter_apply,if_neg]
    intro h
    obtain ⟨a,_,ha⟩ := (PartialOrder.NonemptyFiniteChains.mem_map_iff c g (ULift.up j)).mp h
    exact hj ⟨a.down,congrArg ULift.down ha⟩

/-- Pushing forward the actual affine combination commutes with arbitrary
vertex maps, including maps that identify vertices. -/
theorem simplexCombination_map {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (f : B → C) (v : A → stdSimplex ℝ B) (t : stdSimplex ℝ A) :
    stdSimplex.map f (simplexCombination v t) =
      simplexCombination (fun a => stdSimplex.map f (v a)) t := by
  apply stdSimplex.ext
  exact Simplex.combinationCoordinates_map_target f v t

/-- The actual barycentric projection commutes with every face inclusion. -/
theorem simplexSubdivisionBarycentric_face_natural {n m : SimplexCategory}
    (f : n ⟶ m) (hf : Function.Injective f)
    (x : |SimplexCategory.sd.{u}.obj n|) :
    simplexSubdivisionBarycentric m (SSet.toTop.map (SimplexCategory.sd.map f) x) =
      stdSimplex.map f (simplexSubdivisionBarycentric n x) := by
  obtain ⟨s,t,rfl⟩ := exists_nondegenerate_simplex (SimplexCategory.sd.obj n) x
  let u := SimplexCategory.toTopHomeo ⦋s.dim⦌ t
  have hu : SSet.toTop.map (SSet.yonedaEquiv.symm s.simplex) t =
      simplexPoint _ s.simplex u := by
    rw [simplexPoint_eq_yoneda]
    exact congrArg (SSet.toTop.map (SSet.yonedaEquiv.symm s.simplex))
      ((SimplexCategory.toTopHomeo ⦋s.dim⦌).symm_apply_apply t).symm
  rw [hu,simplexPoint_map,simplexSubdivisionBarycentric_simplex,
    simplexSubdivisionBarycentric_simplex,simplexCombination_map]
  apply congrArg (fun v => simplexCombination v u)
  funext k
  exact (finiteChainBarycenter_map_injective f hf (s.simplex.obj k)).symm

/-- The geometric barycentric projection is homotopic to the actual
simplicial last-vertex map. Every common zero coordinate stays zero
throughout the homotopy, so their common faces are preserved. -/
theorem exists_simplexSubdivisionBarycentric_homotopy (n : SimplexCategory) :
    ∃ H : (simplexSubdivisionBarycentric.{u} n).Homotopy
      ((⟨SimplexCategory.toTopHomeo n,(SimplexCategory.toTopHomeo n).continuous⟩ :
        C(|SSet.stdSimplex.obj n|,stdSimplex ℝ (Fin (n.len+1)))).comp
          (SSet.toTop.map (simplexSubdivisionLastVertex n)).hom),
      ∀ (t : I) (x : |SimplexCategory.sd.{u}.obj n|) (j : Fin (n.len+1)),
        simplexSubdivisionBarycentric n x j = 0 →
        (SimplexCategory.toTopHomeo n (SSet.toTop.map (simplexSubdivisionLastVertex n) x)) j = 0 →
        H (t,x) j = 0 := by
  let a := simplexSubdivisionBarycentric.{u} n
  let b : C(|SimplexCategory.sd.{u}.obj n|,stdSimplex ℝ (Fin (n.len+1))) :=
    (⟨SimplexCategory.toTopHomeo n,(SimplexCategory.toTopHomeo n).continuous⟩ :
      C(|SSet.stdSimplex.obj n|,_)).comp (SSet.toTop.map (simplexSubdivisionLastVertex n)).hom
  let h (z : I × |SimplexCategory.sd.{u}.obj n|) (j : Fin (n.len+1)) : ℝ :=
    (1 - (z.1 : ℝ)) * a z.2 j + (z.1 : ℝ) * b z.2 j
  have hn (z) (j) : 0 ≤ h z j :=
    add_nonneg (mul_nonneg (sub_nonneg.mpr z.1.property.2) ((a z.2).property.1 j))
      (mul_nonneg z.1.property.1 ((b z.2).property.1 j))
  have hs (z) : ∑ j, h z j = 1 := by
    simp only [h,Finset.sum_add_distrib,← Finset.mul_sum,stdSimplex.sum_eq_one,mul_one]
    ring
  have hc : Continuous h := by
    apply continuous_pi
    intro j
    exact ((continuous_const.sub continuous_fst.subtype_val).mul
      ((continuous_apply j).comp (a.continuous.subtype_val.comp continuous_snd))).add
      (continuous_fst.subtype_val.mul
        ((continuous_apply j).comp (b.continuous.subtype_val.comp continuous_snd)))
  let H : a.Homotopy b := {
    toFun := fun z => ⟨h z,hn z,hs z⟩
    continuous_toFun := hc.subtype_mk _
    map_zero_left := by
      intro x
      apply stdSimplex.ext
      funext j
      change (1 - (0 : ℝ)) * a x j + (0 : ℝ) * b x j = (a x).val j
      simp only [sub_zero,one_mul,zero_mul,add_zero]
      rfl
    map_one_left := by
      intro x
      apply stdSimplex.ext
      funext j
      change (1 - (1 : ℝ)) * a x j + (1 : ℝ) * b x j = (b x).val j
      simp only [sub_self,zero_mul,one_mul,zero_add]
      rfl }
  refine ⟨H,?_⟩
  intro t x j ha hb
  change (1 - (t : ℝ)) * a x j + (t : ℝ) * b x j = 0
  change a x j = 0 at ha
  change b x j = 0 at hb
  rw [ha,hb,mul_zero,mul_zero,add_zero]

/-- Last-vertex realization stays in every face containing the geometric
barycentric projection. This uses positivity of the unique open flag
containing a point, rather than an extra boundary hypothesis. -/
theorem simplexSubdivisionBarycentric_zero_lastVertex (n : SimplexCategory)
    (x : |SimplexCategory.sd.{u}.obj n|) (j : Fin (n.len+1))
    (hx : simplexSubdivisionBarycentric n x j = 0) :
    SimplexCategory.toTopHomeo n
      (SSet.toTop.map (simplexSubdivisionLastVertex n) x) j = 0 := by
  classical
  obtain ⟨d,s,t,ht,he⟩ := exists_nondegenerate_interior (SimplexCategory.sd.obj n) x
  let w := SimplexCategory.toTopHomeo ⦋d⦌ t
  have htw : (SimplexCategory.toTopHomeo ⦋d⦌).symm w = t :=
    (SimplexCategory.toTopHomeo ⦋d⦌).symm_apply_apply t
  have hw : ∀ k, 0 < w k := (simplex_interior_iff_positive d w).mp (by rw [htw]; exact ht)
  have hs : simplexPoint _ s.val w = x := by
    rw [simplexPoint_eq_yoneda,htw]
    exact he
  rw [← hs,simplexSubdivisionBarycentric_simplex] at hx
  change Simplex.combinationCoordinates
    (fun k => finiteChainBarycenter n (s.val.obj k)) w j = 0 at hx
  have hz := (Simplex.combinationCoordinates_eq_zero_iff _ w j).mp hx
  have hn (k : Fin (d+1)) : ULift.up j ∉ (s.val.obj k).finset := by
    have hzk := (hz k).resolve_left (ne_of_gt (hw k))
    rw [finiteChainBarycenter_apply] at hzk
    intro hj
    rw [if_pos hj] at hzk
    have hc : (0 : ℝ) < ((s.val.obj k).finset.card : ℝ) :=
      Nat.cast_pos.mpr (Finset.card_pos.mpr (s.val.obj k).nonempty)
    exact (ne_of_gt (inv_pos.mpr hc)) hzk
  rw [← hs,simplexSubdivisionLastVertex_simplex]
  apply simplex_map_apply_not_range
  rintro ⟨k,hk⟩
  apply hn k
  let c : PartialOrder.NonemptyFiniteChains (ULift.{u} (Fin (n.len+1))) := s.val.obj k
  have hm := Finset.max'_mem c.finset c.nonempty
  have heq : c.finset.max' c.nonempty = ULift.up j :=
    ULift.down_injective hk
  exact heq ▸ hm

/-- The geometric subdivision and last-vertex comparison are joined by
an actual homotopy preserving every face of the geometric projection. -/
theorem exists_simplexSubdivisionBarycentric_face_homotopy (n : SimplexCategory) :
    ∃ H : (simplexSubdivisionBarycentric.{u} n).Homotopy
      ((⟨SimplexCategory.toTopHomeo n,(SimplexCategory.toTopHomeo n).continuous⟩ :
        C(|SSet.stdSimplex.obj n|,stdSimplex ℝ (Fin (n.len+1)))).comp
          (SSet.toTop.map (simplexSubdivisionLastVertex n)).hom),
      ∀ (t : I) (x : |SimplexCategory.sd.{u}.obj n|) (j : Fin (n.len+1)),
        simplexSubdivisionBarycentric n x j = 0 → H (t,x) j = 0 := by
  obtain ⟨H,hH⟩ := exists_simplexSubdivisionBarycentric_homotopy.{u} n
  exact ⟨H,fun t x j h => hH t x j h (simplexSubdivisionBarycentric_zero_lastVertex n x j h)⟩

end KIP126.Topology.SimplicialRealization
