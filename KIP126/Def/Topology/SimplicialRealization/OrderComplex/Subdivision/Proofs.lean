module

public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.Subdivision.Data
public import KIP126.Def.Topology.Simplex.BarycentricDecomposition.Uniqueness.Proofs

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory Simplicial Opposite
open scoped Classical

universe u

set_option backward.isDefEq.respectTransparency false

/-- The uniform chain barycenter has its expected positive coordinates. -/
theorem orderChainBarycenter_apply (P : Type u) [PartialOrder P] [Fintype P]
    (c : PartialOrder.NonemptyFiniteChains P) (p : P) :
    orderChainBarycenter P c p = if p ∈ c.finset then (c.finset.card : ℝ)⁻¹ else 0 := by
  classical
  letI : Nonempty c.finset := c.nonempty.to_subtype
  by_cases hp : p ∈ c.finset
  · rw [if_pos hp]
    have h := simplex_map_apply_injective (fun a : c.finset => a.val) Subtype.val_injective
      (stdSimplex.barycenter : stdSimplex ℝ c.finset) ⟨p,hp⟩
    change orderChainBarycenter P c p = _ at h
    exact h.trans (by change ((Fintype.card c.finset : ℝ)⁻¹) = _; rw [Fintype.card_coe])
  · rw [if_neg hp]
    apply simplex_map_apply_not_range (fun a : c.finset => a.val)
    rintro ⟨a,rfl⟩
    exact hp a.property

/-- The actual geometric subdivision projection is affine on each flag. -/
theorem orderSubdivisionCoordinates_simplex (P : Type u) [PartialOrder P] [Fintype P]
    {d : SimplexCategoryᵒᵖ} (s : (nerve (PartialOrder.NonemptyFiniteChains P)).obj d)
    (w : stdSimplex ℝ (Fin (d.unop.len+1))) :
    orderSubdivisionCoordinates P (simplexPoint _ s w) =
      simplexCombination (fun k => orderChainBarycenter P (s.obj k)) w :=
  adjunction_symm_simplex _ (orderSubdivisionCoordinatesAdjoint P) s w

/-- Every actual subdivided order-complex point is supported on the
largest chain in one of its representing flags. -/
theorem orderSubdivisionCoordinates_hasChainSupport (P : Type u)
    [PartialOrder P] [Fintype P] (x : |nerve (PartialOrder.NonemptyFiniteChains P)|) :
    HasChainSupport (orderSubdivisionCoordinates P x) := by
  classical
  obtain ⟨d,s,t,_,he⟩ := exists_nondegenerate_interior
    (nerve (PartialOrder.NonemptyFiniteChains P)) x
  let w := SimplexCategory.toTopHomeo ⦋d⦌ t
  have hs : simplexPoint _ s.val w = x := by
    rw [simplexPoint_eq_yoneda]
    simpa only [w,Homeomorph.symm_apply_apply] using he
  rw [← hs,orderSubdivisionCoordinates_simplex]
  let c := s.val.obj (Fin.last d)
  have hmem (p : P)
      (hp : 0 < simplexCombination (fun k => orderChainBarycenter P (s.val.obj k)) w p) :
      p ∈ c.finset := by
    by_contra hn
    have hz (k : Fin (d+1)) : orderChainBarycenter P (s.val.obj k) p = 0 := by
      rw [orderChainBarycenter_apply,if_neg]
      exact fun h => hn (s.val.monotone (Fin.le_last k) h)
    exact (ne_of_gt hp) (Simplex.combinationCoordinates_zero _ w p hz)
  intro p q hp hq
  exact c.comparable ⟨p,hmem p hp⟩ ⟨q,hmem q hq⟩

/-- Every chain-supported simplex point has an actual preimage in the
flag subdivision, obtained from its positive coordinate levels. -/
theorem orderSubdivisionCoordinates_preimage (P : Type u) [PartialOrder P] [Fintype P]
    (y : stdSimplex ℝ P) (hy : HasChainSupport y) :
    ∃ x : |nerve (PartialOrder.NonemptyFiniteChains P)|,
      orderSubdivisionCoordinates P x = y := by
  classical
  obtain ⟨m,hm,c,w,hc,hmono,hw,hrecon⟩ :=
    Simplex.BarycentricDecomposition.exists_strict_flag y
  have hpos (k : Fin m) (p : P) (hpk : p ∈ c k) : 0 < y p := by
    rw [hrecon p]
    have hterm : 0 < w k * (if p ∈ c k then ((c k).card : ℝ)⁻¹ else 0) := by
      rw [if_pos hpk]
      exact mul_pos (hw k) (inv_pos.mpr (Nat.cast_pos.mpr (Finset.card_pos.mpr (hc k))))
    apply lt_of_lt_of_le hterm
    apply Finset.single_le_sum _ (Finset.mem_univ k)
    intro i _
    apply mul_nonneg (w.property.1 i)
    split_ifs <;> positivity
  cases m with
  | zero => omega
  | succ d =>
    let q (k : Fin (d+1)) : PartialOrder.NonemptyFiniteChains P := {
      finset := c k
      nonempty := hc k
      comparable := fun a b => hy a.val b.val (hpos k a.val a.property) (hpos k b.val b.property) }
    have hq : Monotone q := fun a b hab => hmono.monotone hab
    refine ⟨simplexPoint _ (a := op ⦋d⦌) hq.functor w,?_⟩
    rw [orderSubdivisionCoordinates_simplex]
    apply stdSimplex.ext
    funext p
    change (∑ k, w k * orderChainBarycenter P (q k) p) = y p
    simp only [orderChainBarycenter_apply]
    exact (hrecon p).symm

/-- Positive strict flag coordinates make the actual subdivision
projection injective for every finite partial order. -/
theorem orderSubdivisionCoordinates_injective (P : Type u) [PartialOrder P] [Fintype P] :
    Function.Injective (orderSubdivisionCoordinates P) := by
  classical
  intro x y hxy
  obtain ⟨d,s,w,hsm,hw,hs⟩ := exists_orderComplex_positive_simplex
    (PartialOrder.NonemptyFiniteChains P) x
  obtain ⟨e,r,v,hrm,hv,hr⟩ := exists_orderComplex_positive_simplex
    (PartialOrder.NonemptyFiniteChains P) y
  have hzs (p : P) : orderSubdivisionCoordinates P x p =
      ∑ k, w k * (if p ∈ (s.obj k).finset then ((s.obj k).finset.card : ℝ)⁻¹ else 0) := by
    rw [← hs,orderSubdivisionCoordinates_simplex]
    change (∑ k, w k * orderChainBarycenter P (s.obj k) p) = _
    simp only [orderChainBarycenter_apply]
  have hzr (p : P) : orderSubdivisionCoordinates P x p =
      ∑ k, v k * (if p ∈ (r.obj k).finset then ((r.obj k).finset.card : ℝ)⁻¹ else 0) := by
    rw [hxy,← hr,orderSubdivisionCoordinates_simplex]
    change (∑ k, v k * orderChainBarycenter P (r.obj k) p) = _
    simp only [orderChainBarycenter_apply]
  obtain ⟨hde,hflag,hweight⟩ := Simplex.BarycentricDecomposition.strict_flag_unique
    (orderSubdivisionCoordinates P x) (m := d+1) (n := e+1)
    (fun k => (s.obj k).finset) hsm (fun k => (s.obj k).nonempty) w hw hzs
    (fun k => (r.obj k).finset) hrm (fun k => (r.obj k).nonempty) v hv hzr
  have hde' : d = e := by omega
  subst e
  have hsr : s = r := CategoryTheory.Functor.ext
    (fun k => PartialOrder.NonemptyFiniteChains.ext (congrFun (eq_of_heq hflag) k))
  have hwv : w = v := eq_of_heq hweight
  rw [← hs,← hr,hsr,hwv]

/-- The actual flag subdivision is homeomorphic to the geometric
order complex by its barycentric coordinates. -/
theorem exists_orderSubdivisionCoordinates_homeomorph (P : Type u)
    [PartialOrder P] [Fintype P] :
    ∃ h : |nerve (PartialOrder.NonemptyFiniteChains P)| ≃ₜ
      {y : stdSimplex ℝ P // HasChainSupport y},
      ∀ x, (h x).val = orderSubdivisionCoordinates P x := by
  classical
  letI := finite_nonemptyFiniteChains P
  letI := finite_nerve_of_finite_order (PartialOrder.NonemptyFiniteChains P)
  letI := compactSpace_of_finite (nerve (PartialOrder.NonemptyFiniteChains P))
  let f : C(|nerve (PartialOrder.NonemptyFiniteChains P)|,
      {y : stdSimplex ℝ P // HasChainSupport y}) := {
    toFun := fun x => ⟨orderSubdivisionCoordinates P x,orderSubdivisionCoordinates_hasChainSupport P x⟩
    continuous_toFun := (orderSubdivisionCoordinates P).continuous.subtype_mk _ }
  have hf : Function.Bijective f := ⟨fun _ _ h =>
    orderSubdivisionCoordinates_injective P (congrArg Subtype.val h),by
      intro y
      obtain ⟨x,hx⟩ := orderSubdivisionCoordinates_preimage P y.val y.property
      exact ⟨x,Subtype.ext hx⟩⟩
  let e := Equiv.ofBijective f hf
  exact ⟨Continuous.homeoOfEquivCompactToT2 (f := e) f.continuous,fun _ => rfl⟩

end KIP126.Topology.SimplicialRealization
