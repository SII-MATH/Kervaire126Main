module

public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.Predicates
public import Mathlib.Data.Finset.Sort
public import KIP126.Def.Topology.Simplex.MonotoneCoupling.Representation.Proofs

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory Simplicial Opposite

universe u

set_option backward.isDefEq.respectTransparency false

/-- Every point of an order-complex realization is represented by a
strictly ordered simplex with strictly positive coordinates. -/
theorem exists_orderComplex_positive_simplex (P : Type u) [PartialOrder P]
    (x : |nerve P|) :
    ∃ (d : ℕ) (s : (nerve P).obj (op ⦋d⦌)) (w : stdSimplex ℝ (Fin (d+1))),
      StrictMono s.obj ∧ (∀ k, 0 < w k) ∧ simplexPoint _ s w = x := by
  obtain ⟨d,s,t,ht,he⟩ := exists_nondegenerate_interior (nerve P) x
  let w := SimplexCategory.toTopHomeo ⦋d⦌ t
  have htw : (SimplexCategory.toTopHomeo ⦋d⦌).symm w = t :=
    (SimplexCategory.toTopHomeo ⦋d⦌).symm_apply_apply t
  exact ⟨d,s.val,w,(PartialOrder.mem_nerve_nonDegenerate_iff_strictMono s.val).mp s.property,
    (simplex_interior_iff_positive d w).mp (by rw [htw]; exact ht),
    by rw [simplexPoint_eq_yoneda,htw]; exact he⟩

/-- Coordinates of an actual characteristic simplex are its weights
pushed to its ordered vertex set. -/
theorem orderComplexCoordinates_simplex (P : Type u) [PartialOrder P] [Fintype P]
    {d : SimplexCategoryᵒᵖ} (s : (nerve P).obj d)
    (t : stdSimplex ℝ (Fin (d.unop.len+1))) :
    orderComplexCoordinates P (simplexPoint _ s t) = stdSimplex.map s.obj t :=
  adjunction_symm_simplex _ (orderComplexCoordinatesAdjoint P) s t

/-- Every point of the actual order-complex realization has coordinates
supported on a chain in the order. -/
theorem orderComplexCoordinates_hasChainSupport (P : Type u)
    [PartialOrder P] [Fintype P] (x : |nerve P|) :
    HasChainSupport (orderComplexCoordinates P x) := by
  obtain ⟨d,s,t,ht,he⟩ := exists_nondegenerate_interior (nerve P) x
  let w := SimplexCategory.toTopHomeo ⦋d⦌ t
  have hs : simplexPoint _ s.val w = x := by
    rw [simplexPoint_eq_yoneda]
    simpa only [w,Homeomorph.symm_apply_apply] using he
  rw [← hs,orderComplexCoordinates_simplex]
  intro p q hp hq
  have hmem (a : P) (ha : 0 < stdSimplex.map s.val.obj w a) :
      a ∈ Set.range s.val.obj := by
    by_contra h
    exact (ne_of_gt ha) (simplex_map_apply_not_range s.val.obj w a h)
  obtain ⟨i,rfl⟩ := hmem p hp
  obtain ⟨j,rfl⟩ := hmem q hq
  exact (le_total i j).imp (fun h => s.val.monotone h) (fun h => s.val.monotone h)

/-- Actual order-complex coordinates commute with every monotone map
of finite orders, including maps identifying vertices. -/
theorem orderComplexCoordinates_natural {P Q : Type u}
    [PartialOrder P] [PartialOrder Q] [Fintype P] [Fintype Q]
    (f : P →o Q) (x : |nerve P|) :
    orderComplexCoordinates Q (SSet.toTop.map (nerveMap f.monotone.functor) x) =
      stdSimplex.map f (orderComplexCoordinates P x) := by
  obtain ⟨d,s,t,ht,he⟩ := exists_nondegenerate_interior (nerve P) x
  let w := SimplexCategory.toTopHomeo ⦋d⦌ t
  have hs : simplexPoint _ s.val w = x := by
    rw [simplexPoint_eq_yoneda]
    simpa only [w,Homeomorph.symm_apply_apply] using he
  rw [← hs,simplexPoint_map,orderComplexCoordinates_simplex,
    orderComplexCoordinates_simplex]
  exact (stdSimplex.map_comp_apply s.val.obj f w).symm

/-- Every point with chain support is the coordinate image of an actual
simplex of the order complex. -/
theorem orderComplexCoordinates_preimage (P : Type u) [PartialOrder P] [Fintype P]
    (y : stdSimplex ℝ P) (hy : HasChainSupport y) :
    ∃ x : |nerve P|, orderComplexCoordinates P x = y := by
  classical
  let S := {p : P // 0 < y p}
  have hS : Nonempty S := by
    by_contra h
    have hz (p : P) : y p = 0 := by
      apply le_antisymm _ (y.property.1 p)
      by_contra hp
      exact h ⟨⟨p,lt_of_not_ge hp⟩⟩
    have hsum := stdSimplex.sum_eq_one y
    simp only [hz,Finset.sum_const_zero] at hsum
    norm_num at hsum
  letI : Nonempty S := hS
  letI : LinearOrder S := {
    le_total := fun a b => hy a.val b.val a.property b.property
    toDecidableLE := inferInstance }
  letI : Fintype S := inferInstanceAs (Fintype {p : P // 0 < y p})
  have hsum : ∑ p : S, y p.val = 1 := by
    rw [← Finset.sum_subtype (Finset.univ.filter (fun p => 0 < y p))
      (fun _ => Finset.mem_filter.trans (and_iff_right (Finset.mem_univ _))) (fun p => y p)]
    rw [Finset.sum_filter]
    have hzero (p : P) : (if 0 < y p then y p else 0) = y p := by
      by_cases hp : 0 < y p
      · simp [hp]
      · simp [le_antisymm (le_of_not_gt hp) (y.property.1 p)]
    simp only [hzero,stdSimplex.sum_eq_one]
  let yS : stdSimplex ℝ S := ⟨fun p => y p.val,fun p => (p.property.le),hsum⟩
  obtain ⟨d,hd⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt (Fintype.card_pos (α := S)))
  let e : Fin (d+1) ≃o S := Fintype.orderIsoFinOfCardEq S hd
  let f : Fin (d+1) →o P := {
    toFun := fun k => (e k).val
    monotone' := fun _ _ h => e.monotone h }
  have hfi : Function.Injective f := by
    intro a b hab
    exact e.injective (Subtype.ext hab)
  let w : stdSimplex ℝ (Fin (d+1)) := stdSimplex.map e.symm yS
  refine ⟨simplexPoint (nerve P) (a := op ⦋d⦌) f.monotone.functor w,?_⟩
  rw [orderComplexCoordinates_simplex]
  apply stdSimplex.ext
  funext p
  change stdSimplex.map f w p = y p
  by_cases hp : 0 < y p
  · let a : S := ⟨p,hp⟩
    have hfa : f (e.symm a) = p := congrArg Subtype.val (e.apply_symm_apply a)
    rw [← hfa,simplex_map_apply_injective f hfi]
    change stdSimplex.map e.symm yS (e.symm a) = y (f (e.symm a))
    rw [simplex_map_apply_injective e.symm e.symm.injective,hfa]
    rfl
  · rw [simplex_map_apply_not_range f w p]
    · exact (le_antisymm (le_of_not_gt hp) (y.property.1 p)).symm
    · rintro ⟨k,hk⟩
      exact hp (hk ▸ (e k).property)

/-- The coordinate image of the actual realization is exactly the
geometric order complex, with no triangulation assumption. -/
theorem orderComplexCoordinates_range (P : Type u) [PartialOrder P] [Fintype P]
    (y : stdSimplex ℝ P) :
    y ∈ Set.range (orderComplexCoordinates P) ↔ HasChainSupport y := by
  constructor
  · rintro ⟨x,rfl⟩
    exact orderComplexCoordinates_hasChainSupport P x
  · exact orderComplexCoordinates_preimage P y

/-- Ordered positive simplex coordinates detect equality of actual
order-complex points. -/
theorem orderComplexCoordinates_injective (P : Type u) [PartialOrder P] [Fintype P] :
    Function.Injective (orderComplexCoordinates P) := by
  intro x y hxy
  obtain ⟨d,s,w,hsm,hw,hs⟩ := exists_orderComplex_positive_simplex P x
  obtain ⟨e,r,v,hrm,hv,hr⟩ := exists_orderComplex_positive_simplex P y
  rw [← hs,← hr,orderComplexCoordinates_simplex,orderComplexCoordinates_simplex] at hxy
  obtain ⟨hde,hvertex,hweight⟩ := Simplex.ordered_simplex_representation_unique
    (n := d) (m := e) s.toOrderHom r.toOrderHom hsm.injective hrm.injective w v hw hv hxy
  subst e
  have hsr : s = r := CategoryTheory.Functor.ext
    (fun k => congrArg (fun f : Fin (d+1) →o P => f k) (eq_of_heq hvertex))
  have hwv : w = v := eq_of_heq hweight
  rw [← hs,← hr,hsr,hwv]

/-- The actual realization of a finite order is homeomorphic to its
geometric chain-supported simplex subspace. -/
theorem exists_orderComplexCoordinates_homeomorph (P : Type u)
    [PartialOrder P] [Fintype P] :
    ∃ h : |nerve P| ≃ₜ {y : stdSimplex ℝ P // HasChainSupport y},
      ∀ x, (h x).val = orderComplexCoordinates P x := by
  letI := finite_nerve_of_finite_order P
  letI := compactSpace_of_finite (nerve P)
  let f : C(|nerve P|,{y : stdSimplex ℝ P // HasChainSupport y}) := {
    toFun := fun x => ⟨orderComplexCoordinates P x,orderComplexCoordinates_hasChainSupport P x⟩
    continuous_toFun := (orderComplexCoordinates P).continuous.subtype_mk _ }
  have hf : Function.Bijective f := ⟨fun _ _ h =>
    orderComplexCoordinates_injective P (congrArg Subtype.val h),by
      intro y
      obtain ⟨x,hx⟩ := orderComplexCoordinates_preimage P y.val y.property
      exact ⟨x,Subtype.ext hx⟩⟩
  let e := Equiv.ofBijective f hf
  exact ⟨Continuous.homeoOfEquivCompactToT2 (f := e) f.continuous,fun _ => rfl⟩

/-- Every finite order has a chain-size bound given by its cardinality. -/
theorem orderChainSizeLE_card (P : Type u) [PartialOrder P] [Fintype P] :
    OrderChainSizeLE P (Fintype.card P) := fun c => Finset.card_le_univ c.finset

/-- Subdivision preserves a chain-size bound. The bound therefore stays
fixed through repeated subdivision, which gives a uniform mesh factor. -/
theorem orderChainSizeLE_subdivision (P : Type u) [PartialOrder P] {N : ℕ}
    (hP : OrderChainSizeLE P N) :
    OrderChainSizeLE (PartialOrder.NonemptyFiniteChains P) N := by
  classical
  intro c
  have hp (a : c.finset) : 0 < a.val.finset.card := Finset.card_pos.mpr a.val.nonempty
  let r : c.finset → Fin N := fun a => ⟨a.val.finset.card - 1,by
    have := hP a.val
    have := hp a
    omega⟩
  have hr : Function.Injective r := by
    intro a b hab
    have he : a.val.finset.card = b.val.finset.card := by
      have := congrArg Fin.val hab
      have := hp a
      have := hp b
      dsimp only [r] at *
      omega
    apply Subtype.ext
    apply PartialOrder.NonemptyFiniteChains.ext
    obtain h | h := c.comparable a b
    · exact Finset.eq_of_subset_of_card_le h (le_of_eq he.symm)
    · exact (Finset.eq_of_subset_of_card_le h (le_of_eq he)).symm
  have h := Fintype.card_le_of_injective r hr
  simpa only [Fintype.card_coe,Fintype.card_fin] using h

end KIP126.Topology.SimplicialRealization
