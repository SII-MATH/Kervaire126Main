module

public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.Cone.Data

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory Simplicial Opposite
open scoped unitInterval Classical

universe u

set_option backward.isDefEq.respectTransparency false

variable (P : Type u) [PartialOrder P] [Fintype P]

/-- Coordinates of the actual cone parametrization, including its apex. -/
theorem orderConeParameter_coordinates (t : I) (x : |nerve P|) :
    orderComplexCoordinates (WithTop P) (orderConeParameter P (t, x)) =
      orderConeCoordinates t (orderComplexCoordinates P x) := by
  let e := (exists_orderComplexCoordinates_homeomorph (WithTop P)).choose
  have he := (exists_orderComplexCoordinates_homeomorph (WithTop P)).choose_spec
  have h := he (orderConeParameter P (t, x))
  change (e (e.symm _)).val = _ at h
  rw [e.apply_symm_apply] at h
  exact h.symm

/-- Height zero is precisely the realized simplicial base inclusion. -/
theorem orderConeParameter_zero (x : |nerve P|) :
    orderConeParameter P (0, x) =
      SSet.toTop.map (orderMappingConeSourceTopInclusion P) x := by
  apply orderComplexCoordinates_injective (WithTop P)
  rw [orderConeParameter_coordinates, orderConeCoordinates_zero]
  exact (orderComplexCoordinates_natural
    (orderMappingConeSourceTopEmbedding P).toOrderHom x).symm

/-- Height one is precisely the actual new vertex, independently of the base. -/
theorem orderConeParameter_one (x : |nerve P|) :
    orderConeParameter P (1, x) = orderVertex (WithTop P) ⊤ := by
  apply orderComplexCoordinates_injective (WithTop P)
  rw [orderConeParameter_coordinates, orderConeCoordinates_one, orderComplexCoordinates_vertex]
  apply stdSimplex.ext
  funext p
  by_cases hp : p = ⊤ <;> simp [stdSimplex.vertex, hp]

/-- The actual cone parametrization collapses exactly the entire height-one base. -/
theorem orderConeParameter_eq_iff (t s : I) (x y : |nerve P|) :
    orderConeParameter P (t, x) = orderConeParameter P (s, y) ↔
      t = s ∧ (t = 1 ∨ x = y) := by
  rw [← (orderComplexCoordinates_injective (WithTop P)).eq_iff,
    orderConeParameter_coordinates, orderConeParameter_coordinates, orderConeCoordinates_eq_iff,
    (orderComplexCoordinates_injective P).eq_iff]

/-- Every actual cone point has a base-and-height representative. -/
theorem orderConeParameter_surjective [Nonempty P] :
    Function.Surjective (orderConeParameter P) := by
  intro z
  let w := orderComplexCoordinates (WithTop P) z
  let t : I := ⟨w ⊤, w.property.1 ⊤, stdSimplex.le_one w ⊤⟩
  have hsum : w ⊤ + ∑ p : P, w (p : WithTop P) = 1 := by
    have h := stdSimplex.sum_eq_one w
    change (∑ p : Option P, w p) = 1 at h
    rwa [Fintype.sum_option] at h
  by_cases ht : w ⊤ = 1
  · let x := orderVertex P (Classical.arbitrary P)
    refine ⟨(1, x), ?_⟩
    apply orderComplexCoordinates_injective (WithTop P)
    rw [orderConeParameter_coordinates, orderConeCoordinates_one]
    apply stdSimplex.ext
    funext p
    cases p with
    | top => simpa [stdSimplex.vertex] using ht.symm
    | coe p =>
        have hp : w (p : WithTop P) = 0 := by
          have hle : w (p : WithTop P) ≤ ∑ q : P, w (q : WithTop P) :=
            Finset.single_le_sum (fun (q : P) (_ : q ∈ Finset.univ) => w.property.1 (q : WithTop P))
            (Finset.mem_univ p)
          have hz : ∑ q : P, w (q : WithTop P) = 0 := by linarith
          exact le_antisymm (hle.trans_eq hz) (w.property.1 _)
        simpa [stdSimplex.vertex] using hp.symm
  · have hd : 0 < 1 - w ⊤ := sub_pos.mpr (lt_of_le_of_ne (stdSimplex.le_one w ⊤) ht)
    let v : stdSimplex ℝ P := ⟨fun p => w (p : WithTop P) / (1 - w ⊤),
      fun p => div_nonneg (w.property.1 _) hd.le, by
        rw [← Finset.sum_div]
        have he : ∑ p : P, w (p : WithTop P) = 1 - w ⊤ := by linarith
        rw [he, div_self hd.ne']⟩
    have hv : HasChainSupport v := by
      intro p q hp hq
      have hpos (r : P) (hr : 0 < v r) : 0 < w (r : WithTop P) :=
        (div_pos_iff_of_pos_right hd).mp hr
      exact (orderComplexCoordinates_hasChainSupport (WithTop P) z
        (p : WithTop P) (q : WithTop P) (hpos p hp) (hpos q hq)).imp
        WithTop.coe_le_coe.mp WithTop.coe_le_coe.mp
    obtain ⟨x, hx⟩ := orderComplexCoordinates_preimage P v hv
    refine ⟨(t, x), ?_⟩
    apply orderComplexCoordinates_injective (WithTop P)
    rw [orderConeParameter_coordinates, hx]
    apply stdSimplex.ext
    funext p
    cases p with
    | top => rfl
    | coe p =>
        change (1 - w ⊤) * (w (p : WithTop P) / (1 - w ⊤)) = w (p : WithTop P)
        exact mul_div_cancel₀ _ hd.ne'

/-- The actual cone has the quotient topology of the explicit parametrization. -/
theorem orderConeParameter_isQuotientMap [Nonempty P] :
    Topology.IsQuotientMap (orderConeParameter P) := by
  letI := finite_nerve_of_finite_order P
  letI := compactSpace_of_finite (nerve P)
  letI := ((exists_orderComplexCoordinates_homeomorph (WithTop P)).choose).isEmbedding.t2Space
  exact Topology.IsQuotientMap.of_surjective_continuous
    (orderConeParameter_surjective P) (orderConeParameter P).continuous

end KIP126.Topology.SimplicialRealization
