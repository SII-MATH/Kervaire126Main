module

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Cone.Coordinates.Data

@[expose] section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory Simplicial Opposite
open scoped unitInterval Classical

universe u

set_option backward.isDefEq.respectTransparency false

variable {P : Type u} [PartialOrder P] [Fintype P]

theorem orderConeCoordinates_top (t : I) (y : stdSimplex ℝ P) :
    orderConeCoordinates t y ⊤ = t := rfl

theorem orderConeCoordinates_coe (t : I) (y : stdSimplex ℝ P) (p : P) :
    orderConeCoordinates t y (p : WithTop P) = (1 - (t : ℝ)) * y p := rfl

/-- The actual cone-coordinate operation is continuous, including at the apex. -/
theorem continuous_orderConeCoordinates :
    Continuous (fun z : I × stdSimplex ℝ P => orderConeCoordinates z.1 z.2) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro p
  cases p with
  | top => exact continuous_fst.subtype_val
  | coe p =>
      exact (continuous_const.sub continuous_fst.subtype_val).mul
        ((continuous_apply p).comp continuous_snd.subtype_val)

/-- Adding a maximum preserves the chain support of genuine base coordinates. -/
theorem orderConeCoordinates_hasChainSupport (t : I) (y : stdSimplex ℝ P)
    (hy : HasChainSupport y) : HasChainSupport (orderConeCoordinates t y) := by
  intro p q hp hq
  cases p with
  | top => exact Or.inr le_top
  | coe p =>
      cases q with
      | top => exact Or.inl le_top
      | coe q =>
          have hpos (r : P) (hr : 0 < orderConeCoordinates t y (r : WithTop P)) :
              0 < y r := by
            rw [orderConeCoordinates_coe] at hr
            exact (mul_pos_iff.mp hr).elim And.right
              (fun h => False.elim (not_lt_of_ge (y.property.1 r) h.2))
          exact (hy p q (hpos p hp) (hpos q hq)).imp
            WithTop.coe_le_coe.mpr WithTop.coe_le_coe.mpr

/-- At height zero the cone coordinates are exactly the actual base inclusion. -/
theorem orderConeCoordinates_zero (y : stdSimplex ℝ P) :
    orderConeCoordinates 0 y = stdSimplex.map (fun p : P => (p : WithTop P)) y := by
  apply stdSimplex.ext
  funext p
  cases p with
  | top =>
      rw [orderConeCoordinates_top, simplex_map_apply_not_range]
      · rfl
      · rintro ⟨p, hp⟩
        exact WithTop.coe_ne_top hp
  | coe p =>
      rw [orderConeCoordinates_coe, simplex_map_apply_injective _ WithTop.coe_injective]
      simp

/-- At height one all base points give the same actual apex coordinates. -/
theorem orderConeCoordinates_one (y : stdSimplex ℝ P) :
    orderConeCoordinates 1 y = stdSimplex.vertex (⊤ : WithTop P) := by
  classical
  apply stdSimplex.ext
  funext p
  cases p with
  | top => rw [orderConeCoordinates_top]; simp [stdSimplex.vertex]
  | coe p => rw [orderConeCoordinates_coe]; simp [stdSimplex.vertex]

/-- Cone-coordinate fibers identify exactly the height-one base and nothing else. -/
theorem orderConeCoordinates_eq_iff (t s : I) (y z : stdSimplex ℝ P) :
    orderConeCoordinates t y = orderConeCoordinates s z ↔
      t = s ∧ (t = 1 ∨ y = z) := by
  constructor
  · intro h
    have hts : t = s := Subtype.ext (congrArg (fun a : stdSimplex ℝ (WithTop P) => a ⊤) h)
    subst s
    refine ⟨rfl, ?_⟩
    by_cases ht : t = 1
    · exact Or.inl ht
    · right
      have hn : 1 - (t : ℝ) ≠ 0 := by
        intro hh
        apply ht
        apply Subtype.ext
        exact (sub_eq_zero.mp hh).symm
      apply stdSimplex.ext
      funext p
      exact mul_left_cancel₀ hn
        (congrArg (fun a : stdSimplex ℝ (WithTop P) => a (p : WithTop P)) h)
  · rintro ⟨rfl, ht | rfl⟩
    · rw [ht, orderConeCoordinates_one, orderConeCoordinates_one]
    · rfl

end KIP126.Topology.SimplicialRealization
