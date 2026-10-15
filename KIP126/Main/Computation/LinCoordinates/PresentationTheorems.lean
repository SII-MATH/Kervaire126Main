module

public import KIP126.Computation.LinCoordinates.Presentation
public import KIP126.Main.Computation.LinCoordinates.Model.E2.RelationAlgebra.Proofs
public import KIP126.Main.AdamsSynthetic.SphereAlgebra

@[expose] public section

namespace KIP126.Classical.Adams
open KIP126.Algebra KIP126.LinE2 Sphere.Internal
noncomputable section
namespace LinE2Presentation
@[simp] theorem embed_component (P : LinE2Presentation) (s t : ℕ)
    (x : RelationAt s t) :
    embed (s, t) (P.component s t x) = P.toActual x.val :=
  LinearMap.codRestrictOfInjective_comp_apply _ _ _ _ x


@[simp] theorem embed_comparison (P : LinE2Presentation) (s t : ℕ)
    (ht : t ≤ 261) (x : E2At s t) :
    embed (s, t) (P.comparison s t ht x) =
      P.toActual ((truncateAtEquiv s t ht).symm x).val :=
  P.embed_component s t _


/-- Product compatibility in the bounded range follows from multiplicativity
of the relation-algebra comparison and the truncation equivalence. -/
theorem comparison_mul (P : LinE2Presentation) (s t s' t' : ℕ)
    (h : t + t' ≤ 261) (x : E2At s t) (y : E2At s' t')
    (z : E2At (s + s') (t + t')) (hz : x.val * y.val = z.val) :
    P.comparison (s + s') (t + t') h z =
      P.product s t s' t' (P.comparison s t (by omega) x)
        (P.comparison s' t' (by omega) y) := by
  let a := (truncateAtEquiv s t (by omega)).symm x
  let b := (truncateAtEquiv s' t' (by omega)).symm y
  let c := (truncateAtEquiv (s + s') (t + t') h).symm z
  have ha : truncate a.val = x.val := truncateAtEquiv_symm_apply s t (by omega) x
  have hb : truncate b.val = y.val := truncateAtEquiv_symm_apply s' t' (by omega) y
  have hc : truncate c.val = z.val := truncateAtEquiv_symm_apply (s + s') (t + t') h z
  have hab : relationMultiply a b = c := by
    apply (truncateAtEquiv (s + s') (t + t') h).injective
    apply Subtype.ext
    rw [truncateAtEquiv_apply_val, truncateAtEquiv_apply_val]
    change truncate (a.val * b.val) = truncate c.val
    rw [map_mul, ha, hb, hc, hz]
  apply embed_injective (s + s', t + t')
  change embed (s + s', t + t') (P.comparison (s + s') (t + t') h z) =
    embed ((s, t) + (s', t'))
      (actualE2Product (s, t) (s', t')
        (P.comparison s t (by omega) x) (P.comparison s' t' (by omega) y))
  rw [embed_product, P.embed_comparison, P.embed_comparison, P.embed_comparison]
  change P.toActual c.val = P.toActual a.val * P.toActual b.val
  rw [← P.preservesMul]
  exact congrArg P.toActual (congrArg Subtype.val hab).symm


end LinE2Presentation
end
end KIP126.Classical.Adams
