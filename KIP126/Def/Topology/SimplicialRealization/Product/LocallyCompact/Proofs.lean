module

public import KIP126.Def.Topology.SimplicialRealization.Product.Compact.Proofs

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory MonoidalCategory Simplicial Opposite

universe u

set_option backward.isDefEq.respectTransparency false

/-- The actual product comparison is an isomorphism when the left
realization is locally compact. -/
theorem productComparison_isIso_of_locallyCompact_left (X Y : SSet.{u})
    [LocallyCompactSpace |X|] :
    IsIso (CartesianMonoidalCategory.prodComparison SSet.toTop X Y) := by
  letI : PreservesColimitsOfSize.{0,u} (tensorLeft (SSet.toTop.obj X)) :=
    tensorLeft_preservesColimits_of_locallyCompact _
  let α := CartesianMonoidalCategory.prodComparisonNatTrans SSet.toTop X
  let K := CostructuredArrow.proj uliftYoneda Y ⋙ uliftYoneda
  haveI : IsIso (Functor.whiskerLeft K α) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro j
    exact stdSimplex_right_productComparison_isIso X j.left.len
  exact isIso_app_coconePt_of_preservesColimit K α _ (Presheaf.isColimitTautologicalCocone' Y)

/-- A locally compact right factor also gives the genuine topological
product comparison. -/
theorem productComparison_isIso_of_locallyCompact_right (X Y : SSet.{u})
    [LocallyCompactSpace |Y|] :
    IsIso (CartesianMonoidalCategory.prodComparison SSet.toTop X Y) := by
  letI := productComparison_isIso_of_locallyCompact_left Y X
  have h : CartesianMonoidalCategory.prodComparison SSet.toTop X Y =
      SSet.toTop.map (β_ X Y).hom ≫
        CartesianMonoidalCategory.prodComparison SSet.toTop Y X ≫
        (β_ (SSet.toTop.obj Y) (SSet.toTop.obj X)).hom := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [← Functor.map_comp]
  rw [h]
  infer_instance

/-- Every finite simplicial set supplies the compact factor needed for
an actual ordinary topological product. -/
theorem productComparison_isIso_of_finite_right (X Y : SSet.{u}) [Y.Finite] :
    IsIso (CartesianMonoidalCategory.prodComparison SSet.toTop X Y) := by
  letI := compactSpace_of_finite Y
  letI := realization_t2Space Y
  exact productComparison_isIso_of_locallyCompact_right X Y

end KIP126.Topology.SimplicialRealization
