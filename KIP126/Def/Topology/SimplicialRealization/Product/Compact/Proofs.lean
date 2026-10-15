module

public import KIP126.Def.Topology.SimplicialRealization.Product.Proofs
public import KIP126.Def.Topology.Product.CompactFactor

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory MonoidalCategory Simplicial Opposite

universe u

set_option backward.isDefEq.respectTransparency false

/-- The actual cartesian product comparison for two standard simplices
is an isomorphism of topological spaces. -/
theorem stdSimplex_productComparison_isIso (p q : ℕ) :
    IsIso (CartesianMonoidalCategory.prodComparison SSet.toTop.{u} Δ[p] Δ[q]) := by
  obtain ⟨e,he⟩ := nonempty_stdSimplexProductHomeomorph.{u} p q
  let E := e.trans ((SimplexCategory.toTopHomeo ⦋p⦌).prodCongr
    (SimplexCategory.toTopHomeo ⦋q⦌)).symm
  have h : CartesianMonoidalCategory.prodComparison SSet.toTop.{u} Δ[p] Δ[q] =
      (TopCat.isoOfHomeo E).hom := by
    apply TopCat.ext
    intro x
    change productComparison Δ[p] Δ[q] x = E x
    change productComparison Δ[p] Δ[q] x =
      ((SimplexCategory.toTopHomeo ⦋p⦌).symm (e x).1,
        (SimplexCategory.toTopHomeo ⦋q⦌).symm (e x).2)
    rw [he]
    dsimp [stdSimplexProductComparison]
    rw [Homeomorph.symm_apply_apply,Homeomorph.symm_apply_apply]
  rw [h]
  infer_instance

/-- Product comparison with a standard simplex on the left is an actual
isomorphism for every simplicial set. This extends the finite comparison
through the genuine tautological colimit and the compact-factor adjunction. -/
theorem stdSimplex_left_productComparison_isIso (p : ℕ) (X : SSet.{u}) :
    IsIso (CartesianMonoidalCategory.prodComparison SSet.toTop Δ[p] X) := by
  letI : LocallyCompactSpace |(Δ[p] : SSet.{u})| :=
    (SimplexCategory.toTopHomeo ⦋p⦌).isClosedEmbedding.locallyCompactSpace
  letI : PreservesColimitsOfSize.{0,u}
      (tensorLeft (SSet.toTop.obj (Δ[p] : SSet.{u}))) :=
    tensorLeft_preservesColimits_of_locallyCompact _
  let α := CartesianMonoidalCategory.prodComparisonNatTrans SSet.toTop (Δ[p] : SSet.{u})
  let K := CostructuredArrow.proj uliftYoneda X ⋙ uliftYoneda
  haveI : IsIso (Functor.whiskerLeft K α) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro j
    exact stdSimplex_productComparison_isIso p j.left.len
  exact isIso_app_coconePt_of_preservesColimit K α _ (Presheaf.isColimitTautologicalCocone' X)

/-- The actual realization comparison with a standard simplex on the
right is an isomorphism, with its original two projection maps. -/
theorem stdSimplex_right_productComparison_isIso (X : SSet.{u}) (q : ℕ) :
    IsIso (CartesianMonoidalCategory.prodComparison SSet.toTop X Δ[q]) := by
  letI := stdSimplex_left_productComparison_isIso q X
  have h : CartesianMonoidalCategory.prodComparison SSet.toTop X (Δ[q] : SSet.{u}) =
      SSet.toTop.map (β_ X Δ[q]).hom ≫
        CartesianMonoidalCategory.prodComparison SSet.toTop Δ[q] X ≫
        (β_ (SSet.toTop.obj Δ[q]) (SSet.toTop.obj X)).hom := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [← Functor.map_comp]
  rw [h]
  infer_instance

/-- Realization commutes with product by any standard simplex, as a
homeomorphism that is exactly the two realized simplicial projections. -/
theorem exists_product_stdSimplex_homeomorph (X : SSet.{u}) (q : ℕ) :
    ∃ e : |X ⊗ Δ[q]| ≃ₜ (|X| × stdSimplex ℝ (Fin (q+1))),
      ∀ z, e z = (SSet.toTop.map (fst X Δ[q]) z,
        SimplexCategory.toTopHomeo ⦋q⦌ (SSet.toTop.map (snd X Δ[q]) z)) := by
  letI := stdSimplex_right_productComparison_isIso X q
  let e := TopCat.homeoOfIso (asIso (CartesianMonoidalCategory.prodComparison SSet.toTop X Δ[q]))
  refine ⟨e.trans ((Homeomorph.refl |X|).prodCongr (SimplexCategory.toTopHomeo ⦋q⦌)),?_⟩
  intro z
  rfl

end KIP126.Topology.SimplicialRealization
