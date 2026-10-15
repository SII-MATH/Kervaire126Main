module

public import KIP126.Def.StableHomotopy.Spectra.Realization.Data
public import KIP126.Def.StableHomotopy.Spectra.Realization.Proofs
public import KIP126.Def.Topology.SimplicialRealization.Equalizer.Data

@[expose] public section

section

namespace KIP126.StableHomotopy.Spectra

open CategoryTheory Opposite Simplicial

universe u

/-- The geometric realization of the actual singular simplicial set,
based at the vertex corresponding to the specified point. -/
noncomputable def singularRealization (A : BasedSpace.{u}) : BasedSpace.{u} :=
  basedRealization (TopCat.toSSet.obj A.space) (TopCat.toSSetObj₀Equiv.symm A.point)

/-- Evaluation of singular simplices is the actual realization--singular
adjunction counit. Its basedness and homotopy properties are separate claims. -/
noncomputable def singularEvaluation (A : BasedSpace.{u}) :
    C(singularRealization A, A) :=
  (sSetTopAdj.counit.app A.space).hom

end KIP126.StableHomotopy.Spectra

end

section

namespace KIP126.StableHomotopy.Spectra

open CategoryTheory Opposite Simplicial

universe u

set_option backward.isDefEq.respectTransparency false

/-- Singular evaluation sends the actual chosen vertex exactly to the
original basepoint, by the adjunction triangle identity. -/
theorem singularEvaluation_point (A : BasedSpace.{u}) :
    singularEvaluation A (singularRealization A).point = A.point := by
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (sSetTopAdj.right_triangle_components A.space) (op ⦋0⦌))
    (TopCat.toSSetObj₀Equiv.symm A.point)
  have he := congrArg TopCat.toSSetObj₀Equiv h
  change singularEvaluation A (singularRealization A).point =
    TopCat.toSSetObj₀Equiv (TopCat.toSSetObj₀Equiv.symm A.point) at he
  exact he.trans (TopCat.toSSetObj₀Equiv.apply_symm_apply A.point)

/-- Evaluation on a realized singular simplex is its original continuous map. -/
theorem singularEvaluation_simplex (A : BasedSpace.{u}) (n : ℕ)
    (σ : (TopCat.toSSet.obj A.space).obj (op ⦋n⦌))
    (t : stdSimplex ℝ (Fin (n+1))) :
    singularEvaluation A
      (KIP126.Topology.SimplicialRealization.simplexPoint (TopCat.toSSet.obj A.space) σ t) =
      A.space.toSSetObjEquiv (op ⦋n⦌) σ t := by
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (sSetTopAdj.right_triangle_components A.space) (op ⦋n⦌)) σ
  exact congrArg (fun z => A.space.toSSetObjEquiv (op ⦋n⦌) z t) h

/-- Singular realization is a genuine good based space even when the
original based space has no separation or cofibration hypotheses. -/
theorem singularRealization_isGood (A : BasedSpace.{u}) :
    (singularRealization A).IsGood :=
  basedRealization_isGood _ _

end KIP126.StableHomotopy.Spectra

end
