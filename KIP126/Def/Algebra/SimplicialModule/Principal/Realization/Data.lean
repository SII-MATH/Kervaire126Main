module

public import KIP126.Def.Topology.SimplicialRealization.Pullback.StandardSimplex.Data
public import KIP126.Def.Algebra.SimplicialModule.Principal.Trivialization.Data

@[expose] public section

namespace KIP126.Algebra.SimplicialModule
open CategoryTheory CategoryTheory.Limits Simplicial Opposite
open KIP126.Topology.SimplicialRealization
open scoped MonoidalCategory
universe u
variable {R : Type u} [Ring R]
set_option backward.isDefEq.respectTransparency false

/-- The actual topological pullback over a specified target simplex. -/
abbrev principalRealizationPullback
    {A B : SimplicialObject (ModuleCat.{u} R)} (p : A ⟶ B)
    {n : ℕ} (b : B.obj (op ⦋n⦌)) :=
  {xt : |A ⋙ forget (ModuleCat R)| × |(Δ[n] : SSet.{u})| //
    SSet.toTop.map (Functor.whiskerRight p (forget (ModuleCat R))) xt.1 =
      SSet.toTop.map ((SSet.yonedaEquiv (X := B ⋙ forget (ModuleCat R))).symm b) xt.2}

/-- Translation by a lifted simplex is an actual continuous trivialization
of the topological pullback over that simplex, with the realized kernel as fiber. -/
noncomputable def principalRealizationHomeomorph
    {A B : SimplicialObject (ModuleCat.{u} R)} (p : A ⟶ B)
    {n : ℕ} (b : B.obj (op ⦋n⦌)) (z : A.obj (op ⦋n⦌))
    (hz : (p.app (op ⦋n⦌)).hom z = b) :
    (|kernel p ⋙ forget (ModuleCat R)| × |(Δ[n] : SSet.{u})|) ≃ₜ principalRealizationPullback p b :=
  ((realizationStandardSimplexProductHomeomorph (kernel p ⋙ forget (ModuleCat R)) n).symm.trans
    (TopCat.homeoOfIso (SSet.toTop.mapIso (principalSimplexIso p b z hz)))).trans
      (standardSimplexPullbackHomeomorph (Functor.whiskerRight p (forget (ModuleCat R))) n
        ((SSet.yonedaEquiv (X := B ⋙ forget (ModuleCat R))).symm b))

end KIP126.Algebra.SimplicialModule
