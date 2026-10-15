module

public import KIP126.Def.Algebra.SimplicialModule.Principal.Realization.Data
public import KIP126.Def.Topology.SimplicialRealization.Pullback.StandardSimplex.Proofs
public import KIP126.Def.Algebra.SimplicialModule.Principal.Trivialization.Proofs

@[expose] public section

namespace KIP126.Algebra.SimplicialModule
open CategoryTheory CategoryTheory.Limits Simplicial Opposite
open KIP126.Topology.SimplicialRealization
open scoped MonoidalCategory
universe u
variable {R : Type u} [Ring R]
set_option backward.isDefEq.respectTransparency false

/-- The total-space coordinate is exactly the realization of the explicit
simplicial translation map. -/
@[simp] theorem principalRealizationHomeomorph_fst
    {A B : SimplicialObject (ModuleCat.{u} R)} (p : A ⟶ B)
    {n : ℕ} (b : B.obj (op ⦋n⦌)) (z : A.obj (op ⦋n⦌))
    (hz : (p.app (op ⦋n⦌)).hom z = b)
    (x : |kernel p ⋙ forget (ModuleCat R)| × |(Δ[n] : SSet.{u})|) :
    (principalRealizationHomeomorph p b z hz x).val.1 =
      SSet.toTop.map (principalSimplexMap p z)
        ((realizationStandardSimplexProductHomeomorph (kernel p ⋙ forget (ModuleCat R)) n).symm x) := by
  rw [principalRealizationHomeomorph,Homeomorph.trans_apply,standardSimplexPullbackHomeomorph_fst]
  have h := congrArg SSet.toTop.map (principalSimplexIso_hom_fst p b z hz)
  rw [Functor.map_comp] at h
  exact ConcreteCategory.congr_hom h _

/-- The trivialization preserves the actual simplex coordinate strictly. -/
@[simp] theorem principalRealizationHomeomorph_snd
    {A B : SimplicialObject (ModuleCat.{u} R)} (p : A ⟶ B)
    {n : ℕ} (b : B.obj (op ⦋n⦌)) (z : A.obj (op ⦋n⦌))
    (hz : (p.app (op ⦋n⦌)).hom z = b)
    (x : |kernel p ⋙ forget (ModuleCat R)| × |(Δ[n] : SSet.{u})|) :
    (principalRealizationHomeomorph p b z hz x).val.2 = x.2 := by
  rw [principalRealizationHomeomorph,Homeomorph.trans_apply,standardSimplexPullbackHomeomorph_snd]
  have h := congrArg SSet.toTop.map (principalSimplexIso_hom_snd p b z hz)
  rw [Functor.map_comp] at h
  have hx := ConcreteCategory.congr_hom h
    ((realizationStandardSimplexProductHomeomorph (kernel p ⋙ forget (ModuleCat R)) n).symm x)
  change SSet.toTop.map (pullback.snd _ _) (SSet.toTop.map (principalSimplexIso p b z hz).hom
    ((realizationStandardSimplexProductHomeomorph (kernel p ⋙ forget (ModuleCat R)) n).symm x)) = _
  exact hx.trans (congrArg Prod.snd
    ((realizationStandardSimplexProductHomeomorph (kernel p ⋙ forget (ModuleCat R)) n).apply_symm_apply x))

@[simp] theorem principalRealizationHomeomorph_symm_snd
    {A B : SimplicialObject (ModuleCat.{u} R)} (p : A ⟶ B)
    {n : ℕ} (b : B.obj (op ⦋n⦌)) (z : A.obj (op ⦋n⦌))
    (hz : (p.app (op ⦋n⦌)).hom z = b) (x : principalRealizationPullback p b) :
    ((principalRealizationHomeomorph p b z hz).symm x).2 = x.val.2 := by
  have h := principalRealizationHomeomorph_snd p b z hz
    ((principalRealizationHomeomorph p b z hz).symm x)
  rw [Homeomorph.apply_symm_apply] at h
  exact h.symm

/-- Every simplex of a degreewise surjection has the displayed actual
continuous product trivialization of its topological pullback. -/
theorem principalRealizationHomeomorph_exists_of_degreewise_surjective
    {A B : SimplicialObject (ModuleCat.{u} R)} (p : A ⟶ B)
    (hp : ∀ n : ℕ, Function.Surjective (p.app (op ⦋n⦌)).hom)
    (n : ℕ) (b : B.obj (op ⦋n⦌)) :
    ∃ e : (|kernel p ⋙ forget (ModuleCat R)| × |(Δ[n] : SSet.{u})|) ≃ₜ
      principalRealizationPullback p b, ∀ x, (e x).val.2 = x.2 := by
  obtain ⟨z,hz⟩ := hp n b
  exact ⟨principalRealizationHomeomorph p b z hz, principalRealizationHomeomorph_snd p b z hz⟩


end KIP126.Algebra.SimplicialModule
