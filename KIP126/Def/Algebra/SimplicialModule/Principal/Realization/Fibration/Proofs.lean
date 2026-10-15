module

public import KIP126.Def.Algebra.SimplicialModule.Principal.Realization.Proofs
public import KIP126.Def.Topology.SimplicialRealization.LocalTriviality.Proofs
public import KIP126.Def.Topology.SimplicialRealization.Lifting.Finite.Proofs
public import KIP126.Def.Topology.HomotopyLifting.Bundle

@[expose] public section

namespace KIP126.Algebra.SimplicialModule

open CategoryTheory CategoryTheory.Limits Simplicial Opposite
open KIP126.Topology KIP126.Topology.SimplicialRealization
universe u
variable {R : Type u} [Ring R]
set_option backward.isDefEq.respectTransparency false

/-- Realizing the zero vertex gives an actual point of the realized
underlying simplicial module. -/
theorem realization_nonempty (A : SimplicialObject (ModuleCat.{u} R)) :
    Nonempty |A ⋙ forget (ModuleCat R)| :=
  ⟨simplexPoint (A ⋙ forget (ModuleCat R)) (a := op ⦋0⦌)
    (0 : A.obj (op ⦋0⦌)) default⟩

/-- Each simplex of an arbitrary simplicial base change has an actual
product chart, obtained by flattening the pullback and translating by a lift
of its image simplex. -/
theorem principalRealization_pullback_simplex_triviality
    {A B : SimplicialObject (ModuleCat.{u} R)} (p : A ⟶ B)
    (hp : ∀ n : ℕ, Function.Surjective (p.app (op ⦋n⦌)).hom)
    {X : SSet.{u}} (a : X ⟶ B ⋙ forget (ModuleCat R))
    (n : ℕ) (s : X.obj (op ⦋n⦌)) :
    ∃ e : {z : {z : |A ⋙ forget (ModuleCat R)| × |X| //
        SSet.toTop.map (Functor.whiskerRight p (forget (ModuleCat R))) z.1 =
          SSet.toTop.map a z.2} × |(Δ[n] : SSet.{u})| //
        z.1.val.2 = SSet.toTop.map (SSet.yonedaEquiv.symm s) z.2} ≃ₜ
      (|kernel p ⋙ forget (ModuleCat R)| × |(Δ[n] : SSet.{u})|),
      ∀ z, (e z).2 = z.val.2 := by
  let pT := (SSet.toTop.map (Functor.whiskerRight p (forget (ModuleCat R)))).hom
  let aT := (SSet.toTop.map a).hom
  let sT := (SSet.toTop.map (SSet.yonedaEquiv.symm s)).hom
  let b : B.obj (op ⦋n⦌) := a.app _ s
  have hcomp : SSet.yonedaEquiv.symm s ≫ a = SSet.yonedaEquiv.symm b := by
    apply SSet.yonedaEquiv.injective
    simp only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
    rfl
  have ht : aT.comp sT = (SSet.toTop.map (SSet.yonedaEquiv.symm b)).hom := by
    ext t
    exact ConcreteCategory.congr_hom
      ((SSet.toTop.map_comp _ _).symm.trans (congrArg SSet.toTop.map hcomp)) t
  have hd : ∃ e : {z : |A ⋙ forget (ModuleCat R)| × |(Δ[n] : SSet.{u})| //
      pT z.1 = (aT.comp sT) z.2} ≃ₜ
      (|kernel p ⋙ forget (ModuleCat R)| × |(Δ[n] : SSet.{u})|),
      ∀ z, (e z).2 = z.val.2 := by
    rw [ht]
    obtain ⟨z,hz⟩ := hp n b
    exact ⟨(principalRealizationHomeomorph p b z hz).symm,
      principalRealizationHomeomorph_symm_snd p b z hz⟩
  obtain ⟨e,he⟩ := hd
  exact ⟨(iteratedPullbackHomeomorph pT aT sT).trans e,fun z => he _⟩

/-- A degreewise surjective simplicial module map, restricted to any
finite simplicial base, has genuine open local trivializations. -/
theorem principalRealization_finite_pullback_localTriviality
    {A B : SimplicialObject (ModuleCat.{u} R)} (p : A ⟶ B)
    (hp : ∀ n : ℕ, Function.Surjective (p.app (op ⦋n⦌)).hom)
    {X : SSet.{u}} [X.Finite] (a : X ⟶ B ⋙ forget (ModuleCat R)) :
    ∀ x, ∃ T : Bundle.Trivialization |kernel p ⋙ forget (ModuleCat R)|
      (SSet.toTop.map (pullback.snd (Functor.whiskerRight p (forget (ModuleCat R))) a)).hom,
      x ∈ T.baseSet := by
  letI := realization_nonempty (kernel p)
  let pT := (SSet.toTop.map (Functor.whiskerRight p (forget (ModuleCat R)))).hom
  let aT := (SSet.toTop.map a).hom
  have hlocal := finite_realization_localTriviality_of_simplex_triviality X
    (pullbackSndMap pT aT) (principalRealization_pullback_simplex_triviality p hp a)
  exact localTriviality_of_total_homeomorph (pullbackSndMap pT aT)
    (SSet.toTop.map (pullback.snd (Functor.whiskerRight p (forget (ModuleCat R))) a)).hom
    (finitePullbackHomeomorph (Functor.whiskerRight p (forget (ModuleCat R))) a)
    (finitePullbackHomeomorph_snd (Functor.whiskerRight p (forget (ModuleCat R))) a) hlocal

/-- The geometric realization of a degreewise surjective simplicial
module map has actual relative homotopy lifting for all finite cube boundaries.
The proof uses finite simplicial support, actual open bundle charts, and their
proved cubical lifting property. -/
theorem degreewise_surjective_realization_hasCubicalLifting
    {A B : SimplicialObject (ModuleCat.{u} R)} (p : A ⟶ B)
    (hp : ∀ n : ℕ, Function.Surjective (p.app (op ⦋n⦌)).hom) :
    HomotopyLifting.HasCubicalLifting
      (SSet.toTop.map (Functor.whiskerRight p (forget (ModuleCat R)))).hom := by
  apply hasCubicalLifting_of_finite_subcomplexes
  intro X hX
  letI := hX
  exact HomotopyLifting.hasCubicalLifting_of_locally_trivial _
    (principalRealization_finite_pullback_localTriviality p hp X.ι)

end KIP126.Algebra.SimplicialModule
