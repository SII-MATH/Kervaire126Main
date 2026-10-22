module

/-
Copyright (c) 2026 Jiashuo Zhang and KIP126 contributors.
Released under the MIT license; see LICENSE.
Privately adapted from SII-MATH/Kervaire126Main, commit
c60fbbbb93ee1f225e69bb8b93d06b4f842d031d,
KIP126/Def/StableHomotopy/Spectra/Generators.lean.
-/

import all KIP126.AdamsSynthetic.Internal.Source.PointSet

@[expose] section
namespace KIP126.AdamsSynthetic.Source
open CategoryTheory Topology
open scoped unitInterval
universe u
namespace BasedSpace
/-- The quotient representative [a;t₀,…,tₙ₋₁] in an iterated suspension. -/
def iteratedPoint (A : BasedSpace.{u}) : ∀ n, A → (Fin n → I) → A.iterateSuspension n
  | 0, a, _ => a
  | n+1, a, t => suspensionProjection _ (iteratedPoint A n a (fun i => t i.succ), t 0)

end BasedSpace
namespace Prespectrum
def free (n : ℕ) (A : BasedSpace.{u}) : Prespectrum.{u} :=
  (desuspension^[n]) (suspensionSpectrum A)

/-- The free/evaluation adjunction pins down maps from free prespectra;
it is not an independently chosen assignment of stable maps. -/
theorem freeEvaluation_exists (n : ℕ) (A : BasedSpace.{u}) (X : Prespectrum.{u}) :
    ∃ e : (free n A ⟶ X) ≃ (A ⟶ X.level n),
      ∀ f, HEq ((e f).map) (f.level n) := by
  have freeBase (A : BasedSpace.{u}) (X : Prespectrum.{u}) :
      ∃ e : (suspensionSpectrum A ⟶ X) ≃ (A ⟶ X.level 0),
        ∀ f, (e f).map = f.level 0 := by
    let ev : (suspensionSpectrum A ⟶ X) → (A ⟶ X.level 0) :=
      fun f => ⟨f.level 0, f.point 0⟩
    have hinj : Function.Injective ev := by
      intro f g he
      apply Hom.ext
      funext n
      apply ContinuousMap.ext
      intro x
      induction n with
      | zero => exact congrArg (fun h : A ⟶ X.level 0 => h.map x) he
      | succ n ih =>
        refine Quot.inductionOn x ?_
        rintro ⟨y,t⟩
        exact (f.bond n y t).trans ((congrArg (fun z => X.bond n (z,t)) (ih y)).trans
          (g.bond n y t).symm)
    have hsurj : Function.Surjective ev := by
      intro g
      let levels : ∀ n, A.iterateSuspension n ⟶ X.level n := by
        intro n
        induction n with
        | zero => exact g
        | succ n ih =>
          let raw : C(A.iterateSuspension n × I, X.level (n+1)) :=
            (X.bond n).comp ⟨fun p => (ih.map p.1,p.2),
              (ih.map.continuous.comp continuous_fst).prodMk continuous_snd⟩
          have collapse (p : A.iterateSuspension n × I)
              (hp : BasedSpace.SuspensionCollapsed (A.iterateSuspension n) p) :
              raw p = (X.level (n+1)).point := by
            rcases hp with h | h | h
            · change X.bond n (ih.map p.1,p.2) = _
              rw [h, ih.point, X.bond_point]
            · change X.bond n (ih.map p.1,p.2) = _
              rw [h, X.bond_zero]
            · change X.bond n (ih.map p.1,p.2) = _
              rw [h, X.bond_one]
          have hr : ∀ a b, BasedSpace.SuspensionRelation (A.iterateSuspension n) a b →
              raw a = raw b := fun a b h => (collapse a h.1).trans (collapse b h.2).symm
          exact ⟨⟨Quot.lift raw hr, continuous_quot_lift hr raw.continuous⟩,
            collapse _ (Or.inl rfl)⟩
      let f : suspensionSpectrum A ⟶ X :=
        { level n := (levels n).map
          point n := (levels n).point
          bond n x t := rfl }
      exact ⟨f, rfl⟩
    exact ⟨Equiv.ofBijective ev ⟨hinj, hsurj⟩, fun _ => rfl⟩
  induction n generalizing X with
  | zero =>
    obtain ⟨e, he⟩ := freeBase A X
    exact ⟨e, fun f => heq_of_eq (he f)⟩
  | succ n ih =>
    have hfree : free (n+1) A = desuspension (free n A) :=
      Function.iterate_succ_apply' desuspension n (suspensionSpectrum A)
    rw [hfree]
    let T : Prespectrum.{u} :=
      { level k := X.level (k+1)
        bond k := X.bond (k+1)
        bond_point k := X.bond_point (k+1)
        bond_zero k := X.bond_zero (k+1)
        bond_one k := X.bond_one (k+1) }
    let eD : (desuspension (free n A) ⟶ X) ≃ (free n A ⟶ T) :=
      { toFun f :=
          { level k := f.level (k+1)
            point k := f.point (k+1)
            bond k := f.bond (k+1) }
        invFun g :=
          { level
              | 0 => ContinuousMap.const _ (X.level 0).point
              | k+1 => g.level k
            point := by
              intro k
              cases k with
              | zero => rfl
              | succ k => exact g.point k
            bond := by
              intro k x t
              cases k with
              | zero =>
                change g.level 0 ((free n A).level 0).point = X.bond 0 ((X.level 0).point,t)
                rw [g.point, X.bond_point]
              | succ k => exact g.bond k x t }
        left_inv f := by
          apply Hom.ext
          funext k
          apply ContinuousMap.ext
          intro x
          cases k with
          | zero =>
            cases x
            exact (f.point 0).symm
          | succ k => rfl
        right_inv g := by
          apply Hom.ext
          rfl }
    obtain ⟨e, he⟩ := ih T
    exact ⟨eD.trans e, fun f => he (eD f)⟩

noncomputable def freeEvaluation (n : ℕ) (A : BasedSpace.{u}) (X : Prespectrum.{u}) :
    (free n A ⟶ X) ≃ (A ⟶ X.level n) :=
  (freeEvaluation_exists n A X).choose

noncomputable def freeCounit (X : Prespectrum.{u}) (n : ℕ) : free n (X.level n) ⟶ X :=
  (freeEvaluation n (X.level n) X).symm (𝟙 _)
end Prespectrum
end KIP126.AdamsSynthetic.Source
