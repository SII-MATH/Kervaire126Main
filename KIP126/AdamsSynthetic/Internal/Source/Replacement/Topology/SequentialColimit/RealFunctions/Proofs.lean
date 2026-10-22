module

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SequentialColimit.Proofs
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Instances.Real.Lemmas

@[expose] section

namespace KIP126.Topology

open CategoryTheory CategoryTheory.Limits _root_.Topology

universe u

set_option backward.isDefEq.respectTransparency false

/-- Compatible extension across the actual successive stages extends a
real-valued function on any fixed stage to the genuine sequential colimit. -/
theorem exists_real_extension_nat_colimit
    (F : ℕ ⥤ TopCat.{u}) (c : Cocone F) (hc : IsColimit c)
    (hExt : ∀ k (f : C(F.obj k, ℝ)), ∃ g : C(F.obj (k+1), ℝ),
      ∀ x, g (F.map (homOfLE (Nat.le_succ k)) x) = f x)
    (n : ℕ) (f : C(F.obj n, ℝ)) :
    ∃ g : C(c.pt, ℝ), ∀ x, g (c.ι.app n x) = f x := by
  let A (k : ℕ) := {g : C(F.obj k, ℝ) //
    ∀ h : k ≤ n, ∀ x, g x = f (F.map (homOfLE h) x)}
  have next_exists (k : ℕ) (g : A k) :
      ∃ g' : A (k+1), ∀ x, g'.1 (F.map (homOfLE (Nat.le_succ k)) x) = g.1 x := by
    by_cases hkn : k+1 ≤ n
    · refine ⟨⟨f.comp (F.map (homOfLE hkn)).hom,fun h x => rfl⟩,?_⟩
      intro x
      rw [g.2 (by omega)]
      change f (F.map (homOfLE hkn) (F.map (homOfLE (Nat.le_succ k)) x)) = _
      rw [← TopCat.comp_app,← Functor.map_comp]
      rfl
    · obtain ⟨g',hg'⟩ := hExt k g.1
      exact ⟨⟨g',fun h => (hkn h).elim⟩,hg'⟩
  let initial : A 0 := ⟨f.comp (F.map (homOfLE (Nat.zero_le n))).hom,fun h x => rfl⟩
  let seq : ∀ k, A k := fun k => Nat.rec initial (fun k g => (next_exists k g).choose) k
  have hs (k : ℕ) (x : F.obj k) :
      (seq (k+1)).1 (F.map (homOfLE (Nat.le_succ k)) x) = (seq k).1 x :=
    (next_exists k (seq k)).choose_spec x
  have hseq {k l : ℕ} (h : k ≤ l) (x : F.obj k) :
      (seq l).1 (F.map (homOfLE h) x) = (seq k).1 x := by
    induction l, h using Nat.le_induction with
    | base => simp
    | succ l h ih =>
      have he : homOfLE (by omega : k ≤ l+1) = homOfLE h ≫ homOfLE (Nat.le_succ l) := rfl
      rw [he,Functor.map_comp,TopCat.comp_app,hs]
      exact ih
  let q : Cocone F :=
    { pt := TopCat.of (ULift.{u} ℝ)
      ι :=
        { app := fun k => TopCat.ofHom
            ⟨fun x => ULift.up ((seq k).1 x), continuous_uliftUp.comp (seq k).1.continuous⟩
          naturality := fun k l h => by
            ext x
            apply ULift.ext
            exact hseq (leOfHom h) x } }
  let d := hc.desc q
  refine ⟨⟨fun x => (d x).down, continuous_uliftDown.comp d.hom.continuous⟩,?_⟩
  intro x
  have hd := congrArg ULift.down (ConcreteCategory.congr_hom (hc.fac q n) x)
  exact hd.trans (by change (seq n).1 x = f x; simpa using (seq n).2 (le_refl n) x)

/-- Separation of points by real functions passes to the actual sequential
colimit when those functions extend across successive stages. -/
theorem real_functions_separate_points_nat_colimit
    (F : ℕ ⥤ TopCat.{u}) (c : Cocone F) (hc : IsColimit c)
    (hExt : ∀ k (f : C(F.obj k, ℝ)), ∃ g : C(F.obj (k+1), ℝ),
      ∀ x, g (F.map (homOfLE (Nat.le_succ k)) x) = f x)
    (hSep : ∀ k, ∀ x y : F.obj k, x ≠ y → ∃ f : C(F.obj k, ℝ), f x ≠ f y) :
    ∀ p q : c.pt, p ≠ q → ∃ g : C(c.pt, ℝ), g p ≠ g q := by
  intro p q hpq
  have hc' := isColimitOfPreserves (forget TopCat) hc
  obtain ⟨n,x,hx⟩ := Types.jointly_surjective_of_isColimit hc' p
  obtain ⟨m,y,hy⟩ := Types.jointly_surjective_of_isColimit hc' q
  let kn : n ⟶ max n m := homOfLE (le_max_left n m)
  let km : m ⟶ max n m := homOfLE (le_max_right n m)
  have hn : c.ι.app (max n m) (F.map kn x) = p :=
    (ConcreteCategory.congr_hom (c.w kn) x).trans hx
  have hm : c.ι.app (max n m) (F.map km y) = q :=
    (ConcreteCategory.congr_hom (c.w km) y).trans hy
  have hxy : F.map kn x ≠ F.map km y := by
    intro h
    exact hpq (hn.symm.trans ((congrArg (c.ι.app (max n m)) h).trans hm))
  obtain ⟨f,hf⟩ := hSep (max n m) (F.map kn x) (F.map km y) hxy
  obtain ⟨g,hg⟩ := exists_real_extension_nat_colimit F c hc hExt (max n m) f
  refine ⟨g,?_⟩
  rw [← hn,← hm,hg,hg]
  exact hf

/-- Actual separation by real functions implies the Hausdorff axiom. -/
theorem t2Space_of_real_functions_separate_points {X : Type*} [TopologicalSpace X]
    (h : ∀ x y : X, x ≠ y → ∃ f : C(X, ℝ), f x ≠ f y) : T2Space X := by
  let e : X → (C(X, ℝ) → ℝ) := fun x f => f x
  have he : Function.Injective e := by
    intro x y hxy
    by_contra hne
    obtain ⟨f,hf⟩ := h x y hne
    exact hf (congrFun hxy f)
  exact T2Space.of_injective_continuous he (continuous_pi fun f => f.continuous)

end KIP126.Topology
