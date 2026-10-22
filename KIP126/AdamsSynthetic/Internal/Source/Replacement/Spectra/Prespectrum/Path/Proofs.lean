module

/-
Copyright (c) 2026 Jiashuo Zhang and KIP126 contributors.
Released under the MIT license; see LICENSE.
Privately adapted from SII-MATH/Kervaire126Main, commit
c60fbbbb93ee1f225e69bb8b93d06b4f842d031d,
KIP126/Def/StableHomotopy/Spectra/Prespectrum/Path/Proofs.lean.
-/

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum.Path.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.FiniteSupport.Proofs

@[expose] section

namespace KIP126.AdamsSynthetic.Source.Prespectrum
open CategoryTheory _root_.Topology
open scoped unitInterval
universe u

@[simp] theorem pathConstant_comp_evaluation (X : Prespectrum.{u}) (s : I) :
    pathConstant X ≫ pathEvaluation X s = 𝟙 X := rfl

/-- Contracting the path parameter gives actual based cubical homotopies,
so constant paths induce bijections of every stable homotopy set. -/
theorem pathConstant_stableEquivalence (X : Prespectrum.{u}) :
    stableEquivalences (pathConstant X) := by
  intro d
  have hl (x : StableHomotopy X d) :
      stableHomotopyMap (pathEvaluation X 0) d (stableHomotopyMap (pathConstant X) d x) = x := by
    induction x using Quot.inductionOn with
    | h a => rfl
  have hr (x : StableHomotopy (pathPrespectrum X) d) :
      stableHomotopyMap (pathConstant X) d (stableHomotopyMap (pathEvaluation X 0) d x) = x := by
    induction x using Quot.inductionOn with
    | h a =>
      let p : GenLoop (Fin a.dimension) C(I,X.level a.stage) (ContinuousMap.const _ (X.level a.stage).point) := a.loop
      have H : GenLoop.Homotopic ((a.map (pathEvaluation X 0)).map (pathConstant X)).loop a.loop := by
        refine ⟨{
          toFun := fun z => ⟨fun t => p z.2 (z.1 * t),
            (p z.2).continuous.comp
              (((continuous_const : Continuous (fun _ : I => (z.1 : ℝ))).mul continuous_subtype_val).subtype_mk _)⟩
          continuous_toFun := ?_
          map_zero_left := ?_
          map_one_left := ?_
          prop' := ?_ }⟩
        · apply ContinuousMap.continuous_of_continuous_uncurry
          change Continuous (fun z : (I × (Fin a.dimension → I)) × I =>
            p z.1.2 (z.1.1 * z.2))
          exact (p.val.continuous.comp continuous_fst.snd).eval
            ((continuous_fst.fst.subtype_val.mul continuous_snd.subtype_val).subtype_mk _)
        · intro t
          apply ContinuousMap.ext
          intro s
          simp only [zero_mul]
          rfl
        · intro t
          apply ContinuousMap.ext
          intro s
          simp only [one_mul]
          rfl
        · intro s t ht
          apply ContinuousMap.ext
          intro v
          have hp := p.property t ht
          exact (congrArg (fun p : C(I,X.level a.stage) => p (s * v)) hp).trans
            (congrArg (fun p : C(I,X.level a.stage) => p 0) hp).symm
      change Quot.mk _ ((a.map (pathEvaluation X 0)).map (pathConstant X)) = Quot.mk _ a
      have he : { ((a.map (pathEvaluation X 0)).map (pathConstant X)) with loop := a.loop } = a := by
        cases a
        rfl
      have hs := Quot.sound (StableRelation.homotopy
        ((a.map (pathEvaluation X 0)).map (pathConstant X)) a.loop H)
      simpa only [he] using hs
  exact ⟨fun x y h => (hl x).symm.trans ((congrArg (stableHomotopyMap (pathEvaluation X 0) d) h).trans (hl y)),
    fun x => ⟨stableHomotopyMap (pathEvaluation X 0) d x,hr x⟩⟩

/-- All path evaluations agree after the actual stable localization. -/
theorem source_pathEvaluation_eq (X : Prespectrum.{u}) (s t : I) :
    sourceLocalization.map (pathEvaluation X s) = sourceLocalization.map (pathEvaluation X t) := by
  haveI : IsIso (sourceLocalization.map (pathConstant X)) :=
    stableEquivalences.Q_inverts _ (pathConstant_stableEquivalence X)
  apply (cancel_epi (sourceLocalization.map (pathConstant X))).mp
  rw [← Functor.map_comp, ← Functor.map_comp, pathConstant_comp_evaluation, pathConstant_comp_evaluation]

/-- A based homotopy of the generating maps extends to the path prespectrum;
its endpoint maps therefore agree in the actual stable localization. -/
theorem source_free_maps_eq_of_based_homotopy (n : ℕ) (A : BasedSpace.{u})
    (X : Prespectrum.{u}) (f g : free n A ⟶ X)
    (h : (freeEvaluation n A X f).map.HomotopicRel
      (freeEvaluation n A X g).map {A.point}) :
    sourceLocalization.map f = sourceLocalization.map g := by
  obtain ⟨H⟩ := h
  let kLevel : A ⟶ (pathPrespectrum X).level n :=
    { map := (H.toContinuousMap.comp ⟨Prod.swap,continuous_swap⟩).curry
      point := by
        apply ContinuousMap.ext
        intro s
        exact (H.eq_fst s (Set.mem_singleton _)).trans (freeEvaluation n A X f).point }
  let k : free n A ⟶ pathPrespectrum X := (freeEvaluation n A (pathPrespectrum X)).symm kLevel
  have hzero : k ≫ pathEvaluation X 0 = f := by
    apply (freeEvaluation n A X).injective
    rw [freeEvaluation_natural]
    rw [show freeEvaluation n A (pathPrespectrum X) k = kLevel from Equiv.apply_symm_apply _ _]
    apply BasedSpace.Hom.ext
    apply ContinuousMap.ext
    intro a
    exact H.apply_zero a
  have hone : k ≫ pathEvaluation X 1 = g := by
    apply (freeEvaluation n A X).injective
    rw [freeEvaluation_natural]
    rw [show freeEvaluation n A (pathPrespectrum X) k = kLevel from Equiv.apply_symm_apply _ _]
    apply BasedSpace.Hom.ext
    apply ContinuousMap.ext
    intro a
    exact H.apply_one a
  rw [← hzero, ← hone, Functor.map_comp, Functor.map_comp, source_pathEvaluation_eq X 0 1]


end KIP126.AdamsSynthetic.Source.Prespectrum
