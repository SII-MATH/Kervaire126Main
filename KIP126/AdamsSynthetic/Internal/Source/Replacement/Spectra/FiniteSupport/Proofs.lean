module

/-
Copyright (c) 2026 Jiashuo Zhang and KIP126 contributors.
Released under the MIT license; see LICENSE.
Privately adapted from SII-MATH/Kervaire126Main, commit
c60fbbbb93ee1f225e69bb8b93d06b4f842d031d,
KIP126/Def/StableHomotopy/Spectra/FiniteSupport/Proofs.lean.
-/

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.FiniteSupport.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.CWComplex.FiniteSupport.Proofs

@[expose] section

namespace KIP126.AdamsSynthetic.Source

open CategoryTheory _root_.Topology
open scoped unitInterval

universe u

namespace BasedSpace

/-- An actual based map from a compact space to a CW space factors through
a finite CW subcomplex, including the specified basepoint. -/
theorem map_factor_finite_subcomplex {A B : BasedSpace.{u}}
    [CompactSpace A] [T2Space B] [CWComplex (Set.univ : Set B)] (f : A ⟶ B) :
    ∃ E : CWComplex.Subcomplex (Set.univ : Set B),
      CWComplex.Finite (E : Set B) ∧ ∃ hp : B.point ∈ E,
        ∃ g : A ⟶ B.subspace E hp, g ≫ B.subspaceInclusion E hp = f := by
  obtain ⟨E,hE,he⟩ := KIP126.Topology.cw_compact_subset_finite_subcomplex
    (Set.range f.map) (isCompact_range f.map.continuous) (Set.subset_univ _)
  have hp : B.point ∈ E := he ⟨A.point,f.point⟩
  let g : A ⟶ B.subspace E hp :=
    ⟨⟨fun a => ⟨f.map a,he ⟨a,rfl⟩⟩,f.map.continuous.subtype_mk _⟩,
      Subtype.ext f.point⟩
  exact ⟨E,hE,hp,g,rfl⟩

/-- Every actual cubical loop in a CW space has finite subcomplex support. -/
theorem genLoop_factor_finite_subcomplex (B : BasedSpace.{u})
    [T2Space B] [CWComplex (Set.univ : Set B)] {r : ℕ}
    (p : GenLoop (Fin r) B B.point) :
    ∃ E : CWComplex.Subcomplex (Set.univ : Set B),
      CWComplex.Finite (E : Set B) ∧ ∃ hp : B.point ∈ E,
        ∃ q : GenLoop (Fin r) (B.subspace E hp) (B.subspace E hp).point,
          ∀ x, (q x).1 = p x := by
  obtain ⟨E,hE,he⟩ := KIP126.Topology.cw_compact_subset_finite_subcomplex
    ({B.point} ∪ Set.range p.val)
    (isCompact_singleton.union (isCompact_range p.val.continuous)) (Set.subset_univ _)
  have hp : B.point ∈ E := he (Or.inl (Set.mem_singleton _))
  let q : GenLoop (Fin r) (B.subspace E hp) (B.subspace E hp).point :=
    ⟨⟨fun x => ⟨p x,he (Or.inr ⟨x,rfl⟩)⟩,p.val.continuous.subtype_mk _⟩,
      fun x hx => Subtype.ext (p.property x hx)⟩
  exact ⟨E,hE,hp,q,fun _ => rfl⟩

/-- A based cubical homotopy, including both endpoint loops, takes place
inside one actual finite subcomplex. -/
theorem genLoop_homotopy_factor_finite_subcomplex (B : BasedSpace.{u})
    [T2Space B] [CWComplex (Set.univ : Set B)] {r : ℕ}
    {p q : GenLoop (Fin r) B B.point} (h : GenLoop.Homotopic p q) :
    ∃ E : CWComplex.Subcomplex (Set.univ : Set B),
      CWComplex.Finite (E : Set B) ∧ ∃ hp : B.point ∈ E,
        ∃ p' q' : GenLoop (Fin r) (B.subspace E hp) (B.subspace E hp).point,
          (∀ x, (p' x).1 = p x) ∧ (∀ x, (q' x).1 = q x) ∧
          GenLoop.Homotopic p' q' := by
  obtain ⟨H⟩ := h
  obtain ⟨E,hE,he⟩ := KIP126.Topology.cw_compact_subset_finite_subcomplex
    ({B.point} ∪ Set.range H.toContinuousMap)
    (isCompact_singleton.union (isCompact_range H.continuous)) (Set.subset_univ _)
  have hp : B.point ∈ E := he (Or.inl (Set.mem_singleton _))
  have hpE (x) : p x ∈ E := he (Or.inr ⟨(0,x),H.apply_zero x⟩)
  have hqE (x) : q x ∈ E := he (Or.inr ⟨(1,x),H.apply_one x⟩)
  let p' : GenLoop (Fin r) (B.subspace E hp) (B.subspace E hp).point :=
    ⟨⟨fun x => ⟨p x,hpE x⟩,p.val.continuous.subtype_mk _⟩,
      fun x hx => Subtype.ext (p.property x hx)⟩
  let q' : GenLoop (Fin r) (B.subspace E hp) (B.subspace E hp).point :=
    ⟨⟨fun x => ⟨q x,hqE x⟩,q.val.continuous.subtype_mk _⟩,
      fun x hx => Subtype.ext (q.property x hx)⟩
  refine ⟨E,hE,hp,p',q',fun _ => rfl,fun _ => rfl,⟨?_⟩⟩
  exact {
    toFun := fun x => ⟨H x,he (Or.inr ⟨x,rfl⟩)⟩
    continuous_toFun := H.continuous.subtype_mk _
    map_zero_left := fun x => Subtype.ext (H.apply_zero x)
    map_one_left := fun x => Subtype.ext (H.apply_one x)
    prop' := fun s x hx => Subtype.ext (H.eq_fst s hx) }

end BasedSpace

namespace Prespectrum

/-- At its generating stage the actual free prespectrum is its input space. -/
theorem free_level (n : ℕ) (A : BasedSpace.{u}) : (free n A).level n = A := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change ((desuspension^[n+1]) (suspensionSpectrum A)).level (n+1) = A
    rw [Function.iterate_succ_apply']
    exact ih

/-- The chosen free/evaluation equivalence is natural for actual
prespectrum maps, as follows from its specified level formula. -/
theorem freeEvaluation_natural (n : ℕ) (A : BasedSpace.{u})
    {X Y : Prespectrum.{u}} (f : free n A ⟶ X) (g : X ⟶ Y) :
    freeEvaluation n A Y (f ≫ g) =
      freeEvaluation n A X f ≫ (⟨g.level n,g.point n⟩ : X.level n ⟶ Y.level n) := by
  apply BasedSpace.Hom.ext
  apply eq_of_heq
  have hf := (freeEvaluation_exists n A X).choose_spec f
  have hfg := (freeEvaluation_exists n A Y).choose_spec (f ≫ g)
  apply hfg.trans
  have hc {B : BasedSpace.{u}} (hB : B = A) (a : C(B,X.level n))
      (b : C(A,X.level n)) (hab : HEq a b) :
      HEq ((g.level n).comp a) ((g.level n).comp b) := by
    subst B
    rw [eq_of_heq hab]
  exact hc (free_level n A) (f.level n) (freeEvaluation n A X f).map hf.symm

/-- The actual induced free map has the expected evaluation formula after
composition with any actual prespectrum map. -/
theorem freeEvaluation_freeMap_comp (n : ℕ) {A B : BasedSpace.{u}}
    (f : A ⟶ B) {X : Prespectrum.{u}} (g : free n B ⟶ X) :
    freeEvaluation n A X (freeMap n f ≫ g) = f ≫ freeEvaluation n B X g := by
  rw [freeEvaluation_natural]
  simp only [freeMap, Equiv.apply_symm_apply, Category.assoc]
  have h := freeEvaluation_natural n B (𝟙 (free n B)) g
  rw [Category.id_comp] at h
  rw [← h]

/-- A map from a free prespectrum on a compact based space into a levelwise
CW prespectrum factors through a free prespectrum on an actual finite
subcomplex of the generating level. -/
theorem free_map_factor_finite_subcomplex (n : ℕ) (A : BasedSpace.{u})
    [CompactSpace A] (X : Prespectrum.{u}) [T2Space (X.level n)]
    [CWComplex (Set.univ : Set (X.level n))] (f : free n A ⟶ X) :
    ∃ E : CWComplex.Subcomplex (Set.univ : Set (X.level n)),
      CWComplex.Finite (E : Set (X.level n)) ∧ ∃ hp : (X.level n).point ∈ E,
        ∃ (a : A ⟶ (X.level n).subspace E hp)
          (b : free n ((X.level n).subspace E hp) ⟶ X), freeMap n a ≫ b = f := by
  obtain ⟨E,hE,hp,a,ha⟩ := BasedSpace.map_factor_finite_subcomplex
    (freeEvaluation n A X f)
  let b : free n ((X.level n).subspace E hp) ⟶ X :=
    (freeEvaluation n ((X.level n).subspace E hp) X).symm
      ((X.level n).subspaceInclusion E hp)
  refine ⟨E,hE,hp,a,b,?_⟩
  apply (freeEvaluation n A X).injective
  rw [freeEvaluation_freeMap_comp]
  simpa only [b,Equiv.apply_symm_apply] using ha

end Prespectrum

end KIP126.AdamsSynthetic.Source
