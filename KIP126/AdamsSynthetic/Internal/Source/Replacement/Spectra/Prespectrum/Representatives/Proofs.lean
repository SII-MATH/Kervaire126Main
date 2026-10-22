module

/-
Copyright (c) 2026 Jiashuo Zhang and KIP126 contributors.
Released under the MIT license; see LICENSE.
Privately adapted from SII-MATH/Kervaire126Main, commit
c60fbbbb93ee1f225e69bb8b93d06b4f842d031d,
KIP126/Def/StableHomotopy/Spectra/Prespectrum/Representatives/Proofs.lean.
-/

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum.Representatives.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Sphere.Representatives.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.FiniteSupport.CWType.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum.Path.Proofs

@[expose] section

namespace KIP126.AdamsSynthetic.Source.Prespectrum
open CategoryTheory _root_.Topology
open scoped unitInterval

/-- A homotopy of the actual generating cubes makes the two free sphere
maps equal in the ordinary stable localization. -/
theorem source_freeSphere_maps_eq_of_genLoop_homotopy (n r : ℕ) (X : Prespectrum)
    (p q : GenLoop (Fin r) (X.level n) (X.level n).point)
    (f g : free n (sphereLevel r) ⟶ X)
    (hf : ∀ t, f.level n (freeSphereLoop n r t) = p t)
    (hg : ∀ t, g.level n (freeSphereLoop n r t) = q t)
    (h : GenLoop.Homotopic p q) : sourceLocalization.map f = sourceLocalization.map g := by
  have hfe (t) : (freeEvaluation n (sphereLevel r) X f).map (sphereCube r t) = p t := by
    have he := freeEvaluation_natural n (sphereLevel r) (𝟙 _) f
    rw [Category.id_comp] at he
    exact (congrArg (fun a : sphereLevel r ⟶ X.level n => a.map (sphereCube r t)) he).trans (hf t)
  have hge (t) : (freeEvaluation n (sphereLevel r) X g).map (sphereCube r t) = q t := by
    have he := freeEvaluation_natural n (sphereLevel r) (𝟙 _) g
    rw [Category.id_comp] at he
    exact (congrArg (fun a : sphereLevel r ⟶ X.level n => a.map (sphereCube r t)) he).trans (hg t)
  exact source_free_maps_eq_of_based_homotopy n (sphereLevel r) X f g
    ((genLoop_homotopic_iff_sphereLevel_maps_homotopic r (X.level n) p q
      (freeEvaluation n (sphereLevel r) X f) (freeEvaluation n (sphereLevel r) X g) hfe hge).mp h)

/-- The free/evaluation adjunction turns a cubical loop into a unique actual
prespectrum map whose generating cube is that loop. -/
theorem genLoop_freeSphere_map_exists_unique (X : Prespectrum) (n r : ℕ)
    (p : GenLoop (Fin r) (X.level n) (X.level n).point) :
    ∃! f : free n (sphereLevel r) ⟶ X,
      ∀ t, f.level n (freeSphereLoop n r t) = p t := by
  obtain ⟨g,hg,huniq⟩ := genLoop_sphereLevel_map_exists_unique r (X.level n) p
  let f := (freeEvaluation n (sphereLevel r) X).symm g
  have formula (k : free n (sphereLevel r) ⟶ X) (t : Fin r → I) :
      k.level n (freeSphereLoop n r t) =
        (freeEvaluation n (sphereLevel r) X k).map (sphereCube r t) := by
    have he := freeEvaluation_natural n (sphereLevel r) (𝟙 _) k
    rw [Category.id_comp] at he
    exact (congrArg (fun a : sphereLevel r ⟶ X.level n => a.map (sphereCube r t)) he).symm
  have hf (t) : f.level n (freeSphereLoop n r t) = p t := by
    rw [formula]
    exact (congrArg (fun a : sphereLevel r ⟶ X.level n => a.map (sphereCube r t))
      ((freeEvaluation n (sphereLevel r) X).apply_symm_apply g)).trans (hg t)
  refine ⟨f,hf,?_⟩
  intro k hk
  apply (freeEvaluation n (sphereLevel r) X).injective
  rw [show freeEvaluation n (sphereLevel r) X f = g from Equiv.apply_symm_apply _ _]
  exact huniq _ (fun t => (formula k t).symm.trans (hk t))

/-- Every class of the actual stable quotient is the image of the canonical
generator under an actual map from a shifted free sphere. -/
theorem stableHomotopy_represented_by_freeSphere (X : Prespectrum) (d : ℤ)
    (x : StableHomotopy X d) :
    ∃ (n r : ℕ) (h : (r : ℤ) = d + n) (f : free n (sphereLevel r) ⟶ X),
      stableHomotopyMap f d (freeSphereGenerator d n r h) = x := by
  induction x using Quot.inductionOn with
  | h a =>
    obtain ⟨f,hf,_⟩ := genLoop_freeSphere_map_exists_unique X a.stage a.dimension a.loop
    refine ⟨a.stage,a.dimension,a.degree,f,?_⟩
    change Quot.mk (StableRelation X d)
      ((⟨a.stage,a.dimension,a.degree,freeSphereLoop a.stage a.dimension⟩ :
        Representative (free a.stage (sphereLevel a.dimension)) d).map f) = Quot.mk _ a
    congr 1
    cases a with
    | mk n r h p =>
      dsimp [Representative.map]
      congr 1
      exact GenLoop.ext _ _ hf

/-- With the actual based CW homotopy models of the levels, every stable
class has a representative factoring through a free prespectrum on a finite
CW subcomplex. The finite subcomplex is allowed to depend on the class. -/
theorem stableHomotopy_represented_by_finite_CW_model (X : Prespectrum)
    (hX : ∀ n, (X.level n).HasCWType) (d : ℤ) (x : StableHomotopy X d) :
    ∃ (n r : ℕ) (h : (r : ℤ) = d + n)
      (Y : BasedSpace) (hY : T2Space Y) (cY : CWComplex (Set.univ : Set Y)),
      letI := hY
      letI := cY
      ∃ E : CWComplex.Subcomplex (Set.univ : Set Y),
        CWComplex.Finite (E : Set Y) ∧ ∃ hp : Y.point ∈ E,
          ∃ (a : sphereLevel r ⟶ Y.subspace E hp)
            (b : free n (Y.subspace E hp) ⟶ X),
            stableHomotopyMap (freeMap n a ≫ b) d (freeSphereGenerator d n r h) = x := by
  induction x using Quot.inductionOn with
  | h a =>
    obtain ⟨Y,hY,cY,E,hE,hp,q,bSpace,hq⟩ :=
      BasedSpace.genLoop_factor_finite_model_of_hasCWType (X.level a.stage) (hX a.stage) a.loop
    letI := hY
    letI := cY
    obtain ⟨g,hg,_⟩ := genLoop_sphereLevel_map_exists_unique a.dimension (Y.subspace E hp) q
    let b := (freeEvaluation a.stage (Y.subspace E hp) X).symm bSpace
    let f := freeMap a.stage g ≫ b
    have hf : freeEvaluation a.stage (sphereLevel a.dimension) X f = g ≫ bSpace := by
      rw [freeEvaluation_freeMap_comp]
      exact congrArg (fun k => g ≫ k) (Equiv.apply_symm_apply _ _)
    have formula (t : Fin a.dimension → I) :
        f.level a.stage (freeSphereLoop a.stage a.dimension t) = bSpace.map (q t) := by
      have he := freeEvaluation_natural a.stage (sphereLevel a.dimension) (𝟙 _) f
      rw [Category.id_comp, hf] at he
      have he' := congrArg
        (fun k : sphereLevel a.dimension ⟶ X.level a.stage => k.map (sphereCube a.dimension t)) he
      exact he'.symm.trans (congrArg bSpace.map (hg t))
    refine ⟨a.stage,a.dimension,a.degree,Y,hY,cY,E,hE,hp,g,b,?_⟩
    change Quot.mk (StableRelation X d)
      ((⟨a.stage,a.dimension,a.degree,freeSphereLoop a.stage a.dimension⟩ :
        Representative (free a.stage (sphereLevel a.dimension)) d).map f) = Quot.mk _ a
    have heq : ((⟨a.stage,a.dimension,a.degree,freeSphereLoop a.stage a.dimension⟩ :
        Representative (free a.stage (sphereLevel a.dimension)) d).map f) =
        { a with loop := ⟨bSpace.map.comp q.val,
          fun t ht => (congrArg bSpace.map (q.property t ht)).trans bSpace.point⟩ } := by
      cases a with
      | mk n r h p =>
        dsimp [Representative.map]
        congr 1
        exact GenLoop.ext _ _ formula
    rw [heq]
    have hs := StableRelation.homotopy
      ({ a with loop := ⟨bSpace.map.comp q.val,
          fun t ht => (congrArg bSpace.map (q.property t ht)).trans bSpace.point⟩ }) a.loop hq
    have ht : { a with loop := a.loop } = a := by cases a; rfl
    simpa only [ht] using Quot.sound hs


end KIP126.AdamsSynthetic.Source.Prespectrum
