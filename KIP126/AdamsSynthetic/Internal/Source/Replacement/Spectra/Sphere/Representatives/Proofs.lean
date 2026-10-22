module

/-
Copyright (c) 2026 Jiashuo Zhang and KIP126 contributors.
Released under the MIT license; see LICENSE.
Privately adapted from SII-MATH/Kervaire126Main, commit
c60fbbbb93ee1f225e69bb8b93d06b4f842d031d,
KIP126/Def/StableHomotopy/Spectra/Sphere/Representatives/Proofs.lean.
-/

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Sphere.Representatives.Data

@[expose] section

namespace KIP126.AdamsSynthetic.Source.Prespectrum
open CategoryTheory Topology
open scoped unitInterval

@[simp] theorem sphereCube_succ_apply (n : ℕ) (t : Fin (n+1) → I) :
    sphereCube (n+1) t = BasedSpace.suspensionProjection (sphereLevel n)
      (sphereCube n (fun i => t i.succ), t 0) := rfl

/-- The basepoint and the canonical cube cover the actual sphere quotient. -/
theorem sphereLevel_eq_point_or_sphereCube (n : ℕ) (x : sphereLevel n) :
    x = (sphereLevel n).point ∨ ∃ t, x = sphereCube n t := by
  induction n with
  | zero =>
    change Fin 2 at x
    fin_cases x
    · exact Or.inl rfl
    · exact Or.inr ⟨Fin.elim0, rfl⟩
  | succ n ih =>
    refine Quot.inductionOn x ?_
    rintro ⟨x,s⟩
    rcases ih x with hx | ⟨t,rfl⟩
    · left
      exact BasedSpace.suspensionProjection_collapsed _ _ (Or.inl hx)
    · right
      refine ⟨Fin.cons s t, ?_⟩
      simp only [sphereCube_succ_apply, Fin.cons_succ, Fin.cons_zero]
      rfl

/-- A based map out of the sphere is determined by its canonical cube. -/
theorem sphereLevel_map_ext (n : ℕ) {Y : BasedSpace}
    (f g : sphereLevel n ⟶ Y)
    (h : ∀ t, f.map (sphereCube n t) = g.map (sphereCube n t)) : f = g := by
  apply BasedSpace.Hom.ext
  apply ContinuousMap.ext
  intro x
  rcases sphereLevel_eq_point_or_sphereCube n x with rfl | ⟨t,rfl⟩
  · exact f.point.trans g.point.symm
  · exact h t

/-- Every based cubical loop extends uniquely across the actual sphere quotient.
The inductive extension uses the continuous path space as its target. -/
theorem genLoop_sphereLevel_map_exists_unique (n : ℕ) (Y : BasedSpace)
    (p : GenLoop (Fin n) Y Y.point) :
    ∃! f : sphereLevel n ⟶ Y, ∀ t, f.map (sphereCube n t) = p t := by
  induction n generalizing Y with
  | zero =>
    letI : DiscreteTopology (sphereLevel 0) := inferInstanceAs (DiscreteTopology (Fin 2))
    let f : sphereLevel 0 ⟶ Y :=
      { map := ⟨fun x : Fin 2 => if x = 0 then Y.point else p Fin.elim0,
          continuous_of_discreteTopology⟩
        point := by change (if (0 : Fin 2) = 0 then Y.point else p Fin.elim0) = Y.point; simp }
    refine ⟨f, ?_, ?_⟩
    · intro t
      have ht : t = Fin.elim0 := Subsingleton.elim _ _
      simp [f, sphereCube, ht]
    · intro g hg
      exact sphereLevel_map_ext 0 g f (fun t => (hg t).trans (by simp [f, sphereCube, show t = Fin.elim0 from Subsingleton.elim _ _]))
  | succ n ih =>
    let paths : BasedSpace :=
      { space := TopCat.of C(I,Y)
        point := ContinuousMap.const _ Y.point }
    let rawP : C((Fin n → I) × I,Y) :=
      ⟨fun z => p (Fin.cons z.2 z.1), p.val.continuous.comp (by
        apply continuous_pi
        intro i
        induction i using Fin.cases with
        | zero => exact continuous_snd
        | succ i => exact (continuous_apply i).comp continuous_fst)⟩
    let q : GenLoop (Fin n) paths paths.point := ⟨rawP.curry, by
      intro t ht
      apply ContinuousMap.ext
      intro s
      obtain ⟨i,hi⟩ := ht
      exact p.property _ ⟨i.succ, by simpa using hi⟩⟩
    obtain ⟨g,hg,_⟩ := ih paths q
    let raw : C(sphereLevel n × I,Y) := ContinuousMap.uncurry g.map
    have raw_cube (t : Fin n → I) (s : I) :
        raw (sphereCube n t,s) = p (Fin.cons s t) :=
      congrArg (fun a : C(I,Y) => a s) (hg t)
    have raw_point (s : I) : raw ((sphereLevel n).point,s) = Y.point :=
      congrArg (fun a : C(I,Y) => a s) g.point
    have collapsed (z : sphereLevel n × I)
        (hz : BasedSpace.SuspensionCollapsed (sphereLevel n) z) : raw z = Y.point := by
      rcases hz with hx | hs | hs
      · rw [show z = ((sphereLevel n).point,z.2) from Prod.ext hx rfl]
        exact raw_point z.2
      · rcases sphereLevel_eq_point_or_sphereCube n z.1 with hx | ⟨t,hx⟩
        · rw [show z = ((sphereLevel n).point,z.2) from Prod.ext hx rfl]
          exact raw_point z.2
        · rw [show z = (sphereCube n t,z.2) from Prod.ext hx rfl, raw_cube]
          exact p.property _ ⟨0, Or.inl (by simpa using hs)⟩
      · rcases sphereLevel_eq_point_or_sphereCube n z.1 with hx | ⟨t,hx⟩
        · rw [show z = ((sphereLevel n).point,z.2) from Prod.ext hx rfl]
          exact raw_point z.2
        · rw [show z = (sphereCube n t,z.2) from Prod.ext hx rfl, raw_cube]
          exact p.property _ ⟨0, Or.inr (by simpa using hs)⟩
    have hr : ∀ a b, BasedSpace.SuspensionRelation (sphereLevel n) a b → raw a = raw b :=
      fun a b h => (collapsed a h.1).trans (collapsed b h.2).symm
    let f : sphereLevel (n+1) ⟶ Y :=
      { map := ⟨Quot.lift raw hr, continuous_quot_lift hr raw.continuous⟩
        point := collapsed _ (Or.inl rfl) }
    have hf (t : Fin (n+1) → I) : f.map (sphereCube (n+1) t) = p t := by
      change raw (sphereCube n (fun i => t i.succ), t 0) = p t
      rw [raw_cube]
      congr
      ext i
      induction i using Fin.cases <;> rfl
    exact ⟨f,hf,fun f' hf' => sphereLevel_map_ext (n+1) f' f (fun t => (hf' t).trans (hf t).symm)⟩

/-- The quotient extension preserves and reflects homotopies fixed on the
cube boundary and the sphere basepoint, respectively. -/
theorem genLoop_homotopic_iff_sphereLevel_maps_homotopic (n : ℕ) (Y : BasedSpace)
    (p q : GenLoop (Fin n) Y Y.point) (f g : sphereLevel n ⟶ Y)
    (hf : ∀ t, f.map (sphereCube n t) = p t)
    (hg : ∀ t, g.map (sphereCube n t) = q t) :
    GenLoop.Homotopic p q ↔
      Nonempty (ContinuousMap.HomotopyRel f.map g.map {(sphereLevel n).point}) := by
  constructor
  · rintro ⟨H⟩
    let paths : BasedSpace :=
      { space := TopCat.of C(I,Y)
        point := ContinuousMap.const _ Y.point }
    let pH : GenLoop (Fin n) paths paths.point :=
      ⟨(H.toContinuousMap.comp ⟨Prod.swap,continuous_swap⟩).curry, by
        intro t ht
        apply ContinuousMap.ext
        intro s
        exact (H.eq_fst s ht).trans (p.property t ht)⟩
    obtain ⟨k,hk,_⟩ := genLoop_sphereLevel_map_exists_unique n paths pH
    have point (s : I) : k.map (sphereLevel n).point s = Y.point :=
      congrArg (fun a : C(I,Y) => a s) k.point
    have cube (t : Fin n → I) (s : I) : k.map (sphereCube n t) s = H (s,t) :=
      congrArg (fun a : C(I,Y) => a s) (hk t)
    refine ⟨{
      toFun := fun z => k.map z.2 z.1
      continuous_toFun := (ContinuousMap.uncurry k.map).continuous.comp continuous_swap
      map_zero_left := ?_
      map_one_left := ?_
      prop' := ?_ }⟩
    · intro x
      rcases sphereLevel_eq_point_or_sphereCube n x with rfl | ⟨t,rfl⟩
      · exact (point 0).trans f.point.symm
      · exact (cube t 0).trans ((H.apply_zero t).trans (hf t).symm)
    · intro x
      rcases sphereLevel_eq_point_or_sphereCube n x with rfl | ⟨t,rfl⟩
      · exact (point 1).trans g.point.symm
      · exact (cube t 1).trans ((H.apply_one t).trans (hg t).symm)
    · intro s x hx
      rcases Set.mem_singleton_iff.mp hx with rfl
      exact (point s).trans f.point.symm
  · rintro ⟨H⟩
    refine ⟨{
      toFun := fun z => H (z.1,sphereCube n z.2)
      continuous_toFun := H.continuous.comp
        (continuous_fst.prodMk ((sphereCube n).val.continuous.comp continuous_snd))
      map_zero_left := fun t => (H.apply_zero _).trans (hf t)
      map_one_left := fun t => (H.apply_one _).trans (hg t)
      prop' := ?_ }⟩
    intro s t ht
    change H (s,sphereCube n t) = p t
    have hcube : sphereCube n t = (sphereLevel n).point := (sphereCube n).property t ht
    rw [hcube]
    exact (H.eq_fst s (Set.mem_singleton _)).trans (f.point.trans (p.property t ht).symm)


/-- Each actual sphere level is compact, directly from its suspension quotient. -/
theorem sphereLevel_compactSpace (n : ℕ) : CompactSpace (sphereLevel n) := by
  induction n with
  | zero => exact inferInstanceAs (CompactSpace (Fin 2))
  | succ n ih =>
    letI := ih
    change CompactSpace (Quot (BasedSpace.SuspensionRelation (sphereLevel n)))
    infer_instance

end KIP126.AdamsSynthetic.Source.Prespectrum
