module

public import KIP126.Def.StableHomotopy.Spectra.Suspension.Data
public import KIP126.Def.StableHomotopy.Spectra.Prespectrum.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Spectra.Prespectrum

open CategoryTheory Topology
open scoped unitInterval Topology.Homotopy

universe u

/-- Levelwise bijectivity on based homotopy classes gives bijectivity on
the actual stable quotient. The chosen inverse loops respect stabilization
because the original strict map does. -/
theorem stableEquivalence_of_levelwise_loops {X Y : Prespectrum.{u}} (f : X ⟶ Y)
    (hinj : ∀ n r (p q : GenLoop (Fin r) (X.level n) (X.level n).point),
      GenLoop.Homotopic
        (⟨(f.level n).comp p.val,fun t ht => (congrArg (f.level n) (p.property t ht)).trans (f.point n)⟩ :
          GenLoop (Fin r) (Y.level n) (Y.level n).point)
        ⟨(f.level n).comp q.val,fun t ht => (congrArg (f.level n) (q.property t ht)).trans (f.point n)⟩ →
      GenLoop.Homotopic p q)
    (hsurj : ∀ n r (p : GenLoop (Fin r) (Y.level n) (Y.level n).point),
      ∃ q : GenLoop (Fin r) (X.level n) (X.level n).point,
        GenLoop.Homotopic
          (⟨(f.level n).comp q.val,fun t ht => (congrArg (f.level n) (q.property t ht)).trans (f.point n)⟩ :
            GenLoop (Fin r) (Y.level n) (Y.level n).point) p) :
    stableEquivalences f := by
  classical
  let F (n r : ℕ) (p : GenLoop (Fin r) (X.level n) (X.level n).point) :
      GenLoop (Fin r) (Y.level n) (Y.level n).point :=
    ⟨(f.level n).comp p.val,fun t ht => (congrArg (f.level n) (p.property t ht)).trans (f.point n)⟩
  choose L hL using hsurj
  have hnext (n r : ℕ) (p : GenLoop (Fin r) (X.level n) (X.level n).point) :
      F (n+1) (r+1) (stabilizeLoop X n r p)=stabilizeLoop Y n r (F n r p) := by
    apply GenLoop.ext
    intro t
    exact f.bond n _ _
  intro d
  let R (a : Representative Y d) : Representative X d :=
    ⟨a.stage,a.dimension,a.degree,L a.stage a.dimension a.loop⟩
  have respects : ∀ a b, StableRelation Y d a b → Quot.mk (StableRelation X d) (R a)=Quot.mk _ (R b) := by
    intro a b hab
    cases hab with
    | homotopy p hp =>
      apply Quot.sound
      apply StableRelation.homotopy (R a)
      apply hinj
      exact (hL a.stage a.dimension a.loop).trans (hp.trans (hL a.stage a.dimension p).symm)
    | stabilization =>
      apply (Quot.sound (StableRelation.stabilization (R a))).trans
      have hh : GenLoop.Homotopic (stabilizeLoop X a.stage a.dimension (L _ _ a.loop))
          (L _ _ (stabilizeLoop Y a.stage a.dimension a.loop)) := by
        apply hinj
        change GenLoop.Homotopic (F _ _ (stabilizeLoop X _ _ (L _ _ a.loop))) _
        rw [hnext]
        exact (stabilizeLoop_homotopic Y _ _ _ _ (hL _ _ a.loop)).trans
          (hL _ _ (stabilizeLoop Y _ _ a.loop)).symm
      exact Quot.sound (StableRelation.homotopy (R a).next _ hh)
  let G : StableHomotopy Y d → StableHomotopy X d := Quot.lift (fun a => Quot.mk _ (R a)) respects
  have hGF : Function.LeftInverse G (stableHomotopyMap f d) := by
    intro a
    refine Quot.inductionOn a ?_
    intro a
    change Quot.mk _ (R (a.map f))=Quot.mk _ a
    have h : GenLoop.Homotopic (L a.stage a.dimension (F _ _ a.loop)) a.loop :=
      hinj _ _ _ _ (hL _ _ (F _ _ a.loop))
    exact Quot.sound (StableRelation.homotopy (R (a.map f)) _ h)
  have hFG : Function.RightInverse G (stableHomotopyMap f d) := by
    intro a
    refine Quot.inductionOn a ?_
    intro a
    change Quot.mk _ ((R a).map f)=Quot.mk _ a
    exact Quot.sound (StableRelation.homotopy ((R a).map f) _ (hL _ _ a.loop))
  exact ⟨hGF.injective,hFG.surjective⟩

@[simp] theorem Representative.pad_unpadNext {X : Prespectrum.{u}} {d : ℤ}
    (a : Representative (desuspension X) d) : a.unpadNext.pad = a.next := rfl

@[simp] theorem Representative.unpadNext_pad {X : Prespectrum.{u}} {d : ℤ}
    (a : Representative X (d + 1)) : a.pad.unpadNext = a.next := rfl

theorem Representative.pad_relation {X : Prespectrum.{u}} {d : ℤ}
    {a b : Representative X (d + 1)} (h : StableRelation X (d + 1) a b) :
    StableRelation (desuspension X) d a.pad b.pad := by
  cases h with
  | homotopy p h => exact StableRelation.homotopy a.pad _ h
  | stabilization => exact StableRelation.stabilization a.pad

theorem Representative.unpadNext_relation {X : Prespectrum.{u}} {d : ℤ}
    {a b : Representative (desuspension X) d}
    (h : StableRelation (desuspension X) d a b) :
    StableRelation X (d + 1) a.unpadNext b.unpadNext := by
  cases h with
  | homotopy p h =>
    exact StableRelation.homotopy a.unpadNext _ (stabilizeLoop_homotopic _ _ _ _ _ h)
  | stabilization => exact StableRelation.stabilization a.unpadNext

/-- The padded desuspension has exactly the shifted stable homotopy sets.
The inverse maps are given on actual representatives, and their composites
are one stabilization step. No sphere or suspension theorem is assumed. -/
theorem stableHomotopy_desuspension_equiv (X : Prespectrum.{u}) (d : ℤ) :
    Nonempty (StableHomotopy (desuspension X) d ≃ StableHomotopy X (d + 1)) := by
  refine ⟨{
    toFun := Quot.map Representative.unpadNext (fun _ _ h =>
      Representative.unpadNext_relation h)
    invFun := Quot.map Representative.pad (fun _ _ h => Representative.pad_relation h)
    left_inv := ?_
    right_inv := ?_ }⟩
  · intro x
    induction x using Quot.inductionOn with
    | h a => exact (Quot.sound (StableRelation.stabilization a)).symm
  · intro x
    induction x using Quot.inductionOn with
    | h a => exact (Quot.sound (StableRelation.stabilization a)).symm

theorem Representative.liftPaddedTail_relation {X : Prespectrum.{u}} {d : ℤ}
    {a b : Representative X d} (h : StableRelation X d a b) :
    StableRelation (desuspension (levelTail X)) d a.liftPaddedTail b.liftPaddedTail := by
  cases h with
  | homotopy p h =>
    exact StableRelation.homotopy a.liftPaddedTail _ (stabilizeLoop_homotopic _ _ _ _ _ h)
  | stabilization => exact StableRelation.stabilization a.liftPaddedTail

@[simp] theorem Representative.map_liftPaddedTail {X : Prespectrum.{u}} {d : ℤ}
    (a : Representative X d) : a.liftPaddedTail.map (paddedTailInclusion X) = a.next := rfl

@[simp] theorem Representative.liftPaddedTail_map {X : Prespectrum.{u}} {d : ℤ}
    (a : Representative (desuspension (levelTail X)) d) :
    (a.map (paddedTailInclusion X)).liftPaddedTail = a.next := by
  rcases a with ⟨n, r, hr, p⟩
  cases n with
  | zero =>
    unfold Representative.liftPaddedTail Representative.map Representative.next
    congr 1
    apply GenLoop.ext
    intro t
    exact X.bond_point 0 (t 0)
  | succ n => rfl

/-- Removing finitely many initial levels does not change the stable object.
Here the actual comparison is already a strict prespectrum map. -/
theorem paddedTailInclusion_stableEquivalence (X : Prespectrum.{u}) :
    stableEquivalences (paddedTailInclusion X) := by
  intro d
  let back : StableHomotopy X d → StableHomotopy (desuspension (levelTail X)) d :=
    Quot.map Representative.liftPaddedTail (fun _ _ h => Representative.liftPaddedTail_relation h)
  have hl : Function.LeftInverse back (stableHomotopyMap (paddedTailInclusion X) d) := by
    intro x
    induction x using Quot.inductionOn with
    | h a =>
      change Quot.mk _ ((a.map (paddedTailInclusion X)).liftPaddedTail) = Quot.mk _ a
      rw [Representative.liftPaddedTail_map]
      exact (Quot.sound (StableRelation.stabilization a)).symm
  have hr : Function.RightInverse back (stableHomotopyMap (paddedTailInclusion X) d) := by
    intro x
    induction x using Quot.inductionOn with
    | h a =>
      change Quot.mk _ (a.liftPaddedTail.map (paddedTailInclusion X)) = Quot.mk _ a
      rw [Representative.map_liftPaddedTail]
      exact (Quot.sound (StableRelation.stabilization a)).symm
  exact ⟨hl.injective, hr.surjective⟩

/-- The strict padded-tail comparison is invertible in the specified source
localization, with no separate model-category or convergence assumption. -/
theorem paddedTailInclusion_isIso (X : Prespectrum.{u}) :
    IsIso (sourceLocalization.map (paddedTailInclusion X)) :=
  stableEquivalences.Q_inverts _ (paddedTailInclusion_stableEquivalence X)

end KIP126.StableHomotopy.Spectra.Prespectrum
