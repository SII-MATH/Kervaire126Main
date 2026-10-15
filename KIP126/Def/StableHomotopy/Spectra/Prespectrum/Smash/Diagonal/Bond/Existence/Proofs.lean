module

public import KIP126.Def.StableHomotopy.Spectra.Generators

@[expose] public section

namespace KIP126.StableHomotopy.Spectra
open CategoryTheory _root_.Topology
open scoped unitInterval
namespace Prespectrum

/-- Two consecutive bonds, on their actual quotient representatives. -/
theorem pairedBond_exists (X Y : Prespectrum.{0}) :
    ∃! b : C((X.level 0 |>.smash (Y.level 0)).suspension × I,
        (X.level 1).smash (Y.level 1)),
      (∀ x y s t,
        b (BasedSpace.suspensionProjection _ (BasedSpace.smashPoint _ _ x y,s),t) =
          BasedSpace.smashPoint _ _ (X.bond 0 (x,s)) (Y.bond 0 (y,t))) ∧
      (∀ t, b (((X.level 0).smash (Y.level 0)).suspension.point,t) =
        ((X.level 1).smash (Y.level 1)).point) ∧
      (∀ a, b (a,0) = ((X.level 1).smash (Y.level 1)).point) ∧
      (∀ a, b (a,1) = ((X.level 1).smash (Y.level 1)).point) := by
  have kc (S : CompHaus.{0}) (k : C(S, X.level 1 × Y.level 1)) :
      Continuous (fun s : S => BasedSpace.smashPoint (X.level 1) (Y.level 1) (k s).1 (k s).2) := by
    let ev : (Σ i : (T : CompHaus.{0}) × C(T, X.level 1 × Y.level 1), i.fst) →
        X.level 1 × Y.level 1 := fun q => q.1.2 q.2
    have hi : Continuous (fun s : S => (⟨⟨S,k⟩,s⟩ :
        Σ i : (T : CompHaus.{0}) × C(T, X.level 1 × Y.level 1), i.fst)) :=
      @continuous_sigmaMk _ (fun i : (T : CompHaus.{0}) × C(T, X.level 1 × Y.level 1) => i.fst)
        (fun _ => inferInstance) ⟨S,k⟩
    letI : TopologicalSpace (X.level 1 × Y.level 1) := TopologicalSpace.coinduced ev inferInstance
    exact continuous_quot_mk.comp ((show Continuous ev from continuous_coinduced_rng).comp hi)
  let family (p : X.level 0 × Y.level 0) :
      C(I, C(I, (X.level 1).smash (Y.level 1))) :=
    (⟨fun st : I × I => BasedSpace.smashPoint _ _ (X.bond 0 (p.1,st.1)) (Y.bond 0 (p.2,st.2)),
      kc (CompHaus.of (I × I)) ⟨_,
        ((X.bond 0).continuous.comp (continuous_const.prodMk continuous_fst)).prodMk
          ((Y.bond 0).continuous.comp (continuous_const.prodMk continuous_snd))⟩⟩ :
      C(I × I, (X.level 1).smash (Y.level 1))).curry
  have hf : Continuous[TopologicalSpace.compactlyGenerated.{0} (X.level 0 × Y.level 0),
      inferInstance] family := by
    refine @continuous_from_compactlyGenerated (X.level 0 × Y.level 0) _ _ _ family ?_
    intro S k
    apply ContinuousMap.continuous_of_continuous_uncurry
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact kc (CompHaus.of ((S × I) × I)) ⟨fun p =>
      (X.bond 0 ((k p.1.1).1,p.1.2), Y.bond 0 ((k p.1.1).2,p.2)),
      ((X.bond 0).continuous.comp ((k.continuous.fst.comp continuous_fst.fst).prodMk
        continuous_fst.snd)).prodMk
      ((Y.bond 0).continuous.comp ((k.continuous.snd.comp continuous_fst.fst).prodMk
        continuous_snd))⟩
  let raw (p : (X.level 0 × Y.level 0) × (I × I)) : (X.level 1).smash (Y.level 1) :=
    BasedSpace.smashPoint _ _ (X.bond 0 (p.1.1,p.2.1)) (Y.bond 0 (p.1.2,p.2.2))
  have collapsed (p : X.level 0 × Y.level 0) (st : I × I)
      (hp : p.1 = (X.level 0).point ∨ p.2 = (Y.level 0).point) :
      raw (p,st) = ((X.level 1).smash (Y.level 1)).point := by
    rcases hp with h | h
    · dsimp [raw]
      rw [h, X.bond_point]
      exact BasedSpace.smashPoint_base_left _ _ _
    · dsimp [raw]
      rw [h, Y.bond_point]
      exact BasedSpace.smashPoint_base_right _ _ _
  have hr (st : I × I) : ∀ a b, BasedSpace.SmashRelation (X.level 0) (Y.level 0) a b →
      raw (a,st) = raw (b,st) :=
    fun a b h => (collapsed a st h.1).trans (collapsed b st h.2).symm
  let mid (p : (X.level 0).smash (Y.level 0) × (I × I)) :=
    Quot.lift (fun q => raw (q,p.2)) (hr p.2) p.1
  have hm : Continuous mid := by
    letI : TopologicalSpace (X.level 0 × Y.level 0) :=
      TopologicalSpace.compactlyGenerated.{0} (X.level 0 × Y.level 0)
    apply isQuotientMap_quot_mk.continuous_lift_prod_left
    exact ((⟨family,hf⟩ : C(X.level 0 × Y.level 0,
      C(I,C(I,(X.level 1).smash (Y.level 1))))).uncurry.uncurry.continuous).comp
      ((continuous_fst.prodMk continuous_snd.fst).prodMk continuous_snd.snd)
  have mid_left (s t : I) : mid (((X.level 0).smash (Y.level 0)).point,(s,t)) =
      ((X.level 1).smash (Y.level 1)).point := collapsed _ _ (Or.inl rfl)
  have mid_zero (a : (X.level 0).smash (Y.level 0)) (t : I) :
      mid (a,(0,t)) = ((X.level 1).smash (Y.level 1)).point := by
    refine Quot.inductionOn a ?_
    rintro ⟨x,y⟩
    change BasedSpace.smashPoint _ _ (X.bond 0 (x,0)) (Y.bond 0 (y,t)) = _
    rw [X.bond_zero]
    exact BasedSpace.smashPoint_base_left _ _ _
  have mid_one (a : (X.level 0).smash (Y.level 0)) (t : I) :
      mid (a,(1,t)) = ((X.level 1).smash (Y.level 1)).point := by
    refine Quot.inductionOn a ?_
    rintro ⟨x,y⟩
    change BasedSpace.smashPoint _ _ (X.bond 0 (x,1)) (Y.bond 0 (y,t)) = _
    rw [X.bond_one]
    exact BasedSpace.smashPoint_base_left _ _ _
  have collapse_outer (p : (X.level 0).smash (Y.level 0) × I) (t : I)
      (hp : BasedSpace.SuspensionCollapsed ((X.level 0).smash (Y.level 0)) p) :
      mid (p.1,(p.2,t)) = ((X.level 1).smash (Y.level 1)).point := by
    rcases hp with h | h | h
    · rw [h, mid_left]
    · rw [h, mid_zero]
    · rw [h, mid_one]
  have hrout (t : I) : ∀ a b,
      BasedSpace.SuspensionRelation ((X.level 0).smash (Y.level 0)) a b →
      mid (a.1,(a.2,t)) = mid (b.1,(b.2,t)) :=
    fun a b h => (collapse_outer a t h.1).trans (collapse_outer b t h.2).symm
  let b : C(((X.level 0).smash (Y.level 0)).suspension × I,
      (X.level 1).smash (Y.level 1)) :=
    ⟨fun p => Quot.lift (fun q => mid (q.1,(q.2,p.2))) (hrout p.2) p.1, by
      apply isQuotientMap_quot_mk.continuous_lift_prod_left
      exact hm.comp (continuous_fst.fst.prodMk (continuous_fst.snd.prodMk continuous_snd))⟩
  refine ⟨b, ⟨fun _ _ _ _ => rfl, fun t => mid_left 0 t, ?_, ?_⟩, ?_⟩
  · intro a
    refine Quot.inductionOn a ?_
    rintro ⟨a,s⟩
    refine Quot.inductionOn a ?_
    rintro ⟨x,y⟩
    change BasedSpace.smashPoint _ _ (X.bond 0 (x,s)) (Y.bond 0 (y,0)) = _
    rw [Y.bond_zero]
    exact BasedSpace.smashPoint_base_right _ _ _
  · intro a
    refine Quot.inductionOn a ?_
    rintro ⟨a,s⟩
    refine Quot.inductionOn a ?_
    rintro ⟨x,y⟩
    change BasedSpace.smashPoint _ _ (X.bond 0 (x,s)) (Y.bond 0 (y,1)) = _
    rw [Y.bond_one]
    exact BasedSpace.smashPoint_base_right _ _ _
  · intro c hc
    apply ContinuousMap.ext
    rintro ⟨a,t⟩
    refine Quot.inductionOn a ?_
    rintro ⟨a,s⟩
    refine Quot.inductionOn a ?_
    rintro ⟨x,y⟩
    exact hc.1 x y s t

end Prespectrum
end KIP126.StableHomotopy.Spectra
