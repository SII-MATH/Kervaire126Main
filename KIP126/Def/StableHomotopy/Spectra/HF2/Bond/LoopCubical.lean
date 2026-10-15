module

public import KIP126.Def.StableHomotopy.Spectra.HF2.Bond.PathComparison

@[expose] public section

namespace KIP126.StableHomotopy.Spectra.HF2Bond
open scoped unitInterval

/-- The compact-open based loop space of a specified based topological space. -/
abbrev topologicalLoopLevel (X : BasedSpace.{0}) : BasedSpace.{0} where
  space := TopCat.of (Path X.point X.point)
  point := Path.refl X.point

/-- A cubical loop in the topological loop space, uncurried with the new
interval as first coordinate, exactly as in prespectrum stabilization. -/
def loopUncurry (X : BasedSpace.{0}) (r : ℕ)
    (p : GenLoop (Fin r) (topologicalLoopLevel X) (topologicalLoopLevel X).point) :
    GenLoop (Fin (r + 1)) X X.point := by
  refine ⟨⟨fun u => p (fun i => u i.succ) (u 0), ?_⟩, ?_⟩
  · exact continuous_eval.comp
      ((p.val.continuous.comp (continuous_pi fun i => continuous_apply i.succ)).prodMk
        (continuous_apply 0))
  · rintro u ⟨i, hi⟩
    change p (fun i => u i.succ) (u 0) = X.point
    induction i using Fin.cases with
    | zero => rcases hi with h | h <;> simp only [h, Path.source, Path.target]
    | succ j =>
      have hp := p.property (fun i => u i.succ) ⟨j, hi⟩
      exact congrArg (fun q : Path X.point X.point => q (u 0)) hp

/-- Insert the new first coordinate into a cube continuously. -/
theorem continuous_cube_cons (r : ℕ) :
    Continuous (fun z : (Fin r → I) × I => (Fin.cons z.2 z.1 : Fin (r + 1) → I)) := by
  apply continuous_pi
  intro i
  induction i using Fin.cases with
  | zero => exact continuous_snd
  | succ i => exact (continuous_apply i).comp continuous_fst

/-- Curry the first coordinate of an actual based cubical loop. -/
def loopCurry (X : BasedSpace.{0}) (r : ℕ)
    (p : GenLoop (Fin (r + 1)) X X.point) :
    GenLoop (Fin r) (topologicalLoopLevel X) (topologicalLoopLevel X).point := by
  let f (u : Fin r → I) : Path X.point X.point :=
    { toFun t := p (Fin.cons t u)
      continuous_toFun := p.val.continuous.comp
        ((continuous_cube_cons r).comp (continuous_const.prodMk continuous_id))
      source' := p.property _ ⟨0, Or.inl rfl⟩
      target' := p.property _ ⟨0, Or.inr rfl⟩ }
  refine ⟨⟨f, Path.continuous_uncurry_iff.mp
    (p.val.continuous.comp (continuous_cube_cons r))⟩, ?_⟩
  rintro u ⟨i, hi⟩
  apply Path.ext
  funext t
  exact p.property _ ⟨i.succ, hi⟩

@[simp] theorem loopUncurry_loopCurry (X : BasedSpace.{0}) (r : ℕ)
    (p : GenLoop (Fin (r + 1)) X X.point) :
    loopUncurry X r (loopCurry X r p) = p := by
  apply GenLoop.ext
  intro u
  change p (Fin.cons (u 0) (fun i => u i.succ)) = p u
  congr 1
  ext i
  induction i using Fin.cases <;> rfl

@[simp] theorem loopCurry_loopUncurry (X : BasedSpace.{0}) (r : ℕ)
    (p : GenLoop (Fin r) (topologicalLoopLevel X) (topologicalLoopLevel X).point) :
    loopCurry X r (loopUncurry X r p) = p := by
  apply GenLoop.ext
  intro u
  apply Path.ext
  funext t
  rfl

/-- The actual first-coordinate currying equivalence of based cubical loops. -/
def cubicalLoopEquiv (X : BasedSpace.{0}) (r : ℕ) :
    GenLoop (Fin r) (topologicalLoopLevel X) (topologicalLoopLevel X).point ≃
      GenLoop (Fin (r + 1)) X X.point where
  toFun := loopUncurry X r
  invFun := loopCurry X r
  left_inv := loopCurry_loopUncurry X r
  right_inv := loopUncurry_loopCurry X r

/-- The based cubical map induced by the actual coefficient bond adjoint. -/
noncomputable def bondAdjointLoop (n r : ℕ)
    (p : GenLoop (Fin r) (hf2RealizationLevel n) (hf2RealizationLevel n).point) :
    GenLoop (Fin r) (topologicalLoopLevel (hf2RealizationLevel (n + 1)))
      (topologicalLoopLevel (hf2RealizationLevel (n + 1))).point :=
  ⟨(bondAdjoint n).comp p.val, fun t ht =>
    (congrArg (bondAdjoint n) (p.property t ht)).trans (bondAdjoint_point n)⟩

/-- First-coordinate uncurrying carries actual based relative homotopies to
actual relative homotopies of the enlarged cube. -/
def loopUncurryHomotopy (X : BasedSpace.{0}) (r : ℕ)
    {p q : GenLoop (Fin r) (topologicalLoopLevel X) (topologicalLoopLevel X).point}
    (H : ContinuousMap.HomotopyRel p.val q.val (Cube.boundary (Fin r))) :
    ContinuousMap.HomotopyRel (loopUncurry X r p).val (loopUncurry X r q).val
      (Cube.boundary (Fin (r + 1))) where
  toFun z := H (z.1, fun i => z.2 i.succ) (z.2 0)
  continuous_toFun := continuous_eval.comp
    ((H.continuous.comp (continuous_fst.prodMk
      (continuous_pi fun i => (continuous_apply i.succ).comp continuous_snd))).prodMk
        ((continuous_apply 0).comp continuous_snd))
  map_zero_left u := congrArg (fun a : Path X.point X.point => a (u 0)) (H.apply_zero _)
  map_one_left u := congrArg (fun a : Path X.point X.point => a (u 0)) (H.apply_one _)
  prop' t u hu := by
    change H (t, fun i => u i.succ) (u 0) = loopUncurry X r p u
    refine Eq.trans ?_ ((loopUncurry X r p).property u hu).symm
    obtain ⟨i, hi⟩ := hu
    induction i using Fin.cases with
    | zero => rcases hi with h | h <;> simp only [h, Path.source, Path.target]
    | succ j =>
      have he := H.eq_fst t (x := fun i => u i.succ) ⟨j, hi⟩
      have hp := p.property (fun i => u i.succ) ⟨j, hi⟩
      exact congrArg (fun a : Path X.point X.point => a (u 0)) (he.trans hp)

/-- First-coordinate currying carries an actual based homotopy to a continuous
homotopy through based topological loops. -/
def loopCurryHomotopy (X : BasedSpace.{0}) (r : ℕ)
    {p q : GenLoop (Fin (r + 1)) X X.point}
    (H : ContinuousMap.HomotopyRel p.val q.val (Cube.boundary (Fin (r + 1)))) :
    ContinuousMap.HomotopyRel (loopCurry X r p).val (loopCurry X r q).val
      (Cube.boundary (Fin r)) where
  toFun z :=
    { toFun t := H (z.1, Fin.cons t z.2)
      continuous_toFun := H.continuous.comp
        (continuous_const.prodMk ((continuous_cube_cons r).comp
          (continuous_const.prodMk continuous_id)))
      source' := (H.eq_fst z.1 ⟨0, Or.inl rfl⟩).trans (p.property _ ⟨0, Or.inl rfl⟩)
      target' := (H.eq_fst z.1 ⟨0, Or.inr rfl⟩).trans (p.property _ ⟨0, Or.inr rfl⟩) }
  continuous_toFun := Path.continuous_uncurry_iff.mp
    (H.continuous.comp ((continuous_fst.comp continuous_fst).prodMk
      ((continuous_cube_cons r).comp ((continuous_snd.comp continuous_fst).prodMk continuous_snd))))
  map_zero_left u := by
    apply Path.ext
    funext t
    exact H.apply_zero (Fin.cons t u)
  map_one_left u := by
    apply Path.ext
    funext t
    exact H.apply_one (Fin.cons t u)
  prop' s u hu := by
    apply Path.ext
    funext t
    obtain ⟨i, hi⟩ := hu
    exact H.eq_fst s ⟨i.succ, hi⟩

/-- Uncurrying detects and preserves actual cubical based homotopy. -/
theorem loopUncurry_homotopic_iff (X : BasedSpace.{0}) (r : ℕ)
    (p q : GenLoop (Fin r) (topologicalLoopLevel X) (topologicalLoopLevel X).point) :
    GenLoop.Homotopic (loopUncurry X r p) (loopUncurry X r q) ↔ GenLoop.Homotopic p q := by
  constructor
  · rintro ⟨H⟩
    have h : GenLoop.Homotopic (loopCurry X r (loopUncurry X r p))
        (loopCurry X r (loopUncurry X r q)) := ⟨loopCurryHomotopy X r H⟩
    simpa only [loopCurry_loopUncurry] using h
  · rintro ⟨H⟩
    exact ⟨loopUncurryHomotopy X r H⟩

/-- The actual cubical homotopy-set equivalence π_r(Ω X) ≃ π_(r+1)(X),
with the first-coordinate convention of the fixed prespectrum. -/
def cubicalHomotopyLoopEquiv (X : BasedSpace.{0}) (r : ℕ) :
    HomotopyGroup.Pi r (topologicalLoopLevel X) (topologicalLoopLevel X).point ≃
      HomotopyGroup.Pi (r + 1) X X.point :=
  Quotient.congr (cubicalLoopEquiv X r) fun p q => (loopUncurry_homotopic_iff X r p q).symm

/-- The map on actual cubical homotopy sets induced by the continuous bond
adjoint. No equivalence claim is built into this definition. -/
noncomputable def bondAdjointHomotopyMap (n r : ℕ) :
    HomotopyGroup.Pi r (hf2RealizationLevel n) (hf2RealizationLevel n).point →
      HomotopyGroup.Pi r (topologicalLoopLevel (hf2RealizationLevel (n + 1)))
        (topologicalLoopLevel (hf2RealizationLevel (n + 1))).point :=
  Quotient.map (bondAdjointLoop n r) fun _ _ h => h.comp_continuousMap (bondAdjoint n)

/-- The induced stabilization map on genuine cubical homotopy sets. -/
noncomputable def bondHomotopyMap (n r : ℕ) :
    HomotopyGroup.Pi r (hf2RealizationLevel n) (hf2RealizationLevel n).point →
      HomotopyGroup.Pi (r + 1) (hf2RealizationLevel (n + 1))
        (hf2RealizationLevel (n + 1)).point :=
  cubicalHomotopyLoopEquiv (hf2RealizationLevel (n + 1)) r ∘ bondAdjointHomotopyMap n r

/-- On representatives, the induced map uses exactly the prespectrum's given
structure map and its given first-coordinate stabilization. -/
theorem bondHomotopyMap_mk (n r : ℕ)
    (p : GenLoop (Fin r) (hf2RealizationLevel n) (hf2RealizationLevel n).point) :
    bondHomotopyMap n r ⟦p⟧ =
      ⟦Prespectrum.stabilizeLoop hf2RealizationPrespectrum n r p⟧ := rfl

end KIP126.StableHomotopy.Spectra.HF2Bond
