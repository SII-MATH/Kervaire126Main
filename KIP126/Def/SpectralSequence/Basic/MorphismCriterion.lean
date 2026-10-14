module

public import KIP126.Def.SpectralSequence.Basic.Proofs

@[expose] public section

/-!
# Representative criterion for spectral-sequence morphisms

An ambient map which preserves cycles, sends zero representatives to zero on
the target page, and satisfies the representative differential equation
determines the canonical quotient maps.  This is the KIP126 formulation of
the useful proved part of the historical KIPBase criterion; it works with
KIP126's nested-subobject pages and does not introduce an independent page-map
field.
-/

namespace KIP126.Core.SpectralSequence

open CategoryTheory CategoryTheory.Limits

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {ι : Type w} [AddCommGroup ι] [DecidableEq ι]

structure DifferentialMorphismCriterion
    (E E' : SpectralSequence C ι)
    (f : UnderlyingMorphism ι E.ssData E'.ssData) where
  r₀_eq : E.r₀ = E'.r₀
  diffDeg_eq : E.diffDeg = E'.diffDeg
  survives : ∀ (k : ι) (n : WithTop ℕ),
    ∃ zLift : Subobject.underlying.obj ((E.ssData k).Z n) ⟶
        Subobject.underlying.obj ((E'.ssData k).Z n),
      zLift ≫ ((E'.ssData k).Z n).arrow =
        ((E.ssData k).Z n).arrow ≫ f.φ k
  zero_differential : ∀ (k : ι) (n : WithTop ℕ),
    let β := Subobject.ofLE ((E.ssData k).B n)
      ((E.ssData k).Z n) ((E.ssData k).B_le_Z n)
    β ≫ (survives k n).choose ≫ (E'.ssData k).pageπ n = 0
  differential : ∀ (r : ℤ) (k : ι),
      let n : WithTop ℕ := ↑(r - E.r₀).toNat
      let n' : WithTop ℕ := ↑(r - E'.r₀).toNat
      let hn : n = n' := congrArg
        (fun r₀ => (↑(r - r₀).toNat : WithTop ℕ)) r₀_eq
      let hk : k + E.diffDeg r = k + E'.diffDeg r :=
        congrArg (fun d => k + d) (congrFun diffDeg_eq r)
      ∀ (T : C)
        (x : T ⟶ Subobject.underlying.obj ((E.ssData k).Z n))
        (y : T ⟶ Subobject.underlying.obj
          ((E.ssData (k + E.diffDeg r)).Z n)),
        x ≫ (E.ssData k).pageπ n ≫ E.d r k =
          y ≫ (E.ssData (k + E.diffDeg r)).pageπ n →
        x ≫ (survives k n).choose ≫ (E'.ssData k).pageπ n ≫
          eqToHom (by rw [hn]) ≫ E'.d r k =
        y ≫ (survives (k + E.diffDeg r) n).choose ≫
          (E'.ssData (k + E.diffDeg r)).pageπ n ≫
          eqToHom (by rw [hk, hn])

noncomputable def DifferentialMorphismCriterion.toSSDataMorphism
    {E E' : SpectralSequence C ι}
    {f : UnderlyingMorphism ι E.ssData E'.ssData}
    (H : DifferentialMorphismCriterion E E' f) :
    SSDataMorphism ι E.ssData E'.ssData := {
  φ := f.φ
  preserves_Z := H.survives
  preserves_B := by
    intro k n
    let D := E.ssData k
    let D' := E'.ssData k
    let β := Subobject.ofLE (D.B n) (D.Z n) (D.B_le_Z n)
    let β' := Subobject.ofLE (D'.B n) (D'.Z n) (D'.B_le_Z n)
    let zLift := (H.survives k n).choose
    have hz : zLift ≫ (D'.Z n).arrow = (D.Z n).arrow ≫ f.φ k :=
      (H.survives k n).choose_spec
    have hzero : (β ≫ zLift) ≫ D'.pageπ n = 0 := by
      simpa only [Category.assoc] using H.zero_differential k n
    let bLift := (ShortComplex.exact_cokernel β').lift (β ≫ zLift) hzero
    refine ⟨bLift, ?_⟩
    calc
      bLift ≫ (D'.B n).arrow =
          (bLift ≫ β') ≫ (D'.Z n).arrow := by
            rw [Category.assoc, Subobject.ofLE_arrow]
      _ = (β ≫ zLift) ≫ (D'.Z n).arrow := by
            rw [ShortComplex.Exact.lift_f]
      _ = (D.B n).arrow ≫ f.φ k := by
            rw [Category.assoc, hz, ← Category.assoc,
              Subobject.ofLE_arrow]
}

noncomputable def DifferentialMorphismCriterion.toMorphism
    {E E' : SpectralSequence C ι}
    {f : UnderlyingMorphism ι E.ssData E'.ssData}
    (H : DifferentialMorphismCriterion E E' f) :
    SpectralSequenceMorphism E E' := by
  let F := H.toSSDataMorphism
  let P : PreSSMorphism E.toPreSS E'.toPreSS := {
    toSSDataMorphism := F
    r₀_eq := H.r₀_eq
    diffDeg_eq := H.diffDeg_eq
    comm_d := by
      intro r k
      let n : WithTop ℕ := ↑(r - E.r₀).toNat
      let hn : n = (↑(r - E'.r₀).toNat : WithTop ℕ) :=
        congrArg (fun r₀ => (↑(r - r₀).toNat : WithTop ℕ)) H.r₀_eq
      let hk : k + E.diffDeg r = k + E'.diffDeg r :=
        congrArg (fun d => k + d) (congrFun H.diffDeg_eq r)
      let p := (E.ssData k).pageπ n
      let q := (E.ssData (k + E.diffDeg r)).pageπ n
      haveI : Epi p := inferInstanceAs (Epi (cokernel.π
        (Subobject.ofLE ((E.ssData k).B n) ((E.ssData k).Z n)
          ((E.ssData k).B_le_Z n))))
      haveI : Epi q := inferInstanceAs (Epi (cokernel.π
        (Subobject.ofLE ((E.ssData (k + E.diffDeg r)).B n)
          ((E.ssData (k + E.diffDeg r)).Z n)
          ((E.ssData (k + E.diffDeg r)).B_le_Z n))))
      let g := p ≫ E.d r k
      let P := pullback g q
      haveI : Epi (pullback.fst g q) := inferInstance
      have hrep := H.differential r k P (pullback.fst g q) (pullback.snd g q)
        (pullback.condition)
      have hπ (j : ι) :
          F.cycleMap j n = (H.survives j n).choose := rfl
      apply (cancel_epi p).mp
      apply (cancel_epi (pullback.fst g q)).mp
      dsimp only [P, g, p, q] at hrep ⊢
      simp only [SSDataMorphism.pageMapAt] at ⊢
      simp only [← Category.assoc] at ⊢
      rw [Category.assoc (pullback.fst g q) p (E.d r k)] at ⊢
      rw [pullback.condition] at ⊢
      rw [Category.assoc (pullback.fst g q) p (F.pageMap k n)] at ⊢
      rw [Category.assoc (pullback.snd g q) q
        (F.pageMap (k + E.diffDeg r) n)] at ⊢
      rw [F.pageπ_pageMap, F.pageπ_pageMap] at ⊢
      rw [hπ k, hπ (k + E.diffDeg r)] at ⊢
      convert hrep using 1 <;> simp only [Category.assoc, eqToHom_trans] <;>
        dsimp only [g, q, p, n]
  }
  exact {
    φ := P.φ
    preserves_Z := P.preserves_Z
    preserves_B := P.preserves_B
    r₀_eq := P.r₀_eq
    diffDeg_eq := P.diffDeg_eq
    comm_d := P.comm_d }

theorem DifferentialMorphismCriterion.exists_morphism
    {E E' : SpectralSequence C ι}
    {f : UnderlyingMorphism ι E.ssData E'.ssData}
    (H : DifferentialMorphismCriterion E E' f) :
    ∃ F : SpectralSequenceMorphism E E', ∀ k, F.φ k = f.φ k := by
  exact ⟨H.toMorphism, fun _ => rfl⟩

end KIP126.Core.SpectralSequence
