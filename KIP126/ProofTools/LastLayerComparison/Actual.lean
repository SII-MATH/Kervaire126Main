module

public import KIP126.ProofTools.ExtBoundaryComparison
public import KIP126.ProofTools.LastLayerComparison
import all KIP126.ProofTools.ExtBoundaryComparison
import all KIP126.ProofTools.LastLayerComparison
import all KIP126.ProofTools.LastLayerComparison.Boundary
import all KIP126.ProofTools.GeneralizedMahowald.SuspensionClassLabels

/-! The complete last-layer comparison for the actual selected normalized
triangle. The kernel/image relation and preservation of the same boundary
cutoff are conclusions of the existing geometric comparisons, rather than
extra caller hypotheses. -/

@[expose] section
namespace KIP126.ProofTools.Standard
open CategoryTheory
open KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.AdamsSynthetic KIP126.AdamsSynthetic.Standard
open KIP126.Kervaire.Route KIP126.Literature

/-- The final-layer Surj and NC conditions for the fixed actual triangle,
including the full quotient obstruction isomorphism and the intermediate
cycle-qualified implication. In the application the cutoff is
`p = R + K - 2 ≥ 2`, and `(s,t)` is its final homogeneous source degree. -/
public theorem mahowaldLeibnizLastLayerComparison
    (T : TriangleData model.auxiliary)
    (hf : normalizedExponent model.classicalTower T.f = 1)
    (hg : normalizedExponent model.classicalTower T.g = 0)
    (hh : normalizedExponent model.classicalTower T.h = 0)
    (hT : NormalizedTriangleCompatible model T (by simp [hf,hg,hh]))
    (p : ℕ) (hp : 2 ≤ p) (s t : ℤ) :
    let h := classicalTriangleHMapHom T s t
    let f := cofiberFirstQuotientBoundaryHom T hf s t
    let BX := (boundaries model T.X p (s,t)).toAddSubgroup
    let BY := (boundaries model T.Y p (s+1,t+1)).toAddSubgroup
    f.ker = h.range ∧
    (((∀ a : Ambient model T.X (s,t),
        ∃ z : Ambient model T.Z (s,t+1),
        ∃ b : Ambient model T.X (s,t), b ∈ BX ∧ a = h z + b) ↔
        f.range = BX.map f) ∧
      ((∀ a : Ambient model T.X (s,t),
        ∃ z : Ambient model T.Z (s,t+1),
        ∃ b : Ambient model T.X (s,t), b ∈ BX ∧ a = h z + b) →
        f.range ≤ BY) ∧
      (f.range ≤ BY →
        ((∀ a : Ambient model T.X (s,t),
          ∃ z : Ambient model T.Z (s,t+1),
          ∃ b : Ambient model T.X (s,t), b ∈ BX ∧ a = h z + b) ↔
          f.range ⊓ BY = BX.map f))) ∧
    Nonempty ((BY.comap f ⧸ (h.range ⊔ BX).addSubgroupOf (BY.comap f)) ≃+
      (↥(f.range ⊓ BY) ⧸ (BX.map f).addSubgroupOf (f.range ⊓ BY))) ∧
    (∀ k : ℤ, 1 ≤ k →
      cycles model T.X k (s,t) ≤ boundaries model T.X p (s,t) →
      ∀ a : Ambient model T.X (s,t), IsCycle model T.X k (s,t) a →
      ∃ z : Ambient model T.Z (s,t+1),
        IsCycle model T.Z k (s,t+1) z ∧ a - h z ∈ BX) := by
  let h := classicalTriangleHMapHom T s t
  let f := cofiberFirstQuotientBoundaryHom T hf s t
  let BX := (boundaries model T.X p (s,t)).toAddSubgroup
  let BY := (boundaries model T.Y p (s+1,t+1)).toAddSubgroup
  have hexact : f.ker = h.range :=
    cofiberFirstQuotientBoundary_exact T hf hg hh hT s t
  have hboundary : BX.map f ≤ BY := by
    rintro y ⟨x,hx,rfl⟩
    exact cofiberFirstQuotientBoundary_preservesBoundaries T hf p hp s t x hx
  refine ⟨hexact, lastLayerComparison h f hexact BX BY hboundary,
    lastLayerObstructionIsomorphism h f hexact BX BY hboundary, ?_⟩
  intro k hk hNC a ha
  refine ⟨0, ⟨hk, (cycles model T.Z k (s,t+1)).zero_mem⟩, ?_⟩
  change a - h 0 ∈ boundaries model T.X p (s,t)
  rw [map_zero, sub_zero]
  exact hNC ha.2

private theorem every_label_cycle_one (X : ClassicalObject) (s t : ℤ)
    (x : Ambient model X (s,t)) : IsCycle model X 1 (s,t) x := by
  refine ⟨by omega, ?_⟩
  change ∃ a, cycleLabel model X 0 (s,t) a = x
  have hepi : Epi (cycleLabel model X 0 (s,t)) := by
    haveI : Epi (((model.classical.obj (X.obj model.auxiliary)).ssData (s,t)).pageπ 0) :=
      inferInstanceAs (Epi (CategoryTheory.Limits.cokernel.π _))
    unfold cycleLabel
    simp only [Subobject.ofLE_refl, Category.id_comp]
    infer_instance
  exact (ModuleCat.epi_iff_surjective (cycleLabel model X 0 (s,t))).mp hepi x

/-- The actual final Surj clause retains its original `Z₁` qualifications,
the specified classical desuspension, and its same source-boundary coset.
It is precisely the image equality occurring in the full last-layer
comparison, since every E₂ label belongs to `Z₁`. -/
public theorem mahowaldLeibnizLastLayerSurjectivity_iff
    (T : TriangleData model.auxiliary)
    (hf : normalizedExponent model.classicalTower T.f = 1)
    (hg : normalizedExponent model.classicalTower T.g = 0)
    (hh : normalizedExponent model.classicalTower T.h = 0)
    (hT : NormalizedTriangleCompatible model T (by simp [hf,hg,hh]))
    (p : ℕ) (hp : 2 ≤ p) (s t : ℤ) :
    (∀ a : Ambient model T.X (s,t), IsCycle model T.X 1 (s,t) a →
      ∃ z : Ambient model T.Z (s,t+1), IsCycle model T.Z 1 (s,t+1) z ∧
        ∃ u : Ambient model T.X (s,t),
          (model.classicalSuspension T.X).DesuspendsClass s (t+1)
            ((model.classical.map T.h).pageMap 2 (s,t+1) z)
            (by simpa only [add_sub_cancel_right] using u) ∧
          Congruent model T.X p (s,t) a u) ↔
      (cofiberFirstQuotientBoundaryHom T hf s t).range =
        (boundaries model T.X p (s,t)).toAddSubgroup.map
          (cofiberFirstQuotientBoundaryHom T hf s t) := by
  refine Iff.trans ?_ (mahowaldLeibnizLastLayerComparison T hf hg hh hT p hp s t).2.1.1
  constructor
  · intro hs a
    obtain ⟨z,_,u,hu,hau⟩ := hs a (every_label_cycle_one T.X s t a)
    have hzu : u = classicalTriangleHMapHom T s t z := by
      have cast_eq (n n' : ℤ) (hn : n=n')
          (a b : Ambient model T.X (s,n')) :
          (congrArg (fun q : ℤ => (Ambient model T.X (s,q) : Type)) hn).mpr a =
            (congrArg (fun q : ℤ => (Ambient model T.X (s,q) : Type)) hn).mpr b ↔
          a=b := by
        subst n'; rfl
      apply (cast_eq (t+1-1) t (by omega) _ _).mp
      exact
        (KIP126.ProofTools.Internal.Mahowald.desuspendsClass_eq_iff T.X s (t+1)
          _ _ _ _ hu (classicalTriangleHMapHom_spec T s t z)).mp rfl
    refine ⟨z,a-u,hau.2,?_⟩
    rw [←hzu]
    abel
  · intro hs a _
    obtain ⟨z,b,hb,ha⟩ := hs a
    refine ⟨z,every_label_cycle_one T.Z s (t+1) z,
      classicalTriangleHMapHom T s t z, classicalTriangleHMapHom_spec T s t z,
      ⟨by omega,?_⟩⟩
    rw [ha]
    change b ∈ boundaries model T.X p (s,t) at hb
    simpa only [add_sub_cancel_left] using hb

end KIP126.ProofTools.Standard
