module

public import KIP126.Def.Algebra.Filtration.Data
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.CochainComplexOpposite

@[expose] public section

/-!
# Filtered chain complexes

A filtered chain complex is a Mathlib `ChainComplex` equipped with a decreasing
filtration preserved by the differential.  Unlike the historical KIP core, this
file does not define a second spectral-sequence record or a nested `Z/B`
presentation.  It supplies the associated graded differential needed by a
future construction through Mathlib's spectral-object machinery.
-/

namespace KIP126.SpectralSequence

open CategoryTheory CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A chain complex together with a decreasing filtration preserved by its
differential. -/
structure FilteredComplex (C : Type u) [Category.{v} C] [Abelian C] where
  /-- The underlying Mathlib chain complex. -/
  complex : ChainComplex C ℤ
  /-- A decreasing filtration of the underlying graded object. -/
  filtration : Algebra.Filtration complex.X
  /-- The differential maps every filtration level into the same level in the
next chain degree. -/
  differential_preserves : ∀ (s k : ℤ),
    ∃ φ : Subobject.underlying.obj (filtration.F s k) ⟶
        Subobject.underlying.obj (filtration.F s (k - 1)),
      φ ≫ (filtration.F s (k - 1)).arrow =
        (filtration.F s k).arrow ≫ complex.d k (k - 1)

namespace FilteredComplex

/-! ### Homology of the underlying complex

The following construction keeps the chain-degree convention explicit.  A
homology object at degree `k` is the homology of the short complex
`X (k + 1) ⟶ X k ⟶ X (k - 1)`. -/

noncomputable def homologyShortComplex (FC : FilteredComplex C) (k : ℤ) :
    ShortComplex C :=
  ShortComplex.mk
    (FC.complex.d (k + 1) k)
    (FC.complex.d k (k - 1))
    (FC.complex.d_comp_d (k + 1) k (k - 1))

/-- The homology graded object of the underlying filtered chain complex. -/
noncomputable def homologyObj (FC : FilteredComplex C) : ℤ → C :=
  fun k => (FC.homologyShortComplex k).homology

/-! ### The induced filtration on homology -/

noncomputable def homologyFiltration (FC : FilteredComplex C) :
    Algebra.Filtration FC.homologyObj where
  F s k :=
    let S := FC.homologyShortComplex k
    let I := kernelSubobject S.g ⊓ FC.filtration.F s k
    let hzero : I.arrow ≫ S.g = 0 := by
      rw [show I.arrow = Subobject.ofLE I (kernelSubobject S.g) inf_le_left ≫
        (kernelSubobject S.g).arrow from (Subobject.ofLE_arrow inf_le_left).symm]
      rw [Category.assoc, kernelSubobject_arrow_comp, comp_zero]
    imageSubobject (S.liftCycles I.arrow hzero ≫ S.homologyπ)
  decreasing := by
    intro s k
    let S := FC.homologyShortComplex k
    let I₁ := kernelSubobject S.g ⊓ FC.filtration.F (s + 1) k
    let I₀ := kernelSubobject S.g ⊓ FC.filtration.F s k
    have hle : I₁ ≤ I₀ := inf_le_inf_left _ (FC.filtration.decreasing s k)
    have hzero₁ : I₁.arrow ≫ S.g = 0 := by
      rw [show I₁.arrow = Subobject.ofLE I₁ (kernelSubobject S.g) inf_le_left ≫
        (kernelSubobject S.g).arrow from (Subobject.ofLE_arrow inf_le_left).symm]
      rw [Category.assoc, kernelSubobject_arrow_comp, comp_zero]
    have hzero₀ : I₀.arrow ≫ S.g = 0 := by
      rw [show I₀.arrow = Subobject.ofLE I₀ (kernelSubobject S.g) inf_le_left ≫
        (kernelSubobject S.g).arrow from (Subobject.ofLE_arrow inf_le_left).symm]
      rw [Category.assoc, kernelSubobject_arrow_comp, comp_zero]
    have hlift : S.liftCycles I₁.arrow hzero₁ =
        Subobject.ofLE I₁ I₀ hle ≫ S.liftCycles I₀.arrow hzero₀ := by
      apply (cancel_mono S.iCycles).mp
      rw [S.liftCycles_i, Category.assoc, S.liftCycles_i]
      exact (Subobject.ofLE_arrow hle).symm
    have hlift' : S.liftCycles I₁.arrow hzero₁ ≫ S.homologyπ =
        Subobject.ofLE I₁ I₀ hle ≫
          (S.liftCycles I₀.arrow hzero₀ ≫ S.homologyπ) := by
      rw [← Category.assoc, hlift]
    change imageSubobject (S.liftCycles I₁.arrow hzero₁ ≫ S.homologyπ) ≤
      imageSubobject (S.liftCycles I₀.arrow hzero₀ ≫ S.homologyπ)
    rw [hlift']
    exact imageSubobject_comp_le _ _

/-! ### Cycles and boundaries in an associated graded piece -/

/-- The differential from degree `k + 1` to degree `k`.  The canonical chain
complex already indexes its target by `k`, so no degree transport is needed. -/
noncomputable def dToK (FC : FilteredComplex C) (k : ℤ) :
    FC.complex.X (k + 1) ⟶ FC.complex.X k :=
  FC.complex.d (k + 1) k

/-- The `r`-cycle subobject in the associated graded piece. -/
noncomputable def cycleSubobject (FC : FilteredComplex C)
    (s k : ℤ) (r : WithTop ℕ) :
    Subobject (FC.filtration.associatedGraded s k) :=
  let πV := FC.filtration.toAssociatedGraded s k
  match r with
  | ⊤ =>
    let f := (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1)
    imageSubobject ((kernelSubobject f).arrow ≫ πV)
  | (n : ℕ) =>
    let f := (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1) ≫
      cokernel.π ((FC.filtration.F (s + ↑n) (k - 1)).arrow)
    imageSubobject ((kernelSubobject f).arrow ≫ πV)

/-- The `r`-boundary subobject in the associated graded piece. -/
noncomputable def boundarySubobject (FC : FilteredComplex C)
    (s k : ℤ) (r : WithTop ℕ) :
    Subobject (FC.filtration.associatedGraded s k) :=
  let πV := FC.filtration.toAssociatedGraded s k
  match r with
  | ⊤ =>
    let imgD := imageSubobject (FC.dToK k)
    let I := imgD ⊓ FC.filtration.F s k
    imageSubobject (Subobject.ofLE I (FC.filtration.F s k) inf_le_right ≫ πV)
  | (n : ℕ) =>
    let imgD := imageSubobject
      ((FC.filtration.F (s - ↑n + 1) (k + 1)).arrow ≫ FC.dToK k)
    let I := imgD ⊓ FC.filtration.F s k
    imageSubobject (Subobject.ofLE I (FC.filtration.F s k) inf_le_right ≫ πV)



/-! The filtered complexes and their filtered chain maps form the expected
category.  The proof fields are propositions, so the usual chain-complex
extensionality lemma is enough for the category laws. -/

/-- The differential induced on a fixed associated graded piece. -/
noncomputable def associatedGradedDifferential (FC : FilteredComplex C)
    (s k : ℤ) :
    FC.filtration.associatedGraded s k ⟶
      FC.filtration.associatedGraded s (k - 1) := by
  unfold Algebra.Filtration.associatedGraded
  exact cokernel.desc _
    ((FC.differential_preserves s k).choose ≫
      cokernel.π (Subobject.ofLE (FC.filtration.F (s + 1) (k - 1))
        (FC.filtration.F s (k - 1)) (FC.filtration.decreasing s (k - 1))))
    (by
      have factor :
          Subobject.ofLE (FC.filtration.F (s + 1) k) (FC.filtration.F s k)
              (FC.filtration.decreasing s k) ≫
            (FC.differential_preserves s k).choose =
          (FC.differential_preserves (s + 1) k).choose ≫
            Subobject.ofLE (FC.filtration.F (s + 1) (k - 1))
              (FC.filtration.F s (k - 1)) (FC.filtration.decreasing s (k - 1)) := by
        have mono_arrow : Mono (FC.filtration.F s (k - 1)).arrow := inferInstance
        have lhs_eq :
            (Subobject.ofLE (FC.filtration.F (s + 1) k) (FC.filtration.F s k)
                (FC.filtration.decreasing s k) ≫
              (FC.differential_preserves s k).choose) ≫
                (FC.filtration.F s (k - 1)).arrow =
              (FC.filtration.F (s + 1) k).arrow ≫ FC.complex.d k (k - 1) := by
          rw [Category.assoc, (FC.differential_preserves s k).choose_spec,
            ← Category.assoc, Subobject.ofLE_arrow]
        have rhs_eq :
            ((FC.differential_preserves (s + 1) k).choose ≫
              Subobject.ofLE (FC.filtration.F (s + 1) (k - 1))
                (FC.filtration.F s (k - 1)) (FC.filtration.decreasing s (k - 1))) ≫
                (FC.filtration.F s (k - 1)).arrow =
              (FC.filtration.F (s + 1) k).arrow ≫ FC.complex.d k (k - 1) := by
          rw [Category.assoc, Subobject.ofLE_arrow,
            (FC.differential_preserves (s + 1) k).choose_spec]
        exact mono_arrow.right_cancellation _ _ (lhs_eq.trans rhs_eq.symm)
      rw [← Category.assoc, factor, Category.assoc, cokernel.condition, comp_zero])

section FilteredMorphismLemmas

variable {FC GD GE : FilteredComplex C}

/-- The quotient projection intertwines the associated-graded differential with
the chosen filtered restriction of the original differential. -/
lemma toAssociatedGraded_comp_associatedGradedDifferential
    (FC : FilteredComplex C) (s k : ℤ) :
    FC.filtration.toAssociatedGraded s k ≫
        FC.associatedGradedDifferential s k =
      (FC.differential_preserves s k).choose ≫
        FC.filtration.toAssociatedGraded s (k - 1) := by
  unfold Algebra.Filtration.toAssociatedGraded associatedGradedDifferential
  exact cokernel.π_desc _ _ _

end FilteredMorphismLemmas

end FilteredComplex

end KIP126.SpectralSequence
