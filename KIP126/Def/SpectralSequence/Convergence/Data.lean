module

public import KIP126.Def.SpectralSequence.Basic.Data
import all KIP126.Def.SpectralSequence.Basic.Data
public import KIP126.Def.SpectralSequence.Internal.Algebra.Filtration.Data
import all KIP126.Def.SpectralSequence.Internal.Algebra.Filtration.Data

@[expose] section

/-!
# Internal convergence data for nested-subobject spectral sequences

This file migrates the data declarations from
`KIPBase/SpectralSequence/Convergence.lean`.  The historical public names are preserved. Filtrations and associated-graded
operations are shared with the internal algebra foundation.
-/

namespace KIP126.Core.SpectralSequence

open CategoryTheory CategoryTheory.Limits

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Weak convergence to a filtered graded object. -/
public structure Convergence
    {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    (E : SpectralSequence C ω) {ω' : Type w} (A : ω' → C) (F : Filtration A) where
  /-- Reindexing from spectral-sequence degrees to filtration/stem degrees. -/
  reindex : ω → ℤ × ω'
  /-- The reindexing is bijective. -/
  reindex_bijective : Function.Bijective reindex
  /-- Identification of the infinity page with the associated graded. -/
  iso : ∀ (k : ω),
    (E.ssData k).eInfty ≅ F.associatedGraded (reindex k).1 (reindex k).2

/-- Filtration-degree component of the convergence reindexing. -/
public def Convergence.filtrationDegree
    {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E : SpectralSequence C ω} {ω' : Type w} {A : ω' → C} {F : Filtration A}
    (conv : Convergence E A F) (k : ω) : ℤ :=
  (conv.reindex k).1

/-- Stem-degree component of the convergence reindexing. -/
public def Convergence.stemDegree
    {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E : SpectralSequence C ω} {ω' : Type w} {A : ω' → C} {F : Filtration A}
    (conv : Convergence E A F) (k : ω) : ω' :=
  (conv.reindex k).2

/-- Map on associated graded pieces induced by filtration-compatible maps. -/
public noncomputable def Filtration.inducedAssocGradedMap
    {ω' : Type w} {A₁ A₂ : ω' → C}
    {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    (aMap : ∀ k', A₁ k' ⟶ A₂ k')
    (hcompat : ∀ (s : ℤ) (k' : ω'),
      ∃ (φ : Subobject.underlying.obj (F₁.F s k') ⟶
        Subobject.underlying.obj (F₂.F s k')),
        φ ≫ (F₂.F s k').arrow = (F₁.F s k').arrow ≫ aMap k')
    (s : ℤ) (k' : ω') : F₁.associatedGraded s k' ⟶ F₂.associatedGraded s k' :=
  cokernel.map
    (Subobject.ofLE (F₁.F (s + 1) k') (F₁.F s k') (F₁.mono s k'))
    (Subobject.ofLE (F₂.F (s + 1) k') (F₂.F s k') (F₂.mono s k'))
    (hcompat (s + 1) k').choose
    (hcompat s k').choose
    (by
      apply (cancel_mono ((F₂.F s k').arrow)).mp
      simp only [Category.assoc, Subobject.ofLE_arrow]
      rw [(hcompat s k').choose_spec, (hcompat (s + 1) k').choose_spec,
        ← Category.assoc, Subobject.ofLE_arrow])

/-- Data part of a morphism between convergent spectral sequences. -/
public structure ConvergenceMorphismData
    {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    (conv₁ : Convergence E₁ A₁ F₁) (conv₂ : Convergence E₂ A₂ F₂) where
  /-- Map on infinity pages. -/
  eMap : ∀ (k : ω), (E₁.ssData k).eInfty ⟶ (E₂.ssData k).eInfty
  /-- Map on the target graded objects. -/
  aMap : ∀ (k' : ω'), A₁ k' ⟶ A₂ k'
  /-- The target map preserves the filtrations. -/
  filtration_compat : ∀ (s : ℤ) (k' : ω'),
    ∃ (φ : Subobject.underlying.obj (F₁.F s k') ⟶
      Subobject.underlying.obj (F₂.F s k')),
      φ ≫ (F₂.F s k').arrow = (F₁.F s k').arrow ≫ aMap k'

/-- A morphism between convergent spectral sequences. -/
public structure ConvergenceMorphism
    {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    (conv₁ : Convergence E₁ A₁ F₁) (conv₂ : Convergence E₂ A₂ F₂)
    extends ConvergenceMorphismData conv₁ conv₂ where
  /-- The two reindexings agree. -/
  reindex_eq : conv₁.reindex = conv₂.reindex
  /-- Compatibility with the convergence isomorphisms. -/
  iso_compat : ∀ (k : ω),
    eMap k ≫ (conv₂.iso k).hom ≫
      F₂.transportGraded (congrFun reindex_eq k).symm =
    (conv₁.iso k).hom ≫
      Filtration.inducedAssocGradedMap aMap filtration_compat
        (conv₁.reindex k).1 (conv₁.reindex k).2

/-- A filtration-preserving degreewise map. -/
public structure FilteredMorphism
    {ω : Type w} {A₁ A₂ : ω → C} (F₁ : Filtration A₁) (F₂ : Filtration A₂) where
  /-- Degreewise map. -/
  map : ∀ (k : ω), A₁ k ⟶ A₂ k
  /-- Restriction to every filtration level. -/
  compat : ∀ (s : ℤ) (k : ω),
    ∃ (φ : Subobject.underlying.obj (F₁.F s k) ⟶
      Subobject.underlying.obj (F₂.F s k)),
      φ ≫ (F₂.F s k).arrow = (F₁.F s k).arrow ≫ map k

/-- A filtered morphism induces a map of associated graded pieces. -/
public noncomputable def FilteredMorphism.inducedGrMap
    {ω : Type w} {A₁ A₂ : ω → C}
    {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    (f : FilteredMorphism F₁ F₂) (s : ℤ) (k : ω) :
    F₁.associatedGraded s k ⟶ F₂.associatedGraded s k :=
  Filtration.inducedAssocGradedMap f.map f.compat s k

/-- A spectral sequence packaged with its filtered target and convergence data. -/
structure ConvergingSS
    (C : Type u) [Category.{v} C] [Abelian C]
    (ω : Type w) [AddCommGroup ω] [DecidableEq ω] (ω' : Type w) where
  /-- Underlying spectral sequence. -/
  E : SpectralSequence C ω
  /-- Target graded object. -/
  A : ω' → C
  /-- Filtration on the target. -/
  F : Filtration A
  /-- Convergence identification. -/
  conv : Convergence E A F

/-- Associated-graded map with the restriction maps supplied explicitly. -/
noncomputable def Filtration.inducedGradedMapOfMap
    {ω' : Type w} {A₁ A₂ : ω' → C}
    {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    (φ : ∀ (s : ℤ) (k' : ω'), Subobject.underlying.obj (F₁.F s k') ⟶
      Subobject.underlying.obj (F₂.F s k'))
    (hw : ∀ (s : ℤ) (k' : ω'),
      Subobject.ofLE (F₁.F (s + 1) k') (F₁.F s k') (F₁.mono s k') ≫ φ s k' =
        φ (s + 1) k' ≫
          Subobject.ofLE (F₂.F (s + 1) k') (F₂.F s k') (F₂.mono s k'))
    (s : ℤ) (k' : ω') : F₁.associatedGraded s k' ⟶ F₂.associatedGraded s k' :=
  cokernel.map
    (Subobject.ofLE (F₁.F (s + 1) k') (F₁.F s k') (F₁.mono s k'))
    (Subobject.ofLE (F₂.F (s + 1) k') (F₂.F s k') (F₂.mono s k'))
    (φ (s + 1) k') (φ s k') (hw s k')

end KIP126.Core.SpectralSequence
