module

import all KIP126.SpectralSequence.Internal.Algebra.Graded.Data
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

@[expose] section

/-!
# Filtrations underlying spectral sequences

The public filtration record and associated-graded operations are defined once
at this foundation layer. Filtered complexes, convergence, completion and
truncation use this same record. Other algebra constructions remain private.
Filtrations require only a category; quotients additionally require an abelian
category.
-/

namespace KIP126.Core.SpectralSequence

open CategoryTheory CategoryTheory.Limits

universe u v w

variable {C : Type u} [Category.{v} C]

/-- A decreasing filtration with the historical `mono` field name. -/
public structure Filtration {ω : Type w} (A : ω → C) where
  /-- Filtration subobject at level `s` and grading `k`. -/
  F : ℤ → (k : ω) → Subobject (A k)
  /-- Successive levels form a decreasing family. -/
  mono : ∀ (s : ℤ) (k : ω), F (s + 1) k ≤ F s k

section

variable [Abelian C]

/-- Associated graded piece `F^s A^k / F^(s+1) A^k`. -/
public noncomputable def Filtration.associatedGraded
    {ω : Type w} {A : ω → C} (F : Filtration A) (s : ℤ) (k : ω) : C :=
  cokernel (Subobject.ofLE (F.F (s + 1) k) (F.F s k) (F.mono s k))

/-- Projection from a filtration level to its associated graded piece. -/
public noncomputable def Filtration.toAssociatedGraded
    {ω : Type w} {A : ω → C} (F : Filtration A) (s : ℤ) (k : ω) :
    Subobject.underlying.obj (F.F s k) ⟶ F.associatedGraded s k :=
  cokernel.π (Subobject.ofLE (F.F (s + 1) k) (F.F s k) (F.mono s k))

/-- Transport associated graded pieces along equality of their indices. -/
public noncomputable def Filtration.transportGraded
    {ω' : Type w} {A : ω' → C} (F : Filtration A)
    {r₁ r₂ : ℤ × ω'} (h : r₁ = r₂) :
    F.associatedGraded r₁.1 r₁.2 ⟶ F.associatedGraded r₂.1 r₂.2 :=
  eqToHom (by rw [h])

end

/-- A filtration decreases between any two ordered integer levels. -/
public theorem Filtration.le_of_le {ω : Type w} {A : ω → C}
    (F : Filtration A) {s t : ℤ} (h : s ≤ t) (k : ω) : F.F t k ≤ F.F s k := by
  induction t, h using Int.leInduction with
  | base => exact le_rfl
  | succ t _ ih => exact (F.mono t k).trans ih

namespace Filtration

variable {ι : Type w} {A : CategoryTheory.GradedObject ι C}

/-! ### Maps between arbitrary filtration levels

The successor inequality in `Filtration.mono` is the compact datum from
which all of the maps in the filtration diagram are obtained.  Keeping this
construction here (rather than re-proving it in the filtered-complex layer)
also fixes the variance convention once and for all: for `t ≤ s`, the
decreasing filtration has an inclusion `F s ↪ F t`.
-/

/-- The canonical inclusion `Fˢ Aᵢ ⟶ Fᵗ Aᵢ` when `t ≤ s`. -/
noncomputable def inclusion (F : Filtration A) {t s : ℤ} (h : t ≤ s) (i : ι) :
    Subobject.underlying.obj (F.F s i) ⟶ Subobject.underlying.obj (F.F t i) :=
  Subobject.ofLE (F.F s i) (F.F t i) (F.le_of_le h i)

@[simp]
lemma inclusion_arrow (F : Filtration A) {t s : ℤ} (h : t ≤ s) (i : ι) :
    F.inclusion h i ≫ (F.F t i).arrow = (F.F s i).arrow :=
  Subobject.ofLE_arrow _

@[simp]
lemma inclusion_refl (F : Filtration A) (s : ℤ) (i : ι) :
    F.inclusion (le_rfl : s ≤ s) i = 𝟙 _ := by
  simp [inclusion]

@[reassoc (attr := simp)]
lemma inclusion_comp (F : Filtration A) {r s t : ℤ}
    (hrs : r ≤ s) (hst : s ≤ t) (i : ι) :
    F.inclusion hst i ≫ F.inclusion hrs i = F.inclusion (hrs.trans hst) i := by
  simp [inclusion]

/-- Naturality of a filtration subobject arrow under an equality of grading
indices.  This is the transport lemma needed whenever a complex shape writes
the predecessor as an expression such as `(k + 1) - 1`. -/
lemma transport_arrow (F : Filtration A) (s : ℤ) {i j : ι} (h : i = j) :
    eqToHom (congrArg (fun k => Subobject.underlying.obj (F.F s k)) h) ≫
        (F.F s j).arrow =
      (F.F s i).arrow ≫ eqToHom (congrArg A h) := by
  subst h
  simp

/-- The level inclusions are natural with respect to index transports. -/
lemma inclusion_naturality (F : Filtration A) {t s : ℤ} (h : t ≤ s)
    {i j : ι} (hij : i = j) :
    F.inclusion h i ≫
        eqToHom (congrArg (fun k => Subobject.underlying.obj (F.F t k)) hij) =
      eqToHom (congrArg (fun k => Subobject.underlying.obj (F.F s k)) hij) ≫
        F.inclusion h j := by
  subst hij
  simp


/-- All associated graded pieces, graded by filtration degree and the original
grading index. -/
noncomputable def associatedGradedObject [Abelian C] (F : Filtration A) :
    CategoryTheory.GradedObject (ℤ × ι) C :=
  fun si => F.associatedGraded si.1 si.2

end Filtration

/-- A morphism of filtered graded objects is a graded map whose restriction to
each filtration subobject factors through the corresponding target
subobject. -/
structure InternalFilteredMorphism {ι : Type w}
    {A B : CategoryTheory.GradedObject ι C} (F : Filtration A) (G : Filtration B) where
  /-- The underlying degree-preserving map. -/
  map : A ⟶ B
  /-- Preservation of every filtration level. -/
  preserves : ∀ (s : ℤ) (i : ι),
    ∃ φ : Subobject.underlying.obj (F.F s i) ⟶ Subobject.underlying.obj (G.F s i),
      φ ≫ (G.F s i).arrow = (F.F s i).arrow ≫ map i

namespace InternalFilteredMorphism

variable {ι : Type w}
  {A B D : CategoryTheory.GradedObject ι C}
  {F : Filtration A} {G : Filtration B} {H : Filtration D}

/-- The identity map of a filtered graded object. -/
def id (F : Filtration A) : InternalFilteredMorphism F F where
  map := 𝟙 A
  preserves := fun s i => ⟨𝟙 _, by simp⟩

/-- Composition of filtration-preserving graded maps. -/
def comp (f : InternalFilteredMorphism F G) (g : InternalFilteredMorphism G H) :
    InternalFilteredMorphism F H where
  map := f.map ≫ g.map
  preserves := fun s i => by
    refine ⟨(f.preserves s i).choose ≫ (g.preserves s i).choose, ?_⟩
    change ((f.preserves s i).choose ≫ (g.preserves s i).choose) ≫
      (H.F s i).arrow = (F.F s i).arrow ≫ (f.map i ≫ g.map i)
    rw [Category.assoc, (g.preserves s i).choose_spec, ← Category.assoc,
      (f.preserves s i).choose_spec]
    simp only [Category.assoc]

lemma id_preserves_eq (F : Filtration A) (s : ℤ) (i : ι) :
    ((InternalFilteredMorphism.id F).preserves s i).choose = 𝟙 _ := by
  apply (cancel_mono (F.F s i).arrow).mp
  rw [(InternalFilteredMorphism.id F).preserves s i |>.choose_spec]
  dsimp [InternalFilteredMorphism.id]
  simp

lemma comp_preserves_eq (f : InternalFilteredMorphism F G) (g : InternalFilteredMorphism G H)
    (s : ℤ) (i : ι) :
    ((InternalFilteredMorphism.comp f g).preserves s i).choose =
      (f.preserves s i).choose ≫ (g.preserves s i).choose := by
  apply (cancel_mono (H.F s i).arrow).mp
  calc
    ((InternalFilteredMorphism.comp f g).preserves s i).choose ≫
          (H.F s i).arrow =
        (F.F s i).arrow ≫ (InternalFilteredMorphism.comp f g).map i :=
      (InternalFilteredMorphism.comp f g).preserves s i |>.choose_spec
    _ = ((F.F s i).arrow ≫ f.map i) ≫ g.map i := by
      simp only [InternalFilteredMorphism.comp,
        GradedObject.categoryOfGradedObjects_comp]
      simp only [Category.assoc]
    _ = ((f.preserves s i).choose ≫ (G.F s i).arrow) ≫ g.map i := by
      rw [(f.preserves s i).choose_spec]
    _ = (f.preserves s i).choose ≫
          ((G.F s i).arrow ≫ g.map i) := by simp only [Category.assoc]
    _ = (f.preserves s i).choose ≫
          ((g.preserves s i).choose ≫ (H.F s i).arrow) := by
      rw [(g.preserves s i).choose_spec]
    _ = ((f.preserves s i).choose ≫ (g.preserves s i).choose) ≫
          (H.F s i).arrow := by simp only [Category.assoc]

/-- The map on associated graded pieces induced by a filtration-preserving
morphism. -/
noncomputable def associatedGradedMap [Abelian C] (f : InternalFilteredMorphism F G) (s : ℤ) (i : ι) :
    F.associatedGraded s i ⟶ G.associatedGraded s i :=
  cokernel.map
    (Subobject.ofLE (F.F (s + 1) i) (F.F s i) (F.mono s i))
    (Subobject.ofLE (G.F (s + 1) i) (G.F s i) (G.mono s i))
    (f.preserves (s + 1) i).choose
    (f.preserves s i).choose
    (by
      apply (cancel_mono ((G.F s i).arrow)).mp
      simp only [Category.assoc, Subobject.ofLE_arrow]
      rw [(f.preserves s i).choose_spec, (f.preserves (s + 1) i).choose_spec,
        ← Category.assoc, Subobject.ofLE_arrow])

end InternalFilteredMorphism

end KIP126.Core.SpectralSequence
