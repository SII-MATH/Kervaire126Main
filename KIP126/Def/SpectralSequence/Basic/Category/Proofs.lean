module

public import KIP126.Def.SpectralSequence.Basic.Category.Predicates

@[expose] public section

/-!
# Proofs about the spectral-sequence category
-/

namespace KIP126.Core.SpectralSequence

open CategoryTheory

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C]

@[simp]
theorem PreSSMorphism.pageMap_id
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    (E : PreSS C ι) (r : ℤ) (k : ι) :
    (𝟙 E : E ⟶ E).pageMap r k = 𝟙 _ :=
  SSDataMorphism.pageMapAt_id E r k

@[simp]
theorem PreSSMorphism.pageMap_comp
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    {E E' E'' : PreSS C ι} (f : E ⟶ E') (g : E' ⟶ E'') (r : ℤ) (k : ι) :
    (f ≫ g).pageMap r k = f.pageMap r k ≫ g.pageMap r k :=
  SSDataMorphism.pageMapAt_comp f.toSSDataMorphism g.toSSDataMorphism
    f.r₀_eq g.r₀_eq r k

@[simp]
theorem SpectralSequenceMorphism.pageMap_id
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    (E : SpectralSequence C ι) (r : ℤ) (k : ι) :
    (𝟙 E : E ⟶ E).pageMap r k = 𝟙 _ :=
  PreSSMorphism.pageMap_id E.toPreSS r k

@[simp]
theorem SpectralSequenceMorphism.pageMap_comp
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    {E E' E'' : SpectralSequence C ι} (f : E ⟶ E') (g : E' ⟶ E'')
    (r : ℤ) (k : ι) :
    (f ≫ g).pageMap r k = f.pageMap r k ≫ g.pageMap r k :=
  PreSSMorphism.pageMap_comp f.toPreSSMorphism g.toPreSSMorphism r k

@[simp]
theorem SpectralSequenceMorphism.eInftyMap_id
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    (E : SpectralSequence C ι) (k : ι) :
    (𝟙 E : E ⟶ E).eInftyMap k = 𝟙 _ :=
  SSDataMorphism.pageMap_id E.ssData k ⊤

@[simp]
theorem SpectralSequenceMorphism.eInftyMap_comp
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    {E E' E'' : SpectralSequence C ι} (f : E ⟶ E') (g : E' ⟶ E'') (k : ι) :
    (f ≫ g).eInftyMap k = f.eInftyMap k ≫ g.eInftyMap k :=
  SSDataMorphism.pageMap_comp f.toSSDataMorphism g.toSSDataMorphism k ⊤

/-- A square commutes exactly when its maps commute at every underlying grading. -/
theorem commSq_iff_underlying
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    {W X Y Z : SpectralSequence C ι}
    (f : W ⟶ X) (g : W ⟶ Y) (h : X ⟶ Z) (i : Y ⟶ Z) :
    SpectralSequence.CommSq f g h i ↔
      ∀ (k : ι), f.φ k ≫ h.φ k = g.φ k ≫ i.φ k := by
  constructor
  · intro hsq k
    exact congrFun (congrArg SpectralSequenceMorphism.φ hsq.w) k
  · intro hsq
    constructor
    exact SpectralSequenceMorphism.ext (funext hsq)

end KIP126.Core.SpectralSequence
