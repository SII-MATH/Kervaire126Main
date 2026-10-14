module

import KIP126.Def.SpectralSequence

open CategoryTheory CategoryTheory.Limits
open KIP126.Core KIP126.Core.SpectralSequence

universe u v w

section Detection

variable {C : Type u} [Category.{v} C] [Abelian C]
  {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
  {ω : Type w} {E : SpectralSequence C ι} {A : ω → C} {F : Filtration A}

-- Detection is usable without constructing a convergent spectral sequence.
example (c : Convergence E A F) {T : C} {i : ι}
    (a : T ⟶ Subobject.underlying.obj (F.F (c.reindex i).1 (c.reindex i).2))
    (ha : Detects c (0 : T ⟶ (E.ssData i).eInfty) a) :
    ∃ b : T ⟶ Subobject.underlying.obj
      (F.F ((c.reindex i).1 + 1) (c.reindex i).2),
      b ≫ Subobject.ofLE _ _ (F.mono (c.reindex i).1 (c.reindex i).2) = a :=
  (detect_zero c a).mp ha

-- A finite vanishing interval only uses its actual associated grades.
example (s t : ℤ) (k : ω) (hst : s ≤ t)
    (h : ∀ j : ℤ, s ≤ j → j < t → IsZero (F.associatedGraded j k)) :
    F.F s k = F.F t k := F.eq_of_associatedGraded_isZero s t k hst h

example {E' : SpectralSequence C ι} {B : ω → C} {G : Filtration B}
    {c : Convergence E A F} {c' : Convergence E' B G}
    (m : ConvergenceMorphism c c') (i : ι) :
    m.eMap i ≫ (c'.iso i).hom ≫ G.transportGraded (congrFun m.reindex_eq i).symm =
      (c.iso i).hom ≫ m.filteredMap.inducedGrMap (c.reindex i).1 (c.reindex i).2 :=
  m.iso_compat i

end Detection

section Extension

open FilteredMapExtension

variable {C : Type u} [Category.{v} C] [Abelian C]
  {ω : Type w} {A B : ω → C} {F : Filtration A} {G : Filtration B}
  (f : FilteredMorphism F G) (k : ω) (s n : ℤ)
  {T : C} {x : T ⟶ F.associatedGraded s k}
  {y z : T ⟶ G.associatedGraded (s + n) k}

-- One solution determines the full coset; no subgroup is supplied by the caller.
example (h : Relation f k s n x y) (hz : z ∈ TargetCoset f k s n y) :
    Relation f k s n x z := h.mem_targetCoset_iff.mp hz

example (h : Relation f k s n x y) (hz : Relation f k s n x 0) :
    ¬ Essential f k s n x y := fun he => (essential_iff h).mp he hz

-- Homogeneous ambiguity has actual higher-filtration lifts.
example (hz : z ∈ TargetIndeterminacy f k s n T) :
    0 ≤ n ∧ ∃ (a : T ⟶ Subobject.underlying.obj (F.F (s + 1) k))
      (b : T ⟶ Subobject.underlying.obj (G.F (s + n) k)),
      b ≫ G.toAssociatedGraded (s + n) k = z ∧
      a ≫ (F.F (s + 1) k).arrow ≫ f.map k = b ≫ (G.F (s + n) k).arrow :=
  mem_indeterminacy_iff.mp hz

-- The unrestricted zero-length statement keeps source lifting explicit.
example (y₀ : T ⟶ G.associatedGraded (s + 0) k)
    (ha : ∃ a : T ⟶ Subobject.underlying.obj (F.F s k),
      a ≫ F.toAssociatedGraded s k = x)
    (h : x ≫ f.inducedGrMap s k =
      y₀ ≫ G.transportGraded (show (s + 0, k) = (s, k) by simp)) :
    Relation f k s 0 x y₀ := (relation_zero_iff f k s x y₀).mpr ⟨ha, h⟩

-- On projective probes the same equation supplies the actual ESS relation.
example (hF : F.IsBounded) (hG : G.IsBounded) [Projective T]
    (y₀ : T ⟶ G.associatedGraded (s + 0) k)
    (h : x ≫ f.inducedGrMap s k =
      y₀ ≫ G.transportGraded (show (s + 0, k) = (s, k) by simp)) :
    DifferentialRelation (sequence f hF hG k) 0 (s, 1)
      (x ≫ (sourceIso f hF hG k s).inv)
      (y₀ ≫ (targetIso f hF hG k s 0).inv) :=
  (differentialRelation_iff f hF hG k s 0 x y₀).mpr
    ((relation_zero_iff_of_projective f k s x y₀).mpr h)

-- The filtered-map ambiguity is the full boundary coset of this same ESS.
example (hF : F.IsBounded) (hG : G.IsBounded) (m : ℕ) [Projective T]
    (y z : T ⟶ G.associatedGraded (s + (m : ℤ)) k)
    (h : Relation f k s m x y) :
    (z ≫ (targetIso f hF hG k s m).inv) ∈
      DifferentialTargetCoset (sequence f hF hG k) m (s, 1)
        (y ≫ (targetIso f hF hG k s m).inv) ↔
      z ∈ TargetCoset f k s m y := by
  have hd := (differentialRelation_iff f hF hG k s m x y).mpr h
  exact (DifferentialRelation.mem_targetCoset_iff _ _ _ hd).trans
    ((differentialRelation_iff f hF hG k s m x z).trans h.mem_targetCoset_iff.symm)

end Extension

#check_failure KIP126.Core.SpectralSequence.underlyingComplex
#check_failure KIP126.Core.SpectralSequence.DifferentialMorphismCriterion
#check_failure KIP126.Core.SpectralSequence.SSDataMorphism.toUnderlying
#check_failure KIP126.Core.SpectralSequence.PreSS.forget
#check_failure KIP126.Core.SpectralSequence.SpectralSequenceMorphism.equivPreSSMorphism
#check_failure KIP126.Core.SpectralSequence.inclusion
#check_failure KIP126.Core.SpectralSequence.GradedSSData
#check_failure KIP126.Core.SpectralSequence.EInftyData
