module

public import KIP126.SpectralSequence.Consumer.Extension
public import KIP126.SpectralSequence.Crossing.Proofs
import all KIP126.SpectralSequence.BoundedExtension.UnderlyingComplex.Proofs
import all KIP126.SpectralSequence.FilteredComplex.Solutions.Page.Converse.Proofs

@[expose] section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000

/-! The bounded extension sequence of a specified filtered map. The filtered
complex is an implementation detail; all public types use the original map,
filtrations, graded objects and the generic spectral-sequence language. -/

namespace KIP126.Core.SpectralSequence.FilteredMapExtension

open CategoryTheory CategoryTheory.Limits

universe u v w
variable {C : Type u} [Category.{v} C] [Abelian C]
  {ω : Type w} {A B : ω → C} {F : Filtration A} {G : Filtration B}

/-- The canonical ESS; boundedness is explicit and applies to these filtrations. -/
@[no_expose] public noncomputable def sequence (f : FilteredMorphism F G)
    (hF : F.IsBounded) (hG : G.IsBounded) (k : ω) :
    SpectralSequence C (ℤ × ℤ) :=
  (underlyingComplex f.map f.compat k).toSpectralSequence
    (underlyingComplexBounded f.map f.compat k hF hG)

public theorem sequence_firstPage (f : FilteredMorphism F G)
    (hF : F.IsBounded) (hG : G.IsBounded) (k : ω) :
    (sequence f hF hG k).r₀ = 0 := by rfl

public theorem sequence_diffDeg (f : FilteredMorphism F G)
    (hF : F.IsBounded) (hG : G.IsBounded) (k : ω) (n : ℤ) :
    (sequence f hF hG k).diffDeg n = (n, -1) := by rfl

/-- Source ambient object is the associated grade of the same source filtration. -/
@[no_expose] public noncomputable def sourceIso (f : FilteredMorphism F G)
    (hF : F.IsBounded) (hG : G.IsBounded) (k : ω) (s : ℤ) :
    ((sequence f hF hG k).ssData (s, 1)).V ≅ F.associatedGraded s k :=
  Iso.refl _

/-- Target ambient object is the associated grade at the actual differential target. -/
@[no_expose] public noncomputable def targetIso (f : FilteredMorphism F G)
    (hF : F.IsBounded) (hG : G.IsBounded) (k : ω) (s n : ℤ) :
    ((sequence f hF hG k).ssData ((s, 1) + (sequence f hF hG k).diffDeg n)).V ≅
      G.associatedGraded (s + n) k :=
  Iso.refl _

theorem relation_iff_fiber (f : FilteredMorphism F G) (k : ω) (s n : ℤ)
    {T : C} (x : T ⟶ F.associatedGraded s k)
    (y : T ⟶ G.associatedGraded (s + n) k) :
    Relation f k s n x y ↔
      0 ≤ n ∧ Nonempty (FilteredComplex.Solutions.Fiber
        (underlyingComplex f.map f.compat k) n s 1 x y) := by
  constructor
  · rintro ⟨hn, a, b, ha, hb, he⟩
    refine ⟨hn, ⟨⟨(a, b), (FilteredComplex.Solutions.mem_fiber_iff _).mpr ?_⟩⟩⟩
    refine ⟨ha, hb, ?_⟩
    rw [underlyingComplex_d_one]
    exact he
  · rintro ⟨hn, ⟨⟨z, hz⟩⟩⟩
    obtain ⟨ha, hb, he⟩ := (FilteredComplex.Solutions.mem_fiber_iff z).mp hz
    refine ⟨hn, z.1, z.2, ?_⟩
    refine ⟨ha, hb, ?_⟩
    rw [underlyingComplex_d_one] at he
    exact he

set_option maxHeartbeats 2000000 in
/-- The actual ESS differential relation is precisely the original filtered-map
equation. Projectivity is retained when arbitrary morphism-valued labels are used. -/
public theorem differentialRelation_iff (f : FilteredMorphism F G)
    (hF : F.IsBounded) (hG : G.IsBounded) (k : ω) (s : ℤ) (n : ℕ)
    {T : C} [Projective T] (x : T ⟶ F.associatedGraded s k)
    (y : T ⟶ G.associatedGraded (s + (n : ℤ)) k) :
    DifferentialRelation (sequence f hF hG k) n (s, 1)
      (x ≫ (sourceIso f hF hG k s).inv)
      (y ≫ (targetIso f hF hG k s n).inv) ↔ Relation f k s n x y := by
  rw [relation_iff_fiber, and_iff_right (Int.natCast_nonneg n)]
  change DifferentialRelation
    ((underlyingComplex f.map f.compat k).toSpectralSequence
      (underlyingComplexBounded f.map f.compat k hF hG)) n (s, 1)
    (x ≫ 𝟙 (F.associatedGraded s k)) (y ≫ 𝟙 (G.associatedGraded (s + ↑n) k)) ↔ _
  rw [Category.comp_id, Category.comp_id]
  exact
    FilteredComplex.Solutions.differentialRelation_iff_nonempty_fiber
      (underlyingComplex f.map f.compat k)
      (underlyingComplexBounded f.map f.compat k hF hG) n s 1 x y

end KIP126.Core.SpectralSequence.FilteredMapExtension
