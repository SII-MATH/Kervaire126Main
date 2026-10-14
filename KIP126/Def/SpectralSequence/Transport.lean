module

public import KIP126.Def.SpectralSequence.Consumer.BoundedExtension

@[expose] section

/-! Transport for the actual filtered-map equation.  Associated graded maps,
complete target ambiguity, and essentiality are derived from levelwise
isomorphisms.  No boundedness is imposed on the representative equation. -/
namespace KIP126.Core.SpectralSequence
open CategoryTheory CategoryTheory.Limits
universe u v w w'
variable {C : Type u} [Category.{v} C] [Abelian C]
  {ω : Type w} {ω' : Type w'}
  {A B : ω → C} {A' B' : ω' → C}
  {F : Filtration A} {G : Filtration B}
  {F' : Filtration A'} {G' : Filtration B'}

/-- An isomorphism of two specified filtered pieces, retaining actual
representatives in their ambient objects. -/
public structure FilteredPieceIso (F : Filtration A) (F' : Filtration A')
    (k : ω) (k' : ω') where
  ambient : A k ≅ A' k'
  level : ∀ s, Subobject.underlying.obj (F.F s k) ≅
    Subobject.underlying.obj (F'.F s k')
  level_arrow : ∀ s, (level s).hom ≫ (F'.F s k').arrow =
    (F.F s k).arrow ≫ ambient.hom

namespace FilteredPieceIso
variable {k : ω} {k' : ω'}

public noncomputable def symm (e : FilteredPieceIso F F' k k') : FilteredPieceIso F' F k' k where
  ambient := e.ambient.symm
  level s := (e.level s).symm
  level_arrow s := by
    change (e.level s).inv ≫ (F.F s k).arrow =
      (F'.F s k').arrow ≫ e.ambient.inv
    apply (cancel_epi (e.level s).hom).mp
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    rw [e.level_arrow]
    simp

omit [Abelian C] in
/-- Inclusion maps commute because both composites are the same actual
subobject inclusion in the ambient object. -/
public theorem inclusion_comm (e : FilteredPieceIso F F' k k') (s : ℤ) :
    Subobject.ofLE _ _ (F.mono s k) ≫ (e.level s).hom =
      (e.level (s+1)).hom ≫ Subobject.ofLE _ _ (F'.mono s k') := by
  apply (cancel_mono (F'.F s k').arrow).mp
  simp only [Category.assoc, e.level_arrow, Subobject.ofLE_arrow_assoc,
    Subobject.ofLE_arrow]

public noncomputable def gradedIso (e : FilteredPieceIso F F' k k') (s : ℤ) :
    F.associatedGraded s k ≅ F'.associatedGraded s k' :=
  cokernel.mapIso (Subobject.ofLE _ _ (F.mono s k))
    (Subobject.ofLE _ _ (F'.mono s k')) (e.level (s+1)) (e.level s)
    (e.inclusion_comm s)

public theorem projection_comm (e : FilteredPieceIso F F' k k') (s : ℤ) :
    F.toAssociatedGraded s k ≫ (e.gradedIso s).hom =
      (e.level s).hom ≫ F'.toAssociatedGraded s k' := by
  dsimp only [gradedIso, Filtration.toAssociatedGraded, cokernel.mapIso]
  exact cokernel.π_desc _ _ _

public theorem projection_inv_comm (e : FilteredPieceIso F F' k k') (s : ℤ) :
    F'.toAssociatedGraded s k' ≫ (e.gradedIso s).inv =
      (e.level s).inv ≫ F.toAssociatedGraded s k := by
  apply (cancel_epi (e.level s).hom).mp
  rw [← Category.assoc, ← e.projection_comm]
  simp
end FilteredPieceIso

/-- A commuting square between the actual filtered maps, together with
isomorphisms on every source and target filtration level. -/
public structure FilteredMapTransport (f : FilteredMorphism F G)
    (f' : FilteredMorphism F' G') (k : ω) (k' : ω') where
  source : FilteredPieceIso F F' k k'
  target : FilteredPieceIso G G' k k'
  map_comm : source.ambient.hom ≫ f'.map k' = f.map k ≫ target.ambient.hom

namespace FilteredMapTransport
variable {f : FilteredMorphism F G} {f' : FilteredMorphism F' G'}
  {k : ω} {k' : ω'} (e : FilteredMapTransport f f' k k')
  {T : C} {s n : ℤ}

omit [Abelian C] in
/-- The chosen representatives transport along the actual level isomorphisms. -/
public theorem representative_equation_iff
    (a : T ⟶ Subobject.underlying.obj (F.F s k))
    (b : T ⟶ Subobject.underlying.obj (G.F (s+n) k)) :
    a ≫ (F.F s k).arrow ≫ f.map k = b ≫ (G.F (s+n) k).arrow ↔
      (a ≫ (e.source.level s).hom) ≫ (F'.F s k').arrow ≫ f'.map k' =
        (b ≫ (e.target.level (s+n)).hom) ≫ (G'.F (s+n) k').arrow := by
  have hsource := e.source.level_arrow s
  have htarget := e.target.level_arrow (s+n)
  simp only [Category.assoc]
  rw [← Category.assoc (e.source.level s).hom, hsource, Category.assoc, e.map_comm]
  rw [htarget]
  constructor
  · intro h
    simpa only [Category.assoc] using congrArg (fun z => z ≫ e.target.ambient.hom) h
  · intro h
    apply (cancel_mono e.target.ambient.hom).mp
    simpa only [Category.assoc] using h

public theorem relation_iff
    (x : T ⟶ F.associatedGraded s k)
    (y : T ⟶ G.associatedGraded (s+n) k) :
    FilteredMapExtension.Relation f k s n x y ↔
      FilteredMapExtension.Relation f' k' s n
        (x ≫ (e.source.gradedIso s).hom) (y ≫ (e.target.gradedIso (s+n)).hom) := by
  constructor
  · rintro ⟨hn, a, b, ha, hb, he⟩
    refine ⟨hn, a ≫ (e.source.level s).hom,
      b ≫ (e.target.level (s+n)).hom, ?_, ?_,
      (e.representative_equation_iff a b).mp he⟩
    · rw [Category.assoc, ← e.source.projection_comm, ← Category.assoc, ha]
    · rw [Category.assoc, ← e.target.projection_comm, ← Category.assoc, hb]
  · rintro ⟨hn, a, b, ha, hb, he⟩
    refine ⟨hn, a ≫ (e.source.level s).inv,
      b ≫ (e.target.level (s+n)).inv, ?_, ?_, ?_⟩
    · rw [Category.assoc, ← e.source.projection_inv_comm, ← Category.assoc, ha]
      simp
    · rw [Category.assoc, ← e.target.projection_inv_comm, ← Category.assoc, hb]
      simp
    · apply (e.representative_equation_iff _ _).mpr
      simpa using he

/-- Complete homogeneous ambiguity, rather than a selected correction subgroup. -/
public theorem indeterminacy_iff (z : T ⟶ G.associatedGraded (s+n) k) :
    z ∈ FilteredMapExtension.TargetIndeterminacy f k s n T ↔
      z ≫ (e.target.gradedIso (s+n)).hom ∈
        FilteredMapExtension.TargetIndeterminacy f' k' s n T := by
  simpa only [FilteredMapExtension.TargetIndeterminacy, Set.mem_setOf_eq,
    zero_comp] using e.relation_iff (0 : T ⟶ F.associatedGraded s k) z

public theorem targetCoset_iff (y z : T ⟶ G.associatedGraded (s+n) k) :
    z ∈ FilteredMapExtension.TargetCoset f k s n y ↔
      z ≫ (e.target.gradedIso (s+n)).hom ∈
        FilteredMapExtension.TargetCoset f' k' s n
          (y ≫ (e.target.gradedIso (s+n)).hom) := by
  simpa only [FilteredMapExtension.TargetCoset, Set.mem_setOf_eq,
    Preadditive.sub_comp] using e.indeterminacy_iff (z-y)

public theorem essential_iff (x : T ⟶ F.associatedGraded s k)
    (y : T ⟶ G.associatedGraded (s+n) k) :
    FilteredMapExtension.Essential f k s n x y ↔
      FilteredMapExtension.Essential f' k' s n
        (x ≫ (e.source.gradedIso s).hom) (y ≫ (e.target.gradedIso (s+n)).hom) := by
  unfold FilteredMapExtension.Essential
  rw [e.relation_iff]
  have h := e.targetCoset_iff y (0 : T ⟶ G.associatedGraded (s+n) k)
  simpa only [zero_comp] using and_congr_right (fun _ => not_congr h)

/-- An actual higher-source-filtration essential extension crossing the
selected target level. Nonnegative lengths and the same test object remain explicit. -/
public def NoCrossing (f : FilteredMorphism F G) (k : ω) (s n : ℤ) (T : C) : Prop :=
  ¬ ∃ (a m : ℤ), 0 < a ∧ 0 ≤ m ∧ a + m ≤ n ∧
    ∃ (x : T ⟶ F.associatedGraded (s+a) k)
      (y : T ⟶ G.associatedGraded ((s+a)+m) k),
      FilteredMapExtension.Essential f k (s+a) m x y

include e in
public theorem noCrossing_iff (s n : ℤ) (T : C) :
    NoCrossing f k s n T ↔ NoCrossing f' k' s n T := by
  apply not_congr
  constructor
  · rintro ⟨a, m, ha, hm, hmn, x, y, he⟩
    exact ⟨a, m, ha, hm, hmn, _, _, (e.essential_iff x y).mp he⟩
  · rintro ⟨a, m, ha, hm, hmn, x, y, he⟩
    refine ⟨a, m, ha, hm, hmn, x ≫ (e.source.gradedIso (s+a)).inv,
      y ≫ (e.target.gradedIso ((s+a)+m)).inv, ?_⟩
    apply (e.essential_iff _ _).mpr
    simpa using he

/-- ESS differential transport is available when both actual filtrations
are bounded and the test object is projective. General representative
transport above does not silently assert those hypotheses. -/
public theorem differentialRelation_iff
    (hF : F.IsBounded) (hG : G.IsBounded)
    (hF' : F'.IsBounded) (hG' : G'.IsBounded)
    (s : ℤ) (n : ℕ) [Projective T]
    (x : T ⟶ F.associatedGraded s k)
    (y : T ⟶ G.associatedGraded (s+(n:ℤ)) k) :
    DifferentialRelation (FilteredMapExtension.sequence f hF hG k) n (s,1)
      (x ≫ (FilteredMapExtension.sourceIso f hF hG k s).inv)
      (y ≫ (FilteredMapExtension.targetIso f hF hG k s n).inv) ↔
    DifferentialRelation (FilteredMapExtension.sequence f' hF' hG' k') n (s,1)
      (x ≫ (e.source.gradedIso s).hom ≫
        (FilteredMapExtension.sourceIso f' hF' hG' k' s).inv)
      (y ≫ (e.target.gradedIso (s+(n:ℤ))).hom ≫
        (FilteredMapExtension.targetIso f' hF' hG' k' s n).inv) := by
  rw [FilteredMapExtension.differentialRelation_iff]
  rw [← Category.assoc x, ← Category.assoc y,
    FilteredMapExtension.differentialRelation_iff]
  exact e.relation_iff x y

end FilteredMapTransport
end KIP126.Core.SpectralSequence
