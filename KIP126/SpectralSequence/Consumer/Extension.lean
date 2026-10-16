module

public import KIP126.SpectralSequence.Convergence.Proofs
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic

@[expose] section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

/-! Extension equations for a specified filtered map. The solution relation and
its complete ambiguity are defined from that map, not supplied independently. -/

namespace KIP126.Core.SpectralSequence

open CategoryTheory CategoryTheory.Limits

universe u v w
variable {C : Type u} [Category.{v} C] [Abelian C]
  {ω : Type w} {A B : ω → C} {F : Filtration A} {G : Filtration B}

/-- The filtered map carried by this convergence morphism. -/
public def ConvergenceMorphism.filteredMap
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    {E E' : SpectralSequence C ι}
    {c : Convergence E A F} {c' : Convergence E' B G}
    (m : ConvergenceMorphism c c') : FilteredMorphism F G where
  map := m.aMap
  compat := m.filtration_compat

/-- Quotient projection commutes with the restriction of the same filtered map. -/
public theorem FilteredMorphism.quotient_naturality (f : FilteredMorphism F G)
    (s : ℤ) (k : ω) :
    F.toAssociatedGraded s k ≫ f.inducedGrMap s k =
      (f.compat s k).choose ≫ G.toAssociatedGraded s k := by
  simp only [Filtration.toAssociatedGraded, FilteredMorphism.inducedGrMap,
    Filtration.inducedAssocGradedMap, cokernel.map, cokernel.π_desc]

namespace FilteredMapExtension

/-- The actual representatives of an extension of nonnegative length. -/
public def Relation (f : FilteredMorphism F G) (k : ω) (s n : ℤ)
    {T : C} (x : T ⟶ F.associatedGraded s k)
    (y : T ⟶ G.associatedGraded (s + n) k) : Prop :=
  0 ≤ n ∧ ∃ (a : T ⟶ Subobject.underlying.obj (F.F s k))
    (b : T ⟶ Subobject.underlying.obj (G.F (s + n) k)),
    a ≫ F.toAssociatedGraded s k = x ∧
    b ≫ G.toAssociatedGraded (s + n) k = y ∧
    a ≫ (F.F s k).arrow ≫ f.map k = b ≫ (G.F (s + n) k).arrow

/-- Homogeneous target ambiguity of the same representative equation. -/
public def TargetIndeterminacy (f : FilteredMorphism F G) (k : ω) (s n : ℤ)
    (T : C) : Set (T ⟶ G.associatedGraded (s + n) k) :=
  {z | Relation f k s n (0 : T ⟶ F.associatedGraded s k) z}

/-- All targets differing from `y` by an actual homogeneous solution. -/
public def TargetCoset (f : FilteredMorphism F G) (k : ω) (s n : ℤ)
    {T : C} (y : T ⟶ G.associatedGraded (s + n) k) :
    Set (T ⟶ G.associatedGraded (s + n) k) :=
  {z | z - y ∈ TargetIndeterminacy f k s n T}

/-- Essentiality is nonvanishing modulo the complete target ambiguity. -/
public def Essential (f : FilteredMorphism F G) (k : ω) (s n : ℤ)
    {T : C} (x : T ⟶ F.associatedGraded s k)
    (y : T ⟶ G.associatedGraded (s + n) k) : Prop :=
  Relation f k s n x y ∧ 0 ∉ TargetCoset f k s n y

variable {f : FilteredMorphism F G} {k : ω} {s n : ℤ} {T : C}
  {x x' : T ⟶ F.associatedGraded s k}
  {y y' z : T ⟶ G.associatedGraded (s + n) k}

public theorem Relation.add (h : Relation f k s n x y)
    (h' : Relation f k s n x' y') : Relation f k s n (x + x') (y + y') := by
  obtain ⟨hn, a, b, ha, hb, he⟩ := h
  obtain ⟨_, a', b', ha', hb', he'⟩ := h'
  refine ⟨hn, a + a', b + b', ?_, ?_, ?_⟩
  · simp only [Preadditive.add_comp, ha, ha']
  · simp only [Preadditive.add_comp, hb, hb']
  · simp only [Preadditive.add_comp, he, he']

public theorem Relation.sub (h : Relation f k s n x y)
    (h' : Relation f k s n x' y') : Relation f k s n (x - x') (y - y') := by
  obtain ⟨hn, a, b, ha, hb, he⟩ := h
  obtain ⟨_, a', b', ha', hb', he'⟩ := h'
  refine ⟨hn, a - a', b - b', ?_, ?_, ?_⟩
  · simp only [Preadditive.sub_comp, ha, ha']
  · simp only [Preadditive.sub_comp, hb, hb']
  · simp only [Preadditive.sub_comp, he, he']

/-- Once a target is known, its coset consists exactly of all targets of the same source. -/
public theorem Relation.mem_targetCoset_iff (h : Relation f k s n x y) :
    z ∈ TargetCoset f k s n y ↔ Relation f k s n x z := by
  constructor
  · intro hz
    have hh : Relation f k s n 0 (z - y) := hz
    simpa only [zero_add, sub_add_cancel] using hh.add h
  · intro hz
    change Relation f k s n 0 (z - y)
    simpa only [sub_self] using hz.sub h

/-- A known extension is essential exactly when the same source has no zero target. -/
public theorem essential_iff (h : Relation f k s n x y) :
    Essential f k s n x y ↔ ¬ Relation f k s n x 0 := by
  simp only [Essential, h, true_and, h.mem_targetCoset_iff]

/-- The ambiguity consists exactly of images of higher-source-filtration
corrections, with their actual target lifts and quotient labels. -/
public theorem mem_indeterminacy_iff :
    z ∈ TargetIndeterminacy f k s n T ↔
      0 ≤ n ∧ ∃ (a : T ⟶ Subobject.underlying.obj (F.F (s + 1) k))
        (b : T ⟶ Subobject.underlying.obj (G.F (s + n) k)),
        b ≫ G.toAssociatedGraded (s + n) k = z ∧
        a ≫ (F.F (s + 1) k).arrow ≫ f.map k =
          b ≫ (G.F (s + n) k).arrow := by
  let i := Subobject.ofLE (F.F (s + 1) k) (F.F s k) (F.mono s k)
  constructor
  · rintro ⟨hn, a, b, ha, hb, he⟩
    have ha0 : a ≫ cokernel.π i = 0 := ha
    let a' := Abelian.monoLift i a ha0
    have ha' : a' ≫ i = a := Abelian.monoLift_comp i a ha0
    refine ⟨hn, a', b, hb, ?_⟩
    rw [← ha'] at he
    simpa only [Category.assoc, i, Subobject.ofLE_arrow_assoc] using he
  · rintro ⟨hn, a, b, hb, he⟩
    refine ⟨hn, a ≫ i, b, ?_, hb, ?_⟩
    · change (a ≫ i) ≫ cokernel.π i = 0
      rw [Category.assoc, cokernel.condition, comp_zero]
    · simpa only [Category.assoc, i, Subobject.ofLE_arrow_assoc] using he

theorem zero_lifts_iff (f : FilteredMorphism F G) (k : ω) (s t : ℤ) (h : t = s)
    {T : C} (x : T ⟶ F.associatedGraded s k)
    (y : T ⟶ G.associatedGraded t k) :
    (∃ (a : T ⟶ Subobject.underlying.obj (F.F s k))
      (b : T ⟶ Subobject.underlying.obj (G.F t k)),
      a ≫ F.toAssociatedGraded s k = x ∧ b ≫ G.toAssociatedGraded t k = y ∧
      a ≫ (F.F s k).arrow ≫ f.map k = b ≫ (G.F t k).arrow) ↔
      (∃ a : T ⟶ Subobject.underlying.obj (F.F s k),
        a ≫ F.toAssociatedGraded s k = x) ∧
      x ≫ f.inducedGrMap s k = y ≫ G.transportGraded (congrArg (fun q => (q, k)) h) := by
  subst t
  simp only [Filtration.transportGraded_self, Category.comp_id]
  constructor
  · rintro ⟨a, b, ha, hb, he⟩
    refine ⟨⟨a, ha⟩, ?_⟩
    have hab : a ≫ (f.compat s k).choose = b := by
      apply (cancel_mono (G.F s k).arrow).mp
      rw [Category.assoc, (f.compat s k).choose_spec]
      exact he
    rw [← ha, Category.assoc, f.quotient_naturality,
      ← Category.assoc, hab, hb]
  · rintro ⟨⟨a, ha⟩, h⟩
    refine ⟨a, a ≫ (f.compat s k).choose, ha, ?_, ?_⟩
    · rw [Category.assoc, ← f.quotient_naturality, ← Category.assoc, ha, h]
    · rw [Category.assoc, (f.compat s k).choose_spec]

/-- At length zero the representative equation is the induced graded map equation.
The source lifting condition is retained for arbitrary test objects. -/
public theorem relation_zero_iff (f : FilteredMorphism F G) (k : ω) (s : ℤ)
    {T : C} (x : T ⟶ F.associatedGraded s k)
    (y : T ⟶ G.associatedGraded (s + 0) k) :
    Relation f k s 0 x y ↔
      (∃ a : T ⟶ Subobject.underlying.obj (F.F s k),
        a ≫ F.toAssociatedGraded s k = x) ∧
      x ≫ f.inducedGrMap s k =
        y ≫ G.transportGraded (show (s + 0, k) = (s, k) by simp) := by
  unfold Relation
  rw [and_iff_right (show (0 : ℤ) ≤ 0 from le_rfl)]
  exact zero_lifts_iff f k s (s + 0) (add_zero s) x y

/-- Projective test objects supply the lifting needed for the zero-length formula. -/
public theorem relation_zero_iff_of_projective (f : FilteredMorphism F G)
    (k : ω) (s : ℤ) {T : C} [Projective T]
    (x : T ⟶ F.associatedGraded s k)
    (y : T ⟶ G.associatedGraded (s + 0) k) :
    Relation f k s 0 x y ↔
      x ≫ f.inducedGrMap s k = y ≫ G.transportGraded (show (s + 0, k) = (s, k) by simp) := by
  rw [relation_zero_iff]
  haveI : Epi (F.toAssociatedGraded s k) := inferInstanceAs (Epi (cokernel.π _))
  exact and_iff_right ⟨Projective.factorThru x (F.toAssociatedGraded s k),
    Projective.factorThru_comp x (F.toAssociatedGraded s k)⟩

end FilteredMapExtension
end KIP126.Core.SpectralSequence
