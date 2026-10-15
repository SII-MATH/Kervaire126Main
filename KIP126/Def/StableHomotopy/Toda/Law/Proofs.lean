module

public import KIP126.Def.StableHomotopy.Toda.Juggling.Proofs
public import KIP126.Def.StableHomotopy.Toda.Coset.Proofs

@[expose] public section

/-!
# Generic Toda naturality, suspension, and product containments

Every statement uses the existing cone-based `Relation`. No independent
bracket operation or graded sign is an input. The suspension comparison
and its sign are the ones in the specified shift structure. Products are
transport along an actual exact tensor functor; no exactness of an
arbitrary tensor structure is asserted.

The four-map shuffle is the existing `Toda.juggling`, including its
negative shifted first map. The containments here and that shuffle do
not assert equality of arbitrarily chosen representatives. In particular,
no specific Hopf relation, near-126 Toda value, vanishing of indeterminacy,
or Moss comparison is assumed here.
-/

namespace KIP126.StableHomotopy.Toda

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.MonoidalCategory

set_option backward.isDefEq.respectTransparency false
universe u v u' v'

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor C n)] [Pretriangulated C]

/-- Precomposition gives a containment, with the actual suspended map
on the Toda representative. -/
theorem precompose {A X Y Z W : C} {x : X⟦(1 : ℤ)⟧ ⟶ W}
    {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ W}
    (hx : Relation x f g h) (a : A ⟶ X) :
    Relation (a⟦(1 : ℤ)⟧' ≫ x) (a ≫ f) g h := by
  obtain ⟨Q, i, p, hT, gbar, hg, hx⟩ := hx
  obtain ⟨Q', i', p', hT'⟩ := distinguished_cocone_triangle (a ≫ f)
  obtain ⟨c, hi, hp⟩ := complete_distinguished_triangle_morphism
    (Triangle.mk (a ≫ f) i' p') (Triangle.mk f i p) hT' hT a (𝟙 Y) (by
      change (a ≫ f) ≫ 𝟙 Y = a ≫ f
      exact Category.comp_id _)
  dsimp only [Triangle.mk] at hi hp
  refine ⟨Q', i', p', hT', c ≫ gbar, ?_, ?_⟩
  · rw [← Category.assoc, hi]
    simpa using hg
  · rw [← Category.assoc, hp, Category.assoc, hx, Category.assoc]

/-- Postcomposition gives a containment for the actual target map. -/
theorem postcompose {X Y Z W V : C} {x : X⟦(1 : ℤ)⟧ ⟶ W}
    {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ W}
    (hx : Relation x f g h) (d : W ⟶ V) :
    Relation (x ≫ d) f g (h ≫ d) := by
  obtain ⟨Q, i, p, hT, gbar, hg, hx⟩ := hx
  refine ⟨Q, i, p, hT, gbar, hg, ?_⟩
  rw [← Category.assoc, hx, Category.assoc]

/-- Moving a factor from the first input into the middle input gives
this containment; its reverse is not asserted. -/
theorem absorb_first {X Y Z W V : C} {x : X⟦(1 : ℤ)⟧ ⟶ V}
    {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ W} {d : W ⟶ V}
    (hx : Relation x (f ≫ g) h d) :
    Relation x f (g ≫ h) d := by
  obtain ⟨Q, i, p, hT, hbar, hh, hx⟩ := hx
  obtain ⟨Q', i', p', hT'⟩ := distinguished_cocone_triangle f
  obtain ⟨c, hi, hp⟩ := complete_distinguished_triangle_morphism
    (Triangle.mk f i' p') (Triangle.mk (f ≫ g) i p) hT' hT (𝟙 X) g (by
      change f ≫ g = 𝟙 X ≫ (f ≫ g)
      exact (Category.id_comp _).symm)
  dsimp only [Triangle.mk] at hi hp
  have hp' : p' = c ≫ p := by simpa using hp
  refine ⟨Q', i', p', hT', c ≫ hbar, ?_, ?_⟩
  · rw [← Category.assoc, hi, Category.assoc, hh]
  · rw [hp', Category.assoc, hx, Category.assoc]

/-- Moving a factor from the last input into the middle input gives
this containment; its reverse is not asserted. -/
theorem absorb_last {X Y Z W V : C} {x : X⟦(1 : ℤ)⟧ ⟶ V}
    {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ W} {d : W ⟶ V}
    (hx : Relation x f g (h ≫ d)) :
    Relation x f (g ≫ h) d := by
  obtain ⟨Q, i, p, hT, gbar, hg, hx⟩ := hx
  refine ⟨Q, i, p, hT, gbar ≫ h, ?_, ?_⟩
  · rw [← Category.assoc, hg]
  · simpa only [Category.assoc] using hx

/-- The four-map shuffle identifies the two sets of products, with the
shifted negative sign. It does not equate arbitrary representatives of
the two Toda brackets. The octahedral hypothesis is the one required
by the underlying juggling law. -/
theorem shuffle_iff [IsTriangulated C] {X Y Z W V : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) (d : W ⟶ V)
    (hfg : f ≫ g = 0) (hgh : g ≫ h = 0) (hhd : h ≫ d = 0)
    (z : X⟦(1 : ℤ)⟧ ⟶ V) :
    (∃ x : X⟦(1 : ℤ)⟧ ⟶ W, Relation x f g h ∧ x ≫ d = z) ↔
      ∃ y : Y⟦(1 : ℤ)⟧ ⟶ V,
        Relation y g h d ∧ (-f⟦(1 : ℤ)⟧') ≫ y = z := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨y, hy, he⟩ := juggling hx hhd
    exact ⟨y, hy, he.symm⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨x₀, hx₀⟩ := exists_relation f g h hfg hgh
    obtain ⟨y₀, hy₀, hxy₀⟩ := juggling hx₀ hhd
    obtain ⟨u, v, huv⟩ := indeterminacy_complete hy hy₀
    refine ⟨x₀ + f⟦(1 : ℤ)⟧' ≫ (-v), indeterminacy_left hx₀ (-v), ?_⟩
    have hzero : f⟦(1 : ℤ)⟧' ≫ g⟦(1 : ℤ)⟧' = 0 := by
      rw [← Functor.map_comp, hfg, Functor.map_zero]
    have he := congrArg (fun k => f⟦(1 : ℤ)⟧' ≫ k) huv
    simp only [Preadditive.comp_sub, Preadditive.comp_add, ← Category.assoc,
      hzero, zero_comp, zero_add] at he
    simp only [Preadditive.add_comp, Preadditive.comp_neg, Preadditive.neg_comp]
    rw [hxy₀]
    simp only [Preadditive.neg_comp]
    rw [← he]
    abel

private theorem shifted_triangle_distinguished (n : ℤ) {X Y Q : C}
    (f : X ⟶ Y) (i : Y ⟶ Q) (p : Q ⟶ X⟦(1 : ℤ)⟧)
    (hT : Triangle.mk f i p ∈ distTriang C) :
    Triangle.mk (f⟦n⟧') (i⟦n⟧')
      (n.negOnePow • p⟦n⟧' ≫ (shiftFunctorComm C (1 : ℤ) n).hom.app X) ∈ distTriang C := by
  let e : Y⟦n⟧ ≅ Y⟦n⟧ :=
    { hom := n.negOnePow • 𝟙 _
      inv := n.negOnePow • 𝟙 _
      hom_inv_id := by simp [Linear.comp_units_smul, smul_smul]
      inv_hom_id := by simp [Linear.comp_units_smul, smul_smul] }
  apply isomorphic_distinguished _ (Triangle.shift_distinguished _ hT n)
  refine Triangle.isoMk _ _ (Iso.refl _) e (Iso.refl _) ?_ ?_ ?_
  · simp [Triangle.shiftFunctor, Triangle.mk, Category.id_comp, Category.comp_id, e, Linear.comp_units_smul]
  · simp [Triangle.shiftFunctor, Triangle.mk, Category.id_comp, Category.comp_id, e, Linear.units_smul_comp, Linear.comp_units_smul, smul_smul]
  · simp [Triangle.shiftFunctor, Triangle.mk]

omit [HasZeroObject C] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] in
private theorem shifted_connecting_comp (n : ℤ) {X Q W : C}
    (p : Q ⟶ X⟦(1 : ℤ)⟧) (x : X⟦(1 : ℤ)⟧ ⟶ W) :
    (n.negOnePow • p⟦n⟧' ≫ (shiftFunctorComm C (1 : ℤ) n).hom.app X) ≫
      (n.negOnePow • ((shiftFunctorComm C (1 : ℤ) n).inv.app X ≫ x⟦n⟧')) =
        (p ≫ x)⟦n⟧' := by
  simp only [Linear.units_smul_comp, Linear.comp_units_smul, smul_smul,
    Int.units_mul_self, one_smul, Category.assoc, Iso.hom_inv_id_app_assoc,
    Functor.map_comp]

/-- Suspension transports the entire Toda relation with its forced
`(-1)^n` sign and the actual comparison of the two iterated shifts. -/
theorem suspension_iff (n : ℤ) {X Y Z W : C}
    {x : X⟦(1 : ℤ)⟧ ⟶ W} {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ W} :
    Relation
      (n.negOnePow • ((shiftFunctorComm C (1 : ℤ) n).inv.app X ≫ x⟦n⟧'))
      (f⟦n⟧') (g⟦n⟧') (h⟦n⟧') ↔ Relation x f g h := by
  constructor
  · rintro ⟨Q', i', p', hT', gbar', hg', hx'⟩
    obtain ⟨Q, i, p, hT⟩ := distinguished_cocone_triangle f
    let δ := n.negOnePow • p⟦n⟧' ≫ (shiftFunctorComm C (1 : ℤ) n).hom.app X
    obtain ⟨c, hi, hp⟩ := complete_distinguished_triangle_morphism
      (Triangle.mk (f⟦n⟧') (i⟦n⟧') δ) (Triangle.mk (f⟦n⟧') i' p')
      (shifted_triangle_distinguished n f i p hT) hT' (𝟙 _) (𝟙 _) (by
        change f⟦n⟧' ≫ 𝟙 _ = 𝟙 _ ≫ f⟦n⟧'
        simp only [Category.comp_id, Category.id_comp])
    dsimp only [Triangle.mk] at hi hp
    have hi' : i⟦n⟧' ≫ c = i' := by simpa only [Category.id_comp] using hi
    have hp' : δ = c ≫ p' := by
      erw [(shiftFunctor C (1 : ℤ)).map_id, Category.comp_id] at hp
      exact hp
    let gbar := (shiftFunctor C n).preimage (c ≫ gbar')
    have hgbar : gbar⟦n⟧' = c ≫ gbar' := Functor.map_preimage _ _
    refine ⟨Q, i, p, hT, gbar, ?_, ?_⟩
    · apply (shiftFunctor C n).map_injective
      rw [Functor.map_comp, hgbar, ← Category.assoc, hi', hg']
    · apply (shiftFunctor C n).map_injective
      rw [← shifted_connecting_comp n p x]
      change δ ≫ _ = _
      rw [hp', Category.assoc, hx', Functor.map_comp, hgbar, Category.assoc]
  · rintro ⟨Q, i, p, hT, gbar, hg, hx⟩
    refine ⟨Q⟦n⟧, i⟦n⟧', n.negOnePow • p⟦n⟧' ≫
      (shiftFunctorComm C (1 : ℤ) n).hom.app X,
      shifted_triangle_distinguished n f i p hT, gbar⟦n⟧', ?_, ?_⟩
    · rw [← Functor.map_comp, hg]
    · rw [shifted_connecting_comp, hx, Functor.map_comp]

variable {D : Type u'} [Category.{v'} D] [Preadditive D]
  [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]

/-- An exact functor transports Toda representatives. The shift
comparison belongs to that same functor. General exact functors only
give this containment, not equality of Toda brackets. -/
theorem map (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
    {X Y Z W : C} {x : X⟦(1 : ℤ)⟧ ⟶ W}
    {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ W}
    (hx : Relation x f g h) :
    Relation ((F.commShiftIso (1 : ℤ)).inv.app X ≫ F.map x)
      (F.map f) (F.map g) (F.map h) := by
  obtain ⟨Q, i, p, hT, gbar, hg, hx⟩ := hx
  refine ⟨F.obj Q, F.map i, F.map p ≫ (F.commShiftIso (1 : ℤ)).hom.app X,
    F.map_distinguished (Triangle.mk f i p) hT, F.map gbar, ?_, ?_⟩
  · rw [← F.map_comp, hg]
  · simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
    rw [← F.map_comp, hx, F.map_comp]

variable [MonoidalCategory C]

/-- Tensoring on the right is a product containment when the actual
tensor functor, with its given shift comparison, is exact. -/
theorem tensor_right (V : C) [(tensorRight V).CommShift ℤ]
    [(tensorRight V).IsTriangulated]
    {X Y Z W : C} {x : X⟦(1 : ℤ)⟧ ⟶ W}
    {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ W}
    (hx : Relation x f g h) :
    Relation (((tensorRight V).commShiftIso (1 : ℤ)).inv.app X ≫ (x ▷ V))
      (f ▷ V) (g ▷ V) (h ▷ V) := by
  exact map (tensorRight V) hx

/-- Tensoring on the left is the corresponding product containment
with the actual left-tensor shift comparison. -/
theorem tensor_left (V : C) [(tensorLeft V).CommShift ℤ]
    [(tensorLeft V).IsTriangulated]
    {X Y Z W : C} {x : X⟦(1 : ℤ)⟧ ⟶ W}
    {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ W}
    (hx : Relation x f g h) :
    Relation (((tensorLeft V).commShiftIso (1 : ℤ)).inv.app X ≫ (V ◁ x))
      (V ◁ f) (V ◁ g) (V ◁ h) := by
  exact map (tensorLeft V) hx

end KIP126.StableHomotopy.Toda
