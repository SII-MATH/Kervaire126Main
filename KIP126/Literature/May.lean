module

public import KIP126.AdamsSynthetic.Context

/-! May's signed pushpull consequence on the supplied tensor and suspension
conventions. Source: May (2001), TC3, pp. 12–13 and Lemma 4.6, p. 14;
fixed migration source bbac1fc05843bdf2d56057e6114a38839e939378,
`Def/Kervaire/Route/SourceLanguage.lean` and
`Interface/Solution/Literature/Route/May.lean`. -/

@[expose] section
namespace KIP126.StableHomotopy
open CategoryTheory CategoryTheory.Limits
universe u v
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
set_option backward.isDefEq.respectTransparency false

/-- Apply this exact functor with its specified suspension comparison. -/
public def HoCofiberSequence.map (T : HoCofiberSequence (C := C)) (F : C ⥤ C)
    [F.CommShift ℤ] [F.IsTriangulated] : HoCofiberSequence (C := C) where
  X := F.obj T.X
  Y := F.obj T.Y
  Z := F.obj T.Z
  f := F.map T.f
  g := F.map T.g
  h := F.map T.h ≫ (F.commShiftIso (1 : ℤ)).hom.app T.X
  distinguished := F.map_distinguished _ T.distinguished

/-- The actual boundary map, obtained by desuspending the triangle's last
map; its source and target are the represented homotopy groups. -/
public noncomputable def connectingHomomorphism
    (T : HoCofiberSequence (C := C)) (n : ℤ) :
    HomotopyGroup n T.Z →+ HomotopyGroup (n-1) T.X where
  toFun z := (shiftFunctorAdd' C n (-1) (n-1) (by omega)).hom.app SphereSpectrum ≫
    (shiftFunctor C (-1)).map (z ≫ T.h) ≫
    (shiftFunctorCompIsoId C 1 (-1) (by omega)).hom.app T.X
  map_zero' := by simp only [Functor.map_zero, zero_comp, comp_zero]
  map_add' := by
    intros
    simp only [Preadditive.add_comp, Functor.map_add, Preadditive.comp_add]

end KIP126.StableHomotopy

namespace KIP126.Literature.Route
open CategoryTheory CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy KIP126.Synthetic.Context
universe u v w
variable (Syn : Type u) [SyntheticCategory.{u,v} Syn]

/-- Exact tensor functors with fixed shift choices. Realizing TC3 for
these choices remains an applicability obligation of the source model. -/
public structure MayContext where
  leftShift : ∀ X : Syn, (tensorLeft X).CommShift ℤ
  rightShift : ∀ X : Syn, (tensorRight X).CommShift ℤ
  leftExact : ∀ X : Syn, letI := leftShift X; (tensorLeft X).IsTriangulated
  rightExact : ∀ X : Syn, letI := rightShift X; (tensorRight X).IsTriangulated

/-- The part of TC3 and its pushpull square used by the route. The two
boundaries have opposite signs in the same actual suspension target. -/
public structure MayPushpullData (B : MayContext Syn)
    (T U : HoCofiberSequence (C := Syn)) where
  vertex : Syn
  j1 : vertex ⟶ T.X ⊗ U.Z
  j2 : vertex ⟶ T.Y ⊗ U.Y
  j3 : vertex ⟶ T.Z ⊗ U.X
  square : j1 ≫ (T.f ▷ U.Z) = j2 ≫ (T.Y ◁ U.g)
  other_square : j2 ≫ (T.g ▷ U.Y) = j3 ≫ (T.Z ◁ U.f)
  boundary : letI := B.leftShift; letI := B.rightShift
    letI := B.leftExact; letI := B.rightExact
    j1 ≫ (U.map (tensorLeft T.X)).h = -(j3 ≫ (T.map (tensorRight U.X)).h)
  lift : ∀ (n : ℤ) (a : HomotopyGroup n (T.X ⊗ U.Z))
      (b : HomotopyGroup n (T.Y ⊗ U.Y)),
    a ≫ (T.f ▷ U.Z) = b ≫ (T.Y ◁ U.g) →
    ∃ v : HomotopyGroup n vertex, v ≫ j1 = a ∧ v ≫ j2 = b

/-- Source theorem input, not a construction of a TC3 model. -/
private def MaySourceResults (B : MayContext Syn) : Prop :=
  ∀ T U, Nonempty (MayPushpullData Syn B T U)

public def MayContext.SignedBoundary (B : MayContext Syn) : Prop :=
  letI := B.leftShift; letI := B.rightShift
  letI := B.leftExact; letI := B.rightExact
  ∀ (T U : HoCofiberSequence (C := Syn)) (n : ℤ)
    (a : HomotopyGroup n (T.X ⊗ U.Z)) (b : HomotopyGroup n (T.Y ⊗ U.Y)),
    inducedMap (T.f ▷ U.Z) n a = inducedMap (T.Y ◁ U.g) n b →
    ∃ c : HomotopyGroup n (T.Z ⊗ U.X),
      inducedMap (T.g ▷ U.Y) n b = inducedMap (T.Z ◁ U.f) n c ∧
      connectingHomomorphism (U.map (tensorLeft T.X)) n a =
        -(connectingHomomorphism (T.map (tensorRight U.X)) n c)

variable {Syn}
set_option backward.isDefEq.respectTransparency false in
/-- A common pushpull lift proves the signed formula. -/
private theorem may_signed_boundary_of_source (B : MayContext Syn)
    (hB : MaySourceResults Syn B) : B.SignedBoundary := by
  letI := B.leftShift
  letI := B.rightShift
  letI := B.leftExact
  letI := B.rightExact
  intro T U n a b hab
  rcases hB T U with ⟨P⟩
  rcases P.lift n a b hab with ⟨z, hza, hzb⟩
  refine ⟨z ≫ P.j3, ?_, ?_⟩
  · change b ≫ (T.g ▷ U.Y) = (z ≫ P.j3) ≫ (T.Z ◁ U.f)
    rw [← hzb, Category.assoc, P.other_square, Category.assoc]
  · have hs : a ≫ (U.map (tensorLeft T.X)).h =
        -((z ≫ P.j3) ≫ (T.map (tensorRight U.X)).h) := by
      rw [← hza, Category.assoc, P.boundary]
      simp only [Preadditive.comp_neg, Category.assoc]
    simp only [connectingHomomorphism, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      hs, Functor.map_neg, Preadditive.comp_neg, Preadditive.neg_comp]
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- Sign removal requires exponent two in the actual projected group.
Mod-two Adams coordinates alone do not imply this hypothesis. -/
private theorem may_boundary_projected_of_exponent_two (B : MayContext Syn)
    (hB : MaySourceResults Syn B) (T U : HoCofiberSequence (C := Syn))
    (n : ℤ) (a : HomotopyGroup n (T.X ⊗ U.Z))
    (b : HomotopyGroup n (T.Y ⊗ U.Y))
    (hab : inducedMap (T.f ▷ U.Z) n a = inducedMap (T.Y ◁ U.g) n b)
    {G : Type w} [AddCommGroup G]
    (q : HomotopyGroup (n-1) (T.X ⊗ U.X) →+ G)
    (htwo : ∀ x, q x + q x = 0) :
    letI := B.leftShift; letI := B.rightShift
    letI := B.leftExact; letI := B.rightExact
    ∃ c : HomotopyGroup n (T.Z ⊗ U.X),
      inducedMap (T.g ▷ U.Y) n b = inducedMap (T.Z ◁ U.f) n c ∧
      q (connectingHomomorphism (U.map (tensorLeft T.X)) n a) =
        q (connectingHomomorphism (T.map (tensorRight U.X)) n c) := by
  letI := B.leftShift
  letI := B.rightShift
  letI := B.leftExact
  letI := B.rightExact
  rcases may_signed_boundary_of_source B hB T U n a b hab with ⟨c, hc, hboundary⟩
  refine ⟨c, hc, ?_⟩
  rw [hboundary, map_neg]
  exact neg_eq_of_add_eq_zero_right (htwo _)

end KIP126.Literature.Route
