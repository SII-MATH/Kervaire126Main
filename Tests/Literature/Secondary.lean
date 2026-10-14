module

import KIP126.Def.Literature

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.AdamsSynthetic
open KIP126.Classical.Adams KIP126.Kervaire.Route KIP126.Literature
universe u v w
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w,v} Syn]
  [HasFunctorialCofiber (C := Syn)]

section Delivery
variable (D : Model C Syn) (L : LiteratureInterface D)

example : Route.MayContext.SignedBoundary Syn L.bindings.secondary.may :=
  Route.may_signed_boundary_of_source _ L.results.secondary.may

example : lambdaMultiply 1 L.bindings.secondary.toda.h0 = Route.syntheticTwo :=
  L.results.secondary.toda.lambda_h0

example : sphereProduct L.bindings.secondary.toda.h0 L.bindings.eta = 0 :=
  L.results.secondary.toda.h0_eta

example : MappingSphereCompatibility L.bindings.secondary.moss.composition
    D.sphereAlgebra rfl := L.bindings.secondary.sphereComposition
end Delivery

section Moss
open KIP126.Literature.Moss
variable {H : C} {unit : SphereSpectrum ⟶ H} {A : ClassicalAdamsFamily C}
  {B : ClosedSymmetricTensorTriangulated C} {P : ClassicalTowerPresentation unit A}
  {scope : C → Prop} (S : MappingSpectrumSystem B P scope) (Q : Context S)

/-- The complete defining-system coset is accessible from the public contract. -/
example (r : ℤ) (hr : 3 ≤ r) (W X Y Z : MappingObject scope) (i j k : ℤ × ℤ)
    (a : (sequence S W X).Page r i) (b : (sequence S X Y).Page r j)
    (c : (sequence S Y Z).Page r k)
    (x₀ x : (sequence S W Z).Page r (PageMassey.degree r i j k))
    (hx₀ : PageMassey.Relation S Q.composition r hr x₀ a b c) :
    PageMassey.Relation S Q.composition r hr x a b c ↔
      PageMassey.Indeterminacy S Q.composition r (j := j) a c (x-x₀) :=
  Q.indeterminacy r hr W X Y Z i j k a b c x₀ x hx₀

/-- Both actual product-tower weak-convergence premises and both crossing
conditions remain present when the source theorem is consumed. -/
example (source : SourceResults S Q) (W X Y Z : MappingObject scope)
    (r : ℤ) (hr : 3 ≤ r) (i j k : ℤ × ℤ)
    (hWY : WeakConvergence (P := P) (B := B) W Y)
    (hXZ : WeakConvergence (P := P) (B := B) X Z)
    (a : (sequence S W X).Page r i) (b : (sequence S X Y).Page r j)
    (c : (sequence S Y Z).Page r k)
    (α : abutment (B := B) W X (stem i)) (β : abutment (B := B) X Y (stem j))
    (γ : abutment (B := B) Y Z (stem k))
    (ha : DetectsAbutment S W X r i a α) (hb : DetectsAbutment S X Y r j b β)
    (hc : DetectsAbutment S Y Z r k c γ)
    (hab : (Q.composition.pairing W X Y).ssPairing.pair r i j a b = 0)
    (hbc : (Q.composition.pairing X Y Z).ssPairing.pair r j k b c = 0)
    (hfg : shiftMap W X i (stem j+stem k) α ≫ shiftMap X Y j (stem k) β = 0)
    (hgh : shiftMap X Y j (stem k) β ≫ abutmentMap Y Z k γ = 0)
    (hcross : NoMossCrossingForProducts S W X Y Z r i j k) :
    ∃ (x : (sequence S W Z).Page r (PageMassey.degree r i j k))
      (ξ : abutment (B := B) W Z (stem (PageMassey.degree r i j k))),
      PageMassey.Relation S Q.composition r hr x a b c ∧
      PermanentCycle S W Z r (PageMassey.degree r i j k) x ∧
      DetectsAbutment S W Z r (PageMassey.degree r i j k) x ξ ∧
      KIP126.StableHomotopy.Toda.Relation (todaMap r W Z i j k ξ)
        (shiftMap W X i (stem j+stem k) α) (shiftMap X Y j (stem k) β)
        (abutmentMap Y Z k γ) :=
  source.at S W X Y Z r hr i j k hWY hXZ a b c α β γ ha hb hc hab hbc hfg hgh hcross
end Moss

section May
variable (B : Route.MayContext Syn) (source : Route.MaySourceResults Syn B)

example (T U : HoCofiberSequence (C := Syn)) (n : ℤ)
    (a : HomotopyGroup n (T.X ⊗ U.Z)) (b : HomotopyGroup n (T.Y ⊗ U.Y))
    (hab : inducedMap (T.f ▷ U.Z) n a = inducedMap (T.Y ◁ U.g) n b) :
    letI := B.leftShift; letI := B.rightShift
    letI := B.leftExact; letI := B.rightExact
    ∃ c : HomotopyGroup n (T.Z ⊗ U.X),
      inducedMap (T.g ▷ U.Y) n b = inducedMap (T.Z ◁ U.f) n c ∧
      connectingHomomorphism (U.map (tensorLeft T.X)) n a =
        -(connectingHomomorphism (T.map (tensorRight U.X)) n c) :=
  Route.may_signed_boundary_of_source B source T U n a b hab
end May

section Toda
example {X Y Z W : C} {x₀ x : X⟦(1 : ℤ)⟧ ⟶ W}
    {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ W} (hx₀ : Toda.Relation x₀ f g h) :
    Toda.Relation x f g h ↔ ∃ (y : Y⟦(1 : ℤ)⟧ ⟶ W) (z : X⟦(1 : ℤ)⟧ ⟶ Z),
      x-x₀ = f⟦(1 : ℤ)⟧' ≫ y + z ≫ h := Toda.relation_iff_indeterminacy hx₀

#check_failure KIP126.StableHomotopy.Toda.indeterminacy_left
#check_failure KIP126.StableHomotopy.Toda.indeterminacy_right
#check_failure KIP126.StableHomotopy.Toda.indeterminacy_complete
#check_failure KIP126.StableHomotopy.Toda.shifted_triangle_distinguished
end Toda
