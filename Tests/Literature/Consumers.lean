module

import KIP126.Def.Literature

/-! Ordinary public-import consumers of the same correlated input. -/
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.AdamsSynthetic
open KIP126.Core.SpectralSequence KIP126.Kervaire.Route KIP126.Literature
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w,v} Syn]
  [HasFunctorialCofiber (C := Syn)] (D : Model C Syn) (L : LiteratureInterface D)

example : sphereFirstQuotient D 1 64 (h6FirstQuotient D) = D.standardClasses.standardH6 :=
  h6FirstQuotient_label D

example : ∃ θ : BiHom 62 64 (S_0_0 : Syn), Theta5Detected D θ :=
  theta5_detected_exists D L.results.classical

example : L.bindings.theta5 + L.bindings.theta5 = 0 :=
  L.results.classical.theta5_order_two D

example (T : Theta5Transport D L.bindings.toClassicalBindings)
    (a b : BiHom 62 64 (S_0_0 : Syn)) (ha : Theta5Detected D a) (hb : Theta5Detected D b) :
    a+a=0 ∧ FiltrationAtLeast D.syntheticTower 6 (a-b) :=
  ⟨theta5_order_two D L.results.classical T a ha,
    theta5_indeterminacy_AF_ge_6 D L.results.classical T a b ha hb⟩

example : sphereFirstQuotient D 1 2 (quotientClass 1 L.bindings.eta) = D.standardClasses.standardHi 1 :=
  L.results.classical.eta_label

example (X : C) (n i : ℤ) (hX : IsConnected X n) (hi : i ≤ n) :
    Subsingleton (ModTwoHomology D.coefficients i X) :=
  L.results.foundation.connected_homology_vanishing X n hX i hi

example (i : ℤ) (hi : i ≤ -1) : Subsingleton (HomotopyGroup (C := C) i SphereSpectrum) :=
  L.results.foundation.sphere_connected i hi

example (n : ℤ) (X : C) :
    ModTwoCohomology D n X ≃+ (ModTwoHomology D.coefficients (-n) X →+ ZMod 2) :=
  L.results.foundation.universal_coefficient n X

example (T : TriangleData D.auxiliary) :
    (L.results.triangles.normalized_cofiber T).triangle D ∈ distTriang Syn :=
  (L.results.triangles.normalized_cofiber T).distinguished D

example (T : TriangleData D.auxiliary)
    (hsum : normalizedExponent D.classicalTower T.f + normalizedExponent D.classicalTower T.g +
      normalizedExponent D.classicalTower T.h = 1) :
    ∃ (f : D.nu.functor.obj (T.X.obj D.auxiliary) ⟶ D.nu.functor.obj (T.Y.obj D.auxiliary))
      (g : D.nu.functor.obj (T.Y.obj D.auxiliary) ⟶ D.nu.functor.obj (T.Z.obj D.auxiliary))
      (h : D.nu.functor.obj (T.Z.obj D.auxiliary) ⟶
        (shiftFunctor Syn (1 : ℤ)).obj (D.nu.functor.obj (T.X.obj D.auxiliary))),
      CategoryTheory.Pretriangulated.Triangle.mk f g h ∈ distTriang Syn :=
  L.results.triangles.unshifted T hsum

example (X : ClassicalObject) (N : ℤ)
    (hN : DegeneratesAt (D.classical.obj (X.obj D.auxiliary)) N) :
    DegeneratesAt (D.family.nu D.nu (X.obj D.auxiliary)).sequence N :=
  L.results.rigidity.degeneration X N hN

example (X : ClassicalObject) (r s t w : ℤ) (hr : 2 ≤ r) (hw : t < w) :
    IsZero ((D.family.nu D.nu (X.obj D.auxiliary)).Page r (s,t,w)) :=
  L.results.rigidity.above_diagonal X r hr s t w hw

example (X : ClassicalObject) (s t w : ℤ) (hw : w ≤ t)
    (x : (D.classical.obj (X.obj D.auxiliary)).Page 2 (s,t)) :
    comparisonPageMap D X (L.bindings.rigidity.inversion.data X) 2 s t w
      (nuWeightLabel D X s t w hw x) = x :=
  L.bindings.rigidity.inversion.e2 X s t w hw x

example (X : ClassicalObject) (r s t w : ℤ) (hr : 2 ≤ r) (hw : r-2 ≤ t-w)
    (x : (D.classical.obj (X.obj D.auxiliary)).Page r (s,t)) :
    syntheticDifferential D X r s t w
        (L.bindings.rigidity.free.classicalLift D X r hr s t w hw x) =
      L.bindings.rigidity.free.classicalLift D X r hr (s+r) (t+r-1) w (by omega)
        (classicalDifferential D X r s t x) :=
  L.bindings.rigidity.free.classicalLift_differential D X r hr s t w hw x

example (X : ClassicalObject) (n : ℕ) (hn : 0 < n) (r s t w : ℤ)
    (hr : 2 ≤ r) (hlo : 0 ≤ t-w) (hhi : t-w+r-2 < n) :
    IsIso ((D.family.quotientProjection (D.nu.functor.obj (X.obj D.auxiliary)) n).pageMap r (s,t,w)) :=
  (L.results.rigidity.finite_quotient X n hn).safe r s t w hr hlo hhi

example (X : ClassicalObject) (s t w₁ w₂ : ℤ) (h₁ : w₁ ≤ w₂) (h₂ : w₂ ≤ t) :
    Epi (L.bindings.rigidity.weights.map X s t w₁ w₂ h₁ h₂) :=
  L.weight_epi D X s t w₁ w₂ h₁ h₂

example (X : ClassicalObject) (q : ℕ) (hq : 0 < q) (p : ℤ × ℤ) (w : ℤ) :
    HEq (L.bindings.infinityShift.finiteLambdaMap D X q 0 hq p w)
      (𝟙 (((D.family.quotient (D.nu.functor.obj (X.obj D.auxiliary)) q).sequence.ssData (p.1,p.2,w)).eInfty)) :=
  L.bindings.infinityShift.finiteLambdaMap_zero D X q hq p w

example (X : ClassicalObject) (s t w₁ w₂ : ℤ) (h₁ : w₁ ≤ w₂) (h₂ : w₂ ≤ t)
    (x : ((D.family.nu D.nu (X.obj D.auxiliary)).sequence.ssData (s,t,w₁)).eInfty) : True := by
  fail_if_success
    have wrong := L.bindings.rigidity.weights.map X s t w₁ w₂ h₁ h₂ x
  trivial

/-- A different model does not satisfy this one's literature contract. -/
example (D' : Model C Syn) (L' : LiteratureInterface D') : True := by
  fail_if_success
    have wrong : LiteratureInterface D := L'
  trivial

/-- The repaired h₆ object cannot be used as a synthetic sphere lift. -/
example : True := by
  fail_if_success
    have wrong : BiHom 63 64 (S_0_0 : Syn) := h6FirstQuotient D
  trivial

/-- The selected ν triangle consumes all three fixed normalized maps. -/
example : normalizedTriangle D D.auxiliary.nuRouteTriangle
    (L.bindings.nuCofiber.exponent_sum D) ∈ distTriang Syn :=
  L.bindings.nuCofiber.distinguished D

example : sphereFirstQuotient D 1 4
    (quotientClass 1 (normalizedNu D L.bindings.nuCofiber.nu_exponent)) =
      D.standardClasses.standardHi 2 :=
  L.bindings.nuCofiber.normalized_label

/-- Selected-model transport is usable from L, without pretending that the
selected spectrum itself satisfies the source completion hypotheses. -/
example (X : ClassicalObject) (s t : ℤ)
    (x : (D.classical.obj (X.obj D.auxiliary)).Page 2 (s,t))
    (a : BiHom (t-s) t (nuZero D X))
    (hx : NonzeroSurvival (D.classical.obj (X.obj D.auxiliary)) (s,t) x)
    (ha : quotientClass 1 a = firstLabel D X s t x) :
    ClassicalDetects (D.classicalConvergence X) (s,t) x
      (realizeNuZero D L.bindings.realization X a) :=
  L.bindings.realizationTransport.detection X s t x a hx ha

example (X : ClassicalObject) (s t : ℤ)
    (x : (D.classical.obj (X.obj D.auxiliary)).Page 2 (s,t))
    (a : HomotopyGroup (t-s) (X.obj D.auxiliary))
    (hx : NonzeroSurvival (D.classical.obj (X.obj D.auxiliary)) (s,t) x)
    (ha : ClassicalDetects (D.classicalConvergence X) (s,t) x a) :
    ∃ b : BiHom (t-s) t (nuZero D X), quotientClass 1 b = firstLabel D X s t x ∧
      realizeNuZero D L.bindings.realization X b = a :=
  L.bindings.realizationTransport.prescribed_lift X s t x a hx ha

example (X : ClassicalObject) (s t : ℤ) (r : ℕ) (hr : 1 ≤ r)
    (x : (D.classical.obj (X.obj D.auxiliary)).Page 2 (s,t))
    (a : BiHom (t-s) t (nuZero D X))
    (hx : ClassicalPermanentCycle D X (s,t) x)
    (hs : SurvivesTo (D.classical.obj (X.obj D.auxiliary)) (r+1) (s,t) x)
    (ha : quotientClass 1 a = firstLabel D X s t x) : lambdaMultiply (r-1) a ≠ 0 :=
  L.bindings.realizationTransport.lifetime X s t r hr x a hx hs ha

example (X : ClassicalObject) (s t : ℤ) (r : ℕ) (hr : 2 ≤ r)
    (y : (D.classical.obj (X.obj D.auxiliary)).Page 2 (s,t))
    (hy : ClassicalPermanentCycle D X (s,t) y)
    (hit : HitOnPage (D.classical.obj (X.obj D.auxiliary)) r (s,t) y) :
    ∃ a : BiHom (t-s) t (nuZero D X), quotientClass 1 a = firstLabel D X s t y ∧
      lambdaMultiply (r-1) a = 0 :=
  L.bindings.realizationTransport.boundary_lift X s t r hr y hy hit
