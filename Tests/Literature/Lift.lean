module

import KIP126.Def.Literature

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.AdamsSynthetic
open KIP126.Kervaire.Route KIP126.Literature
universe u v w
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w,v} Syn]
  [HasFunctorialCofiber (C := Syn)] (D : Model C Syn) (L : LiteratureInterface D)

/-- No selected-object witness or bound k≤1 is needed for the full lift. -/
example {X Y : C} (f : X ⟶ Y) (k : ℕ)
    (hf : MapFiltrationAtLeast D.classicalTower f k) :
    ∃ a : D.nu.functor.obj X ⟶
      (SyntheticCategory.biShift (0,-(k : ℤ))).obj (D.nu.functor.obj Y),
      a ≫ lambdaPow k (D.nu.functor.obj Y) = D.nu.functor.map f := by
  obtain ⟨F⟩ := L.results.lifts.lift f k hf
  exact ⟨F.map, F.factorization⟩

/-- The criterion recovers both endpoint conditions, not merely exactness
at the middle term of homology. -/
example (T : Triangle C) (hT : T ∈ distTriang C) (hν : NuImageIsCofiber D T) (n : ℤ) :
    Function.Injective (modTwoHomologyMap D.coefficients T.mor₁ n) ∧
    Function.Surjective (modTwoHomologyMap D.coefficients T.mor₂ n) := by
  have h := (L.results.lifts.nu_cofiber T hT).mp hν n
  exact ⟨h.1,h.2.2⟩

example (T : Triangle C) (hT : T ∈ distTriang C)
    (hH : HomologyShortExact D.coefficients T) :
    ∃ δ : D.nu.functor.obj T.obj₃ ⟶ (D.nu.functor.obj T.obj₁)⟦(1 : ℤ)⟧,
      Triangle.mk (D.nu.functor.map T.mor₁) (D.nu.functor.map T.mor₂) δ ∈ distTriang Syn :=
  (L.results.lifts.nu_cofiber T hT).mpr hH

/-- The same lift supplies factorization, the triangle and comparison with
every full lift; the comparison conclusion is only λ torsion. -/
example (T : Triangle C) (hT : T ∈ distTriang C)
    (hfil : MapFiltrationAtLeast D.classicalTower T.mor₃ 1)
    (hH : HomologyShortExact D.coefficients T) :
    ∃ F : SyntheticTriangleLift D T,
      (Triangle.mk (D.nu.functor.map T.mor₁) (D.nu.functor.map T.mor₂)
        (F.connecting ≫ (D.nu.boundaryLandingIso T.obj₁).hom) ∈ distTriang Syn) ∧
      (∀ (k : ℕ) (hk : 1 ≤ k) (G : SyntheticFullLift D T.mor₃ k),
        ∃ n : ℕ, lambdaPow n (D.nu.functor.obj T.obj₃) ≫
          (F.connecting-G.normalizedMap D hk) = 0) := by
  obtain ⟨F,hF⟩ := L.results.lifts.triangle_lift T hT hfil hH
  exact ⟨F,F.distinguished,hF⟩

example : NuExactTriangleInput D.coefficients D.nu :=
  L.results.lifts.nu_cofiber.toNuExactTriangleInput D

/-- Middle exactness alone is rejected by the corrected model input. -/
example (T : Triangle C) (hT : T ∈ distTriang C)
    (hmid : ∀ n, Function.Exact
      (modTwoHomologyMap D.coefficients T.mor₁ n)
      (modTwoHomologyMap D.coefficients T.mor₂ n)) : True := by
  fail_if_success
    have wrong := D.nuExactTriangle.preserves T hT hmid
  trivial
