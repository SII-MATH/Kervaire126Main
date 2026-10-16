module

import KIP126.Literature

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.AdamsSynthetic
open KIP126.Kervaire.Route KIP126.Literature
open KIP126.AdamsSynthetic.Standard (Spectrum SyntheticSpectrum model)
open KIP126.Literature.Standard (lift nu_cofiber triangle_lift)
noncomputable section

/-- No selected-object witness or bound k≤1 is needed for the full lift. -/
example {X Y : Spectrum} (f : X ⟶ Y) (k : ℕ)
    (hf : MapFiltrationAtLeast model.classicalTower f k) :
    ∃ a : model.nu.functor.obj X ⟶
      (SyntheticCategory.biShift (0,-(k : ℤ))).obj (model.nu.functor.obj Y),
      a ≫ lambdaPow k (model.nu.functor.obj Y) = model.nu.functor.map f := by
  obtain ⟨F⟩ := lift f k hf
  exact ⟨F.map, F.factorization⟩

/-- The criterion recovers both endpoint conditions, not merely exactness
at the middle term of homology. -/
example (T : Triangle Spectrum) (hT : T ∈ distTriang Spectrum) (hν : NuImageIsCofiber model T) (n : ℤ) :
    Function.Injective (modTwoHomologyMap model.coefficients T.mor₁ n) ∧
    Function.Surjective (modTwoHomologyMap model.coefficients T.mor₂ n) := by
  have h := (nu_cofiber T hT).mp hν n
  exact ⟨h.1,h.2.2⟩

example (T : Triangle Spectrum) (hT : T ∈ distTriang Spectrum)
    (hH : HomologyShortExact model.coefficients T) :
    ∃ δ : model.nu.functor.obj T.obj₃ ⟶ (model.nu.functor.obj T.obj₁)⟦(1 : ℤ)⟧,
      Triangle.mk (model.nu.functor.map T.mor₁) (model.nu.functor.map T.mor₂) δ ∈ distTriang SyntheticSpectrum :=
  (nu_cofiber T hT).mpr hH

/-- The same lift supplies factorization, the triangle and comparison with
every full lift; the comparison conclusion is only λ torsion. -/
example (T : Triangle Spectrum) (hT : T ∈ distTriang Spectrum)
    (hfil : MapFiltrationAtLeast model.classicalTower T.mor₃ 1)
    (hH : HomologyShortExact model.coefficients T) :
    ∃ F : SyntheticTriangleLift model T,
      (Triangle.mk (model.nu.functor.map T.mor₁) (model.nu.functor.map T.mor₂)
        (F.connecting ≫ (model.nu.boundaryLandingIso T.obj₁).hom) ∈ distTriang SyntheticSpectrum) ∧
      (∀ (k : ℕ) (hk : 1 ≤ k) (G : SyntheticFullLift model T.mor₃ k),
        ∃ n : ℕ, lambdaPow n (model.nu.functor.obj T.obj₃) ≫
          (F.connecting-G.normalizedMap model hk) = 0) := by
  obtain ⟨F,hF⟩ := triangle_lift T hT hfil hH
  exact ⟨F,F.distinguished,hF⟩

example : NuExactTriangleInput model.coefficients model.nu :=
  nu_cofiber.toNuExactTriangleInput model

/-- Middle exactness alone is rejected by the corrected model input. -/
example (T : Triangle Spectrum) (_hT : T ∈ distTriang Spectrum)
    (_hmid : ∀ n, Function.Exact
      (modTwoHomologyMap model.coefficients T.mor₁ n)
      (modTwoHomologyMap model.coefficients T.mor₂ n)) : True := by
  fail_if_success
    have wrong := model.nuExactTriangle.preserves T _hT _hmid
  trivial
