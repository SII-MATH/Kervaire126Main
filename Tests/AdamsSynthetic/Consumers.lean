module

import KIP126.Def.AdamsSynthetic

/-! Ordinary-import consumers of the fixed project background.
Only actual objects, maps, classes and mathematical hypotheses are parameters. -/
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.Classical.Adams KIP126.Synthetic.SpectralSequence
open KIP126.Core.SpectralSequence KIP126.AdamsSynthetic KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
example (X : Spectrum) : classical.map (𝟙 X) = 𝟙 (classical.obj X) := classical.map_id X

example {X Y Z : Spectrum} (f : X ⟶ Y) (g : Y ⟶ Z) :
    classical.map (f ≫ g) = classical.map f ≫ classical.map g := classical.map_comp f g

-- Naturality is for the actual induced page maps and differentials.
example {X Y : Spectrum} (f : X ⟶ Y) (r : ℤ) (p : Bidegree) :
    classical.pageMap f r p ≫ (classical.obj Y).d r p =
      (classical.obj X).d r p ≫ classical.pageMap f r (p + (classical.obj X).diffDeg r) ≫
        eqToHom (by rw [(classical.map f).diffDeg_eq]) :=
  (classical.map f).pageMap_comm_d r p

example {X Y : Spectrum} (f : X ⟶ Y) (r : ℤ) (p : Bidegree)
    (x : (classical.obj X).Page 2 p) (y : (classical.obj X).Page r p)
    (h : RepresentsOnPage (classical.obj X) r p x y) :
    RepresentsOnPage (classical.obj Y) r p (classical.pageMap f 2 p x) (classical.pageMap f r p y) :=
  (classical.map f).representsOnPage h

example {X Y : Spectrum} (f : X ⟶ Y) (r : ℤ) (p q : Bidegree)
    (x : (classical.obj X).Page 2 p) (y : (classical.obj X).Page 2 q)
    (h : HasDifferential (classical.obj X) r p q x y) :
    HasDifferential (classical.obj Y) r p q (classical.pageMap f 2 p x) (classical.pageMap f 2 q y) :=
  (classical.map f).hasDifferential h


example : classical.sphere.Page 2 (2, 128) := standardClasses.standardH6Square

example : standardClasses.standardH6Square = sphereAlgebra.product (1, 64) (1, 64) standardClasses.standardH6 standardClasses.standardH6 :=
  standardClasses.standardH6Square_eq_product

-- The final target is obtained only from the explicit finite-page and tail
-- hypotheses. In particular, E₂ nonvanishing alone is not substituted here.
example (N : ℤ) (hN : 2 ≤ N)
    (hfinite : SurvivesTo classical.sphere N (2, 128) standardClasses.standardH6Square)
    (hout : ∀ r : ℤ, N ≤ r → classical.sphere.d r (2, 128) = 0)
    (hin : ∀ r : ℤ, N ≤ r → classical.sphere.d r ((2, 128) - classical.sphere.diffDeg r) = 0) :
    NonzeroSurvival classical.sphere (2, 128) standardClasses.standardH6Square := by
  have hstart : classical.sphere.r₀ = 2 := classical.firstPage SphereSpectrum
  exact nonzeroSurvival_of_survivesTo classical.sphere N (by rw [hstart]; exact hN)
    (2, 128) standardClasses.standardH6Square hfinite hout hin

example (X : SyntheticSpectrum) : family.map (𝟙 X) = 𝟙 (family.obj X).sequence := family.map_id X

example {X Y Z : SyntheticSpectrum} (f : X ⟶ Y) (g : Y ⟶ Z) :
    family.map (f ≫ g) = family.map f ≫ family.map g := family.map_comp f g

example {X Y : SyntheticSpectrum} (f : X ⟶ Y) (r : ℤ) (i : Tridegree) :
    family.pageMap f r i ≫ (family.obj Y).sequence.d r i =
      (family.obj X).sequence.d r i ≫
        family.pageMap f r (i + (family.obj X).sequence.diffDeg r) ≫
          eqToHom (by rw [(family.map f).diffDeg_eq]) :=
  (family.map f).pageMap_comm_d r i

example : (family.nu nu SphereSpectrum).sequence ≅ family.sphere.sequence := family.nuSphereIso nu

example (X : SyntheticSpectrum) (n : ℕ) :
    (family.obj X).sequence ⟶ (family.obj (XModLambdaN X n)).sequence :=
  family.quotientProjection X n

example : family.sphere.E₂ (2, 128, 128) :=
  comparison.sphereE2 2 128 0 standardClasses.standardH6Square

example (X Y : ClassicalObject)
    (f : X.obj auxiliary ⟶ Y.obj auxiliary) (a s t : ℤ) (k : ℕ)
    (x : (classical.obj (X.obj auxiliary)).Page 2 (s, t)) :
    family.pageMap ((SyntheticCategory.biShift (0, a)).map (nu.functor.map f))
        2 (s, t, t+a-k) (comparison.nuE2 X a s t k x) =
      comparison.nuE2 Y a s t k (classical.pageMap f 2 (s, t) x) :=
  comparison.nu_natural X Y f a s t k x


end
