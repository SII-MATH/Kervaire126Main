module

import KIP126.Def.AdamsSynthetic


/-! Consumer checks use only ordinary imports and supplied interface values.
The examples never construct a global Adams system or assume the final target. -/

open CategoryTheory KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.Classical.Adams KIP126.Synthetic.SpectralSequence
open KIP126.Core.SpectralSequence KIP126.AdamsSynthetic KIP126.Kervaire.Route

universe u v w
noncomputable section

section Classical
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  (A : ClassicalAdamsFamily C)

example (X : C) : A.map (𝟙 X) = 𝟙 (A.obj X) := A.map_id X

example {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    A.map (f ≫ g) = A.map f ≫ A.map g := A.map_comp f g

-- Naturality is for the actual induced page maps and differentials.
example {X Y : C} (f : X ⟶ Y) (r : ℤ) (p : Bidegree) :
    A.pageMap f r p ≫ (A.obj Y).d r p =
      (A.obj X).d r p ≫ A.pageMap f r (p + (A.obj X).diffDeg r) ≫
        eqToHom (by rw [(A.map f).diffDeg_eq]) :=
  (A.map f).pageMap_comm_d r p

example {X Y : C} (f : X ⟶ Y) (r : ℤ) (p : Bidegree)
    (x : (A.obj X).Page 2 p) (y : (A.obj X).Page r p)
    (h : RepresentsOnPage (A.obj X) r p x y) :
    RepresentsOnPage (A.obj Y) r p (A.pageMap f 2 p x) (A.pageMap f r p y) :=
  (A.map f).representsOnPage h

example {X Y : C} (f : X ⟶ Y) (r : ℤ) (p q : Bidegree)
    (x : (A.obj X).Page 2 p) (y : (A.obj X).Page 2 q)
    (h : HasDifferential (A.obj X) r p q x y) :
    HasDifferential (A.obj Y) r p q (A.pageMap f 2 p x) (A.pageMap f 2 q y) :=
  (A.map f).hasDifferential h

example [HasFunctorialCofiber (C := C)] (aux : AuxiliaryData C) :
    A.obj (ClassicalObject.sphere.obj aux) = A.sphere := rfl

variable (P : SphereE2Algebra A) (H : StandardSphereClasses A P)

example : A.sphere.Page 2 (2, 128) := H.standardH6Square

example : H.standardH6Square = P.product (1, 64) (1, 64) H.standardH6 H.standardH6 :=
  H.standardH6Square_eq_product

-- The final target is obtained only from the explicit finite-page and tail
-- hypotheses. In particular, E₂ nonvanishing alone is not substituted here.
example (N : ℤ) (hN : 2 ≤ N)
    (hfinite : SurvivesTo A.sphere N (2, 128) H.standardH6Square)
    (hout : ∀ r : ℤ, N ≤ r → A.sphere.d r (2, 128) = 0)
    (hin : ∀ r : ℤ, N ≤ r → A.sphere.d r ((2, 128) - A.sphere.diffDeg r) = 0) :
    NonzeroSurvival A.sphere (2, 128) H.standardH6Square := by
  have hstart : A.sphere.r₀ = 2 := A.firstPage SphereSpectrum
  exact nonzeroSurvival_of_survivesTo A.sphere N (by rw [hstart]; exact hN)
    (2, 128) H.standardH6Square hfinite hout hin

-- Every name below is also used successfully above. These failures concern
-- different dependent inputs, rather than an absent declaration.
#check_failure (fun (A B : ClassicalAdamsFamily C) (x : A.sphere.Page 2 (2, 128)) =>
  (x : B.sphere.Page 2 (2, 128)))

#check_failure (fun (A : ClassicalAdamsFamily C) (P Q : SphereE2Algebra A)
    (H : StandardSphereClasses A P) => (H : StandardSphereClasses A Q))
end Classical

section Synthetic
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  (A : ClassicalAdamsFamily C) (F : SyntheticAdamsFamily Syn)
  (N : NuFunctorData C Syn) (aux : AuxiliaryData C)

example (X : Syn) : F.map (𝟙 X) = 𝟙 (F.obj X).sequence := F.map_id X

example {X Y Z : Syn} (f : X ⟶ Y) (g : Y ⟶ Z) :
    F.map (f ≫ g) = F.map f ≫ F.map g := F.map_comp f g

example {X Y : Syn} (f : X ⟶ Y) (r : ℤ) (i : Tridegree) :
    F.pageMap f r i ≫ (F.obj Y).sequence.d r i =
      (F.obj X).sequence.d r i ≫
        F.pageMap f r (i + (F.obj X).sequence.diffDeg r) ≫
          eqToHom (by rw [(F.map f).diffDeg_eq]) :=
  (F.map f).pageMap_comm_d r i

example : (F.nu N SphereSpectrum).sequence ≅ F.sphere.sequence := F.nuSphereIso N

example (X : Syn) (n : ℕ) :
    (F.obj X).sequence ⟶ (F.obj (XModLambdaN X n)).sequence :=
  F.quotientProjection X n

example (K : E2Comparison A F N aux) (P : SphereE2Algebra A)
    (H : StandardSphereClasses A P) : F.sphere.E₂ (2, 128, 128) :=
  K.sphereE2 2 128 0 H.standardH6Square

example (K : E2Comparison A F N aux) (X Y : ClassicalObject)
    (f : X.obj aux ⟶ Y.obj aux) (a s t : ℤ) (k : ℕ)
    (x : (A.obj (X.obj aux)).Page 2 (s, t)) :
    F.pageMap ((SyntheticCategory.biShift (0, a)).map (N.functor.map f))
        2 (s, t, t+a-k) (K.nuE2 X a s t k x) =
      K.nuE2 Y a s t k (A.pageMap f 2 (s, t) x) :=
  K.nu_natural X Y f a s t k x

#check_failure (fun (A B : ClassicalAdamsFamily C) (F : SyntheticAdamsFamily Syn)
    (N : NuFunctorData C Syn) (aux : AuxiliaryData C) (K : E2Comparison A F N aux) =>
  (K : E2Comparison B F N aux))
end Synthetic

section ActualMap
variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]

example (F : SyntheticAdamsFamily Syn) {X Y : Syn} (g : X ⟶ Y)
    {FX : Filtration (syntheticHomotopy X)} {FY : Filtration (syntheticHomotopy Y)}
    (cx : Convergence (F.obj X).sequence (syntheticHomotopy X) FX)
    (cy : Convergence (F.obj Y).sequence (syntheticHomotopy Y) FY)
    (M : ConvergentMap F g cx cy) (p : ℤ × ℤ) :
    M.filteredMap.map p = syntheticHomotopyMap g p := M.filteredMap_map p

#check_failure (fun (F : SyntheticAdamsFamily Syn) (X Y : Syn) (g h : X ⟶ Y)
    (FX : Filtration (syntheticHomotopy X)) (FY : Filtration (syntheticHomotopy Y))
    (cx : Convergence (F.obj X).sequence (syntheticHomotopy X) FX)
    (cy : Convergence (F.obj Y).sequence (syntheticHomotopy Y) FY)
    (M : ConvergentMap F g cx cy) => (M : ConvergentMap F h cx cy))
end ActualMap

end
