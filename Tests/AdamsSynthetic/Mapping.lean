module

import KIP126.Def.AdamsSynthetic

/-! Ordinary-import consumption of the mapping contracts. The tests use
arbitrary supplied systems and include an actual permanent-representative
product argument and rejection of unrelated family/convergence data. -/
open CategoryTheory CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.AdamsSynthetic
universe u v
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)] {H : C} {unit : SphereSpectrum ⟶ H}
  {A : ClassicalAdamsFamily C} {B : ClosedSymmetricTensorTriangulated C}
  {P : ClassicalTowerPresentation unit A} {scope : C → Prop}
  (S : MappingSpectrumSystem B P scope) (M : MappingComposition S)

example (X Y : C) (n : ℤ) (a : HomotopyGroup n (mappingSpectrum B X Y)) :
    (shiftFunctor C n).obj X ⟶ Y := mappingHomotopyEquiv B n X Y a

example : A.obj (mappingSpectrum B SphereSpectrum SphereSpectrum) ≅ A.sphere :=
  sphereMappingAdamsIso B A

example (X Y Z : MappingObject scope) (s t : ℤ) :
    (M.pairing X Y Z).ssPairing.parity (s,t) = ((t-s : ℤ) : ZMod 2) :=
  M.parity_apply X Y Z s t

example (X : MappingObject scope) :
    (M.identity X).abutment = (mappingHomotopyZeroEquiv B X.val X.val).symm (𝟙 X.val) := by
  apply (mappingHomotopyZeroEquiv B X.val X.val).injective
  rw [M.identity_actual, Equiv.apply_symm_apply]

-- A product with nonzero E∞ image survives using one common infinite cycle.
example (X Y Z : MappingObject scope) (i j : ℤ × ℤ)
    (x : InfiniteCycles (S.hom X Y).underlying.E i)
    (y : InfiniteCycles (S.hom Y Z).underlying.E j)
    (hnonzero : (M.pairing X Y Z).eInftyPair i j
      (((S.hom X Y).underlying.E.ssData i).pageπ ⊤ x)
      (((S.hom Y Z).underlying.E.ssData j).pageπ ⊤ y) ≠ 0) :
    NonzeroSurvival (S.hom X Z).underlying.E (i+j)
      ((M.pairing X Y Z).ssPairing.pair 2 i j
        (infinityToPage (S.hom X Y).underlying.E 2 i x)
        (infinityToPage (S.hom Y Z).underlying.E 2 j y)) := by
  refine ⟨(M.pairing X Y Z).cyclePairAtInfinity i j x y, ?_, ?_⟩
  · exact ((M.pairing X Y Z).finitePagePair_compatible 2 i j
      (by change (A.obj _).r₀ ≤ 2; rw [A.firstPage])
      (by change (A.obj _).r₀ ≤ 2; rw [A.firstPage])
      (by change (A.obj _).r₀ ≤ 2; rw [A.firstPage]) x y).symm
  · rw [(M.pairing X Y Z).eInftyPair_induced]
    exact hnonzero

example (X Y : MappingObject scope) (p : ℤ × ℤ)
    (x : ((S.hom X Y).underlying.E.ssData p).eInfty) :
    HEq ((M.pairing X X Y).eInftyPair (0,0) p (M.identity X).eInfty x) x :=
  M.eInfty_left_unital X Y p x

example (X Y : MappingObject scope) (p : ℤ × ℤ)
    (x : ((S.hom X Y).underlying.E.ssData p).eInfty) :
    HEq ((M.pairing X Y Y).eInftyPair p (0,0) x (M.identity Y).eInfty) x :=
  M.eInfty_right_unital X Y p x

example (X Y : MappingObject scope) (n : ℤ) (x : (S.hom X Y).underlying.A n) :
    HEq ((M.pairing X X Y).abutmentPair 0 n (M.identity X).abutment x) x :=
  M.abutment_left_unital X Y n x

example (X Y : MappingObject scope) (n : ℤ) (x : (S.hom X Y).underlying.A n) :
    HEq ((M.pairing X Y Y).abutmentPair n 0 x (M.identity Y).abutment) x :=
  M.abutment_right_unital X Y n x

example (W X Y Z : MappingObject scope) (i j k : ℤ × ℤ)
    (x : ((S.hom W X).underlying.E.ssData i).eInfty)
    (y : ((S.hom X Y).underlying.E.ssData j).eInfty)
    (z : ((S.hom Y Z).underlying.E.ssData k).eInfty) :
    HEq ((M.pairing W Y Z).eInftyPair (i+j) k ((M.pairing W X Y).eInftyPair i j x y) z)
      ((M.pairing W X Z).eInftyPair i (j+k) x ((M.pairing X Y Z).eInftyPair j k y z)) :=
  M.eInfty_associative W X Y Z i j k x y z

example (W X Y Z : MappingObject scope) (i j k : ℤ)
    (x : (S.hom W X).underlying.A i) (y : (S.hom X Y).underlying.A j)
    (z : (S.hom Y Z).underlying.A k) :
    HEq ((M.pairing W Y Z).abutmentPair (i+j) k ((M.pairing W X Y).abutmentPair i j x y) z)
      ((M.pairing W X Z).abutmentPair i (j+k) x ((M.pairing X Y Z).abutmentPair j k y z)) :=
  M.abutment_associative W X Y Z i j k x y z

example (X Y Z : MappingObject scope) (s t i j : ℤ)
    (x : FiltrationPiece (S.hom X Y).underlying.F s i)
    (y : FiltrationPiece (S.hom Y Z).underlying.F t j) :
    ∃ z : FiltrationPiece (S.hom X Z).underlying.F (s+t) (i+j),
      ((S.hom X Z).underlying.F.F (s+t) (i+j)).arrow z =
        (M.pairing X Y Z).abutmentPair i j
          (((S.hom X Y).underlying.F.F s i).arrow x)
          (((S.hom Y Z).underlying.F.F t j).arrow y) :=
  ⟨(M.pairing X Y Z).filteredAbutmentPair s t i j x y,
    (M.pairing X Y Z).filteredAbutmentPair_compatible s t i j x y⟩

example (E : MappingEnrichment M) (X Y : MappingObject scope) :
    E.enriched.Hom X Y = S.hom X Y := E.hom_eq X Y

-- Enriched composition acts on actual elementary page tensors by the given
-- multiplication, rather than by an arbitrary relabeling of pairing data.
example (E : MappingEnrichment M) (X Y Z : MappingObject scope) (r : ℤ) (i j : ℤ × ℤ)
    (x : (S.hom X Y).underlying.E.Page r i)
    (y : (S.hom Y Z).underlying.E.Page r j) :
    letI := E.monoidal
    let f : (S.hom X Y ⊗ S.hom Y Z) ⟶ S.hom X Z :=
      eqToHom (congrArg₂ (fun A B : ConvergingSequence.{0,v} ℤ => A ⊗ B)
        (E.hom_eq X Y).symm (E.hom_eq Y Z).symm) ≫ E.enriched.comp X Y Z ≫
          eqToHom (E.hom_eq X Z)
    f.sequence.pageMap r (i+j) ((E.tensorPairing X Y Z).ssPairing.pair r i j x y) =
      (M.pairing X Y Z).ssPairing.pair r i j x y :=
  E.composition_page X Y Z r i j x y

example (E : MappingEnrichment M) (X Y Z : MappingObject scope) (i j : ℤ × ℤ)
    (x : ((S.hom X Y).underlying.E.ssData i).eInfty)
    (y : ((S.hom Y Z).underlying.E.ssData j).eInfty) :
    letI := E.monoidal
    let f : (S.hom X Y ⊗ S.hom Y Z) ⟶ S.hom X Z :=
      eqToHom (congrArg₂ (fun A B : ConvergingSequence.{0,v} ℤ => A ⊗ B)
        (E.hom_eq X Y).symm (E.hom_eq Y Z).symm) ≫ E.enriched.comp X Y Z ≫
          eqToHom (E.hom_eq X Z)
    f.sequence.eInftyMap (i+j) ((E.tensorPairing X Y Z).eInftyPair i j x y) =
      (M.pairing X Y Z).eInftyPair i j x y :=
  E.composition_eInfty X Y Z i j x y

-- The enriched abutment composition is actual composition of shifted maps.
example (E : MappingEnrichment M) (X Y Z : MappingObject scope) (a b : ℤ)
    (x : (S.hom X Y).underlying.A a) (y : (S.hom Y Z).underlying.A b) :
    letI := E.monoidal
    let f : (S.hom X Y ⊗ S.hom Y Z) ⟶ S.hom X Z :=
      eqToHom (congrArg₂ (fun A B : ConvergingSequence.{0,v} ℤ => A ⊗ B)
        (E.hom_eq X Y).symm (E.hom_eq Y Z).symm) ≫ E.enriched.comp X Y Z ≫
          eqToHom (E.hom_eq X Z)
    mappingHomotopyEquiv B (a+b) X.val Z.val
      (f.convergence.aMap (a+b) ((E.tensorPairing X Y Z).abutmentPair a b x y)) =
      (shiftFunctorAdd C a b).hom.app X.val ≫
        (shiftFunctor C b).map (mappingHomotopyEquiv B a X.val Y.val x) ≫
        mappingHomotopyEquiv B b Y.val Z.val y := by
  letI := E.monoidal
  exact (congrArg (mappingHomotopyEquiv B (a+b) X.val Z.val)
    (E.composition_abutment X Y Z a b x y)).trans (M.abutment_compatible X Y Z a b x y)

example (algebra : SphereE2Algebra A) (hSphere : scope SphereSpectrum)
    (h : MappingSphereCompatibility M algebra hSphere) :
    (sphereMappingAdamsIso B A).hom.pageMap 2 (0,0)
      ((M.identity ⟨SphereSpectrum,hSphere⟩).page 2) = algebra.unit := h.unit

example (E : MappingEnrichment M) (X : MappingObject scope) :
    letI := E.monoidal
    let f : 𝟙_ (ConvergingSequence.{0,v} ℤ) ⟶ S.hom X X :=
      E.enriched.id X ≫ eqToHom (E.hom_eq X X)
    f.convergence.aMap 0 E.unit_data.abutment = (M.identity X).abutment :=
  E.identity_abutment X

example (A' : ClassicalAdamsFamily C)
    (P' : ClassicalTowerPresentation unit A') (_S' : MappingSpectrumSystem B P' scope)
    (X Y : MappingObject scope) (_x : (S.hom X Y).underlying.E.Page 2 (0,0)) : True := by
  fail_if_success have : (_S'.hom X Y).underlying.E.Page 2 (0,0) := _x
  trivial

example (_P' : ClassicalTowerPresentation unit A)
    (_c : ClassicalTowerConvergence P (mappingSpectrum B SphereSpectrum SphereSpectrum)) : True := by
  fail_if_success have : ClassicalTowerConvergence _P' (mappingSpectrum B SphereSpectrum SphereSpectrum) := _c
  trivial
