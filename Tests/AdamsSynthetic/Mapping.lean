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
example (X Y : Spectrum) (n : ℤ) (a : HomotopyGroup n (mappingSpectrum closedBackground X Y)) :
    (shiftFunctor Spectrum n).obj X ⟶ Y := mappingHomotopyEquiv closedBackground n X Y a

example : classical.obj (mappingSpectrum closedBackground SphereSpectrum SphereSpectrum) ≅ classical.sphere :=
  sphereMappingAdamsIso closedBackground classical

example (X Y Z : MappingObject (IsFiniteSpectrum (C := Spectrum))) (s t : ℤ) :
    (mappingComposition.pairing X Y Z).ssPairing.parity (s,t) = ((t-s : ℤ) : ZMod 2) :=
  mappingComposition.parity_apply X Y Z s t

example (X : MappingObject (IsFiniteSpectrum (C := Spectrum))) :
    (mappingComposition.identity X).abutment = (mappingHomotopyZeroEquiv closedBackground X.val X.val).symm (𝟙 X.val) := by
  apply (mappingHomotopyZeroEquiv closedBackground X.val X.val).injective
  rw [mappingComposition.identity_actual, Equiv.apply_symm_apply]

-- classical product with nonzero mappingEnrichment∞ image survives using one common infinite cycle.
example (X Y Z : MappingObject (IsFiniteSpectrum (C := Spectrum))) (i j : ℤ × ℤ)
    (x : InfiniteCycles (mappingSystem.hom X Y).underlying.E i)
    (y : InfiniteCycles (mappingSystem.hom Y Z).underlying.E j)
    (hnonzero : (mappingComposition.pairing X Y Z).eInftyPair i j
      (((mappingSystem.hom X Y).underlying.E.ssData i).pageπ ⊤ x)
      (((mappingSystem.hom Y Z).underlying.E.ssData j).pageπ ⊤ y) ≠ 0) :
    NonzeroSurvival (mappingSystem.hom X Z).underlying.E (i+j)
      ((mappingComposition.pairing X Y Z).ssPairing.pair 2 i j
        (infinityToPage (mappingSystem.hom X Y).underlying.E 2 i x)
        (infinityToPage (mappingSystem.hom Y Z).underlying.E 2 j y)) := by
  refine ⟨(mappingComposition.pairing X Y Z).cyclePairAtInfinity i j x y, ?_, ?_⟩
  · exact ((mappingComposition.pairing X Y Z).finitePagePair_compatible 2 i j
      (by change (classical.obj _).r₀ ≤ 2; rw [classical.firstPage])
      (by change (classical.obj _).r₀ ≤ 2; rw [classical.firstPage])
      (by change (classical.obj _).r₀ ≤ 2; rw [classical.firstPage]) x y).symm
  · rw [(mappingComposition.pairing X Y Z).eInftyPair_induced]
    exact hnonzero

example (X Y : MappingObject (IsFiniteSpectrum (C := Spectrum))) (p : ℤ × ℤ)
    (x : ((mappingSystem.hom X Y).underlying.E.ssData p).eInfty) :
    HEq ((mappingComposition.pairing X X Y).eInftyPair (0,0) p (mappingComposition.identity X).eInfty x) x :=
  mappingComposition.eInfty_left_unital X Y p x

example (X Y : MappingObject (IsFiniteSpectrum (C := Spectrum))) (p : ℤ × ℤ)
    (x : ((mappingSystem.hom X Y).underlying.E.ssData p).eInfty) :
    HEq ((mappingComposition.pairing X Y Y).eInftyPair p (0,0) x (mappingComposition.identity Y).eInfty) x :=
  mappingComposition.eInfty_right_unital X Y p x

example (X Y : MappingObject (IsFiniteSpectrum (C := Spectrum))) (n : ℤ) (x : (mappingSystem.hom X Y).underlying.A n) :
    HEq ((mappingComposition.pairing X X Y).abutmentPair 0 n (mappingComposition.identity X).abutment x) x :=
  mappingComposition.abutment_left_unital X Y n x

example (X Y : MappingObject (IsFiniteSpectrum (C := Spectrum))) (n : ℤ) (x : (mappingSystem.hom X Y).underlying.A n) :
    HEq ((mappingComposition.pairing X Y Y).abutmentPair n 0 x (mappingComposition.identity Y).abutment) x :=
  mappingComposition.abutment_right_unital X Y n x

example (W X Y Z : MappingObject (IsFiniteSpectrum (C := Spectrum))) (i j k : ℤ × ℤ)
    (x : ((mappingSystem.hom W X).underlying.E.ssData i).eInfty)
    (y : ((mappingSystem.hom X Y).underlying.E.ssData j).eInfty)
    (z : ((mappingSystem.hom Y Z).underlying.E.ssData k).eInfty) :
    HEq ((mappingComposition.pairing W Y Z).eInftyPair (i+j) k ((mappingComposition.pairing W X Y).eInftyPair i j x y) z)
      ((mappingComposition.pairing W X Z).eInftyPair i (j+k) x ((mappingComposition.pairing X Y Z).eInftyPair j k y z)) :=
  mappingComposition.eInfty_associative W X Y Z i j k x y z

example (W X Y Z : MappingObject (IsFiniteSpectrum (C := Spectrum))) (i j k : ℤ)
    (x : (mappingSystem.hom W X).underlying.A i) (y : (mappingSystem.hom X Y).underlying.A j)
    (z : (mappingSystem.hom Y Z).underlying.A k) :
    HEq ((mappingComposition.pairing W Y Z).abutmentPair (i+j) k ((mappingComposition.pairing W X Y).abutmentPair i j x y) z)
      ((mappingComposition.pairing W X Z).abutmentPair i (j+k) x ((mappingComposition.pairing X Y Z).abutmentPair j k y z)) :=
  mappingComposition.abutment_associative W X Y Z i j k x y z

example (X Y Z : MappingObject (IsFiniteSpectrum (C := Spectrum))) (s t i j : ℤ)
    (x : FiltrationPiece (mappingSystem.hom X Y).underlying.F s i)
    (y : FiltrationPiece (mappingSystem.hom Y Z).underlying.F t j) :
    ∃ z : FiltrationPiece (mappingSystem.hom X Z).underlying.F (s+t) (i+j),
      ((mappingSystem.hom X Z).underlying.F.F (s+t) (i+j)).arrow z =
        (mappingComposition.pairing X Y Z).abutmentPair i j
          (((mappingSystem.hom X Y).underlying.F.F s i).arrow x)
          (((mappingSystem.hom Y Z).underlying.F.F t j).arrow y) :=
  ⟨(mappingComposition.pairing X Y Z).filteredAbutmentPair s t i j x y,
    (mappingComposition.pairing X Y Z).filteredAbutmentPair_compatible s t i j x y⟩

example (X Y : MappingObject (IsFiniteSpectrum (C := Spectrum))) :
    mappingEnrichment.enriched.Hom X Y = mappingSystem.hom X Y := mappingEnrichment.hom_eq X Y

-- Enriched composition acts on actual elementary page tensors by the given
-- multiplication, rather than by an arbitrary relabeling of pairing data.
example (X Y Z : MappingObject (IsFiniteSpectrum (C := Spectrum))) (r : ℤ) (i j : ℤ × ℤ)
    (x : (mappingSystem.hom X Y).underlying.E.Page r i)
    (y : (mappingSystem.hom Y Z).underlying.E.Page r j) :
    letI := mappingEnrichment.monoidal
    let f : (mappingSystem.hom X Y ⊗ mappingSystem.hom Y Z) ⟶ mappingSystem.hom X Z :=
      eqToHom (congrArg₂ (fun classical closedBackground : ConvergingSequence.{0,0} ℤ => classical ⊗ closedBackground)
        (mappingEnrichment.hom_eq X Y).symm (mappingEnrichment.hom_eq Y Z).symm) ≫ mappingEnrichment.enriched.comp X Y Z ≫
          eqToHom (mappingEnrichment.hom_eq X Z)
    f.sequence.pageMap r (i+j) ((mappingEnrichment.tensorPairing X Y Z).ssPairing.pair r i j x y) =
      (mappingComposition.pairing X Y Z).ssPairing.pair r i j x y :=
  mappingEnrichment.composition_page X Y Z r i j x y

example (X Y Z : MappingObject (IsFiniteSpectrum (C := Spectrum))) (i j : ℤ × ℤ)
    (x : ((mappingSystem.hom X Y).underlying.E.ssData i).eInfty)
    (y : ((mappingSystem.hom Y Z).underlying.E.ssData j).eInfty) :
    letI := mappingEnrichment.monoidal
    let f : (mappingSystem.hom X Y ⊗ mappingSystem.hom Y Z) ⟶ mappingSystem.hom X Z :=
      eqToHom (congrArg₂ (fun classical closedBackground : ConvergingSequence.{0,0} ℤ => classical ⊗ closedBackground)
        (mappingEnrichment.hom_eq X Y).symm (mappingEnrichment.hom_eq Y Z).symm) ≫ mappingEnrichment.enriched.comp X Y Z ≫
          eqToHom (mappingEnrichment.hom_eq X Z)
    f.sequence.eInftyMap (i+j) ((mappingEnrichment.tensorPairing X Y Z).eInftyPair i j x y) =
      (mappingComposition.pairing X Y Z).eInftyPair i j x y :=
  mappingEnrichment.composition_eInfty X Y Z i j x y

-- The enriched abutment composition is actual composition of shifted maps.
example (X Y Z : MappingObject (IsFiniteSpectrum (C := Spectrum))) (a b : ℤ)
    (x : (mappingSystem.hom X Y).underlying.A a) (y : (mappingSystem.hom Y Z).underlying.A b) :
    letI := mappingEnrichment.monoidal
    let f : (mappingSystem.hom X Y ⊗ mappingSystem.hom Y Z) ⟶ mappingSystem.hom X Z :=
      eqToHom (congrArg₂ (fun classical closedBackground : ConvergingSequence.{0,0} ℤ => classical ⊗ closedBackground)
        (mappingEnrichment.hom_eq X Y).symm (mappingEnrichment.hom_eq Y Z).symm) ≫ mappingEnrichment.enriched.comp X Y Z ≫
          eqToHom (mappingEnrichment.hom_eq X Z)
    mappingHomotopyEquiv closedBackground (a+b) X.val Z.val
      (f.convergence.aMap (a+b) ((mappingEnrichment.tensorPairing X Y Z).abutmentPair a b x y)) =
      (shiftFunctorAdd Spectrum a b).hom.app X.val ≫
        (shiftFunctor Spectrum b).map (mappingHomotopyEquiv closedBackground a X.val Y.val x) ≫
        mappingHomotopyEquiv closedBackground b Y.val Z.val y := by
  letI := mappingEnrichment.monoidal
  exact (congrArg (mappingHomotopyEquiv closedBackground (a+b) X.val Z.val)
    (mappingEnrichment.composition_abutment X Y Z a b x y)).trans (mappingComposition.abutment_compatible X Y Z a b x y)


example (X : MappingObject (IsFiniteSpectrum (C := Spectrum))) :
    letI := mappingEnrichment.monoidal
    let f : 𝟙_ (ConvergingSequence.{0,0} ℤ) ⟶ mappingSystem.hom X X :=
      mappingEnrichment.enriched.id X ≫ eqToHom (mappingEnrichment.hom_eq X X)
    f.convergence.aMap 0 mappingEnrichment.unit_data.abutment = (mappingComposition.identity X).abutment :=
  mappingEnrichment.identity_abutment X


end
