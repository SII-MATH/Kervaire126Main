module

public import KIP126.Def.SpectralSequence.Multiplicative
public import KIP126.Def.SpectralSequence.Basic.Category.Proofs

@[expose] section

/-! Converging spectral sequences with their full finite-page morphisms.
The older convergence-only category forgets finite pages; it cannot serve as
the ambient category for an enrichment which represents all-page pairings. -/
namespace KIP126.Core.SpectralSequence
open CategoryTheory
universe u v
variable {R : Type u} [CommRing R]
noncomputable section

/-- A wrapper selecting the full, rather than convergence-only, morphisms. -/
public structure ConvergingSequence (R : Type u) [CommRing R] where
  underlying : ConvergingSS (ModuleCat.{v} R) (ℤ × ℤ) ℤ

/-- A finite-page morphism and a filtered target map, with the same E∞ map. -/
public structure ConvergingSequenceMorphism (X Y : ConvergingSequence.{u,v} R) where
  sequence : X.underlying.E ⟶ Y.underlying.E
  convergence : ConvergenceMorphism X.underlying.conv Y.underlying.conv
  eInfty_compatible : ∀ p, convergence.eMap p = sequence.eInftyMap p

namespace ConvergingSequenceMorphism
variable {X Y Z : ConvergingSequence.{u,v} R}

@[ext] public theorem ext {f g : ConvergingSequenceMorphism X Y}
    (hs : f.sequence = g.sequence) (hc : f.convergence = g.convergence) : f = g := by
  cases f
  cases g
  cases hs
  cases hc
  rfl

public def id (X : ConvergingSequence.{u,v} R) : ConvergingSequenceMorphism X X where
  sequence := 𝟙 _
  convergence := (𝟙 X.underlying : X.underlying ⟶ X.underlying)
  eInfty_compatible p := (SpectralSequenceMorphism.eInftyMap_id X.underlying.E p).symm

public def comp (f : ConvergingSequenceMorphism X Y) (g : ConvergingSequenceMorphism Y Z) :
    ConvergingSequenceMorphism X Z where
  sequence := f.sequence ≫ g.sequence
  convergence := @CategoryStruct.comp (ConvergingSS (ModuleCat.{v} R) (ℤ × ℤ) ℤ)
    _ X.underlying Y.underlying Z.underlying f.convergence g.convergence
  eInfty_compatible p := by
    change f.convergence.eMap p ≫ g.convergence.eMap p =
      (f.sequence ≫ g.sequence).eInftyMap p
    rw [f.eInfty_compatible, g.eInfty_compatible, SpectralSequenceMorphism.eInftyMap_comp]
end ConvergingSequenceMorphism

public instance : Category (ConvergingSequence.{u,v} R) where
  Hom := ConvergingSequenceMorphism
  id := ConvergingSequenceMorphism.id
  comp := ConvergingSequenceMorphism.comp
  id_comp _f := ConvergingSequenceMorphism.ext (Category.id_comp _) (Category.id_comp _)
  comp_id _f := ConvergingSequenceMorphism.ext (Category.comp_id _) (Category.comp_id _)
  assoc {W X Y Z} f g h := ConvergingSequenceMorphism.ext
    (Category.assoc f.sequence g.sequence h.sequence)
    (@Category.assoc (ConvergingSS (ModuleCat.{v} R) (ℤ × ℤ) ℤ)
      _ W.underlying X.underlying Y.underlying Z.underlying
      f.convergence g.convergence h.convergence)

end
end KIP126.Core.SpectralSequence
