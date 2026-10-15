module

public import KIP126.Def.StableHomotopy.Spectra.Prespectrum.Replacement.Cubical.Order.Initial
public import KIP126.Def.StableHomotopy.Spectra.Prespectrum.Replacement.Cubical.Order.Sequence
public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.Sigma.Attachment.Cubical.Sequence.Data
public import KIP126.Def.StableHomotopy.Spectra.Realization.Data

@[expose] public section

namespace KIP126.StableHomotopy.Spectra.Prespectrum

open CategoryTheory CategoryTheory.Limits Simplicial Opposite
open KIP126.Topology.SimplicialRealization

universe u

set_option backward.isDefEq.respectTransparency false

/-- The initial model uses the original one-point replacement stage,
with the actual cone vertex representing its basepoint. -/
noncomputable def cubicalReplacementInitialOrderModel (X : Prespectrum.{u}) (n : ℕ) :
    OrderRealizationModel ((cubicalReplacementLevelSequence X n).obj 0) where
  order := PartOrd.of (WithTop (orderProperChains (ULift.{u} (Fin 1))))
  equivalence := (zeroPrespectrumLevelOrderHomeomorph.{u} n).toHomotopyEquiv

/-- The actual simplicial sequence obtained from the compatible order
models of the original replacement level. -/
noncomputable def cubicalReplacementSimplicialSequence (X : Prespectrum.{u}) (n : ℕ) :
    ℕ ⥤ SSet.{u} :=
  cubicalOrderSequence (cubicalReplacementLevelSequence X n)
    (cubicalReplacementLevelSequence_attachCells X n)
    (cubicalReplacementInitialOrderModel X n) ⋙ PartOrd.nerveFunctor

/-- The actual simplicial colimit of those stage models. -/
noncomputable def cubicalReplacementSimplicialModel (X : Prespectrum.{u}) (n : ℕ) : SSet.{u} :=
  colimit (cubicalReplacementSimplicialSequence X n)

/-- Retain the actual initial cone vertex in the simplicial colimit. -/
noncomputable def cubicalReplacementModelVertex (X : Prespectrum.{u}) (n : ℕ) :
    (cubicalReplacementSimplicialModel X n).obj (op ⦋0⦌) :=
  (colimit.ι (cubicalReplacementSimplicialSequence X n) 0).app (op ⦋0⦌)
    (OrderHom.const (Fin 1)
      (⊤ : WithTop (orderProperChains (ULift.{u} (Fin 1))))).monotone.functor

/-- An actual based CW candidate for the original replacement level,
with its specified original-stage vertex; comparison is proved separately. -/
noncomputable def cubicalReplacementRealizedModel (X : Prespectrum.{u}) (n : ℕ) :
    BasedSpace.{u} :=
  basedRealization (cubicalReplacementSimplicialModel X n) (cubicalReplacementModelVertex X n)

/-- The original stage comparisons induce a specified actual map from
the realization of the simplicial colimit to the original replacement level. -/
noncomputable def cubicalReplacementRealizedComparison (X : Prespectrum.{u}) (n : ℕ) :
    (cubicalReplacementRealizedModel X n).space ⟶
      ((cubicalReplacementFunctor.obj X).level n).space :=
  (isColimitOfPreserves SSet.toTop
    (colimit.isColimit (cubicalReplacementSimplicialSequence X n))).desc
      ((Cocone.precompose
        (cubicalOrderSequenceComparison (cubicalReplacementLevelSequence X n)
          (cubicalReplacementLevelSequence_attachCells X n)
          (cubicalReplacementInitialOrderModel X n))).obj
            (cubicalReplacementLevelCocone X n))

end KIP126.StableHomotopy.Spectra.Prespectrum
