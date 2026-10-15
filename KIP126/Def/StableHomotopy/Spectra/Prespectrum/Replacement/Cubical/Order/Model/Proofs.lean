module

public import KIP126.Def.StableHomotopy.Spectra.Prespectrum.Replacement.Cubical.Order.Model.Data
public import KIP126.Def.StableHomotopy.Spectra.Realization.Proofs
public import KIP126.Def.StableHomotopy.Spectra.Singular.Homotopy.Approximation.Proofs
public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.Sigma.Attachment.Cubical.Sequence.Embedding.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Spectra.Prespectrum

open CategoryTheory CategoryTheory.Limits Simplicial Opposite
open KIP126.Topology.SimplicialRealization

universe u

set_option backward.isDefEq.respectTransparency false

/-- The specified global comparison retains every original stage comparison
and original replacement inclusion exactly. -/
theorem cubicalReplacementRealizedComparison_stage (X : Prespectrum.{u}) (n k : ℕ) :
    SSet.toTop.map (colimit.ι (cubicalReplacementSimplicialSequence X n) k) ≫
      cubicalReplacementRealizedComparison X n =
    (cubicalOrderSequenceComparison (cubicalReplacementLevelSequence X n)
      (cubicalReplacementLevelSequence_attachCells X n)
      (cubicalReplacementInitialOrderModel X n)).app k ≫
        (cubicalReplacementLevelCocone X n).ι.app k :=
  (isColimitOfPreserves SSet.toTop
    (colimit.isColimit (cubicalReplacementSimplicialSequence X n))).fac _ k

/-- The actual candidate is a based CW realization, independently of the
separate homotopy-equivalence proof for its original comparison. -/
theorem cubicalReplacementRealizedModel_isGood (X : Prespectrum.{u}) (n : ℕ) :
    (cubicalReplacementRealizedModel X n).IsGood :=
  basedRealization_isGood _ _

/-- The specified global comparison carries the retained initial vertex to
the specified original replacement point. -/
theorem cubicalReplacementRealizedComparison_point (X : Prespectrum.{u}) (n : ℕ) :
    cubicalReplacementRealizedComparison X n
      (cubicalReplacementRealizedModel X n).point =
        ((cubicalReplacementFunctor.obj X).level n).point := by
  let v : (cubicalReplacementSimplicialSequence X n).obj 0 |>.obj (op ⦋0⦌) :=
    (OrderHom.const (Fin 1)
      (⊤ : WithTop (orderProperChains (ULift.{u} (Fin 1))))).monotone.functor
  have hp := basedRealization_map_point
    (colimit.ι (cubicalReplacementSimplicialSequence X n) 0) v
  change SSet.toTop.map (colimit.ι (cubicalReplacementSimplicialSequence X n) 0)
    (basedRealization ((cubicalReplacementSimplicialSequence X n).obj 0) v).point =
      (cubicalReplacementRealizedModel X n).point at hp
  rw [← hp]
  have h := ConcreteCategory.congr_hom
    (cubicalReplacementRealizedComparison_stage X n 0)
    (basedRealization ((cubicalReplacementSimplicialSequence X n).obj 0) v).point
  apply h.trans
  have hzero :
      (cubicalOrderSequenceComparison (cubicalReplacementLevelSequence X n)
        (cubicalReplacementLevelSequence_attachCells X n)
        (cubicalReplacementInitialOrderModel X n)).app 0
          (basedRealization ((cubicalReplacementSimplicialSequence X n).obj 0) v).point =
          (zeroPrespectrum.{u}.level n).point := by
    exact @Subsingleton.elim PUnit _ _ _
  change (cubicalReplacementLevelCocone X n).ι.app 0
    ((cubicalOrderSequenceComparison (cubicalReplacementLevelSequence X n)
      (cubicalReplacementLevelSequence_attachCells X n)
      (cubicalReplacementInitialOrderModel X n)).app 0 _) = _
  rw [hzero]
  exact cubicalReplacementLevelCocone_inclusion_point X n 0

end KIP126.StableHomotopy.Spectra.Prespectrum
