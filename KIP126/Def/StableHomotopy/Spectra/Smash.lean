module

public import KIP126.Def.StableHomotopy.Spectra.Prespectrum.Smash.Good.Predicates
public import KIP126.Def.StableHomotopy.Spectra.Prespectrum
public import Mathlib.AlgebraicTopology.SimplicialSet.Subdivision
public import Mathlib.Data.Finset.Max
public import Mathlib.AlgebraicTopology.TopologicalSimplex
public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
public import KIP126.Def.Topology.SimplicialRealization.Equalizer.Proofs
public import KIP126.Def.Topology.SimplicialRealization.Boundary.Proofs
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Order.Hom.WithTopBot
public import Mathlib.Data.Fintype.WithTopBot
public import Mathlib.Data.Finset.Sort
public import KIP126.Def.Topology.Simplex.MonotoneCoupling.Representation.Proofs
public import Mathlib.Data.Fin.Rev
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Order.Hom.Set
public import Mathlib.Order.NonemptyFiniteChains
public import Mathlib.Order.Preorder.Finite
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.Topology.Homotopy.Basic
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Algebra.Order.Archimedean.Basic
public import KIP126.Def.Topology.SimplicialRealization.Relative.Proofs
public import Mathlib.Topology.Homotopy.Contractible
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Finite.Sum
public import Mathlib.Order.WithBot
public import KIP126.Def.Topology.Simplex.ClosedBall.Proofs
public import KIP126.Def.Topology.HomotopyLifting.Data
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.CategoryTheory.Comma.Arrow
public import KIP126.Def.StableHomotopy.Spectra.Generators
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.WithTerminal.Cone
public import Mathlib.CategoryTheory.Limits.Shapes.Equivalence
public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.Topology.Path
public import Mathlib.CategoryTheory.SmallObject.Construction
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.LiftingProperties.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.AlgebraicTopology.RelativeCellComplex.AttachCells
public import Mathlib.Topology.Category.TopCat.Limits.Products
public import KIP126.Def.Topology.HomotopyLifting.Proofs
public import KIP126.Def.Topology.HomotopyGroup.ContinuousMap.Data
public import Mathlib.Topology.Piecewise
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.Topology.ContinuousMap.Basic
public import KIP126.Def.Topology.Pushout.Proofs
public import KIP126.Def.StableHomotopy.Spectra.Prespectrum.Proofs
public import Mathlib.CategoryTheory.Types.Basic
public import KIP126.Def.Topology.CWComplex.FiniteSupport.Proofs
public import KIP126.Def.StableHomotopy.Spectra.PointSet
public import Mathlib.Topology.Compactification.OnePoint.Basic
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Algebra.Colimit.DirectLimit
public import Mathlib.Algebra.Group.TransferInstance
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Adjunction.Limits
public import KIP126.Def.Topology.SequentialColimit.Proofs
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.CategoryTheory.Filtered.Connected
public import KIP126.Def.Topology.Pushout.Cells.Proofs
public import KIP126.Def.Topology.HomotopyExtension.Proofs
public import KIP126.Def.Topology.Ball.HomotopyExtension.Proofs
public import Mathlib.Topology.FiberBundle.Trivialization
public import Mathlib.Topology.Homotopy.Equiv
public import Mathlib.Data.Sigma.Order
public import KIP126.Def.Topology.SimplicialRealization.CompactlyGenerated.Proofs
public import KIP126.Def.Topology.SimplicialRealization.Classical.Charts.Proofs
public import KIP126.Def.Topology.SimplicialRealization.Equalizer.Data
public import KIP126.Def.Topology.SimplicialRealization.Pullback.StandardSimplex.Data
public import Mathlib.CategoryTheory.Limits.Types.Pushouts
public import Mathlib.CategoryTheory.Limits.Types.Coproducts
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.Order.UpperLower.Basic
public import KIP126.Def.Topology.SimplicialRealization.FiniteSupport.Proofs
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import KIP126.Def.Topology.HomotopyExtension.Predicates
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
public import KIP126.Def.Topology.HomotopyExtension.Data
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.Order.DenselyOrdered
public import KIP126.Def.Topology.ClosedCover.Proofs
public import Mathlib.Topology.Compactness.CompactlyGeneratedSpace
public import KIP126.Def.StableHomotopy.Spectra.Prespectrum.Smash.Diagonal.Map.Data

@[expose] public section

/-! A point-set sequential smash construction. The even level 2n is
Xₙ∧Yₙ, and the intervening odd level is its suspension. Thus both suspension
coordinates are accounted for; Xₙ∧Yₙ is never incorrectly put in level n.
The point-set definitions and good replacements are imported from their
dedicated modules. The double bonds follow MMSS, Definition 11.6.
Descent to the stable localization still requires the flatness statement
(cf. MMSS, Proposition 11.7), which is not established in this file. -/
namespace KIP126.StableHomotopy.Spectra
open CategoryTheory _root_.Topology
open scoped unitInterval
namespace Prespectrum

/-- The zeroth-stage inclusion is the free/evaluation counit. -/
noncomputable def zeroStage (X : Prespectrum.{0}) : suspensionSpectrum (X.level 0) ⟶ X :=
  freeCounit X 0

end Prespectrum
end KIP126.StableHomotopy.Spectra
