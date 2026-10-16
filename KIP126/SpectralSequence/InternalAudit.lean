module
import all KIP126.SpectralSequence
import all KIP126.SpectralSequence.Basic
import all KIP126.SpectralSequence.Basic.Category.Data
import all KIP126.SpectralSequence.Basic.Category.Predicates
import all KIP126.SpectralSequence.Basic.Category.Proofs
import all KIP126.SpectralSequence.Basic.Data
import all KIP126.SpectralSequence.Basic.MorphismCriterion
import all KIP126.SpectralSequence.Basic.PageHomology.Data
import all KIP126.SpectralSequence.Basic.Predicates
import all KIP126.SpectralSequence.Basic.Proofs
import all KIP126.SpectralSequence.BoundedExtension
import all KIP126.SpectralSequence.BoundedExtension.BoundedComplex.Data
import all KIP126.SpectralSequence.BoundedExtension.Chain.Data
import all KIP126.SpectralSequence.BoundedExtension.Chain.Proofs
import all KIP126.SpectralSequence.BoundedExtension.Detection.Predicates
import all KIP126.SpectralSequence.BoundedExtension.Morphism.Construction.Data
import all KIP126.SpectralSequence.BoundedExtension.Morphism.Construction.Proofs
import all KIP126.SpectralSequence.BoundedExtension.Morphism.Data
import all KIP126.SpectralSequence.BoundedExtension.Morphism.Proofs
import all KIP126.SpectralSequence.BoundedExtension.SelfComplex.Data
import all KIP126.SpectralSequence.BoundedExtension.Sequence.Data
import all KIP126.SpectralSequence.BoundedExtension.Sequence.Predicates
import all KIP126.SpectralSequence.BoundedExtension.Sequence.Proofs
import all KIP126.SpectralSequence.BoundedExtension.SpectralSequence.Data
import all KIP126.SpectralSequence.BoundedExtension.SpectralSequence.Proofs
import all KIP126.SpectralSequence.BoundedExtension.Square.Construction.Data
import all KIP126.SpectralSequence.BoundedExtension.Square.Data
import all KIP126.SpectralSequence.BoundedExtension.Square.Proofs
import all KIP126.SpectralSequence.BoundedExtension.TwoTerm.Data
import all KIP126.SpectralSequence.BoundedExtension.TwoTerm.Proofs
import all KIP126.SpectralSequence.BoundedExtension.UnderlyingComplex.Data
import all KIP126.SpectralSequence.BoundedExtension.UnderlyingComplex.Proofs
import all KIP126.SpectralSequence.Commutativity
import all KIP126.SpectralSequence.Commutativity.Basic.Proofs
import all KIP126.SpectralSequence.Commutativity.Detection.Data
import all KIP126.SpectralSequence.Commutativity.Detection.Proofs
import all KIP126.SpectralSequence.Commutativity.Predicates
import all KIP126.SpectralSequence.Commutativity.Square.Data
import all KIP126.SpectralSequence.Commutativity.Square.Proofs
import all KIP126.SpectralSequence.Completion.Comparison.Data
import all KIP126.SpectralSequence.Completion.Comparison.Proofs
import all KIP126.SpectralSequence.Completion.CompletedFiltration.Data
import all KIP126.SpectralSequence.Completion.Data
import all KIP126.SpectralSequence.Completion.Predicates
import all KIP126.SpectralSequence.Completion.Proofs
import all KIP126.SpectralSequence.Completion.UniversalProperty.Data
import all KIP126.SpectralSequence.Completion.UniversalProperty.Proofs
import all KIP126.SpectralSequence.Computation.API.Predicates
import all KIP126.SpectralSequence.Computation.Morphism.Proofs
import all KIP126.SpectralSequence.Computation.PageThree.Proofs
import all KIP126.SpectralSequence.Computation.Predicates
import all KIP126.SpectralSequence.Computation.Proofs
import all KIP126.SpectralSequence.Computation.State.Predicates
import all KIP126.SpectralSequence.Computation.State.Proofs
import all KIP126.SpectralSequence.Consumer.BoundedExtension
import all KIP126.SpectralSequence.Consumer.Extension
import all KIP126.SpectralSequence.Convergence.Category.Data
import all KIP126.SpectralSequence.Convergence.Data
import all KIP126.SpectralSequence.Convergence.Predicates
import all KIP126.SpectralSequence.Convergence.Proofs
import all KIP126.SpectralSequence.Convergence.Vanishing.Proofs
import all KIP126.SpectralSequence.Crossing.Data
import all KIP126.SpectralSequence.Crossing.Predicates
import all KIP126.SpectralSequence.Crossing.Proofs
import all KIP126.SpectralSequence.Extension.Complex.Data
import all KIP126.SpectralSequence.Extension.Complex.Proofs
import all KIP126.SpectralSequence.Extension.Data
import all KIP126.SpectralSequence.Extension.Proofs
import all KIP126.SpectralSequence.FilteredComplex
import all KIP126.SpectralSequence.FilteredComplex.Crossing
import all KIP126.SpectralSequence.FilteredComplex.Crossing.Proofs
import all KIP126.SpectralSequence.FilteredComplex.Data
import all KIP126.SpectralSequence.FilteredComplex.HomologyTarget.Data
import all KIP126.SpectralSequence.FilteredComplex.SSData
import all KIP126.SpectralSequence.FilteredComplex.SSData.Data
import all KIP126.SpectralSequence.FilteredComplex.SSData.Predicates
import all KIP126.SpectralSequence.FilteredComplex.SSData.Proofs
import all KIP126.SpectralSequence.FilteredComplex.SSDataConstruction.Data
import all KIP126.SpectralSequence.FilteredComplex.SSDataConstruction.Proofs
import all KIP126.SpectralSequence.FilteredComplex.Solutions.Affine.Data
import all KIP126.SpectralSequence.FilteredComplex.Solutions.AffineRestriction.Proofs
import all KIP126.SpectralSequence.FilteredComplex.Solutions.Data
import all KIP126.SpectralSequence.FilteredComplex.Solutions.Finiteness.Proofs
import all KIP126.SpectralSequence.FilteredComplex.Solutions.Morphism.Data
import all KIP126.SpectralSequence.FilteredComplex.Solutions.Morphism.Proofs
import all KIP126.SpectralSequence.FilteredComplex.Solutions.Obstruction.Data
import all KIP126.SpectralSequence.FilteredComplex.Solutions.Obstruction.Proofs
import all KIP126.SpectralSequence.FilteredComplex.Solutions.Page.Converse.Proofs
import all KIP126.SpectralSequence.FilteredComplex.Solutions.Page.Proofs
import all KIP126.SpectralSequence.FilteredComplex.Solutions.Proofs
import all KIP126.SpectralSequence.FilteredComplex.Solutions.Restriction.Data
import all KIP126.SpectralSequence.FilteredComplex.Solutions.Restriction.Proofs
import all KIP126.SpectralSequence.FilteredComplex.SpectralSequenceConstruction.Data
import all KIP126.SpectralSequence.FilteredComplex.WeakConvergence.Comparison.Proofs
import all KIP126.SpectralSequence.FilteredComplex.WeakConvergence.Data
import all KIP126.SpectralSequence.FilteredDifferential.Boundaries
import all KIP126.SpectralSequence.FilteredDifferential.Cycles
import all KIP126.SpectralSequence.FilteredDifferential.Data
import all KIP126.SpectralSequence.FilteredDifferential.Helpers
import all KIP126.SpectralSequence.FilteredDifferential.Proofs
import all KIP126.SpectralSequence.FilteredDifferential.SquareZero
import all KIP126.SpectralSequence.FilteredPage.Data
import all KIP126.SpectralSequence.FilteredPage.Proofs
import all KIP126.SpectralSequence.FinitePageCalculus.Proofs
import all KIP126.SpectralSequence.Internal.Algebra.Coefficients.Data
import all KIP126.SpectralSequence.Internal.Algebra.Completion.Data
import all KIP126.SpectralSequence.Internal.Algebra.Filtration.Data
import all KIP126.SpectralSequence.Internal.Algebra.Filtration.Predicates
import all KIP126.SpectralSequence.Internal.Algebra.Filtration.Proofs
import all KIP126.SpectralSequence.Internal.Algebra.Graded.Data
import all KIP126.SpectralSequence.Internal.Algebra.Truncation.Data
import all KIP126.SpectralSequence.Internal.Algebra.Truncation.Proofs
import all KIP126.SpectralSequence.ModuleQuotient.Data
import all KIP126.SpectralSequence.ModuleQuotient.Proofs
import all KIP126.SpectralSequence.ModuleSubobject.Proofs
import all KIP126.SpectralSequence.Multiplicative
import all KIP126.SpectralSequence.MultiplicativeCategory
import all KIP126.SpectralSequence.PageComparison.Data
import all KIP126.SpectralSequence.PageComparison.Predicates
import all KIP126.SpectralSequence.PageComparison.Raw.Data
import all KIP126.SpectralSequence.PageComparison.Raw.Proofs
import all KIP126.SpectralSequence.PageLevel.Data
import all KIP126.SpectralSequence.PageLevel.Proofs
import all KIP126.SpectralSequence.Permanence.Predicates
import all KIP126.SpectralSequence.Permanence.Proofs
import all KIP126.SpectralSequence.Representatives.Proofs
import all KIP126.SpectralSequence.Transport
import all KIP126.SpectralSequence.Truncation
import all KIP126.SpectralSequence.Truncation.Data
import all KIP126.SpectralSequence.Truncation.Predicates
import all KIP126.SpectralSequence.Truncation.Proofs
import all KIP126.SpectralSequence.UnboundedExtension.TruncatedComplex.Data
import all KIP126.SpectralSequence.UnboundedExtension.TruncatedComplex.Proofs
import all KIP126.SpectralSequence.UnboundedExtension.TruncatedSpectralSequence.Data


import Lean

/-! Internal trust audit. This module exports nothing. It inspects private
implementation declarations as well as the public interface. -/
open Lean Elab Command
set_option maxHeartbeats 0
set_option maxRecDepth 8192
run_cmd do
  let env ← getEnv
  let mut checked : Nat := 0
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless (`KIP126).isPrefixOf mod do continue
    if info.isAxiom then
      throwError "Project axiom declaration: {name}"
    let axioms ← collectAxioms name
    let unexpected := axioms.filter fun n =>
      n != `propext && n != `Classical.choice && n != `Quot.sound
    unless unexpected.isEmpty do
      throwError "Unexpected axiom dependency in {name}: {unexpected}"
    checked := checked + 1
  logInfo m!"SpectralSequence internal trust audit: {checked} declarations; only propext, Classical.choice, Quot.sound permitted"
