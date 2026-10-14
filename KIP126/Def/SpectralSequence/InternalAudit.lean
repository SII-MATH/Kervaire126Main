module

import all KIP126.Def.Algebra.Coefficients.Data
import all KIP126.Def.Algebra.Completion.Data
import all KIP126.Def.Algebra.Filtration.Data
import all KIP126.Def.Algebra.Filtration.Predicates
import all KIP126.Def.Algebra.Filtration.Proofs
import all KIP126.Def.Algebra.Graded.Data
import all KIP126.Def.Algebra.Truncation.Data
import all KIP126.Def.Algebra.Truncation.Proofs
import all KIP126.Def.SpectralSequence.Basic.Category.Data
import all KIP126.Def.SpectralSequence.Basic.Category.Predicates
import all KIP126.Def.SpectralSequence.Basic.Category.Proofs
import all KIP126.Def.SpectralSequence.Basic.Data
import all KIP126.Def.SpectralSequence.Basic.MorphismCriterion
import all KIP126.Def.SpectralSequence.Basic.PageHomology.Data
import all KIP126.Def.SpectralSequence.Basic.Predicates
import all KIP126.Def.SpectralSequence.Basic.Proofs
import all KIP126.Def.SpectralSequence.Basic
import all KIP126.Def.SpectralSequence.BoundedExtension.BoundedComplex.Data
import all KIP126.Def.SpectralSequence.BoundedExtension.Chain.Data
import all KIP126.Def.SpectralSequence.BoundedExtension.Chain.Proofs
import all KIP126.Def.SpectralSequence.BoundedExtension.Detection.Predicates
import all KIP126.Def.SpectralSequence.BoundedExtension.Morphism.Construction.Data
import all KIP126.Def.SpectralSequence.BoundedExtension.Morphism.Construction.Proofs
import all KIP126.Def.SpectralSequence.BoundedExtension.Morphism.Data
import all KIP126.Def.SpectralSequence.BoundedExtension.Morphism.Proofs
import all KIP126.Def.SpectralSequence.BoundedExtension.SelfComplex.Data
import all KIP126.Def.SpectralSequence.BoundedExtension.Sequence.Data
import all KIP126.Def.SpectralSequence.BoundedExtension.Sequence.Predicates
import all KIP126.Def.SpectralSequence.BoundedExtension.Sequence.Proofs
import all KIP126.Def.SpectralSequence.BoundedExtension.SpectralSequence.Data
import all KIP126.Def.SpectralSequence.BoundedExtension.SpectralSequence.Proofs
import all KIP126.Def.SpectralSequence.BoundedExtension.Square.Construction.Data
import all KIP126.Def.SpectralSequence.BoundedExtension.Square.Data
import all KIP126.Def.SpectralSequence.BoundedExtension.Square.Proofs
import all KIP126.Def.SpectralSequence.BoundedExtension.TwoTerm.Data
import all KIP126.Def.SpectralSequence.BoundedExtension.TwoTerm.Proofs
import all KIP126.Def.SpectralSequence.BoundedExtension.UnderlyingComplex.Data
import all KIP126.Def.SpectralSequence.BoundedExtension.UnderlyingComplex.Proofs
import all KIP126.Def.SpectralSequence.BoundedExtension
import all KIP126.Def.SpectralSequence.Commutativity.Basic.Proofs
import all KIP126.Def.SpectralSequence.Commutativity.Detection.Data
import all KIP126.Def.SpectralSequence.Commutativity.Detection.Proofs
import all KIP126.Def.SpectralSequence.Commutativity.Predicates
import all KIP126.Def.SpectralSequence.Commutativity.Square.Data
import all KIP126.Def.SpectralSequence.Commutativity.Square.Proofs
import all KIP126.Def.SpectralSequence.Commutativity
import all KIP126.Def.SpectralSequence.Completion.Comparison.Data
import all KIP126.Def.SpectralSequence.Completion.Comparison.Proofs
import all KIP126.Def.SpectralSequence.Completion.CompletedFiltration.Data
import all KIP126.Def.SpectralSequence.Completion.Data
import all KIP126.Def.SpectralSequence.Completion.Predicates
import all KIP126.Def.SpectralSequence.Completion.Proofs
import all KIP126.Def.SpectralSequence.Completion.UniversalProperty.Data
import all KIP126.Def.SpectralSequence.Completion.UniversalProperty.Proofs
import all KIP126.Def.SpectralSequence.Computation.API.Predicates
import all KIP126.Def.SpectralSequence.Computation.Morphism.Proofs
import all KIP126.Def.SpectralSequence.Computation.PageThree.Proofs
import all KIP126.Def.SpectralSequence.Computation.Predicates
import all KIP126.Def.SpectralSequence.Computation.Proofs
import all KIP126.Def.SpectralSequence.Computation.State.Predicates
import all KIP126.Def.SpectralSequence.Computation.State.Proofs
import all KIP126.Def.SpectralSequence.Consumer.BoundedExtension
import all KIP126.Def.SpectralSequence.Consumer.Extension
import all KIP126.Def.SpectralSequence.Convergence.Category.Data
import all KIP126.Def.SpectralSequence.Convergence.Data
import all KIP126.Def.SpectralSequence.Convergence.Predicates
import all KIP126.Def.SpectralSequence.Convergence.Proofs
import all KIP126.Def.SpectralSequence.Convergence.Vanishing.Proofs
import all KIP126.Def.SpectralSequence.Crossing.Data
import all KIP126.Def.SpectralSequence.Crossing.Predicates
import all KIP126.Def.SpectralSequence.Crossing.Proofs
import all KIP126.Def.SpectralSequence.Extension.Complex.Data
import all KIP126.Def.SpectralSequence.Extension.Complex.Proofs
import all KIP126.Def.SpectralSequence.Extension.Data
import all KIP126.Def.SpectralSequence.Extension.Proofs
import all KIP126.Def.SpectralSequence.FilteredComplex.Crossing.Proofs
import all KIP126.Def.SpectralSequence.FilteredComplex.Crossing
import all KIP126.Def.SpectralSequence.FilteredComplex.Data
import all KIP126.Def.SpectralSequence.FilteredComplex.HomologyTarget.Data
import all KIP126.Def.SpectralSequence.FilteredComplex.SSData.Data
import all KIP126.Def.SpectralSequence.FilteredComplex.SSData.Predicates
import all KIP126.Def.SpectralSequence.FilteredComplex.SSData.Proofs
import all KIP126.Def.SpectralSequence.FilteredComplex.SSData
import all KIP126.Def.SpectralSequence.FilteredComplex.SSDataConstruction.Data
import all KIP126.Def.SpectralSequence.FilteredComplex.SSDataConstruction.Proofs
import all KIP126.Def.SpectralSequence.FilteredComplex.Solutions.Affine.Data
import all KIP126.Def.SpectralSequence.FilteredComplex.Solutions.AffineRestriction.Proofs
import all KIP126.Def.SpectralSequence.FilteredComplex.Solutions.Data
import all KIP126.Def.SpectralSequence.FilteredComplex.Solutions.Finiteness.Proofs
import all KIP126.Def.SpectralSequence.FilteredComplex.Solutions.Morphism.Data
import all KIP126.Def.SpectralSequence.FilteredComplex.Solutions.Morphism.Proofs
import all KIP126.Def.SpectralSequence.FilteredComplex.Solutions.Obstruction.Data
import all KIP126.Def.SpectralSequence.FilteredComplex.Solutions.Obstruction.Proofs
import all KIP126.Def.SpectralSequence.FilteredComplex.Solutions.Page.Converse.Proofs
import all KIP126.Def.SpectralSequence.FilteredComplex.Solutions.Page.Proofs
import all KIP126.Def.SpectralSequence.FilteredComplex.Solutions.Proofs
import all KIP126.Def.SpectralSequence.FilteredComplex.Solutions.Restriction.Data
import all KIP126.Def.SpectralSequence.FilteredComplex.Solutions.Restriction.Proofs
import all KIP126.Def.SpectralSequence.FilteredComplex.SpectralSequenceConstruction.Data
import all KIP126.Def.SpectralSequence.FilteredComplex.WeakConvergence.Comparison.Proofs
import all KIP126.Def.SpectralSequence.FilteredComplex.WeakConvergence.Data
import all KIP126.Def.SpectralSequence.FilteredComplex
import all KIP126.Def.SpectralSequence.FilteredDifferential.Boundaries
import all KIP126.Def.SpectralSequence.FilteredDifferential.Cycles
import all KIP126.Def.SpectralSequence.FilteredDifferential.Data
import all KIP126.Def.SpectralSequence.FilteredDifferential.Helpers
import all KIP126.Def.SpectralSequence.FilteredDifferential.Proofs
import all KIP126.Def.SpectralSequence.FilteredDifferential.SquareZero
import all KIP126.Def.SpectralSequence.FilteredPage.Data
import all KIP126.Def.SpectralSequence.FilteredPage.Proofs
import all KIP126.Def.SpectralSequence.FinitePageCalculus.Proofs
import all KIP126.Def.SpectralSequence.ModuleQuotient.Data
import all KIP126.Def.SpectralSequence.ModuleQuotient.Proofs
import all KIP126.Def.SpectralSequence.ModuleSubobject.Proofs
import all KIP126.Def.SpectralSequence.PageComparison.Data
import all KIP126.Def.SpectralSequence.PageComparison.Predicates
import all KIP126.Def.SpectralSequence.PageComparison.Raw.Data
import all KIP126.Def.SpectralSequence.PageComparison.Raw.Proofs
import all KIP126.Def.SpectralSequence.PageLevel.Data
import all KIP126.Def.SpectralSequence.PageLevel.Proofs
import all KIP126.Def.SpectralSequence.Permanence.Predicates
import all KIP126.Def.SpectralSequence.Permanence.Proofs
import all KIP126.Def.SpectralSequence.Representatives.Proofs
import all KIP126.Def.SpectralSequence.Truncation.Data
import all KIP126.Def.SpectralSequence.Truncation.Predicates
import all KIP126.Def.SpectralSequence.Truncation.Proofs
import all KIP126.Def.SpectralSequence.Truncation
import all KIP126.Def.SpectralSequence.UnboundedExtension.TruncatedComplex.Data
import all KIP126.Def.SpectralSequence.UnboundedExtension.TruncatedComplex.Proofs
import all KIP126.Def.SpectralSequence.UnboundedExtension.TruncatedSpectralSequence.Data
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
