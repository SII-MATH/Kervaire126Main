module
import all KIP126.AdamsSynthetic
import all KIP126.AdamsSynthetic.AdamsFiltration
import all KIP126.AdamsSynthetic.Background
import all KIP126.AdamsSynthetic.Coherence
import all KIP126.AdamsSynthetic.Comparisons
import all KIP126.AdamsSynthetic.Compatibility
import all KIP126.AdamsSynthetic.Configuration
import all KIP126.AdamsSynthetic.ConsumerOperations
import all KIP126.AdamsSynthetic.Context
import all KIP126.AdamsSynthetic.Detection
import all KIP126.AdamsSynthetic.ESSShift
import all KIP126.AdamsSynthetic.Enrichment
import all KIP126.AdamsSynthetic.Extension
import all KIP126.AdamsSynthetic.ExtensionLabels
import all KIP126.AdamsSynthetic.ExtensionWitnesses
import all KIP126.AdamsSynthetic.ExtensionZero
import all KIP126.AdamsSynthetic.Families
import all KIP126.AdamsSynthetic.HomologyExactness
import all KIP126.AdamsSynthetic.Mapping
import all KIP126.AdamsSynthetic.MappingComposition
import all KIP126.AdamsSynthetic.MappingDetection
import all KIP126.AdamsSynthetic.MappingEnrichment
import all KIP126.AdamsSynthetic.Normalized
import all KIP126.AdamsSynthetic.PageExtensions
import all KIP126.AdamsSynthetic.Quotients
import all KIP126.AdamsSynthetic.Realization
import all KIP126.AdamsSynthetic.Recovery
import all KIP126.AdamsSynthetic.Sphere
import all KIP126.AdamsSynthetic.SphereTensor
import all KIP126.AdamsSynthetic.Standard
import all KIP126.AdamsSynthetic.Standard.Background
import all KIP126.AdamsSynthetic.Standard.ClassicalSupport
import all KIP126.AdamsSynthetic.Standard.Filtration
import all KIP126.AdamsSynthetic.Standard.FirstQuotientCompatibility
import all KIP126.AdamsSynthetic.Standard.Operations
import all KIP126.AdamsSynthetic.Standard.Realization
import all KIP126.AdamsSynthetic.Standard.Separation
import all KIP126.AdamsSynthetic.Suspension
import all KIP126.AdamsSynthetic.System
import all KIP126.AdamsSynthetic.Tower
import all KIP126.AdamsSynthetic.Weight
import all KIP126.AdamsSynthetic.Internal.Milnor.Cobar
import all KIP126.AdamsSynthetic.Internal.Milnor.Cohomology
import all KIP126.AdamsSynthetic.Internal.Milnor.Complex
import all KIP126.AdamsSynthetic.Internal.Milnor.Hi
import all KIP126.AdamsSynthetic.Internal.Milnor.Polynomial.Data
import all KIP126.AdamsSynthetic.Internal.Milnor.Polynomial.Grading
import all KIP126.AdamsSynthetic.Internal.Milnor.Polynomial.Multiplication
import all KIP126.AdamsSynthetic.Internal.Milnor.Polynomial.Normalization
import all KIP126.AdamsSynthetic.Internal.Milnor.Polynomial.Preservation
import all KIP126.AdamsSynthetic.Internal.SphereBHS.Inverse
import all KIP126.AdamsSynthetic.Internal.SphereBHS.Milnor
import all KIP126.AdamsSynthetic.Internal.SphereBHS.Tower
import all KIP126.AdamsSynthetic.Internal.Source.AdamsSequence
import all KIP126.AdamsSynthetic.Internal.Source.AdamsTower
import all KIP126.AdamsSynthetic.Internal.Source.AdamsNaturality
import all KIP126.AdamsSynthetic.Internal.Source.Completion
import all KIP126.AdamsSynthetic.Internal.Source.DerivedSmash
import all KIP126.AdamsSynthetic.Internal.Source.MilnorComparison
import all KIP126.AdamsSynthetic.Internal.Source.PointSet
import all KIP126.AdamsSynthetic.Internal.Source.PointSetRecognition
import all KIP126.AdamsSynthetic.Internal.Source.Prespectrum
import all KIP126.AdamsSynthetic.Internal.Source.Recognition
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.BasedSpace.AdjoinPoint.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.BasedSpace.AdjoinPoint.Inclusion
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.BasedSpace.AdjoinPoint.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.BasedSpace.Colimit.Cells.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.BasedSpace.Colimit.Cells.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.BasedSpace.Colimit.Cells.Universal.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.BasedSpace.Colimit.Connected.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.BasedSpace.Colimit.Instances
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.BasedSpace.HomotopyEquivalence.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.BasedSpace.HomotopyExtension.AdjoinPoint.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.BasedSpace.HomotopyExtension.Suspension.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.BasedSpace.Loop.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.BasedSpace.Suspension.Cell
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.BasedSpace.Suspension.Cell.Boundary
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.BasedSpace.Suspension.Cell.Iterate.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.BasedSpace.Suspension.Cell.Pushout.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.BasedSpace.Under.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.FiniteSupport.CWType.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.FiniteSupport.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.FiniteSupport.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Generators
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.PointSet
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum.Colimit.Bond
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum.Colimit.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum.Colimit.Evaluation.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum.Colimit.Level.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum.Colimit.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum.Free.CompactFactor.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum.Free.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum.Free.Geometry.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum.Free.Lifting.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum.Free.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum.HomotopyFunctor.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum.HomotopyFunctor.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum.HomotopyGroup.Abelian.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum.HomotopyGroup.Abelian.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum.HomotopyGroup.Colimit.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum.HomotopyGroup.Colimit.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum.HomotopyGroup.Comparison
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum.HomotopyGroup.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum.HomotopyGroup.Map.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum.HomotopyGroup.Map.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum.HomotopyGroup.Map.Stability.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum.HomotopyGroup.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum.HomotopyGroup.System
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum.Loop.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum.Path.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum.Path.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum.Replacement.Cells.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum.Replacement.Cells.Evaluation.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum.Replacement.Cells.Geometry.Attachment.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum.Replacement.Cells.Geometry.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum.Replacement.Cells.Geometry.Refinement.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum.Replacement.Cells.HomotopyExtension.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum.Replacement.Cells.Lifting.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum.Replacement.Cells.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum.Replacement.Cubical.CompactlyGenerated.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum.Replacement.Cubical.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum.Replacement.Cubical.Good.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum.Replacement.Cubical.HomotopyExtension.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum.Replacement.Cubical.Order.Initial
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum.Replacement.Cubical.Order.Model.Comparison
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum.Replacement.Cubical.Order.Model.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum.Replacement.Cubical.Order.Model.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum.Replacement.Cubical.Order.Sequence
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum.Replacement.Cubical.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum.Replacement.Cubical.WellBased.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum.Representatives.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum.Representatives.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum.Tail.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum.Tail.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum.Zero.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Realization.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Realization.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Singular
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Singular.Cylinder.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Singular.Cylinder.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Singular.Homotopy.Approximation.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Sphere.Representatives.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Sphere.Representatives.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Suspension.Compact.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Suspension.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Suspension.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.Ball.HomotopyExtension.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.Ball.HomotopyExtension.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.CWComplex.Cells.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.CWComplex.ClosedEmbedding.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.CWComplex.FiniteSupport.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.CWComplex.Hausdorff.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.CWComplex.RealFunctions.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.CategoryTheory.CellAttachment.Basic.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.CategoryTheory.CellAttachment.Extension.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.CategoryTheory.CellAttachment.Refinement.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.ClosedCover.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.Colimit.CompactlyGenerated.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.Collapse.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.Coproduct.Homotopy.Small.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.Cylinder.Endpoints.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.Cylinder.Endpoints.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.Homotopy.CompactParameter.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.HomotopyExtension.Cells.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.HomotopyExtension.Closure.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.HomotopyExtension.CylinderCorner.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.HomotopyExtension.CylinderCorner.Extension.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.HomotopyExtension.CylinderCorner.Gluing.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.HomotopyExtension.CylinderCorner.Homotopy.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.HomotopyExtension.CylinderCorner.HomotopyEquivalence.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.HomotopyExtension.CylinderCorner.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.HomotopyExtension.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.HomotopyExtension.HomotopyEquivalence.Extension.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.HomotopyExtension.HomotopyEquivalence.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.HomotopyExtension.HomotopyEquivalence.Relative.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.HomotopyExtension.NDR.Predicates
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.HomotopyExtension.NDR.Product.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.HomotopyExtension.NDR.Product.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.HomotopyExtension.NDR.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.HomotopyExtension.NDR.Retraction.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.HomotopyExtension.Predicates
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.HomotopyExtension.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.HomotopyExtension.Retraction.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.HomotopyGroup.ContinuousMap.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.HomotopyLifting.Cube
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.HomotopyLifting.Cube.Boundary.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.HomotopyLifting.Cube.Boundary.Extension.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.HomotopyLifting.Cube.Boundary.Predicates
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.HomotopyLifting.Cube.Boundary.Product.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.HomotopyLifting.Cube.Boundary.Product.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.HomotopyLifting.Cube.Boundary.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.HomotopyLifting.Cube.Boundary.Topology.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.HomotopyLifting.Cube.ClosedBall
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.HomotopyLifting.Cube.Product.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.HomotopyLifting.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.HomotopyLifting.Predicates
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.HomotopyLifting.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.MappingCylinder.Diagram.Contraction.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.MappingCylinder.Diagram.Contraction.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.MappingCylinder.Diagram.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.MappingCylinder.Diagram.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.Product.CompactFactor
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.Pushout.Cells.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.Pushout.Equivalence.General.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.Pushout.Equivalence.HomotopicAttachment.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.Pushout.Equivalence.HomotopySquare.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.Pushout.Equivalence.OrderMappingCylinder.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.Pushout.Equivalence.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.Pushout.Homotopy.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.Pushout.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.Pushout.RealFunctions.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.Pushout.Separation.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SequentialColimit.Compact.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SequentialColimit.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SequentialColimit.RealFunctions.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SequentialColimit.Separation.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SequentialColimit.Telescope.Comparison.Equivalence.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SequentialColimit.Telescope.Comparison.Injectivity.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SequentialColimit.Telescope.Comparison.Invariance.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SequentialColimit.Telescope.Comparison.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SequentialColimit.Telescope.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SequentialColimit.Telescope.Homotopy.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SequentialColimit.Telescope.Map.Homotopy.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SequentialColimit.Telescope.Map.HomotopyEquivalence.ClosedHEP.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SequentialColimit.Telescope.Map.HomotopyEquivalence.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SequentialColimit.Telescope.Map.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SequentialColimit.Telescope.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SequentialColimit.Telescope.Rectification.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SequentialColimit.Telescope.Triangle.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.Simplex.BarycentricDecomposition.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.Simplex.BarycentricDecomposition.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.Simplex.BarycentricDecomposition.Uniqueness.Basic
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.Simplex.BarycentricDecomposition.Uniqueness.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.Simplex.BarycentricDecomposition.Uniqueness.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.Simplex.BarycentricSubdivisionMesh.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.Simplex.BarycentricSubdivisionMesh.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.Simplex.ClosedBall.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.Simplex.ClosedBall.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.Simplex.Combination.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.Simplex.Combination.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.Simplex.Combination.Vector.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.Simplex.Homotopy.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.Simplex.MonotoneCoupling.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.Simplex.MonotoneCoupling.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.Simplex.MonotoneCoupling.Representation.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.Simplex.MonotoneCoupling.Uniqueness
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.Simplex.Reindex
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.Boundary.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.CWComplex.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.CWComplex.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.Classical.Charts.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.Classical.Charts.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.Classical.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.Classical.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.Classical.Structure.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.CompactlyGenerated.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.DiskPair.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.Equalizer.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.Equalizer.Identification.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.Equalizer.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.FiniteSupport.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Approximation.ArbitraryTarget.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Approximation.Homotopy.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Approximation.Order.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Approximation.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Attachment.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Attachment.Equivalence.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Attachment.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Boundary.Cone.Cube.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Boundary.Cone.Cube.Existence.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Boundary.Cone.Cube.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Boundary.Cone.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Boundary.Cone.Iteration.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Boundary.Cone.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Boundary.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Boundary.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Boundary.Simplex.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Carrier.Homotopy.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Carrier.Image.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Carrier.Predicates
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Carrier.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Compact.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Cone.Coordinates.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Cone.Coordinates.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Cone.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Cone.Extension.Empty.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Cone.Extension.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Cone.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.LastVertex
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.LastVertex.Map.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.MappingCone.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.MappingCone.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.MappingCylinder.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.MappingCylinder.Homotopy.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.MappingCylinder.Homotopy.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.MappingCylinder.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Mesh.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Mesh.Predicates
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Mesh.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Predicates
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Sigma.Approximation.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Sigma.Attachment
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Sigma.Attachment.Cubical.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Sigma.Attachment.Cubical.Sequence.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Sigma.Attachment.Cubical.Sequence.Embedding.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Sigma.Attachment.Cubical.Sequence.Model
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Sigma.Attachment.Model.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Sigma.Cone.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Sigma.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Sigma.Homotopy.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Sigma.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Stars.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Stars.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Subdivision.Comparison.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Subdivision.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Subdivision.Equivalence.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Subdivision.Iteration.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Subdivision.Iteration.Mesh.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Subdivision.Iteration.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Subdivision.Iteration.Stars.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Subdivision.Iteration.Vertices
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Subdivision.Linear.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Subdivision.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Suborder.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Suborder.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Suborder.Subdivision.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Suborder.Subdivision.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.Product.Compact.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.Product.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.Product.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.Pullback
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.Pullback.Identification.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.Pullback.StandardSimplex.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.Relative.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.Relative.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.Subdivision.Barycentric.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.Subdivision.Barycentric.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.Subdivision.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.Subdivision.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SmallObject.Sequence.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SmallObject.Sequence.Functorial.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SmallObject.Sequence.Functorial.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SmallObject.Sequence.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Sphere
import all KIP126.AdamsSynthetic.Internal.Source.SurvivalTransport
import all KIP126.AdamsSynthetic.Source
import all KIP126.AdamsSynthetic.Standard.Source
import all KIP126.AdamsSynthetic.Standard.Ext
import all KIP126.AdamsSynthetic.Internal.SteenrodComodules
import all KIP126.AdamsSynthetic.Internal.SteenrodComodules.Abelian
import all KIP126.AdamsSynthetic.Internal.SteenrodComodules.Biproduct
import all KIP126.AdamsSynthetic.Internal.SteenrodComodules.Cokernel
import all KIP126.AdamsSynthetic.Internal.SteenrodComodules.Kernel


public meta import Checks.Registry.AdamsSynthetic
import Lean

/-! Trust audit for fixed upstream declarations. Only the exact individually
registered proof/construction holes are permitted; project axioms and synthetic
(elaboration-error) holes are always rejected. SpectralSequence stays sorry-free. -/
open Lean Elab Command
set_option maxHeartbeats 0
set_option maxRecDepth 8192
run_cmd do
  let ledger ← Lean.ofExcept <| Json.parse Checks.Registry.AdamsSynthetic.proofObligationLedger
  let entries ← Lean.ofExcept <| ledger.getObjValAs? (Array Json) "obligations"
  let expected : Array Json ← entries.filterM fun (row : Json) => do
    let mod ← Lean.ofExcept <| row.getObjValAs? String "module"
    pure ((`KIP126.AdamsSynthetic).isPrefixOf mod.toName)
  let expectedNames : Array String ← expected.mapM fun (row : Json) => Lean.ofExcept <| row.getObjValAs? String "name"
  let env ← getEnv
  let mut checked : Nat := 0
  let mut holes : Array String := #[]
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless (`KIP126.AdamsSynthetic).isPrefixOf mod do continue
    if info.isAxiom then throwError "Project axiom declaration: {name}"
    let body := info.value? (allowOpaque := true)
    if info.type.hasSyntheticSorry || body.any (·.hasSyntheticSorry) then
      throwError "Synthetic sorry from failed elaboration: {name}"
    if info.type.hasSorry || body.any (·.hasSorry) then
      holes := holes.push name.toString
      let some entry := expected.find? (fun e => e.getObjValAs? String "name" == .ok name.toString)
        | throwError "Unregistered proof/construction obligation: {name}"
      let expectedType ← Lean.ofExcept <| entry.getObjValAs? String "type_fingerprint"
      let expectedBody ← Lean.ofExcept <| entry.getObjValAs? String "body_fingerprint"
      unless expectedType == toString (hash (toString info.type)) &&
          expectedBody == toString (hash (toString body)) do
        throwError "Registered obligation changed; review its exact type/body: {name}"
    let axioms ← collectAxioms name
    let unexpected := axioms.filter fun n =>
      n != `propext && n != `Classical.choice && n != `Quot.sound && n != `sorryAx
    unless unexpected.isEmpty do
      throwError "Unexpected axiom dependency in {name}: {unexpected}"
    checked := checked + 1
  -- These generic tower proofs are independent of the fixed background and
  -- must not delegate their responsibility to another registered placeholder.
  let towerRoots : Array Name := #[
    `KIP126.AdamsSynthetic.Internal.Source.towerDifferential_exists,
    `KIP126.AdamsSynthetic.Internal.Source.towerD_comp,
    `KIP126.AdamsSynthetic.Internal.Source.towerD_kernel,
    `KIP126.AdamsSynthetic.Internal.Source.towerD_image,
    `KIP126.AdamsSynthetic.Internal.Source.canonicalTowerMap,
    `KIP126.AdamsSynthetic.Internal.Source.towerSSDataMap,
    `KIP126.AdamsSynthetic.Internal.Source.towerSequenceMap,
    `KIP126.AdamsSynthetic.Internal.Source.canonicalSequenceMap]
  for target in towerRoots do
    let candidates := env.constants.toList.filter fun (name, _) =>
      ((privateToUserName? name).getD name) == target
    unless candidates.length == 1 do
      throwError "Expected one private tower proof: {target}"
    let name := candidates.head!.1
    let axioms ← collectAxioms name
    unless axioms.all (fun n => n == `propext || n == `Classical.choice || n == `Quot.sound) do
      throwError "Generic tower proof has an unfinished dependency: {name}: {axioms}"
  unless holes.qsort (· < ·) == expectedNames.qsort (· < ·) do
    throwError "Proof obligation registry has stale or missing declarations: {holes}"
  logInfo m!"AdamsSynthetic trust audit: {checked} declarations; {holes.size} individually registered pending proofs/constructions; no project axioms"
