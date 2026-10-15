module

public import KIP126.Literature.Background.AlgebraRealization
public import KIP126.Literature.Standard.Milnor
public import KIP126.Def.ClassicalAdams.MilnorCohomology.Comparison.Data
public import KIP126.Def.ClassicalAdams.MilnorCohomology.Multiplication.Data
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.CategoryTheory.GradedObject.Braiding
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.Transfer
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Comon_
public import Mathlib.CategoryTheory.Monad.Algebra
public import Mathlib.CategoryTheory.GradedObject.Single
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.LinearAlgebra.Dimension.LinearMap
public import Mathlib.CategoryTheory.Preadditive.LeftExact
public import Mathlib.CategoryTheory.Preadditive.EilenbergMoore
public import Mathlib.CategoryTheory.Monad.Limits
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import KIP126.Def.Steenrod.MilnorCobar.Polynomial.Monomials.Full.Data
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import KIP126.Def.Steenrod.MilnorCobar.Polynomial.Grading.Proofs
public import KIP126.Def.Steenrod.MilnorCobar.Polynomial.Monomials.Full.Proofs
public import KIP126.Def.Steenrod.MilnorCobar.Polynomial.Normalization.Proofs
public import KIP126.Def.Steenrod.MilnorCobar.Polynomial.Multiplication.Proofs
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.BigOperators.Intervals
public import KIP126.Def.Steenrod.MilnorCobar.Polynomial.Monomials.Words.Equiv.Data
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.CategoryTheory.Abelian.Injective.Ext
public import KIP126.Def.ClassicalAdams.MilnorCohomology.Comparison.Proofs
public import KIP126.Def.ClassicalAdams.MilnorCohomology.Multiplication.Proofs
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import KIP126.Def.Steenrod.MilnorCobar.Polynomial.Monomials.Words.H6.Proofs
public import KIP126.Def.ClassicalAdams.MilnorCooperations.Proofs
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Category.ModuleCat.Injective
public import Mathlib.RingTheory.SimpleModule.InjectiveProjective
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import KIP126.Def.ClassicalAdams.MilnorCohomology.Proofs
public import KIP126.Def.Synthetic.NormalizedMap.SphereDegreeOne

@[expose] public section

/-! The assumed algebra and realization comparisons on the fixed synthetic
Adams context. The detector algebra, its unit and the normalized η lift all
refer to the same specified objects and functors. -/

namespace KIP126.Def

open CategoryTheory

/-- The assumed algebra, realization and weight comparisons on the fixed
synthetic Adams context. -/
noncomputable abbrev standardAdamsSyntheticComparisons := KIP126.AdamsSynthetic.standardAdamsSyntheticComparisons

/-- The detector algebra has the specified detecting spectrum as its carrier.
No CSV coordinates or BR21 theorem are built into this algebra object. -/
noncomputable def standardTmfTarget :
    CategoryTheory.Mon KIP126.Classical.Adams.standardFoundation.Spectrum :=
  letI := standardAdamsSyntheticComparisons.algebra.classicalSymmetric
  letI := standardAdamsSyntheticComparisons.algebra.syntheticSymmetric
  { X := KIP126.Classical.Adams.standardAdamsComparison.hopfAndDetector.detector
    mon := standardAdamsSyntheticComparisons.algebra.detector.classical }

/-- The chosen synthetic η is the normalized lift of the specified
classical η, regraded by its stated filtration property. -/
noncomputable def standardEta :
    KIP126.Synthetic.Context.BiHom 1 2
      (KIP126.Synthetic.Context.S_0_0 : standardSyntheticContext.Syn) :=
  let D := KIP126.Classical.Adams.standardAdamsComparison
  (KIP126.AdamsSynthetic.etaSourceIso D
    (KIP126.Synthetic.Context.normalizedExponent_sphere_degree_one
      KIP126.Classical.Adams.standardFoundation.hf2 D.hopfAndDetector.etaMap)).hom ≫
    (D.normalizedMap (.shift 1 .sphere) .sphere D.hopfAndDetector.etaMap).map ≫ D.nu.unitIso.hom

end KIP126.Def
