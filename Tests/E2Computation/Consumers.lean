module

import KIP126.E2Computation

/-! The algebraic E₂ comparison, basis and product data are available without
importing later differential records or either operation theorem. -/
namespace Tests.E2Computation
open KIP126.Core.SpectralSequence
open KIP126.AdamsSynthetic.Standard KIP126.Computation.Standard

theorem archivedBasis (s t : ℕ) (ht : t ≤ 261) (i : Fin (archive.basisCount s t)) :
    (comparison s t ht).symm ((coordinates s t ht).symm (Finsupp.single i 1)) =
      (archive.basisMonomial s t i).value sourceData sourceGenerator :=
  comparison_symm_coordinates_basis s t ht i

theorem productComparison (s t s' t' : ℕ) (ht : t+t' ≤ 261)
    (x : sourceData.component s t) (y : sourceData.component s' t') :
    comparison (s+s') (t+t') ht (sourceData.product s t s' t' x y) =
      model.sphereAlgebra.product (s,t) (s',t')
        (comparison s t (by omega) x) (comparison s' t' (by omega) y) :=
  comparison_product s t s' t' ht x y

theorem squareIdentification :
    comparison 2 128 (by decide)
      (sourceData.product 1 64 1 64 (sourceData.atom .h6) (sourceData.atom .h6)) =
      model.standardClasses.standardH6Square := h6_square

example : True := by
  fail_if_success have _ := comparison 2 262 (by decide)
  trivial

open CategoryTheory KIP126.Classical.Adams

/-- The unbounded second-line basis is consumed before any later Adams
calculation; it is not obtained by dropping the archive's degree bound. -/
example (t : ℤ) (x : model.classical.sphere.Page 2 (2,t)) (hx : x ≠ 0) :
    ∃ i j : ℕ, i ≤ j ∧
      ∃ degree : hiDegree i + hiDegree j = (2,t),
        x = (eqToHom (congrArg (ActualE2At model.classical) degree))
          (KIP126.Literature.Standard.hiProduct i j) :=
  KIP126.E2Computation.two_line_exhaustive t x hx

end Tests.E2Computation
