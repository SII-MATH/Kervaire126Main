module

public import KIP126.Main.Computation.LinCoordinates.Basis.Data
public import KIP126.Computation.LinCoordinates.Certificates.BasisCertification.Predicates
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

@[expose] public section


/-! Basis properties obtained from the actual E₂ coordinate equivalences
and their CSV compatibility in the same external hypotheses. -/

namespace KIP126.LinE2

open KIP126.Algebra

theorem dataBasis_val (s t : ℕ) (ht : t ≤ 261) (i : BasisIndex s t) :
    (dataBasis s t ht i).val = basisValue (basisRowAt s t i) :=
  KIP126.Main.AdamsSynthetic.computation.theorems.sphereBasis.csv_values s t ht i

/-- The tabulated coordinate vectors form a basis of the CSV quotient,
by comparison with the basis of actual E₂ in the computation hypotheses. -/
theorem basisTable_correct (s t : ℕ) (ht : t ≤ 261) : BasisTableCorrect s t :=
  ⟨dataBasis s t ht, dataBasis_val s t ht⟩

theorem dataBasis_ne_zero (s t : ℕ) (ht : t ≤ 261) (i : BasisIndex s t) :
    dataBasis s t ht i ≠ 0 := (dataBasis s t ht).ne_zero i

theorem dataCoordinates_basis (s t : ℕ) (ht : t ≤ 261) (i : BasisIndex s t) :
    dataCoordinates s t ht (dataBasis s t ht i) = Finsupp.single i 1 :=
  (dataBasis s t ht).repr_self i

/-- Reconstruct an element from its unique coordinates in the specified basis. -/
theorem dataCoordinates_reconstruct (s t : ℕ) (ht : t ≤ 261) (x : E2At s t) :
    (dataCoordinates s t ht).symm (dataCoordinates s t ht x) = x :=
  (dataCoordinates s t ht).symm_apply_apply x

theorem data_finrank (s t : ℕ) (ht : t ≤ 261) :
    Module.finrank F2 (E2At s t) = (basisRowsAt s t).size := by
  simpa [BasisIndex] using Module.finrank_eq_card_basis (dataBasis s t ht)

end KIP126.LinE2
