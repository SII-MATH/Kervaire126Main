module

public import KIP126.Main.Computation.LinCoordinates.Interpretation.Basis.Data
public import KIP126.Main.Computation.LinCoordinates.Basis.Proofs

@[expose] public section

namespace KIP126.Classical.Adams
open KIP126.LinE2

theorem sphereE2Coordinates_basis (s t : ℕ) (ht : t ≤ 261) (i : BasisIndex s t) :
    sphereE2Coordinates s t ht (sphereE2Basis s t ht i) = Finsupp.single i 1 :=
  (sphereE2Coordinates s t ht).apply_symm_apply _

/-- The quotient-algebra basis and actual sphere basis correspond under
the same presentation in the external hypotheses. -/
theorem linToSphereE2_dataBasis (s t : ℕ) (ht : t ≤ 261) (i : BasisIndex s t) :
    linToSphereE2 s t ht (dataBasis s t ht i) = sphereE2Basis s t ht i :=
  (linToSphereE2 s t ht).apply_symm_apply _

theorem sphereE2Basis_ne_zero (s t : ℕ) (ht : t ≤ 261) (i : BasisIndex s t) :
    sphereE2Basis s t ht i ≠ 0 := by
  intro h
  apply dataBasis_ne_zero s t ht i
  apply (linToSphereE2 s t ht).injective
  simpa only [linToSphereE2_dataBasis, map_zero] using h

theorem sphereE2Coordinates_reconstruct (s t : ℕ) (ht : t ≤ 261)
    (x : sphereAdamsData.Page 2 ((s : ℤ), (t : ℤ))) :
    (sphereE2Coordinates s t ht).symm (sphereE2Coordinates s t ht x) = x :=
  (sphereE2Coordinates s t ht).symm_apply_apply x

end KIP126.Classical.Adams
