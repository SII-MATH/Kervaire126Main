module

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.CWComplex.Proofs

@[expose] section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory CategoryTheory.Limits Simplicial Opposite Set

universe u

/-- A concrete choice of the proved disk parametrization of the standard
simplex, with the maximum norm used by the classical CW definition. -/
noncomputable def simplexDiskHomeomorph (n : ℕ) :
    stdSimplex ℝ (Fin (n+1)) ≃ₜ Metric.closedBall (0 : Fin n → ℝ) 1 :=
  (Simplex.exists_stdSimplex_closedBall_homeomorph n).choose

/-- The characteristic disk map of an actual nondegenerate simplex. -/
noncomputable def simplexCharacteristic (X : SSet.{u}) (n : ℕ) (s : X.nonDegenerate n) :
    C(Metric.closedBall (0 : Fin n → ℝ) 1, |X|) :=
  ⟨fun x => SSet.toTop.map (SSet.yonedaEquiv.symm s.1)
    ((SimplexCategory.toTopHomeo ⦋n⦌).symm ((simplexDiskHomeomorph n).symm x)),
    (SSet.toTop.map (SSet.yonedaEquiv.symm s.1)).hom.continuous.comp
      ((SimplexCategory.toTopHomeo ⦋n⦌).symm.continuous.comp
        (simplexDiskHomeomorph n).symm.continuous)⟩

/-- The corresponding cell in the actual realized skeletal attachment. -/
def simplexCellIndex (X : SSet.{u}) (n : ℕ) (s : X.nonDegenerate n) :
    ((cellComplex X).attachCells n (by simp)).ι :=
  { simplex := s.1, nonDegenerate := s.2, notMem := by simp }

/-- A total representative of the characteristic map. Its values outside
the closed ball are irrelevant to the CW structure. -/
noncomputable def simplexCharacteristicExtension (X : SSet.{u}) (n : ℕ)
    (s : X.nonDegenerate n) (x : Fin n → ℝ) : |X| := by
  classical
  exact if hx : x ∈ Metric.closedBall (0 : Fin n → ℝ) 1 then
    simplexCharacteristic X n s ⟨x,hx⟩
  else simplexCharacteristic X n s ⟨0,Metric.mem_closedBall_self zero_le_one⟩

end KIP126.Topology.SimplicialRealization
