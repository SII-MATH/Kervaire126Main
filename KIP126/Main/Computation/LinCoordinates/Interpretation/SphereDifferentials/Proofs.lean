module

public import KIP126.Main.Computation.LinCoordinates.Interpretation.Differentials.Proofs

@[expose] public section

/-! Six sphere differentials from the computation log, interpreted on the
standard Adams spectral sequence. Five follow from `sphereTable_sound`;
row 5541 uses the Adams one-line theorem and independently established
coordinates. These statements specify differentials and do not establish
later-page nonvanishing. The stronger statement associated with basis.d2
record 513 is expressed by `SphereDifferentialFacts.d2_h0Six_h6`. -/

namespace KIP126.Computation.LinCalculations.SphereDifferentials

set_option maxRecDepth 4096

/-- Fact 7.13(2); proofs.db/log.id=5990.
CSV (s,t,index): [8, 133] [1] → [10, 134] [2, 4]. -/
theorem d2_x_125_8 : DifferentialStatement ⟨5990, "d2", 8, 133, 2, [1], [2, 4]⟩ :=
  differential_of_lookup 3 39 _ (by rfl)

/-- Lemma 7.16, classical Toda bracket argument; proofs.db/log.id=5541.
CSV (s,t,index): [1, 64] [0] → [3, 65] [0]. -/
theorem d2_h6 : DifferentialStatement ⟨5541, "d2", 1, 64, 2, [0], [0]⟩ :=
  KIP126.Computation.LinCalculations.row5541

/-- Lemma 7.14(1); proofs.db/log.id=153768.
CSV (s,t,index): [13, 137] [2] → [16, 139] [0]. -/
theorem d3_h4_x_109_12 : DifferentialStatement ⟨153768, "D", 13, 137, 3, [2], [0]⟩ :=
  differential_of_lookup 28 43 _ (by rfl)

/-- Lemma 7.14(2); proofs.db/log.id=462481.
CSV (s,t,index): [15, 138] [2] → [18, 140] [2]. -/
theorem d3_h0Sq_x_123_13_2 : DifferentialStatement ⟨462481, "N", 15, 138, 3, [2], [2]⟩ :=
  differential_of_lookup 57 55 _ (by rfl)

/-- Lemma 7.16; proofs.db/log.id=929469.
CSV (s,t,index): [4, 130] [0] → [7, 132] [0]. -/
theorem d3_x_126_4 : DifferentialStatement ⟨929469, "N", 4, 130, 3, [0], [0]⟩ :=
  differential_of_lookup 60 80 _ (by rfl)

/-- Lemma 7.14(2); proofs.db/log.id=2671068.
CSV (s,t,index): [11, 134] [0, 1, 3] → [18, 140] [1]. -/
theorem d7_x_123_11_combination : DifferentialStatement ⟨2671068, "D", 11, 134, 7, [0, 1, 3], [1]⟩ :=
  differential_of_lookup 85 2 _ (by rfl)

end KIP126.Computation.LinCalculations.SphereDifferentials
