module

public import KIP126.Main.Computation.LinCoordinates.Interpretation.Differentials.Certificate
public import KIP126.Def.SpectralSequence.Computation.Proofs
public import KIP126.Main.Computation.AdamsOneLine.H6

@[expose] public section


namespace KIP126.Computation.LinCalculations

/-- Every row found in the fixed differential table satisfies its Adams
statement, by the common table-soundness hypothesis. -/
theorem differential_of_lookup (shard offset : Nat) (row : DifferentialRow)
    (h : RawData.lookup shard offset = some row) : DifferentialStatement row :=
  sphereTable_sound shard offset row h

/-- Interpret a table differential in the sphere Adams sequence. The source
and target coordinate witnesses remain explicit and must be identified
with the polynomial expressions used in the paper. -/
theorem DifferentialStatement.hasDifferential {row : DifferentialRow}
    (h : DifferentialStatement row) :
    ∃ (hx : row.t ≤ 261) (hy : row.t + row.r - 1 ≤ 261)
      (x : LinE2.E2At row.s row.t)
      (y : LinE2.E2At (row.s + row.r) (row.t + row.r - 1)),
      HasCoordinates x row.x ∧ HasCoordinates y row.dx ∧
      SpectralSequence.HasDifferential Classical.Adams.sphereAdamsData row.r
        (row.s, row.t) (((row.s + row.r : Nat) : ℤ), ((row.t + row.r - 1 : Nat) : ℤ))
        (Classical.Adams.linToSphereE2 row.s row.t hx x)
        (Classical.Adams.linToSphereE2 (row.s + row.r) (row.t + row.r - 1) hy y) := by
  obtain ⟨hx, hy, x, y, hcx, hcy, hd, xr, yr, hrx, hry, heq⟩ := h
  exact ⟨hx, hy, x, y, hcx, hcy, hd, xr, yr, hrx, hry, heq⟩

set_option maxRecDepth 2048 in
/-- Row 5541 follows from the Adams one-line theorem and the specified
presentation, using independently checked source and target coordinates. -/
theorem row5541 : DifferentialStatement ⟨5541, "d2", 1, 64, 2, [0], [0]⟩ :=
  KIP126.Main.Computation.LinCoordinates.row5541
    KIP126.Main.AdamsSynthetic.literature
    KIP126.Main.AdamsSynthetic.computation.interpretation.presentation

end KIP126.Computation.LinCalculations
