module

public import KIP126.Computation.LinCoordinates.Interpretation.Near126.Names.Data

@[expose] public section

namespace KIP126.Computation.Near126

theorem Atom.index_lt (a : Atom) : a.record.1 < KIP126.LinE2.RawData.generatorCount := by
  cases a <;> decide

set_option maxRecDepth 10000 in
set_option linter.unusedSimpArgs false in
/-- Kernel-checked names and degrees; this does not verify a differential. -/
theorem Atom.record_eq (a : Atom) :
    KIP126.LinE2.RawData.generators[a.record.1]! = a.record.2 := by
  cases a <;>
    simp [Atom.record, KIP126.LinE2.RawData.generators,
      KIP126.LinE2.RawData.generatorRow, KIP126.LinE2.RawData.generatorChunkIndex,
      KIP126.LinE2.RawData.generatorCount,
      KIP126.LinE2.RawData.generatorChunk0, KIP126.LinE2.RawData.generatorChunk1,
      KIP126.LinE2.RawData.generatorChunk2, KIP126.LinE2.RawData.generatorChunk5,
      KIP126.LinE2.RawData.generatorChunk7,
      KIP126.LinE2.RawData.generatorChunk8, KIP126.LinE2.RawData.generatorChunk10,
      KIP126.LinE2.RawData.generatorChunk11, KIP126.LinE2.RawData.generatorChunk12,
      KIP126.LinE2.RawData.generatorChunk13,
      Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?]

theorem Atom.degree_eq (a : Atom) :
    KIP126.LinE2.generatorDegree ⟨a.record.1, a.index_lt⟩ = a.record.2.2 := by
  unfold KIP126.LinE2.generatorDegree
  rw [a.record_eq]

end KIP126.Computation.Near126
