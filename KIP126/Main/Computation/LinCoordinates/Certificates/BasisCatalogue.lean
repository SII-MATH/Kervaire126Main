module

public import KIP126.Computation.LinCoordinates.Model.BasisCatalogue.Data
public import KIP126.Def.ComputationModel.BasisRows.Parsing

@[expose] public section

/-! Certify success and row membership for the original strict CSV parser.
These facts do not assert linear independence, spanning, or sphere comparison. -/
namespace KIP126.LinE2.BasisCatalogue
open SquareDetection

theorem rawLine_decode_success (h : chunksValid RawData.basisChunks.toList = true)
    (line : String) (hl : line ∈ RawData.basisChunks.toList.flatMap (·.splitOn "\n")) :
    ∃ row, decodeBasisRow line = .ok row := by
  obtain ⟨chunk, hc, hl⟩ := List.mem_flatMap.mp hl
  have hv : chunkValid chunk.toList = true := List.all_eq_true.mp h chunk hc
  rw [SquareDetection.splitOn_newline] at hl
  obtain ⟨cs, hcs, rfl⟩ := List.mem_map.mp hl
  apply decode_success
  rw [String.toList_ofList]
  exact List.all_eq_true.mp hv cs hcs

theorem row_mem_of_rawLine (h : chunksValid RawData.basisChunks.toList = true)
    (line : String) (hl : line ∈ RawData.basisChunks.toList.flatMap (·.splitOn "\n"))
    (row : BasisRow) (hr : decodeBasisRow line = .ok row) : row ∈ basisRows := by
  obtain ⟨rows, hp, hm⟩ := decode_list_members _ (rawLine_decode_success h)
  have heq : basisRows = rows := by
    unfold basisRows parseBasisRows
    rw [hp]
    rfl
  rw [heq]
  exact hm line hl row hr

theorem rawLine_mem_of_chars (i : ℕ) (hi : i < RawData.basisChunks.size)
    (cs : List Char) (h : cs ∈ RawData.basisChunks[i].toList.splitOn '\n') :
    String.ofList cs ∈ RawData.basisChunks.toList.flatMap (·.splitOn "\n") := by
  apply List.mem_flatMap.mpr
  refine ⟨RawData.basisChunks[i], Array.getElem_mem_toList hi, ?_⟩
  rw [SquareDetection.splitOn_newline]
  exact List.mem_map_of_mem h

theorem rawLine_mem_of_join (i : ℕ) (hi : i < RawData.basisChunks.size)
    (a cs b : List Char)
    (hc : RawData.basisChunks[i] = String.ofList (a ++ '\n' :: (cs ++ '\n' :: b)))
    (hcs : '\n' ∉ cs) :
    String.ofList cs ∈ RawData.basisChunks.toList.flatMap (·.splitOn "\n") := by
  apply rawLine_mem_of_chars i hi cs
  rw [hc, String.toList_ofList, List.splitOn_append_cons_self,
    List.splitOn_append_cons_self, List.splitOn_eq_singleton hcs]
  simp

end KIP126.LinE2.BasisCatalogue
