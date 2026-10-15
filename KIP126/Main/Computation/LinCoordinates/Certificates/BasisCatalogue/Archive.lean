module

public import KIP126.Main.Computation.LinCoordinates.Tactic.LinBasisCatalogue

import all Init.Data.List.SplitOn.Basic

@[expose] public section


/-! Kernel certificates for all original basis CSV chunks. Parser success
is not mathematical linear independence or generation. -/
namespace KIP126.LinE2.BasisCatalogue
set_option maxRecDepth 100000
set_option Elab.async false
private theorem chunk0 : chunksValid ((RawData.basisChunks.toList.drop 0).take 1) = true := by
  lin_basis_chunks 0 1

private theorem chunk1 : chunksValid ((RawData.basisChunks.toList.drop 1).take 1) = true := by
  lin_basis_chunks 1 1

private theorem chunk2 : chunksValid ((RawData.basisChunks.toList.drop 2).take 1) = true := by
  lin_basis_chunks 2 1

private theorem chunk3 : chunksValid ((RawData.basisChunks.toList.drop 3).take 1) = true := by
  lin_basis_chunks 3 1

private theorem chunk4 : chunksValid ((RawData.basisChunks.toList.drop 4).take 1) = true := by
  lin_basis_chunks 4 1

private theorem chunk5 : chunksValid ((RawData.basisChunks.toList.drop 5).take 1) = true := by
  lin_basis_chunks 5 1

private theorem chunk6 : chunksValid ((RawData.basisChunks.toList.drop 6).take 1) = true := by
  lin_basis_chunks 6 1

private theorem chunk7 : chunksValid ((RawData.basisChunks.toList.drop 7).take 1) = true := by
  lin_basis_chunks 7 1

private theorem chunk8 : chunksValid ((RawData.basisChunks.toList.drop 8).take 1) = true := by
  lin_basis_chunks 8 1

private theorem chunk9 : chunksValid ((RawData.basisChunks.toList.drop 9).take 1) = true := by
  lin_basis_chunks 9 1

private theorem chunk10 : chunksValid ((RawData.basisChunks.toList.drop 10).take 1) = true := by
  lin_basis_chunks 10 1

private theorem chunk11 : chunksValid ((RawData.basisChunks.toList.drop 11).take 1) = true := by
  lin_basis_chunks 11 1

private theorem chunk12 : chunksValid ((RawData.basisChunks.toList.drop 12).take 1) = true := by
  lin_basis_chunks 12 1

private theorem chunk13 : chunksValid ((RawData.basisChunks.toList.drop 13).take 1) = true := by
  lin_basis_chunks 13 1

private theorem chunk14 : chunksValid ((RawData.basisChunks.toList.drop 14).take 1) = true := by
  lin_basis_chunks 14 1

private theorem chunk15 : chunksValid ((RawData.basisChunks.toList.drop 15).take 1) = true := by
  lin_basis_chunks 15 1

private theorem chunk16 : chunksValid ((RawData.basisChunks.toList.drop 16).take 1) = true := by
  lin_basis_chunks 16 1

private theorem chunk17 : chunksValid ((RawData.basisChunks.toList.drop 17).take 1) = true := by
  lin_basis_chunks 17 1

private theorem chunk18 : chunksValid ((RawData.basisChunks.toList.drop 18).take 1) = true := by
  lin_basis_chunks 18 1

private theorem chunk19 : chunksValid ((RawData.basisChunks.toList.drop 19).take 1) = true := by
  lin_basis_chunks 19 1

private theorem chunk20 : chunksValid ((RawData.basisChunks.toList.drop 20).take 1) = true := by
  lin_basis_chunks 20 1

private theorem chunk21 : chunksValid ((RawData.basisChunks.toList.drop 21).take 1) = true := by
  lin_basis_chunks 21 1

private theorem chunk22 : chunksValid ((RawData.basisChunks.toList.drop 22).take 1) = true := by
  lin_basis_chunks 22 1

private theorem chunk23 : chunksValid ((RawData.basisChunks.toList.drop 23).take 1) = true := by
  lin_basis_chunks 23 1

theorem archivedChunks_valid : chunksValid RawData.basisChunks.toList = true := by
  lin_basis_compose chunk0 chunk1 chunk2 chunk3 chunk4 chunk5 chunk6 chunk7 chunk8 chunk9 chunk10 chunk11 chunk12 chunk13 chunk14 chunk15 chunk16 chunk17 chunk18 chunk19 chunk20 chunk21 chunk22 chunk23

end KIP126.LinE2.BasisCatalogue
