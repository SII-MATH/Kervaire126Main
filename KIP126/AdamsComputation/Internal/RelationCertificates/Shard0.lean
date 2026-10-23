module

import all KIP126.AdamsComputation.Internal.ArchiveData
import all KIP126.AdamsComputation.Internal.RelationCertificate

/-! Fixed relation certificates, chunk indices 0–57. The proof-producing
checker is unchanged: each character quotation and Boolean result is checked
by the kernel against the original ordered archive data. -/

@[expose] section
namespace KIP126.Computation.CachedStandard
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

private theorem migrationSourceChunk0 :
    (archiveSourceRelationChunks[0].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[0]))

private theorem migrationSourceChunk1 :
    (archiveSourceRelationChunks[1].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[1]))

private theorem migrationSourceChunk2 :
    (archiveSourceRelationChunks[2].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[2]))

private theorem migrationSourceChunk3 :
    (archiveSourceRelationChunks[3].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[3]))

private theorem migrationSourceChunk4 :
    (archiveSourceRelationChunks[4].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[4]))

private theorem migrationSourceChunk5 :
    (archiveSourceRelationChunks[5].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[5]))

private theorem migrationSourceChunk6 :
    (archiveSourceRelationChunks[6].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[6]))

private theorem migrationSourceChunk7 :
    (archiveSourceRelationChunks[7].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[7]))

private theorem migrationSourceChunk8 :
    (archiveSourceRelationChunks[8].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[8]))

private theorem migrationSourceChunk9 :
    (archiveSourceRelationChunks[9].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[9]))

private theorem migrationSourceChunk10 :
    (archiveSourceRelationChunks[10].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[10]))

private theorem migrationSourceChunk11 :
    (archiveSourceRelationChunks[11].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[11]))

private theorem migrationSourceChunk12 :
    (archiveSourceRelationChunks[12].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[12]))

private theorem migrationSourceChunk13 :
    (archiveSourceRelationChunks[13].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[13]))

private theorem migrationSourceChunk14 :
    (archiveSourceRelationChunks[14].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[14]))

private theorem migrationSourceChunk15 :
    (archiveSourceRelationChunks[15].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[15]))

private theorem migrationSourceChunk16 :
    (archiveSourceRelationChunks[16].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[16]))

private theorem migrationSourceChunk17 :
    (archiveSourceRelationChunks[17].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[17]))

private theorem migrationSourceChunk18 :
    (archiveSourceRelationChunks[18].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[18]))

private theorem migrationSourceChunk19 :
    (archiveSourceRelationChunks[19].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[19]))

private theorem migrationSourceChunk20 :
    (archiveSourceRelationChunks[20].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[20]))

private theorem migrationSourceChunk21 :
    (archiveSourceRelationChunks[21].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[21]))

private theorem migrationSourceChunk22 :
    (archiveSourceRelationChunks[22].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[22]))

private theorem migrationSourceChunk23 :
    (archiveSourceRelationChunks[23].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[23]))

private theorem migrationSourceChunk24 :
    (archiveSourceRelationChunks[24].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[24]))

private theorem migrationSourceChunk25 :
    (archiveSourceRelationChunks[25].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[25]))

private theorem migrationSourceChunk26 :
    (archiveSourceRelationChunks[26].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[26]))

private theorem migrationSourceChunk27 :
    (archiveSourceRelationChunks[27].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[27]))

private theorem migrationSourceChunk28 :
    (archiveSourceRelationChunks[28].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[28]))

private theorem migrationSourceChunk29 :
    (archiveSourceRelationChunks[29].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[29]))

private theorem migrationSourceChunk30 :
    (archiveSourceRelationChunks[30].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[30]))

private theorem migrationSourceChunk31 :
    (archiveSourceRelationChunks[31].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[31]))

private theorem migrationSourceChunk32 :
    (archiveSourceRelationChunks[32].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[32]))

private theorem migrationSourceChunk33 :
    (archiveSourceRelationChunks[33].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[33]))

private theorem migrationSourceChunk34 :
    (archiveSourceRelationChunks[34].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[34]))

private theorem migrationSourceChunk35 :
    (archiveSourceRelationChunks[35].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[35]))

private theorem migrationSourceChunk36 :
    (archiveSourceRelationChunks[36].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[36]))

private theorem migrationSourceChunk37 :
    (archiveSourceRelationChunks[37].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[37]))

private theorem migrationSourceChunk38 :
    (archiveSourceRelationChunks[38].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[38]))

private theorem migrationSourceChunk39 :
    (archiveSourceRelationChunks[39].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[39]))

private theorem migrationSourceChunk40 :
    (archiveSourceRelationChunks[40].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[40]))

private theorem migrationSourceChunk41 :
    (archiveSourceRelationChunks[41].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[41]))

private theorem migrationSourceChunk42 :
    (archiveSourceRelationChunks[42].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[42]))

private theorem migrationSourceChunk43 :
    (archiveSourceRelationChunks[43].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[43]))

private theorem migrationSourceChunk44 :
    (archiveSourceRelationChunks[44].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[44]))

private theorem migrationSourceChunk45 :
    (archiveSourceRelationChunks[45].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[45]))

private theorem migrationSourceChunk46 :
    (archiveSourceRelationChunks[46].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[46]))

private theorem migrationSourceChunk47 :
    (archiveSourceRelationChunks[47].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[47]))

private theorem migrationSourceChunk48 :
    (archiveSourceRelationChunks[48].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[48]))

private theorem migrationSourceChunk49 :
    (archiveSourceRelationChunks[49].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[49]))

private theorem migrationSourceChunk50 :
    (archiveSourceRelationChunks[50].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[50]))

private theorem migrationSourceChunk51 :
    (archiveSourceRelationChunks[51].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[51]))

private theorem migrationSourceChunk52 :
    (archiveSourceRelationChunks[52].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[52]))

private theorem migrationSourceChunk53 :
    (archiveSourceRelationChunks[53].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[53]))

private theorem migrationSourceChunk54 :
    (archiveSourceRelationChunks[54].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[54]))

private theorem migrationSourceChunk55 :
    (archiveSourceRelationChunks[55].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[55]))

private theorem migrationSourceChunk56 :
    (archiveSourceRelationChunks[56].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[56]))

private theorem migrationSourceChunk57 :
    (archiveSourceRelationChunks[57].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[57]))

end KIP126.Computation.CachedStandard
