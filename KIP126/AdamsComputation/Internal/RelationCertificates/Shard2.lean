module

import all KIP126.AdamsComputation.Internal.ArchiveData
import all KIP126.AdamsComputation.Internal.RelationCertificate

/-! Fixed relation certificates, chunk indices 114–170. The proof-producing
checker is unchanged: each character quotation and Boolean result is checked
by the kernel against the original ordered archive data. -/

@[expose] section
namespace KIP126.Computation.CachedStandard
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

private theorem migrationSourceChunk114 :
    (archiveSourceRelationChunks[114].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[114]))

private theorem migrationSourceChunk115 :
    (archiveSourceRelationChunks[115].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[115]))

private theorem migrationSourceChunk116 :
    (archiveSourceRelationChunks[116].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[116]))

private theorem migrationSourceChunk117 :
    (archiveSourceRelationChunks[117].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[117]))

private theorem migrationSourceChunk118 :
    (archiveSourceRelationChunks[118].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[118]))

private theorem migrationSourceChunk119 :
    (archiveSourceRelationChunks[119].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[119]))

private theorem migrationSourceChunk120 :
    (archiveSourceRelationChunks[120].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[120]))

private theorem migrationSourceChunk121 :
    (archiveSourceRelationChunks[121].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[121]))

private theorem migrationSourceChunk122 :
    (archiveSourceRelationChunks[122].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[122]))

private theorem migrationSourceChunk123 :
    (archiveSourceRelationChunks[123].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[123]))

private theorem migrationSourceChunk124 :
    (archiveSourceRelationChunks[124].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[124]))

private theorem migrationSourceChunk125 :
    (archiveSourceRelationChunks[125].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[125]))

private theorem migrationSourceChunk126 :
    (archiveSourceRelationChunks[126].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[126]))

private theorem migrationSourceChunk127 :
    (archiveSourceRelationChunks[127].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[127]))

private theorem migrationSourceChunk128 :
    (archiveSourceRelationChunks[128].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[128]))

private theorem migrationSourceChunk129 :
    (archiveSourceRelationChunks[129].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[129]))

private theorem migrationSourceChunk130 :
    (archiveSourceRelationChunks[130].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[130]))

private theorem migrationSourceChunk131 :
    (archiveSourceRelationChunks[131].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[131]))

private theorem migrationSourceChunk132 :
    (archiveSourceRelationChunks[132].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[132]))

private theorem migrationSourceChunk133 :
    (archiveSourceRelationChunks[133].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[133]))

private theorem migrationSourceChunk134 :
    (archiveSourceRelationChunks[134].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[134]))

private theorem migrationSourceChunk135 :
    (archiveSourceRelationChunks[135].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[135]))

private theorem migrationSourceChunk136 :
    (archiveSourceRelationChunks[136].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[136]))

private theorem migrationSourceChunk137 :
    (archiveSourceRelationChunks[137].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[137]))

private theorem migrationSourceChunk138 :
    (archiveSourceRelationChunks[138].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[138]))

private theorem migrationSourceChunk139 :
    (archiveSourceRelationChunks[139].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[139]))

private theorem migrationSourceChunk140 :
    (archiveSourceRelationChunks[140].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[140]))

private theorem migrationSourceChunk141 :
    (archiveSourceRelationChunks[141].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[141]))

private theorem migrationSourceChunk142 :
    (archiveSourceRelationChunks[142].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[142]))

private theorem migrationSourceChunk143 :
    (archiveSourceRelationChunks[143].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[143]))

private theorem migrationSourceChunk144 :
    (archiveSourceRelationChunks[144].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[144]))

private theorem migrationSourceChunk145 :
    (archiveSourceRelationChunks[145].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[145]))

private theorem migrationSourceChunk146 :
    (archiveSourceRelationChunks[146].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[146]))

private theorem migrationSourceChunk147 :
    (archiveSourceRelationChunks[147].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[147]))

private theorem migrationSourceChunk148 :
    (archiveSourceRelationChunks[148].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[148]))

private theorem migrationSourceChunk149 :
    (archiveSourceRelationChunks[149].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[149]))

private theorem migrationSourceChunk150 :
    (archiveSourceRelationChunks[150].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[150]))

private theorem migrationSourceChunk151 :
    (archiveSourceRelationChunks[151].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[151]))

private theorem migrationSourceChunk152 :
    (archiveSourceRelationChunks[152].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[152]))

private theorem migrationSourceChunk153 :
    (archiveSourceRelationChunks[153].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[153]))

private theorem migrationSourceChunk154 :
    (archiveSourceRelationChunks[154].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[154]))

private theorem migrationSourceChunk155 :
    (archiveSourceRelationChunks[155].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[155]))

private theorem migrationSourceChunk156 :
    (archiveSourceRelationChunks[156].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[156]))

private theorem migrationSourceChunk157 :
    (archiveSourceRelationChunks[157].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[157]))

private theorem migrationSourceChunk158 :
    (archiveSourceRelationChunks[158].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[158]))

private theorem migrationSourceChunk159 :
    (archiveSourceRelationChunks[159].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[159]))

private theorem migrationSourceChunk160 :
    (archiveSourceRelationChunks[160].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[160]))

private theorem migrationSourceChunk161 :
    (archiveSourceRelationChunks[161].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[161]))

private theorem migrationSourceChunk162 :
    (archiveSourceRelationChunks[162].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[162]))

private theorem migrationSourceChunk163 :
    (archiveSourceRelationChunks[163].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[163]))

private theorem migrationSourceChunk164 :
    (archiveSourceRelationChunks[164].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[164]))

private theorem migrationSourceChunk165 :
    (archiveSourceRelationChunks[165].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[165]))

private theorem migrationSourceChunk166 :
    (archiveSourceRelationChunks[166].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[166]))

private theorem migrationSourceChunk167 :
    (archiveSourceRelationChunks[167].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[167]))

private theorem migrationSourceChunk168 :
    (archiveSourceRelationChunks[168].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[168]))

private theorem migrationSourceChunk169 :
    (archiveSourceRelationChunks[169].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[169]))

private theorem migrationSourceChunk170 :
    (archiveSourceRelationChunks[170].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[170]))

end KIP126.Computation.CachedStandard
