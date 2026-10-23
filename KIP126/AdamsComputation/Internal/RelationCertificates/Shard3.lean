module

import all KIP126.AdamsComputation.Internal.ArchiveData
import all KIP126.AdamsComputation.Internal.RelationCertificate

/-! Fixed relation certificates, chunk indices 171–226. The proof-producing
checker is unchanged: each character quotation and Boolean result is checked
by the kernel against the original ordered archive data. -/

@[expose] section
namespace KIP126.Computation.CachedStandard
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

private theorem migrationSourceChunk171 :
    (archiveSourceRelationChunks[171].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[171]))

private theorem migrationSourceChunk172 :
    (archiveSourceRelationChunks[172].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[172]))

private theorem migrationSourceChunk173 :
    (archiveSourceRelationChunks[173].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[173]))

private theorem migrationSourceChunk174 :
    (archiveSourceRelationChunks[174].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[174]))

private theorem migrationSourceChunk175 :
    (archiveSourceRelationChunks[175].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[175]))

private theorem migrationSourceChunk176 :
    (archiveSourceRelationChunks[176].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[176]))

private theorem migrationSourceChunk177 :
    (archiveSourceRelationChunks[177].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[177]))

private theorem migrationSourceChunk178 :
    (archiveSourceRelationChunks[178].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[178]))

private theorem migrationSourceChunk179 :
    (archiveSourceRelationChunks[179].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[179]))

private theorem migrationSourceChunk180 :
    (archiveSourceRelationChunks[180].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[180]))

private theorem migrationSourceChunk181 :
    (archiveSourceRelationChunks[181].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[181]))

private theorem migrationSourceChunk182 :
    (archiveSourceRelationChunks[182].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[182]))

private theorem migrationSourceChunk183 :
    (archiveSourceRelationChunks[183].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[183]))

private theorem migrationSourceChunk184 :
    (archiveSourceRelationChunks[184].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[184]))

private theorem migrationSourceChunk185 :
    (archiveSourceRelationChunks[185].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[185]))

private theorem migrationSourceChunk186 :
    (archiveSourceRelationChunks[186].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[186]))

private theorem migrationSourceChunk187 :
    (archiveSourceRelationChunks[187].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[187]))

private theorem migrationSourceChunk188 :
    (archiveSourceRelationChunks[188].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[188]))

private theorem migrationSourceChunk189 :
    (archiveSourceRelationChunks[189].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[189]))

private theorem migrationSourceChunk190 :
    (archiveSourceRelationChunks[190].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[190]))

private theorem migrationSourceChunk191 :
    (archiveSourceRelationChunks[191].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[191]))

private theorem migrationSourceChunk192 :
    (archiveSourceRelationChunks[192].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[192]))

private theorem migrationSourceChunk193 :
    (archiveSourceRelationChunks[193].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[193]))

private theorem migrationSourceChunk194 :
    (archiveSourceRelationChunks[194].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[194]))

private theorem migrationSourceChunk195 :
    (archiveSourceRelationChunks[195].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[195]))

private theorem migrationSourceChunk196 :
    (archiveSourceRelationChunks[196].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[196]))

private theorem migrationSourceChunk197 :
    (archiveSourceRelationChunks[197].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[197]))

private theorem migrationSourceChunk198 :
    (archiveSourceRelationChunks[198].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[198]))

private theorem migrationSourceChunk199 :
    (archiveSourceRelationChunks[199].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[199]))

private theorem migrationSourceChunk200 :
    (archiveSourceRelationChunks[200].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[200]))

private theorem migrationSourceChunk201 :
    (archiveSourceRelationChunks[201].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[201]))

private theorem migrationSourceChunk202 :
    (archiveSourceRelationChunks[202].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[202]))

private theorem migrationSourceChunk203 :
    (archiveSourceRelationChunks[203].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[203]))

private theorem migrationSourceChunk204 :
    (archiveSourceRelationChunks[204].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[204]))

private theorem migrationSourceChunk205 :
    (archiveSourceRelationChunks[205].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[205]))

private theorem migrationSourceChunk206 :
    (archiveSourceRelationChunks[206].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[206]))

private theorem migrationSourceChunk207 :
    (archiveSourceRelationChunks[207].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[207]))

private theorem migrationSourceChunk208 :
    (archiveSourceRelationChunks[208].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[208]))

private theorem migrationSourceChunk209 :
    (archiveSourceRelationChunks[209].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[209]))

private theorem migrationSourceChunk210 :
    (archiveSourceRelationChunks[210].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[210]))

private theorem migrationSourceChunk211 :
    (archiveSourceRelationChunks[211].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[211]))

private theorem migrationSourceChunk212 :
    (archiveSourceRelationChunks[212].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[212]))

private theorem migrationSourceChunk213 :
    (archiveSourceRelationChunks[213].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[213]))

private theorem migrationSourceChunk214 :
    (archiveSourceRelationChunks[214].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[214]))

private theorem migrationSourceChunk215 :
    (archiveSourceRelationChunks[215].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[215]))

private theorem migrationSourceChunk216 :
    (archiveSourceRelationChunks[216].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[216]))

private theorem migrationSourceChunk217 :
    (archiveSourceRelationChunks[217].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[217]))

private theorem migrationSourceChunk218 :
    (archiveSourceRelationChunks[218].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[218]))

private theorem migrationSourceChunk219 :
    (archiveSourceRelationChunks[219].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[219]))

private theorem migrationSourceChunk220 :
    (archiveSourceRelationChunks[220].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[220]))

private theorem migrationSourceChunk221 :
    (archiveSourceRelationChunks[221].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[221]))

private theorem migrationSourceChunk222 :
    (archiveSourceRelationChunks[222].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[222]))

private theorem migrationSourceChunk223 :
    (archiveSourceRelationChunks[223].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[223]))

private theorem migrationSourceChunk224 :
    (archiveSourceRelationChunks[224].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[224]))

private theorem migrationSourceChunk225 :
    (archiveSourceRelationChunks[225].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[225]))

private theorem migrationSourceChunk226 :
    (archiveSourceRelationChunks[226].toList.splitOn '\n').all KIP126.Computation.RelationCertificate.good = true := by
  run_tac KIP126.Computation.RelationCertificate.certifyRelationChunk (← `(archiveSourceRelationChunks[226]))

end KIP126.Computation.CachedStandard
