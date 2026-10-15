module

public import KIP126.Main.Literature.EtaRows.Proofs

@[expose] public section

/-! Finite enumeration and conditional nonvanishing for the transcribed η rows.
The nonvanishing assertion below uses supplied maps and supplied differential
values. It neither constructs such data nor proves their existence. -/
namespace KIP126.Classical.ExtensionSS

open KIP126.Classical.Adams

namespace EtaDifferentialIndex

/-- The row identities form a closed finite type. -/
instance : Fintype EtaDifferentialIndex where
  elems := {.d₁, .d₂, .d₃, .d₄, .d₂Inessential}
  complete id := by cases id <;> simp

end EtaDifferentialIndex

/-- A prescribed differential is nonzero when its specified row map is nonzero.
Both premises are retained in `etaMaps` and `pageData`; this is not an
unconditional realization theorem for Example 2.11. -/
theorem etaTable_differential_ne_zero
    {stable : StableHomotopyContext} {X Y : stable.Spectrum}
    {source : ClassicalAdamsSS stable X} {target : ClassicalAdamsSS stable Y}
    (etaMaps : EtaExtensionMaps source target etaESSDifferentials)
    (pageData : EtaExtensionDifferentials etaMaps etaESSDifferentials)
    (id : EtaDifferentialIndex) :
    pageData.d id.row.length id.row.sourceDegree id.row.targetDegree ≠ 0 := by
  rw [pageData.row id.row (EtaDifferentialIndex.row_mem_etaESSDifferentials id)]
  exact etaMaps.rowMap_nonzero id.row
    (EtaDifferentialIndex.row_mem_etaESSDifferentials id)

end KIP126.Classical.ExtensionSS
