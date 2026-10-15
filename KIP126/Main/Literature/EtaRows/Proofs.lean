module

public import KIP126.Literature.EtaExtension.Classes

@[expose] public section

namespace KIP126.Classical.ExtensionSS

open KIP126.Classical.Adams


namespace EtaDifferentialIndex

@[simp] theorem all_length : all.length = 5 := rfl

@[simp] theorem mem_all (id : EtaDifferentialIndex) : id ∈ all := by
  cases id <;> simp [all]

/-- Every stable identity selects a row in the existing eta-ESS catalogue. -/
theorem row_mem_etaESSDifferentials (id : EtaDifferentialIndex) :
    id.row ∈ etaESSDifferentials := by
  cases id <;> simp [row, etaESSDifferentials]

/-- The stable identities enumerate exactly the existing five-row catalogue. -/
theorem range_row : Set.range row = etaESSDifferentials := by
  ext differential
  constructor
  · rintro ⟨id, rfl⟩
    exact row_mem_etaESSDifferentials id
  · intro h
    simp only [etaESSDifferentials, Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with h | h | h | h | h
    · exact ⟨.d₁, h.symm⟩
    · exact ⟨.d₂, h.symm⟩
    · exact ⟨.d₃, h.symm⟩
    · exact ⟨.d₄, h.symm⟩
    · exact ⟨.d₂Inessential, h.symm⟩

end EtaDifferentialIndex

namespace EtaExtensionClasses

variable {stable : StableHomotopyContext} {X Y : stable.Spectrum}
  {source : ClassicalAdamsSS stable X} {target : ClassicalAdamsSS stable Y}

@[simp] theorem sourceClass_degree (data : EtaExtensionClasses source target)
    (id : EtaDifferentialIndex) :
    (data.sourceClass id).degree = id.row.sourceDegree :=
  (data.typedRow id).sourceClass_degree

@[simp] theorem targetClass_degree (data : EtaExtensionClasses source target)
    (id : EtaDifferentialIndex) :
    (data.targetClass id).degree = id.row.targetDegree :=
  (data.typedRow id).targetClass_degree

/-- The specified η-extension classes satisfy the five-row differential table. -/
theorem evidence_claim (data : EtaExtensionClasses source target) :
    KIP126.Classical.ExtensionSS.EtaTable.IsEtaDifferentialTable etaESSDifferentials :=
  data.evidence

end EtaExtensionClasses

end KIP126.Classical.ExtensionSS
