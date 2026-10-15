module

public import KIP126.Def.ClassicalESS.Eta.Rows
public import KIP126.Literature.EtaExtension.Table

@[expose] public section

/-! Typed representatives for the five η-extension rows of Example 2.11.
The class records specify representatives and degrees. Their `evidence` field
is only equality with the transcribed table, not a proof of actual differentials. -/
namespace KIP126.Classical.ExtensionSS

open KIP126.Classical.Adams

/-- Indices for the five specified η-extension differentials. -/
inductive EtaDifferentialIndex
  | d₁
  | d₂
  | d₃
  | d₄
  | d₂Inessential
  deriving DecidableEq, Repr, Inhabited

namespace EtaDifferentialIndex

/-- The canonical existing differential selected by a stable row identity. -/
def row : EtaDifferentialIndex → EtaDifferential
  | .d₁ => etaD₁
  | .d₂ => etaD₂
  | .d₃ => etaD₃
  | .d₄ => etaD₄
  | .d₂Inessential => etaD₂Inessential

/-- The five row identities in their canonical table order. -/
def all : List EtaDifferentialIndex := [.d₁, .d₂, .d₃, .d₄, .d₂Inessential]

end EtaDifferentialIndex

/-- The generic degree-constrained class pair at one row of Example 2.11. -/
abbrev EtaExtensionClassPair {stable : StableHomotopyContext}
    {X Y : stable.Spectrum}
    (source : ClassicalAdamsSS stable X)
    (target : ClassicalAdamsSS stable Y)
    (id : EtaDifferentialIndex) :=
  EtaClassPair source target id.row

/-- The η class and representatives of the five transcribed rows.
The table equality records the chosen catalogue; it supplies no additional
spectral-sequence differential or nonvanishing result. -/
structure EtaExtensionClasses {stable : StableHomotopyContext}
    {X Y : stable.Spectrum}
    (source : ClassicalAdamsSS stable X)
    (target : ClassicalAdamsSS stable Y)
    extends EtaClassFamily source target EtaDifferentialIndex EtaDifferentialIndex.row where
  evidence : EtaTable.IsEtaDifferentialTable etaESSDifferentials

namespace EtaExtensionClasses

variable {stable : StableHomotopyContext} {X Y : stable.Spectrum}
  {source : ClassicalAdamsSS stable X} {target : ClassicalAdamsSS stable Y}

/-- The typed source representative of a canonical row. -/
def sourceClass (data : EtaExtensionClasses source target) (id : EtaDifferentialIndex) :
    AdamsClass source :=
  (data.typedRow id).sourceClass

/-- The typed target representative of a canonical row. -/
def targetClass (data : EtaExtensionClasses source target) (id : EtaDifferentialIndex) :
    AdamsClass target :=
  (data.typedRow id).targetClass

end EtaExtensionClasses

end KIP126.Classical.ExtensionSS
