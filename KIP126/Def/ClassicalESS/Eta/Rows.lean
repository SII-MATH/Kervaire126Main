module

public import KIP126.Def.ClassicalESS.Eta.Data

@[expose] public section

/-! Adams representatives indexed by an arbitrary family of η-extension rows.
The row family specifies the bidegrees; its realization by spectral-sequence
differentials is a separate condition. -/
namespace KIP126.Classical.ExtensionSS

open KIP126.Classical.Adams

/-- Source and target Adams classes in the bidegrees of one specified row. -/
structure EtaClassPair {stable : StableHomotopyContext}
    {X Y : stable.Spectrum}
    (source : ClassicalAdamsSS stable X)
    (target : ClassicalAdamsSS stable Y)
    (row : EtaDifferential) where
  sourceClass : AdamsClass source
  targetClass : AdamsClass target
  sourceClass_degree : sourceClass.degree = row.sourceDegree
  targetClass_degree : targetClass.degree = row.targetDegree

/-- A degree-(1,2) η class and representatives for an indexed family of rows.
No equality with a particular finite table or differential assertion is included. -/
structure EtaClassFamily {stable : StableHomotopyContext}
    {X Y : stable.Spectrum}
    (source : ClassicalAdamsSS stable X)
    (target : ClassicalAdamsSS stable Y)
    (ι : Type) (row : ι → EtaDifferential) where
  eta : AdamsClass source
  eta_degree : eta.degree = (1, 2)
  typedRow : (id : ι) → EtaClassPair source target (row id)

namespace EtaClassFamily

variable {stable : StableHomotopyContext} {X Y : stable.Spectrum}
  {source : ClassicalAdamsSS stable X} {target : ClassicalAdamsSS stable Y}
  {ι : Type} {row : ι → EtaDifferential}

/-- The source representative specified by a row index. -/
def sourceClass (data : EtaClassFamily source target ι row) (id : ι) :
    AdamsClass source :=
  (data.typedRow id).sourceClass

/-- The target representative specified by a row index. -/
def targetClass (data : EtaClassFamily source target ι row) (id : ι) :
    AdamsClass target :=
  (data.typedRow id).targetClass

end EtaClassFamily
end KIP126.Classical.ExtensionSS
