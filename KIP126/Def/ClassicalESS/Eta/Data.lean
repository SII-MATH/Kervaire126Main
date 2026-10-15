module

public import KIP126.Def.ClassicalAdams.SphereSequence.Data
public import KIP126.Def.SpectralSequence.PageLevel.Data

public import Mathlib.Algebra.Homology.SpectralSequence.Basic

@[expose] public section

/-!
# Interfaces for classical η-extension spectral sequences

The classical η-extension spectral sequence has differential degree `(n,n)`.
The row set is an explicit parameter. Page differentials act on the specified
source and target E∞ groups; no finite table or instance of these data is
chosen here.
-/

namespace KIP126.Classical.ExtensionSS

open CategoryTheory CategoryTheory.Limits
open KIP126.Classical.Adams
open KIP126.Algebra
open KIP126.SpectralSequence


abbrev Index := Bidegree
abbrev Coeff := F2ModuleCat

/-- The `(n,n)` differential shape of a classical eta-ESS page. -/
def etaESSShape (n : ℤ) : ComplexShape Index := ComplexShape.up' (n, n)

/-- 把扩张长度送入 Mathlib 所需的整数页形状。 -/
def etaESSShapeAt (n : ExtensionLength) : ComplexShape Index :=
  etaESSShape n.toInt

def etaESSPageLevel : PageLevelConvention where
  firstPage := 0
  admissibleFrom := 0
  page := fun r => r
  cycleLevel := fun r => r
  quotientExponent := fun r => r
  page_first := by norm_num
  page_succ := by intro r; norm_num
  cycle_succ := by intro r; norm_num
  quotient_succ := by intro r; norm_num
  cycleLevel_eq_quotientExponent := by intro r; rfl

/-- One named finite eta-ESS differential with its mathematical degrees. -/
structure EtaDifferential where
  source : String
  target : String
  length : ℕ
  sourceDegree : Index
  targetDegree : Index
  sourceFiltration : ℤ
  targetFiltration : ℤ
  essential : Bool
  deriving DecidableEq, Repr, Inhabited

/-! ### η-extension maps and page differentials -/

structure EtaExtensionMaps {stable : StableHomotopyContext}
    {X Y : stable.Spectrum}
    (source : ClassicalAdamsSS stable X)
    (target : ClassicalAdamsSS stable Y)
    (rows : Set EtaDifferential) where
  sourceInfinity : GradedObject Index Coeff
  targetInfinity : GradedObject Index Coeff
  eta : AdamsClass source
  sourceClass : EtaDifferential → AdamsClass source
  targetClass : EtaDifferential → AdamsClass target
  sourceClass_degree : ∀ row, (sourceClass row).degree = row.sourceDegree
  targetClass_degree : ∀ row, (targetClass row).degree = row.targetDegree
  etaMap : ∀ b, sourceInfinity b ⟶ targetInfinity b
  rowMap : ∀ row : EtaDifferential,
    sourceInfinity row.sourceDegree ⊞ targetInfinity row.sourceDegree ⟶
      sourceInfinity row.targetDegree ⊞ targetInfinity row.targetDegree
  rowMap_nonzero : ∀ row, row ∈ rows → rowMap row ≠ 0

noncomputable def E₀ {stable : StableHomotopyContext} {X Y : stable.Spectrum}
    {source : ClassicalAdamsSS stable X} {target : ClassicalAdamsSS stable Y}
    {rows : Set EtaDifferential}
    (A : EtaExtensionMaps source target rows) : GradedObject Index Coeff :=
  fun b => A.sourceInfinity b ⊞ A.targetInfinity b

/-! The page differentials act between the specified source and target Adams
E∞ groups; `rowMap` records their values on the η-extension classes. -/

structure EtaExtensionDifferentials {stable : StableHomotopyContext}
    {X Y : stable.Spectrum}
    {source : ClassicalAdamsSS stable X}
    {target : ClassicalAdamsSS stable Y}
    {rows : Set EtaDifferential}
    (etaMaps : EtaExtensionMaps source target rows)
    (differentials : Set EtaDifferential) where
  d : ∀ (_n : ℤ) (i j : Index), E₀ etaMaps i ⟶ E₀ etaMaps j
  shape : ∀ (_n : ℤ) (i j : Index), ¬(etaESSShape _n).Rel i j → d _n i j = 0
  d_comp_d : ∀ (n : ℤ) (i j k : Index), d n i j ≫ d n j k = 0
  row : ∀ (row : EtaDifferential), row ∈ differentials →
    d row.length row.sourceDegree row.targetDegree = etaMaps.rowMap row

noncomputable def etaPage {stable : StableHomotopyContext}
    {X Y : stable.Spectrum}
    {source : ClassicalAdamsSS stable X}
    {target : ClassicalAdamsSS stable Y}
    {rows : Set EtaDifferential}
    {etaMaps : EtaExtensionMaps source target rows}
    {differentials : Set EtaDifferential}
    (pageData : EtaExtensionDifferentials etaMaps differentials) (n : ℤ) :
    HomologicalComplex Coeff (etaESSShape n) where
  X := E₀ etaMaps
  d := pageData.d n
  shape := pageData.shape n
  d_comp_d' := by intro i j k hij hjk; exact pageData.d_comp_d n i j k

abbrev ClassicalEtaESS := SpectralSequence Coeff etaESSShape 0

def differentialDegree (n : ExtensionLength) : Index := (n.toInt, n.toInt)

end KIP126.Classical.ExtensionSS
