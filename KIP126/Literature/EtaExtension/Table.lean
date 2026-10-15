module

public import KIP126.Def.ClassicalESS.Eta.Data

@[expose] public section

/-! The five η-extension rows transcribed from MainPaper Example 2.11.
The labels, lengths, bidegrees and essential flags are fixed source data.
This transcription does not assert that a chosen spectral sequence realizes
these differentials. -/
namespace KIP126.Classical.ExtensionSS

def etaD₁ : EtaDifferential :=
  { source := "h₅d₀", target := "h₁h₅d₀", length := 1
    sourceDegree := (5, 51), targetDegree := (6, 52)
    sourceFiltration := 5, targetFiltration := 6
    essential := true }

def etaD₂ : EtaDifferential :=
  { source := "Δh₁g", target := "d₀l", length := 2
    sourceDegree := (9, 55), targetDegree := (11, 57)
    sourceFiltration := 9, targetFiltration := 11
    essential := true }

def etaD₃ : EtaDifferential :=
  { source := "h₁g₂", target := "Δh₂c₁", length := 3
    sourceDegree := (5, 51), targetDegree := (8, 54)
    sourceFiltration := 5, targetFiltration := 8
    essential := true }

def etaD₄ : EtaDifferential :=
  { source := "h₃²h₅", target := "Mh₁", length := 4
    sourceDegree := (3, 49), targetDegree := (7, 53)
    sourceFiltration := 3, targetFiltration := 7
    essential := true }

def etaD₂Inessential : EtaDifferential :=
  { source := "h₀h₃²h₅", target := "h₁h₅d₀", length := 2
    sourceDegree := (4, 50), targetDegree := (6, 52)
    sourceFiltration := 4, targetFiltration := 6
    essential := false }

/-- The five specified η-extension differentials. -/
def etaESSDifferentials : Set EtaDifferential :=
  {etaD₁, etaD₂, etaD₃, etaD₄, etaD₂Inessential}

end KIP126.Classical.ExtensionSS

namespace KIP126.Classical.ExtensionSS.EtaTable

/-- Equality with the specified finite table of η-extension differentials. -/
def IsEtaDifferentialTable (rows : Set KIP126.Classical.ExtensionSS.EtaDifferential) : Prop :=
  rows = KIP126.Classical.ExtensionSS.etaESSDifferentials

end KIP126.Classical.ExtensionSS.EtaTable
