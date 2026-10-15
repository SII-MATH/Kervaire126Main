module

public import KIP126.Def.Synthetic.MapFiltration.Proofs
public import KIP126.Def.SpectralSequence.BoundedExtension.UnderlyingComplex.Data
public import KIP126.Def.SpectralSequence.FilteredComplex.Solutions.Data
public import KIP126.Def.Synthetic.PageExtension.Relation.Data

@[expose] public section

/-! The actual two-term filtered complex of a synthetic map, without a
globally bounded filtration. Finite extension equations and their complete
indeterminacy are meaningful even for an untruncated sphere (π₀ is 2-adic).
This does not claim strong convergence of an unbounded ESS. -/
namespace KIP126.Synthetic.SpectralSequence
open CategoryTheory KIP126.SpectralSequence
open KIP126.StableHomotopy KIP126.Synthetic.Context
universe u v
noncomputable section
variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]
  [HasFunctorialCofiber (C := Syn)] {H : Syn} (unit : S_0_0 ⟶ H)

def extensionComplex {X Y : Syn} (g : X ⟶ Y) (p : ℤ × ℤ) :
    FilteredComplex (ModuleCat.{v} ℤ) :=
  underlyingComplex (syntheticHomotopyMap g) (homotopyMap_filtration_compatible unit g) p

/-- E₀ comparison at the source term of this very two-term complex. -/
def extensionSourceIso {F : SyntheticAdamsFamily Syn} {X Y : Syn} (g : X ⟶ Y)
    (c : TowerConvergence unit F X) (p : ℤ × ℤ) (s : ℤ) :
    ((F.obj X).sequence.ssData (s, p.1 + s, p.2)).eInfty ≅
      (extensionComplex unit g p).assocGraded s 1 :=
  c.identification (s, p.1 + s, p.2) ≪≫ eqToIso (by
    change (towerFiltration unit X).associatedGraded s (p.1 + s - s, p.2) = _
    rw [show p.1 + s - s = p.1 by omega]
    rfl)

def extensionTargetIso {F : SyntheticAdamsFamily Syn} {X Y : Syn} (g : X ⟶ Y)
    (c : TowerConvergence unit F Y) (p : ℤ × ℤ) (s : ℤ) :
    ((F.obj Y).sequence.ssData (s, p.1 + s, p.2)).eInfty ≅
      (extensionComplex unit g p).assocGraded s 0 :=
  c.identification (s, p.1 + s, p.2) ≪≫ eqToIso (by
    change (towerFiltration unit Y).associatedGraded s (p.1 + s - s, p.2) = _
    rw [show p.1 + s - s = p.1 by omega]
    rfl)
end
end KIP126.Synthetic.SpectralSequence
