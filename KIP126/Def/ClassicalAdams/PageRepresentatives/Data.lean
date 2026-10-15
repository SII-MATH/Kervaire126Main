module

public import KIP126.Def.ClassicalAdams.TowerSSData.Sequence.Data
public import KIP126.Def.StableHomotopy.Cohomology.Data

@[expose] public section

/-!
# The paper's cycle and boundary submodules of actual Adams E₂

The tower's raw ambient module is the kernel of its first differential.
It is not E₂: its initial boundary module still has to be divided out.
The paper's Z₁ = E₂ and B₁ = 0 therefore use images under the initial
quotient map, as well as a shift of the raw cycle/boundary index.
-/

namespace KIP126.Classical.Adams.PageRepresentatives

open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology

universe u v
noncomputable section

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  (H : Mod2EilenbergMacLane (C := C)) (X : C)

/-- The common class labels are elements of the actual second page. -/
abbrev Ambient (p : ℤ × ℤ) :=
  (adamsTowerInternalSpectralSequence H.unit X).Page 2 p

/-- A raw cycle representative projected to E₂. -/
def cycleMap (n : WithTop ℕ) (p : ℤ × ℤ) :
    Subobject.underlying.obj
      (((adamsTowerInternalSpectralSequence H.unit X).ssData p).Z n) ⟶
        Ambient H X p :=
  let D := (adamsTowerInternalSpectralSequence H.unit X).ssData p
  Subobject.ofLE (D.Z n) (D.Z 0) (D.Z_anti bot_le) ≫ D.pageπ 0

/-- A raw boundary representative projected to E₂. -/
def boundaryMap (n : WithTop ℕ) (p : ℤ × ℤ) :
    Subobject.underlying.obj
      (((adamsTowerInternalSpectralSequence H.unit X).ssData p).B n) ⟶
        Ambient H X p :=
  let D := (adamsTowerInternalSpectralSequence H.unit X).ssData p
  Subobject.ofLE (D.B n) (D.Z 0)
    ((D.B_le_Z n).trans (D.Z_anti bot_le)) ≫ D.pageπ 0

/-- Paper Z_c consists of E₂ classes surviving the differentials through d_c.
The intended range is c ≥ 1; the predicate `IsCycle` records that range. -/
def cycles (level : ℤ) (p : ℤ × ℤ) : Submodule ℤ (Ambient H X p) :=
  LinearMap.range (cycleMap H X (↑(level - 1).toNat) p).hom

/-- Paper B_c consists of E₂ classes killed through page c. -/
def boundaries (level : ℤ) (p : ℤ × ℤ) : Submodule ℤ (Ambient H X p) :=
  LinearMap.range (boundaryMap H X (↑(level - 1).toNat) p).hom

/-- E₂ classes with an actual common Z∞ representative. Nonzero is not required. -/
def permanentCycles (p : ℤ × ℤ) : Submodule ℤ (Ambient H X p) :=
  LinearMap.range (cycleMap H X ⊤ p).hom

end
end KIP126.Classical.Adams.PageRepresentatives
