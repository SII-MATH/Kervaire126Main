module

public import KIP126.Def.ClassicalAdams.PageRepresentatives.Data
public import KIP126.Def.SpectralSequence.Computation.Predicates

@[expose] public section

namespace KIP126.Classical.Adams.PageRepresentatives

open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology

universe u v
noncomputable section

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  (H : Mod2EilenbergMacLane (C := C)) (X : C)

/-- Membership in paper Z_c, with its valid index range explicit. -/
def IsCycle (level : ℤ) (p : ℤ × ℤ) (x : Ambient H X p) : Prop :=
  1 ≤ level ∧ x ∈ cycles H X level p

/-- Membership in paper B_c; this does not assert a nonzero incoming hit. -/
def IsBoundary (level : ℤ) (p : ℤ × ℤ) (x : Ambient H X p) : Prop :=
  1 ≤ level ∧ x ∈ boundaries H X level p

/-- A common infinite-cycle representative, allowing the zero class. -/
def IsPermanent (p : ℤ × ℤ) (x : Ambient H X p) : Prop :=
  x ∈ permanentCycles H X p

/-- Equality modulo the actual paper boundary submodule. -/
def Congruent (level : ℤ) (p : ℤ × ℤ) (x y : Ambient H X p) : Prop :=
  IsBoundary H X level p (x - y)

/-- The actual Adams differential on common E₂ labels, with the degree
transport checked by `HasDifferential`. It is never a freely chosen operation. -/
def DifferentialAt (r : ℤ) (p q : ℤ × ℤ)
    (x : Ambient H X p) (y : Ambient H X q) : Prop :=
  2 ≤ r ∧ KIP126.SpectralSequence.HasDifferential
    (adamsTowerInternalSpectralSequence H.unit X) r p q x y

/-- MainPaper Definition `classicalcrossdiff`: a crossing of a length-r
Adams differential beginning at p, viewed on page `page`. Its witness is an
essential differential in the actual Adams sequence, with the same stems.
This is distinct from the direction used in Moss's theorem. -/
def HasCrossingOn (r page : ℤ) (p : ℤ × ℤ) : Prop :=
  ∃ a b : ℤ, 0 < a ∧ a ≤ page - 2 ∧ 0 ≤ b ∧ b ≤ r - page ∧
    ∃ (x : Ambient H X (p.1 + a, p.2 + a))
      (y : Ambient H X (p.1 + r - b, p.2 + r - b - 1)),
      KIP126.SpectralSequence.HasNonzeroDifferential
        (adamsTowerInternalSpectralSequence H.unit X) (r - a - b)
        (p.1 + a, p.2 + a) (p.1 + r - b, p.2 + r - b - 1) x y

/-- Absence of paper-direction crossings in the stated, valid page range. -/
def NoCrossingOn (r page : ℤ) (p : ℤ × ℤ) : Prop :=
  2 ≤ page ∧ page ≤ r ∧ ¬ HasCrossingOn H X r page p

end
end KIP126.Classical.Adams.PageRepresentatives
