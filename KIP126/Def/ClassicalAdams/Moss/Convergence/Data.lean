module

public import KIP126.Def.ClassicalAdams.Moss.Mapping.Proofs
public import KIP126.Def.SpectralSequence.Convergence.Data

@[expose] public section

/-! Convergence data with the sequence, abutment and filtration already fixed. -/

namespace KIP126.Classical.Adams.Moss

open CategoryTheory CategoryTheory.MonoidalCategory KIP126.StableHomotopy
open KIP126.SpectralSequence

universe u v
noncomputable section

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] [MonoidalClosed C]
  {H : C} (unit : 𝟙_ C ⟶ H)

/-- The decreasing filtration is the image of the actual tower projections. -/
def mappingFiltration (X Y : C) : Filtration (mappingAbutment X Y) where
  F s n := (ModuleCat.subobjectModule _).symm (mappingFiltrationSubmodule unit X Y s n)
  mono s n := (ModuleCat.subobjectModule _).symm.monotone
    (mappingFiltrationSubmodule_antitone unit X Y n (by omega : s ≤ s + 1))

/-- A convergence input for this fixed mapping Adams tower. It supplies only
the missing E∞ identification; the filtered target and regrading are fixed. -/
structure MappingAdamsConvergence (X Y : C) where
  identification : ∀ k : ℤ × ℤ,
    ((mappingSequence unit X Y).ssData k).eInfty ≅
      (mappingFiltration unit X Y).associatedGraded k.1 (k.2 - k.1)

/-- The generic convergence API applied to the same objects and filtration. -/
def MappingAdamsConvergence.toConvergence {X Y : C}
    (c : MappingAdamsConvergence unit X Y) :
    Convergence (mappingSequence unit X Y) (mappingAbutment X Y)
      (mappingFiltration unit X Y) where
  reindex k := (k.1, k.2 - k.1)
  reindex_bijective := by
    constructor
    · rintro ⟨s, t⟩ ⟨s', t'⟩ h
      simp only [Prod.mk.injEq] at h ⊢
      exact ⟨h.1, by omega⟩
    · rintro ⟨s, n⟩
      exact ⟨(s, n + s), by simp⟩
  iso := c.identification

end
end KIP126.Classical.Adams.Moss
