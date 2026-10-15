module

public import KIP126.Def.ClassicalAdams.Detection.Proofs

@[expose] public section

namespace KIP126.Classical.Adams.TowerDetection
open CategoryTheory CategoryTheory.MonoidalCategory KIP126.StableHomotopy
open KIP126.SpectralSequence
universe u v
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : 𝟙_ C ⟶ H)
def filtration (X : C) : Filtration (homotopy X) where
  F s n := (ModuleCat.subobjectModule _).symm (filtrationSubmodule unit X s n)
  mono s n := (ModuleCat.subobjectModule _).symm.monotone
    (filtrationSubmodule_antitone unit X n (by omega : s ≤ s + 1))

/-- One representative in the intersection of ALL actual tower cycles. -/
abbrev InfiniteRepresentative (X : C) (p : ℤ × ℤ) :=
  (Subobject.underlying.obj
    (((adamsTowerInternalSpectralSequence unit X).ssData p).Z ⊤) : ModuleCat ℤ)

/-- Forget the cycle membership, retaining the original cofiber-layer class
in E₁.  The internal ambient object is the actual Z₂ submodule of E₁. -/
def infiniteRepresentativeE1 (X : C) (p : ℤ × ℤ)
    (z : InfiniteRepresentative unit X p) : adamsE1 unit X p.1 p.2 :=
  ((((adamsTowerInternalSpectralSequence unit X).ssData p).Z ⊤).arrow z).val

end
end KIP126.Classical.Adams.TowerDetection
