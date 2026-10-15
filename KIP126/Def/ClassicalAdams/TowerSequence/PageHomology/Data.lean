module

public import KIP126.Def.ClassicalAdams.TowerSequence.PagePassage.Proofs

@[expose] public section

/-!
# Homology of the actual Adams quotient pages

The tower's page-passage quotient map identifies the homology of each page
with the next page. This comparison applies to both the nested-subobject and
Mathlib presentations of the Adams spectral sequence.
-/

namespace KIP126.Classical.Adams

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {H : C} (unit : 𝟙_ C ⟶ H) (X : C)

/-- The page-passage isomorphism obtained by inverting the specified quotient map. -/
def adamsPageHomologyIso (r : ℕ) (hr : 1 ≤ r) (p : ℤ × ℤ) :
    (adamsPageComplex unit X r hr).homology p ≅
      adamsPageObject unit X (r + 1) (by omega) p :=
  ((adamsPageComplex unit X r hr).sc p).moduleCatHomologyIso ≪≫
    (LinearEquiv.ofBijective (adamsNextPageToHomology unit X r hr p)
      (adamsNextPageToHomology_bijective unit X r hr p)).toModuleIso.symm

end

end KIP126.Classical.Adams
