module

public import KIP126.Def.ClassicalAdams.TowerNaturality.Layer.Proofs
public import KIP126.Def.ClassicalAdams.TowerSSData.Sequence.Data

@[expose] public section

namespace KIP126.Classical.Adams
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
universe u v
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : 𝟙_ C ⟶ H)
  {X Y : C} (f : X ⟶ Y)

/-- Restriction of the actual layer map to r-cycles. -/
def adamsCycleInduced (r : ℕ) (hr : 1 ≤ r) (s t : ℤ) :
    adamsCycles unit X r hr s t →ₗ[ℤ] adamsCycles unit Y r hr s t :=
  ((adamsE1Induced unit f s t).comp (adamsCycles unit X r hr s t).subtype).codRestrict
    (adamsCycles unit Y r hr s t)
    (fun a => adamsE1Induced_mem_cycles unit f r hr s t a.property)

/-- The spectrum map induces a map of actual quotient pages. -/
def adamsPageInduced (r : ℕ) (hr : 1 ≤ r) (s t : ℤ) :
    adamsPage unit X r hr s t →ₗ[ℤ] adamsPage unit Y r hr s t :=
  (adamsCycleBoundaries unit X r hr s t).mapQ
    (adamsCycleBoundaries unit Y r hr s t) (adamsCycleInduced unit f r hr s t) (by
      intro a ha
      exact adamsE1Induced_mem_boundaries unit f r hr s t ha)

/-- The induced E₂ map in the internal SSData representation, transported
through the proved identity-on-representatives quotient comparisons. -/
def adamsInternalE2Induced (p : ℤ × ℤ) :
    (adamsTowerInternalSpectralSequence unit X).Page 2 p →ₗ[ℤ]
      (adamsTowerInternalSpectralSequence unit Y).Page 2 p :=
  (adamsTowerSSDataPageIso unit Y p.1 p.2 0).inv.hom.comp
    ((adamsPageInduced unit f 2 (by decide) p.1 p.2).comp
      (adamsTowerSSDataPageIso unit X p.1 p.2 0).hom.hom)

end
end KIP126.Classical.Adams
