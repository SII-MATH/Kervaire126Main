module

public import KIP126.Def.ClassicalAdams.TowerNaturality.Morphism.Proofs
public import KIP126.Def.SpectralSequence.Computation.Proofs
public import KIP126.Def.SpectralSequence.Basic.Category.Proofs

@[expose] public section

namespace KIP126.Classical.Adams
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
set_option backward.isDefEq.respectTransparency false
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : 𝟙_ C ⟶ H)
  {X Y : C} (f : X ⟶ Y)

/-- The SSData E₂ map agrees with the constructed quotient-page map. -/
theorem adamsInternalE2Induced_coordinates (p : ℤ × ℤ)
    (x : (adamsTowerInternalSpectralSequence unit X).Page 2 p) :
    (adamsTowerSSDataPageIso unit Y p.1 p.2 0).hom
        (adamsInternalE2Induced unit f p x) =
      adamsPageInduced unit f 2 (by decide) p.1 p.2
        ((adamsTowerSSDataPageIso unit X p.1 p.2 0).hom x) := by
  change (adamsTowerSSDataPageIso unit Y p.1 p.2 0).toLinearEquiv
    ((adamsTowerSSDataPageIso unit Y p.1 p.2 0).toLinearEquiv.symm _) = _
  exact LinearEquiv.apply_symm_apply _ _

end KIP126.Classical.Adams
