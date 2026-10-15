module

public import KIP126.Def.StableHomotopy.Context.Suspension.Data

@[expose] public section

namespace KIP126.StableHomotopy
open CategoryTheory
universe u v
set_option backward.isDefEq.respectTransparency false
variable {C : Type u} [StableHomotopyCategory.{u, v} C]

/-- The specified desuspension is bijective because shift is an equivalence. -/
theorem homotopyDesuspend_bijective (X : C) (n : ℤ) :
    Function.Bijective (homotopyDesuspend X n) := by
  let e := (shiftFunctorAdd' C n (-1) (n - 1) (by omega)).app SphereSpectrum
  let d := (shiftFunctorCompIsoId C 1 (-1) (by omega)).app X
  constructor
  · intro a b h
    change e.hom ≫ (shiftFunctor C (-1 : ℤ)).map a ≫ d.hom =
      e.hom ≫ (shiftFunctor C (-1 : ℤ)).map b ≫ d.hom at h
    apply (shiftFunctor C (-1 : ℤ)).map_injective
    apply (cancel_epi e.hom).mp
    apply (cancel_mono d.hom).mp
    simpa only [Category.assoc] using h
  · intro b
    refine ⟨(shiftFunctor C (-1 : ℤ)).preimage (e.inv ≫ b ≫ d.inv), ?_⟩
    change e.hom ≫ (shiftFunctor C (-1 : ℤ)).map
      ((shiftFunctor C (-1 : ℤ)).preimage _) ≫ d.hom = b
    rw [Functor.map_preimage]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.hom_inv_id_assoc]

/-- Desuspension commutes with the actual shifted target map. -/
theorem homotopyDesuspend_postcompose {X Y : C} (f : X ⟶ Y) (n : ℤ)
    (a : HomotopyGroup n (X⟦(1 : ℤ)⟧)) :
    homotopyDesuspend Y n (a ≫ f⟦(1 : ℤ)⟧') = homotopyDesuspend X n a ≫ f := by
  change _ ≫ (shiftFunctor C (-1 : ℤ)).map (a ≫ f⟦(1 : ℤ)⟧') ≫ _ = _
  rw [Functor.map_comp]
  have h := (shiftFunctorCompIsoId C 1 (-1) (by omega)).hom.naturality f
  change (shiftFunctor C (-1 : ℤ)).map (f⟦(1 : ℤ)⟧') ≫ _ = _ ≫ f at h
  simp only [Category.assoc]
  rw [h]
  simp only [homotopyDesuspend, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Category.assoc]

end KIP126.StableHomotopy
