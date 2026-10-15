module

public import KIP126.Def.StableHomotopy.Context.Proofs

import all KIP126.Def.StableHomotopy.Context.Proofs

@[expose] public section

namespace KIP126.StableHomotopy

open CategoryTheory

universe u v

set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [StableHomotopyCategory.{u, v} C]

/-- Naturality of the connecting homomorphism from its last triangle square.
The other squares are unnecessary for this identity of represented maps. -/
theorem connectingHomomorphism_naturality (T U : HoCofiberSequence (C := C))
    (a : T.X ⟶ U.X) (c : T.Z ⟶ U.Z)
    (h : c ≫ U.h = T.h ≫ a⟦(1 : ℤ)⟧') (n : ℤ) (z : HomotopyGroup n T.Z) :
    connectingHomomorphism U n (inducedMap c n z) =
      inducedMap a (n - 1) (connectingHomomorphism T n z) := by
  simp only [connectingHomomorphism, inducedMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    Functor.id_obj, eqToHom_refl, Category.id_comp, Category.comp_id]
  change (shiftFunctorAdd' C n (-1) (n - 1) (by omega)).hom.app SphereSpectrum ≫
    (shiftFunctor C (-1)).map ((z ≫ c) ≫ U.h) ≫
      (shiftFunctorCompIsoId C 1 (-1) (by omega)).hom.app U.X =
    ((shiftFunctorAdd' C n (-1) (n - 1) (by omega)).hom.app SphereSpectrum ≫
      (shiftFunctor C (-1)).map (z ≫ T.h) ≫
        (shiftFunctorCompIsoId C 1 (-1) (by omega)).hom.app T.X) ≫ a
  rw [Category.assoc z c, h, ← Category.assoc z T.h, Functor.map_comp]
  have hn := (shiftFunctorCompIsoId C 1 (-1) (by omega)).hom.naturality a
  change (shiftFunctor C (-1)).map (a⟦(1 : ℤ)⟧') ≫ _ = _ ≫ a at hn
  simpa only [Category.assoc] using congrArg
    (fun f => (shiftFunctorAdd' C n (-1) (n - 1) (by omega)).hom.app SphereSpectrum ≫
      (shiftFunctor C (-1)).map (z ≫ T.h) ≫ f) hn

/-- Reindexing the degree commutes with postcomposition on represented homotopy. -/
theorem inducedMap_cast {X Y : C} (f : X ⟶ Y) {n m : ℤ} (h : n = m)
    (x : HomotopyGroup n X) :
    inducedMap f m (LinearEquiv.cast (R := ℤ) (M := fun i => HomotopyGroup i X) h x) =
      LinearEquiv.cast (R := ℤ) (M := fun i => HomotopyGroup i Y) h (inducedMap f n x) := by
  subst m
  rfl

end KIP126.StableHomotopy
