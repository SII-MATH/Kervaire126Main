module

public import KIP126.Def.ClassicalAdams.TowerHomology.FirstDifferential.Data
public import KIP126.Def.StableHomotopy.Cohomology.Coaction.Unit.Proofs
public import KIP126.Def.StableHomotopy.Context.Connecting.Proofs

import all KIP126.Def.StableHomotopy.Context.Proofs

@[expose] public section

namespace KIP126.Classical.Adams

noncomputable section

open CategoryTheory MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology

universe u v

set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C))

/-- The general connecting construction agrees with the actual resolution boundary. -/
theorem adamsResolutionSequence_connecting (X : C) (n : ℤ)
    (x : Mod2Homology H n X) :
    connectingHomomorphism (adamsResolutionSequence H X) n x =
      adamsResolutionBoundary H.unit X 0 n x := by
  simp only [connectingHomomorphism, adamsResolutionSequence, adamsResolutionBoundary,
    AddMonoidHom.coe_mk, ZeroHom.coe_mk, Functor.id_obj,
    eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

/-- The bidegree form of the resolution differential is just degree reindexing
of the same representative differential at the actual stage `T_s`. -/
theorem adamsResolutionDifferential_eq_homologyD1 (X : C) (s : ℕ) (t : ℤ)
    (x : Mod2Homology H (t - s) (adamsTower H.unit X s)) :
    adamsResolutionDifferential H.unit X s t x =
      LinearEquiv.cast (R := ℤ)
        (M := fun n => Mod2Homology H n (adamsTower H.unit X (s + 1)))
        (show t - s - 1 = t - (s + 1 : ℕ) by omega)
        (adamsHomologyD1 H (adamsTower H.unit X s) (t - s) x) := by
  exact inducedMap_cast (adamsUnit H.unit (adamsTower H.unit X (s + 1)))
    (show t - s - 1 = t - (s + 1 : ℕ) by omega)
    (adamsResolutionBoundary H.unit X s (t - s) x)

/-- Link to the actual first quotient-page differential, without a coordinate input. -/
theorem adamsPageD_one_homologyD1 (X : C) (s : ℕ) (t : ℤ)
    (x : adamsPage H.unit X 1 le_rfl s t) :
    adamsPageOneHomologyEquiv H.unit X (s + 1) t
      ((adamsPageD H.unit X 1 le_rfl (s, t) ((s + 1 : ℕ), t)).hom x) =
        LinearEquiv.cast (R := ℤ)
          (M := fun n => Mod2Homology H n (adamsTower H.unit X (s + 1)))
          (show t - s - 1 = t - (s + 1 : ℕ) by omega)
          (adamsHomologyD1 H (adamsTower H.unit X s) (t - s)
            (adamsPageOneHomologyEquiv H.unit X s t x)) := by
  rw [adamsPageD_one_homology, adamsResolutionDifferential_eq_homologyD1]

omit [HasFunctorialCofiber (C := C)] in
/-- The free action removes the outer unit on represented homology. -/
theorem adamsHomologyAction_outerUnit (R : Mod2RingStructure H) (X : C) (n : ℤ)
    (x : Mod2Homology H n X) :
    adamsHomologyAction H R X n (mod2OuterUnitMap H X n x) = x := by
  change (x ≫ _) ≫ _ = x
  rw [Category.assoc, mod2FreeAction_outerUnit, Category.comp_id]

variable [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]
  [(mod2UnitNatTrans H).CommShift ℤ]

/-- The last square of the map from the actual unit triangle to its smash
with `H`; its commutativity is derived from unit naturality and shift coherence. -/
theorem adamsResolutionSequence_unit_last_square (X : C) :
    adamsUnit H.unit (H.HF2 ⊗ X) ≫ (adamsHomologySequence H X).h =
      (adamsResolutionSequence H X).h ≫
        (adamsUnit H.unit (fiber (adamsUnit H.unit X)))⟦(1 : ℤ)⟧' := by
  change adamsUnit H.unit (H.HF2 ⊗ X) ≫
    H.HF2 ◁ adamsResolutionConnecting H.unit X 0 ≫
      ((tensorLeft H.HF2).commShiftIso (1 : ℤ)).hom.app (fiber (adamsUnit H.unit X)) = _
  rw [← Category.assoc, mod2AdamsUnit_naturality, Category.assoc]
  erw [mod2Unit_shift H (fiber (adamsUnit H.unit X)) 1]
  rfl

/-- The first differential is the smashed connecting homomorphism after
outer unit insertion. This is proved, not a differential-compatibility input. -/
theorem adamsHomologyD1_eq_boundary_outerUnit (X : C) (n : ℤ)
    (x : Mod2Homology H n X) :
    adamsHomologyD1 H X n x =
      adamsHomologyBoundary H X n (mod2OuterUnitMap H X n x) := by
  change inducedMap (adamsUnit H.unit (fiber (adamsUnit H.unit X))) (n - 1)
    (adamsResolutionBoundary H.unit X 0 n x) =
      connectingHomomorphism (adamsHomologySequence H X) n
        (inducedMap (adamsUnit H.unit (H.HF2 ⊗ X)) n x)
  rw [← adamsResolutionSequence_connecting]
  exact (connectingHomomorphism_naturality (adamsResolutionSequence H X)
    (adamsHomologySequence H X) (adamsUnit H.unit (fiber (adamsUnit H.unit X)))
    (adamsUnit H.unit (H.HF2 ⊗ X)) (adamsResolutionSequence_unit_last_square H X) n x).symm

end

end KIP126.Classical.Adams
