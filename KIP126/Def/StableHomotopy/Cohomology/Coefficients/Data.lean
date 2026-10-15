module

public import KIP126.Def.StableHomotopy.Cohomology.Coefficients.Basic.Proofs
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Module.ZMod

@[expose] public section

/-! Mod-two scalar structures derived from the specified H-ring and additive tensor.
No page, differential, scalar action, or Milnor coordinates are postulated. -/

namespace KIP126.StableHomotopy.Cohomology

noncomputable section

open CategoryTheory MonoidalCategory KIP126.Classical.Adams

universe u v

set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  (H : Mod2EilenbergMacLane (C := C))

variable [MonoidalPreadditive C] (R : Mod2RingStructure H)

/-- The canonical F₂ action on the existing homology group, derived from two-torsion.
This is an explicit local structure, not a globally selected instance. -/
abbrev mod2HomologyModule (n : ℤ) (X : C) : Module (ZMod 2) (Mod2Homology H n X) :=
  AddCommGroup.zmodModule (mod2Homology_two_nsmul_zero H R n X)

/-- The F₂ action on the coefficient spectrum's actual πₙ. Keeping this
separate from `mod2CohomologyModule` prevents a cohomological sign change
from silently regrading coefficient and cooperation calculations. -/
abbrev mod2HF2HomotopyModule (n : ℤ) : Module (ZMod 2) (HomotopyGroup n H.HF2) :=
  AddCommGroup.zmodModule (mod2HF2Homotopy_two_nsmul_zero H R n)

/-- The specified π₀ coordinate is automatically linear for the derived scalars. -/
def mod2Pi0LinearEquiv :
    letI := mod2HF2HomotopyModule H R 0
    HomotopyGroup 0 H.HF2 ≃ₗ[ZMod 2] ZMod 2 :=
  letI := mod2HF2HomotopyModule H R 0
  { H.pi0Equiv with map_smul' := ZMod.map_smul H.pi0Equiv }

/-- The actual cooperation counit, now F₂-linear without any polynomial coordinates. -/
def cooperationCounitF2 (n : ℤ) :
    letI := mod2HomologyModule H R n H.HF2
    letI := mod2HF2HomotopyModule H R n
    Mod2Cooperations H n →ₗ[ZMod 2] HomotopyGroup n H.HF2 :=
  letI := mod2HomologyModule H R n H.HF2
  letI := mod2HF2HomotopyModule H R n
  (cooperationCounit H R n).toZModLinearMap 2

/-- The existing homology group bundled with its derived F₂ scalar action. -/
def mod2HomologyF2 (n : ℤ) (X : C) : ModuleCat.{v} (ZMod 2) :=
  letI := mod2HomologyModule H R n X
  ModuleCat.of (ZMod 2) (Mod2Homology H n X)

/-- The original pushforward, now F₂-linear; its underlying function is unchanged. -/
def mod2HomologyF2Map {X Y : C} (f : X ⟶ Y) (n : ℤ) :
    mod2HomologyF2 H R n X ⟶ mod2HomologyF2 H R n Y :=
  letI := mod2HomologyModule H R n X
  letI := mod2HomologyModule H R n Y
  ModuleCat.ofHom ((Mod2Homology.pushforward H f n).toZModLinearMap 2)

end

end KIP126.StableHomotopy.Cohomology
