module

public import KIP126.Def.StableHomotopy.Cohomology.Cooperations.Kunneth.Data
public import KIP126.Def.ClassicalAdams.Coefficients.Data

@[expose] public section

namespace KIP126.Classical.Adams

noncomputable section

open CategoryTheory MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C] [MonoidalPreadditive C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)
  (K : Mod2CooperationKunneth H R)

/-- Multiplication compatibility, rather than a page-coordinate hypothesis,
identifies the action kernel with the tensor augmentation kernel. -/
theorem adamsHomologyKunneth_map_ker (X : C) (n : ℤ) :
    letI := mod2HomologyModule H R n X
    letI := mod2HomologyModule H R n (H.HF2 ⊗ X)
    (LinearMap.ker ((adamsHomologyAction H R X n).toAddMonoidHom.toZModLinearMap 2)).map
      (K.comparison X n).toLinearMap =
        LinearMap.ker (cooperationTensorAugmentation H R (fun i => mod2HomologyF2 H R i X) n) := by
  letI := mod2HomologyModule H R n X
  letI := mod2HomologyModule H R n (H.HF2 ⊗ X)
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    change cooperationTensorAugmentation H R _ n (K.comparison X n x) = 0
    rw [K.action_comparison]
    exact hx
  · intro hz
    refine ⟨(K.comparison X n).symm z, ?_, (K.comparison X n).apply_symm_apply z⟩
    change inducedMap (mod2FreeAction H R X) n ((K.comparison X n).symm z) = 0
    rw [← K.action_comparison, LinearEquiv.apply_symm_apply]
    exact hz

end

end KIP126.Classical.Adams
