module

public import KIP126.Def.Topology.FiberBundle.Transport.Data
public import Mathlib.Topology.FiberBundle.Trivialization

@[expose] public section

namespace KIP126.Topology

variable {E A B P F : Type*}
  [TopologicalSpace E] [TopologicalSpace A] [TopologicalSpace B]
  [TopologicalSpace P] [TopologicalSpace F]
set_option backward.isDefEq.respectTransparency false

/-- Flatten an actual iterated topological pullback, retaining its base
coordinate and its original total-space point. -/
def iteratedPullbackHomeomorph (p : C(E,P)) (a : C(A,P)) (b : C(B,A)) :
    {z : {z : E × A // p z.1 = a z.2} × B // pullbackSndMap p a z.1 = b z.2} ≃ₜ
      {z : E × B // p z.1 = (a.comp b) z.2} where
  toFun z := ⟨(z.val.1.val.1,z.val.2),z.val.1.property.trans (congrArg a z.property)⟩
  invFun z := ⟨(⟨(z.val.1,b z.val.2),z.property⟩,z.val.2),rfl⟩
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      exact Prod.ext rfl z.property.symm
    · rfl
  right_inv _ := rfl
  continuous_toFun :=
    ((continuous_fst.comp (continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val))).prodMk
      (continuous_snd.comp continuous_subtype_val)).subtype_mk _
  continuous_invFun :=
    (((continuous_fst.comp continuous_subtype_val).prodMk
      (b.continuous.comp (continuous_snd.comp continuous_subtype_val))).subtype_mk _).prodMk
      (continuous_snd.comp continuous_subtype_val) |>.subtype_mk _

/-- Pullback along a homeomorphism of the base is homeomorphic to the
original total space through its actual first coordinate. -/
def pullbackBaseHomeomorph (p : C(E,P)) (a : A ≃ₜ P) :
    {z : E × A // p z.1 = a z.2} ≃ₜ E where
  toFun z := z.val.1
  invFun x := ⟨(x,a.symm (p x)),(a.apply_symm_apply (p x)).symm⟩
  left_inv z := by
    apply Subtype.ext
    refine Prod.ext ?_ ?_
    · rfl
    · exact a.injective (by simpa only [Homeomorph.apply_symm_apply] using z.property)
  right_inv _ := rfl
  continuous_toFun := continuous_fst.comp continuous_subtype_val
  continuous_invFun := (continuous_id.prodMk (a.symm.continuous.comp p.continuous)).subtype_mk _

end KIP126.Topology
