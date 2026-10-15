module

public import KIP126.Def.Topology.HomotopyLifting.Predicates
public import Mathlib.Topology.FiberBundle.Trivialization

@[expose] public section

namespace KIP126.Topology.HomotopyLifting
open scoped unitInterval
set_option backward.isDefEq.respectTransparency false

/-- An actual retraction of the cylinder onto its prescribed horn extends
fiber coordinates inside one actual bundle chart. -/
theorem exists_relativeLift_of_retraction
    {E B F : Type*} [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace F]
    (f : C(E,B)) (T : Bundle.Trivialization F f)
    {Z : Type*} [TopologicalSpace Z] (S : Set Z)
    (r : C(I × Z,CylinderHorn Z S)) (hr : ∀ z : CylinderHorn Z S, r z.val = z)
    (g : C(CylinderHorn Z S,E))
    (H : C(I × Z,B)) (hH : ∀ z, H z ∈ T.baseSet)
    (hcomm : ∀ z, f (g z) = H z.val) :
    ∃ L : C(I × Z,E), (∀ z, f (L z) = H z) ∧
      (∀ z, L z.val = g z) := by
  have hg (z : CylinderHorn Z S) : g z ∈ T.source := by
    apply T.mem_source.mpr
    rw [hcomm]
    exact hH z.val
  let gF : C(CylinderHorn Z S,F) :=
    ⟨fun z => (T (g z)).2, (T.continuousOn_toFun.comp_continuous g.continuous hg).snd⟩
  let L : C(I × Z,E) :=
    ⟨fun z => T.invFun (H z,gF (r z)),
      T.continuousOn_invFun.comp_continuous
        (H.continuous.prodMk (gF.continuous.comp r.continuous))
        (fun z => T.mem_target.mpr (hH z))⟩
  refine ⟨L,fun z => T.proj_symm_apply (T.mem_target.mpr (hH z)),?_⟩
  intro z
  change T.invFun (H z.val,gF (r z.val)) = g z
  rw [hr]
  change T.invFun (H z.val,(T (g z)).2) = g z
  rw [← hcomm z]
  exact T.symm_apply_mk_proj (hg z)


end KIP126.Topology.HomotopyLifting
