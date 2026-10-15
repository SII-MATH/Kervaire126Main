module

public import Mathlib.Topology.Homotopy.Path

@[expose] public section

namespace KIP126.Topology

open scoped unitInterval
universe u v
variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]

/-- Project the contraction path of a point in the actual fiber to a based
loop in the target. -/
def contractionFiberLoop (f : C(E,B)) (e : E)
    (c : ContinuousMap.Homotopy (ContinuousMap.const E e) (ContinuousMap.id E)) :
    C({x : E // f x = f e}, Path (f e) (f e)) where
  toFun x := {
    toFun t := f (c (t,x.val))
    continuous_toFun := f.continuous.comp (c.continuous.comp
      (continuous_id.prodMk continuous_const))
    source' := by rw [c.apply_zero]; rfl
    target' := by rw [c.apply_one]; exact x.property }
  continuous_toFun := Path.continuous_uncurry_iff.mp (by
    change Continuous (fun z : {x : E // f x = f e} × I => f (c (z.2,z.1.val)))
    fun_prop)

end KIP126.Topology
