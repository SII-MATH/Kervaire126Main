module

public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.ContinuousMap.Basic

@[expose] public section

namespace KIP126.Topology

universe u v w z

variable {E : Type u} {A : Type v} {P : Type w} {F : Type z}
  [TopologicalSpace E] [TopologicalSpace A] [TopologicalSpace P] [TopologicalSpace F]

/-- The actual second projection of a topological pullback. -/
def pullbackSndMap (p : C(E,P)) (a : C(A,P)) : C({z : E × A // p z.1 = a z.2},A) :=
  ⟨fun z => z.1.2,continuous_snd.comp continuous_subtype_val⟩

/-- Move a point between two fibers of a genuine product chart by
preserving its fiber coordinate. -/
noncomputable def fiberChartTransport (p : C(E,P)) (a : C(A,P))
    (e : {z : E × A // p z.1 = a z.2} ≃ₜ (F × A))
    (z : {z : E × A // p z.1 = a z.2}) (x : A) : E :=
  (e.symm ((e z).1,x)).1.1

end KIP126.Topology
