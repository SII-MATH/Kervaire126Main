module

public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.LocalAtTarget
public import Mathlib.Topology.ContinuousMap.Basic

@[expose] public section

namespace KIP126.Topology.HomotopyLifting

open _root_.Topology

variable {E P F ι : Type*} [TopologicalSpace E] [TopologicalSpace P]
  [TopologicalSpace F] (D : ι → Type*) [∀ i, TopologicalSpace (D i)]

/-- Pulling back over a topological disjoint union is the disjoint union
of the actual pullbacks over its summands. -/
def sigmaPullbackHomeomorph (p : C(E, P)) (a : C((Σ i, D i), P)) :
    (Σ i, {z : E × D i // p z.1 = a ⟨i, z.2⟩}) ≃ₜ
      {z : E × (Σ i, D i) // p z.1 = a z.2} := by
  let e : (Σ i, {z : E × D i // p z.1 = a ⟨i, z.2⟩}) ≃
      {z : E × (Σ i, D i) // p z.1 = a z.2} := {
    toFun := fun z => ⟨(z.2.val.1, ⟨z.1, z.2.val.2⟩), z.2.property⟩
    invFun := fun z => ⟨z.val.2.1, ⟨(z.val.1, z.val.2.2), z.property⟩⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  refine e.toHomeomorphOfContinuousOpen ?_ ?_
  · apply continuous_sigma
    intro i
    exact ((continuous_fst.comp continuous_subtype_val).prodMk
      (continuous_sigmaMk.comp (continuous_snd.comp continuous_subtype_val))).subtype_mk _
  · apply isOpenMap_sigma.mpr
    intro i
    exact (IsOpenMap.id.prodMap (isOpenMap_sigmaMk (i := i))).restrictPreimage
      {z : E × (Σ i, D i) | p z.1 = a z.2}

/-- A componentwise homeomorphism of topological disjoint unions. -/
def sigmaComponentHomeomorph {D' : ι → Type*} [∀ i, TopologicalSpace (D' i)]
    (e : ∀ i, D i ≃ₜ D' i) : (Σ i, D i) ≃ₜ Σ i, D' i where
  toEquiv := Equiv.sigmaCongrRight (fun i => (e i).toEquiv)
  continuous_toFun := Continuous.sigma_map (fun i => (e i).continuous)
  continuous_invFun := Continuous.sigma_map (fun i => (e i).symm.continuous)

/-- Product coordinates on each pullback summand assemble to actual
product coordinates on the pullback over their disjoint union. -/
def sigmaPullbackProductHomeomorph (p : C(E, P)) (a : C((Σ i, D i), P))
    (e : ∀ i, {z : E × D i // p z.1 = a ⟨i, z.2⟩} ≃ₜ F × D i) :
    {z : E × (Σ i, D i) // p z.1 = a z.2} ≃ₜ F × (Σ i, D i) :=
  (sigmaPullbackHomeomorph D p a).symm.trans
    ((sigmaComponentHomeomorph _ (fun i => (e i).trans (Homeomorph.prodComm F (D i)))).trans
      (Homeomorph.sigmaProdDistrib.symm.trans (Homeomorph.prodComm (Σ i, D i) F)))

end KIP126.Topology.HomotopyLifting
