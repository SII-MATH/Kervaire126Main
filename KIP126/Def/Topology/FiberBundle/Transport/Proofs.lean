module

public import KIP126.Def.Topology.FiberBundle.Transport.Data

@[expose] public section

namespace KIP126.Topology

universe u v w z

variable {E : Type u} {A : Type v} {P : Type w} {F : Type z}
  [TopologicalSpace E] [TopologicalSpace A] [TopologicalSpace P] [TopologicalSpace F]

set_option backward.isDefEq.respectTransparency false

/-- The inverse chart preserves the original base coordinate. -/
theorem fiberChart_symm_snd (p : C(E,P)) (a : C(A,P))
    (e : {z : E × A // p z.1 = a z.2} ≃ₜ (F × A))
    (he : ∀ z, (e z).2 = z.1.2) (x : F × A) : (e.symm x).1.2 = x.2 := by
  have h := he (e.symm x)
  rw [e.apply_symm_apply] at h
  exact h.symm

/-- Transport along the chart lies over the prescribed new base point. -/
theorem fiberChartTransport_projection (p : C(E,P)) (a : C(A,P))
    (e : {z : E × A // p z.1 = a z.2} ≃ₜ (F × A))
    (he : ∀ z, (e z).2 = z.1.2) (z : {z : E × A // p z.1 = a z.2}) (x : A) :
    p (fiberChartTransport p a e z x) = a x := by
  have h := (e.symm ((e z).1,x)).2
  rw [fiberChart_symm_snd p a e he] at h
  exact h

/-- Transport to the current base point fixes the original total-space point. -/
theorem fiberChartTransport_self (p : C(E,P)) (a : C(A,P))
    (e : {z : E × A // p z.1 = a z.2} ≃ₜ (F × A))
    (he : ∀ z, (e z).2 = z.1.2) (z : {z : E × A // p z.1 = a z.2}) :
    fiberChartTransport p a e z z.1.2 = z.1.1 := by
  have h : ((e z).1,z.1.2) = e z := Prod.ext rfl (he z).symm
  change (e.symm ((e z).1,z.1.2)).1.1 = z.1.1
  rw [h,e.symm_apply_apply]

/-- Chart transport is jointly continuous in the original point and
the new base coordinate. -/
theorem fiberChartTransport_continuous (p : C(E,P)) (a : C(A,P))
    (e : {z : E × A // p z.1 = a z.2} ≃ₜ (F × A)) :
    Continuous (fun z : {z : E × A // p z.1 = a z.2} × A =>
      fiberChartTransport p a e z.1 z.2) :=
  continuous_fst.comp (continuous_subtype_val.comp (e.symm.continuous.comp
    ((continuous_fst.comp (e.continuous.comp continuous_fst)).prodMk continuous_snd)))

/-- Two successive changes of the base coordinate preserve the same
fiber coordinate and agree with direct transport. -/
theorem fiberChartTransport_trans (p : C(E,P)) (a : C(A,P))
    (e : {z : E × A // p z.1 = a z.2} ≃ₜ (F × A))
    (he : ∀ z, (e z).2 = z.1.2) (z : {z : E × A // p z.1 = a z.2}) (x y : A) :
    fiberChartTransport p a e
      ⟨(fiberChartTransport p a e z x,x),fiberChartTransport_projection p a e he z x⟩ y =
        fiberChartTransport p a e z y := by
  have hz : (⟨(fiberChartTransport p a e z x,x),
      fiberChartTransport_projection p a e he z x⟩ : {z : E × A // p z.1 = a z.2}) =
      e.symm ((e z).1,x) := by
    apply Subtype.ext
    exact Prod.ext rfl (fiberChart_symm_snd p a e he ((e z).1,x)).symm
  rw [hz]
  unfold fiberChartTransport
  rw [e.apply_symm_apply]

end KIP126.Topology
