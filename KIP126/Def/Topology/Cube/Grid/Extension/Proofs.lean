module

public import KIP126.Def.Topology.Cube.Grid.Layers.Proofs
public import KIP126.Def.Topology.HomotopyLifting.Cube.Faces.Horn

@[expose] public section

namespace KIP126.Topology.Cube

open scoped unitInterval
set_option backward.isDefEq.respectTransparency false

/-- Extend a prescribed lift from the earlier layers across one actual
grid cell whose image lies in one bundle chart. -/
theorem exists_gridCell_lift
    {E B F : Type*} [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace F]
    (f : C(E,B)) (T : Bundle.Trivialization F f) {n m : ℕ}
    (k : Fin (n+1) → Fin (m+1)) (H : C((Fin (n+1) → I),B))
    (hH : ∀ x ∈ gridCell (n+1) m k, H x ∈ T.baseSet)
    (g : C(gridPast n m (gridDegree k),E)) (hg : ∀ x, f (g x) = H x.val) :
    ∃ L : C(gridCell (n+1) m k,E), (∀ x, f (L x) = H x.val) ∧
      (∀ x (hx : x.val ∈ gridPast n m (gridDegree k)), L x = g ⟨x.val,hx⟩) := by
  let e := (HomotopyLifting.cubeCylinderHomeomorph n).trans (gridCellHomeomorph (n+1) m k)
  let h : C(I × (Fin n → I),B) :=
    ⟨fun z => H (e z).val,H.continuous.comp (continuous_subtype_val.comp e.continuous)⟩
  have hp (z : I × (Fin n → I)) :
      (e z).val ∈ gridPast n m (gridDegree k) ↔
        z.1 = 0 ∨ z.2 ∈ HomotopyLifting.cubeFacesBoundary n (gridIncomingFaces k) :=
    (gridCell_mem_past_iff k (HomotopyLifting.cubeCylinderHomeomorph n z)).trans
      (gridIncoming_cylinder_iff k z)
  let a : C(HomotopyLifting.CylinderHorn (Fin n → I)
      (HomotopyLifting.cubeFacesBoundary n (gridIncomingFaces k)),
      gridPast n m (gridDegree k)) :=
    ⟨fun z => ⟨(e z.val).val,(hp z.val).mpr z.property⟩,
      ((continuous_subtype_val.comp e.continuous).comp continuous_subtype_val).subtype_mk _⟩
  obtain ⟨L,hL,hLa⟩ := HomotopyLifting.exists_relativeLift_faces_in_trivialization
    f T (gridIncomingFaces k) (g.comp a) h (fun z => hH (e z).val (e z).property)
    (fun z => hg (a z))
  refine ⟨L.comp ⟨e.symm,e.symm.continuous⟩,?_,?_⟩
  · intro x
    simpa only [ContinuousMap.comp_apply,ContinuousMap.coe_mk,h,Homeomorph.apply_symm_apply] using hL (e.symm x)
  · intro x hx
    have hz := (hp (e.symm x)).mp (by simpa only [Homeomorph.apply_symm_apply] using hx)
    have he := hLa ⟨e.symm x,hz⟩
    change L (e.symm x) = g ⟨x.val,hx⟩
    simpa only [ContinuousMap.comp_apply,a,ContinuousMap.coe_mk,Homeomorph.apply_symm_apply] using he

end KIP126.Topology.Cube
