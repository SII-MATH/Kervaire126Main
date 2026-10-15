module

public import KIP126.Def.Topology.Cube.Grid.Layers.Data
public import KIP126.Def.Topology.HomotopyLifting.Data
public import KIP126.Def.Topology.HomotopyLifting.Predicates
public import KIP126.Def.Topology.Cube.Grid.Global.Proofs
public import Mathlib.Topology.FiberBundle.Basic

@[expose] public section

section

namespace KIP126.Topology.HomotopyLifting

open scoped unitInterval

/-- The standard cylinder bottom and side are the global grid horn after
inserting the time parameter as the first cube coordinate. -/
def gridHornHomeomorph (n : ℕ) :
    CylinderHorn (Fin n → I) (_root_.Cube.boundary (Fin n)) ≃ₜ
      Cube.gridGlobalHorn n :=
  (cubeCylinderHomeomorph n).subtype (fun _ => Iff.rfl)

end KIP126.Topology.HomotopyLifting

end

section

namespace KIP126.Topology.HomotopyLifting

open scoped unitInterval
set_option backward.isDefEq.respectTransparency false

theorem gridHornHomeomorph_val (n : ℕ)
    (z : CylinderHorn (Fin n → I) (_root_.Cube.boundary (Fin n))) :
    (gridHornHomeomorph n z).val = cubeCylinderHomeomorph n z.val := rfl

/-- A chart cover of a cubical homotopy image supplies an actual relative
lift, fixed on its prescribed bottom and its entire spatial boundary. -/
theorem exists_relativeLift_of_chart_cover
    {E B F ι : Type*} [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace F]
    (f : C(E, B)) (T : ι → Bundle.Trivialization F f) (n : ℕ)
    (g : C(CylinderHorn (Fin n → I) (_root_.Cube.boundary (Fin n)), E))
    (H : C(I × (Fin n → I), B)) (hcover : Set.range H ⊆ ⋃ i, (T i).baseSet)
    (hcomm : ∀ z, f (g z) = H z.val) :
    ∃ L : C(I × (Fin n → I), E), (∀ z, f (L z) = H z) ∧
      (∀ z, L z.val = g z) := by
  let e := cubeCylinderHomeomorph n
  let h := gridHornHomeomorph n
  let H' : C((Fin (n + 1) → I), B) := H.comp ⟨e.symm, e.symm.continuous⟩
  let g' : C(Cube.gridGlobalHorn n, E) := g.comp ⟨h.symm, h.symm.continuous⟩
  have hcover' : Set.range H' ⊆ ⋃ i, (T i).baseSet := by
    rintro _ ⟨x, rfl⟩
    exact hcover ⟨e.symm x, rfl⟩
  obtain ⟨L, hL, hLg⟩ := Cube.exists_cube_lift_of_chart_cover f T n H' hcover' g'
    (fun x => hcomm (h.symm x))
  refine ⟨L.comp ⟨e, e.continuous⟩, ?_, ?_⟩
  · intro z
    simpa only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, H',
      Homeomorph.symm_apply_apply] using hL (e z)
  · intro z
    simpa only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, g', h,
      gridHornHomeomorph_val, Homeomorph.symm_apply_apply] using hLg (h z)

/-- An actual cover by bundle charts implies relative lifting for every
finite cube boundary pair. -/
theorem hasCubicalLifting_of_chart_cover
    {E B F ι : Type*} [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace F]
    (f : C(E, B)) (T : ι → Bundle.Trivialization F f)
    (hcover : ⋃ i, (T i).baseSet = Set.univ) : HasCubicalLifting f := by
  intro n g H hcomm
  exact exists_relativeLift_of_chart_cover f T n g H
    (by rw [hcover]; exact Set.subset_univ _) hcomm

/-- Local triviality at every base point implies actual cubical lifting. -/
theorem hasCubicalLifting_of_locally_trivial
    {E B F : Type*} [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace F]
    (f : C(E, B)) (hlocal : ∀ b : B, ∃ T : Bundle.Trivialization F f, b ∈ T.baseSet) :
    HasCubicalLifting f :=
  hasCubicalLifting_of_chart_cover f (fun T : Bundle.Trivialization F f => T)
    (Set.iUnion_eq_univ_iff.mpr hlocal)

end KIP126.Topology.HomotopyLifting

end
