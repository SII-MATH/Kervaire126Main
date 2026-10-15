module

public import KIP126.Def.Topology.Cube.Grid.Extension.Proofs
public import KIP126.Def.Topology.ClosedCover.Proofs

@[expose] public section

namespace KIP126.Topology.Cube

open scoped unitInterval
set_option backward.isDefEq.respectTransparency false

/-- Simultaneously attach one grid layer, preserving the actual old lift. -/
theorem exists_gridLayer_lift
    {E B F : Type*} [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace F]
    (f : C(E,B)) {n m : ℕ} (H : C((Fin (n+1) → I),B))
    (hchart : ∀ k : Fin (n+1) → Fin (m+1), ∃ T : Bundle.Trivialization F f,
      ∀ x ∈ gridCell (n+1) m k, H x ∈ T.baseSet)
    (r : ℕ) (g : C(gridPast n m r,E)) (hg : ∀ x, f (g x) = H x.val) :
    ∃ L : C(gridPast n m (r+1),E), (∀ x, f (L x) = H x.val) ∧
      (∀ x : gridPast n m r, L ⟨x.val,gridPast_mono n m (Nat.le_succ r) x.property⟩ = g x) := by
  classical
  let J := {k : Fin (n+1) → Fin (m+1) // gridDegree k = r}
  let C : J → Set (Fin (n+1) → I) := fun k => gridCell (n+1) m k.val
  have hext (k : J) : ∃ L : C(C k,E), (∀ x, f (L x) = H x.val) ∧
      (∀ x (hx : x.val ∈ gridPast n m r), L x = g ⟨x.val,hx⟩) := by
    obtain ⟨T,hT⟩ := hchart k.val
    have hh := exists_gridCell_lift f T k.val H hT
    rw [k.property] at hh
    exact hh g hg
  choose L hL hagree using hext
  have hs : gridPast n m (r+1) = gridPast n m r ∪ ⋃ k : J, C k := by
    rw [gridPast_succ]
    congr 1
    ext x
    simp only [Set.mem_setOf_eq,Set.mem_iUnion]
    constructor
    · rintro ⟨k,hk,hx⟩
      exact ⟨⟨k,hk⟩,hx⟩
    · rintro ⟨k,hx⟩
      exact ⟨k.val,k.property,hx⟩
  obtain ⟨G,hG,hGg,_⟩ := ClosedCover.exists_extension_over (gridPast n m r) C
    (gridPast_isClosed n m r) (fun k => gridCell_isClosed (n+1) m k.val)
    (fun k l hkl => gridCell_same_layer_inter_subset_past k.val l.val k.property l.property
      (fun he => hkl (Subtype.ext he))) f H g L hg hL hagree
  let a : C(gridPast n m (r+1),↥(gridPast n m r ∪ ⋃ k : J, C k)) :=
    ⟨fun x => ⟨x.val,hs ▸ x.property⟩,continuous_subtype_val.subtype_mk _⟩
  exact ⟨G.comp a,fun x => hG (a x),fun x => hGg x⟩

/-- Finitely many relative cell extensions give a lift on the whole
cube, strictly preserving the original bottom and spatial boundary. -/
theorem exists_cube_lift_of_grid_charts
    {E B F : Type*} [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace F]
    (f : C(E,B)) {n m : ℕ} (H : C((Fin (n+1) → I),B))
    (hchart : ∀ k : Fin (n+1) → Fin (m+1), ∃ T : Bundle.Trivialization F f,
      ∀ x ∈ gridCell (n+1) m k, H x ∈ T.baseSet)
    (g : C(gridGlobalHorn n,E)) (hg : ∀ x, f (g x) = H x.val) :
    ∃ L : C((Fin (n+1) → I),E), (∀ x, f (L x) = H x) ∧
      (∀ x : gridGlobalHorn n, L x.val = g x) := by
  have hi (r : ℕ) : ∃ L : C(gridPast n m r,E), (∀ x, f (L x) = H x.val) ∧
      (∀ x : gridGlobalHorn n, L ⟨x.val,Or.inl x.property⟩ = g x) := by
    induction r with
    | zero =>
      let a : C(gridPast n m 0,gridGlobalHorn n) :=
        ⟨fun x => ⟨x.val,gridPast_zero n m ▸ x.property⟩,continuous_subtype_val.subtype_mk _⟩
      exact ⟨g.comp a,fun x => hg (a x),fun _ => rfl⟩
    | succ r ihr =>
      obtain ⟨L,hL,hLg⟩ := ihr
      obtain ⟨G,hG,hGL⟩ := exists_gridLayer_lift f H hchart r L hL
      exact ⟨G,hG,fun x => (hGL ⟨x.val,Or.inl x.property⟩).trans (hLg x)⟩
  obtain ⟨G,hG,hGg⟩ := hi ((n+1)*m+1)
  have ha (x : Fin (n+1) → I) : x ∈ gridPast n m ((n+1)*m+1) := by
    rw [gridPast_eq_univ]
    trivial
  let a : C((Fin (n+1) → I),gridPast n m ((n+1)*m+1)) :=
    ⟨fun x => ⟨x,ha x⟩,continuous_id.subtype_mk ha⟩
  exact ⟨G.comp a,fun x => hG (a x),fun x => hGg x⟩

/-- Any actual chart cover of the homotopy image supplies a continuous
lift of the whole finite cube relative to its prescribed horn. -/
theorem exists_cube_lift_of_chart_cover
    {E B F ι : Type*} [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace F]
    (f : C(E,B)) (T : ι → Bundle.Trivialization F f)
    (n : ℕ) (H : C((Fin (n+1) → I),B))
    (hcover : Set.range H ⊆ ⋃ i, (T i).baseSet)
    (g : C(gridGlobalHorn n,E)) (hg : ∀ x, f (g x) = H x.val) :
    ∃ L : C((Fin (n+1) → I),E), (∀ x, f (L x) = H x) ∧
      (∀ x : gridGlobalHorn n, L x.val = g x) := by
  obtain ⟨m,hm⟩ := exists_grid_image_subordinate (n+1) H (fun i => (T i).baseSet)
    (fun i => (T i).open_baseSet) hcover
  exact exists_cube_lift_of_grid_charts (m := m) f H (fun k => by
    obtain ⟨i,hi⟩ := hm k
    exact ⟨T i,fun x hx => hi ⟨x,hx,rfl⟩⟩) g hg

end KIP126.Topology.Cube
