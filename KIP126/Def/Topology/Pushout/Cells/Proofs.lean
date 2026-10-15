module

public import KIP126.Def.Topology.Pushout.RealFunctions.Proofs

@[expose] public section

namespace KIP126.Topology

open CategoryTheory CategoryTheory.Limits _root_.Topology Set

universe u

set_option backward.isDefEq.respectTransparency false

/-- The actual topological pushout detects openness on its two pieces. -/
theorem isOpen_iff_of_topological_pushout
    {S A B P : TopCat.{u}} {i : S ⟶ A} {f : S ⟶ B} {a : A ⟶ P} {b : B ⟶ P}
    (h : IsPushout i f a b) (U : Set P) :
    IsOpen U ↔ IsOpen (a ⁻¹' U) ∧ IsOpen (b ⁻¹' U) := by
  simpa only [← isOpen_compl_iff,Set.preimage_compl,compl_compl] using
    (isClosed_iff_of_topological_pushout h Uᶜ)

/-- A cell point away from the attaching boundary acquires no additional
identifications in the actual pushout. -/
theorem pushout_cell_eq_of_outside_boundary
    {S A B P : TopCat.{u}} [NormalSpace A] [T1Space A]
    {i : S ⟶ A} {f : S ⟶ B} {a : A ⟶ P} {b : B ⟶ P}
    (h : IsPushout i f a b) (hi : IsClosedEmbedding i)
    {x y : A} (hx : x ∉ Set.range i) (hxy : a x = a y) : x = y := by
  by_contra hne
  obtain ⟨g,hg⟩ := pushout_distinct_cell_points_real_separation h hi x y hx hne
  exact hg (congrArg g hxy)

/-- The cell source minus its attaching boundary is genuinely open embedded
in the new attachment stage, providing the actual interior cell charts. -/
theorem isOpenEmbedding_pushout_boundary_complement
    {S A B P : TopCat.{u}} [NormalSpace A] [T1Space A]
    {i : S ⟶ A} {f : S ⟶ B} {a : A ⟶ P} {b : B ⟶ P}
    (h : IsPushout i f a b) (hi : IsClosedEmbedding i) :
    IsOpenEmbedding (fun x : {x : A // x ∉ Set.range i} => a x.1) := by
  apply IsOpenEmbedding.of_continuous_injective_isOpenMap
    (a.hom.continuous.comp continuous_subtype_val)
  · intro x y hxy
    exact Subtype.ext (pushout_cell_eq_of_outside_boundary h hi x.2 hxy)
  · intro U hU
    apply (isOpen_iff_of_topological_pushout h _).mpr
    constructor
    · have he : a ⁻¹' ((fun x : {x : A // x ∉ Set.range i} => a x.1) '' U) = Subtype.val '' U := by
        ext y
        constructor
        · rintro ⟨x,hx,hxy⟩
          exact ⟨x,hx,pushout_cell_eq_of_outside_boundary h hi x.2 hxy⟩
        · rintro ⟨x,hx,rfl⟩
          exact ⟨x,hx,rfl⟩
      change IsOpen (a ⁻¹' ((fun x : {x : A // x ∉ Set.range i} => a x.1) '' U))
      rw [he]
      exact hi.isClosed_range.isOpen_compl.isOpenMap_subtype_val U hU
    · have he : b ⁻¹' ((fun x : {x : A // x ∉ Set.range i} => a x.1) '' U) = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        rintro y ⟨x,hx,hxy⟩
        obtain ⟨s,hs,_⟩ :=
          (Types.pushoutCocone_inl_eq_inr_iff_of_isColimit
            (h.map (forget TopCat)).isColimit hi.injective x.1 y).mp hxy
        exact x.2 ⟨s,hs⟩
      change IsOpen (b ⁻¹' ((fun x : {x : A // x ∉ Set.range i} => a x.1) '' U))
      rw [he]
      exact isOpen_empty

end KIP126.Topology
