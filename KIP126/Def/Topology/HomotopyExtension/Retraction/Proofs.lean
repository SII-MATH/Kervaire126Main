module

public import KIP126.Def.Topology.HomotopyExtension.Proofs
public import KIP126.Def.Topology.HomotopyLifting.Cube

@[expose] public section

namespace KIP126.Topology.HomotopyExtension

open CategoryTheory Set _root_.Topology
open scoped unitInterval

universe u

set_option backward.isDefEq.respectTransparency false

/-- Homotopy extension supplies an actual retraction of the cylinder onto
its bottom together with the full cylinder on the image. -/
theorem HasHomotopyExtension.exists_cylinder_retraction {A B : TopCat.{u}}
    {i : A ⟶ B} (hi : HasHomotopyExtension i) :
    ∃ r : C(B × I, B × I),
      (∀ b, r (b, 0) = (b, 0)) ∧
      (∀ a t, r (i a, t) = (i a, t)) ∧
      (∀ q, (r q).2 = 0 ∨ (r q).1 ∈ range i) := by
  let S := {q : B × I // q.2 = 0 ∨ q.1 ∈ range i}
  let f : C(B, S) := ⟨fun b => ⟨(b, 0), Or.inl rfl⟩,
    (continuous_id.prodMk continuous_const).subtype_mk _⟩
  let p : C(A × I, S) := ⟨fun q => ⟨(i q.1, q.2), Or.inr ⟨q.1, rfl⟩⟩,
    ((i.hom.continuous.comp continuous_fst).prodMk continuous_snd).subtype_mk _⟩
  obtain ⟨H, hH, hHi⟩ := hi (TopCat.of S) f p (fun _ => rfl)
  exact ⟨⟨fun q => (H q).val, continuous_subtype_val.comp H.continuous⟩,
    fun b => congrArg Subtype.val (hH b),
    fun a t => congrArg Subtype.val (hHi a t), fun q => (H q).property⟩

/-- A cylinder retraction onto the bottom and a closed embedded image
gives full homotopy extension, with exact agreement on the image. -/
theorem hasHomotopyExtension_of_cylinder_retraction {A B : TopCat.{u}}
    (i : A ⟶ B) (hi : IsClosedEmbedding i) (r : C(B × I, B × I))
    (hzero : ∀ b, r (b, 0) = (b, 0))
    (hside : ∀ a t, r (i a, t) = (i a, t))
    (hr : ∀ q, (r q).2 = 0 ∨ (r q).1 ∈ range i) :
    HasHomotopyExtension i := by
  classical
  intro Y f p hp
  let e := hi.isEmbedding.toHomeomorph
  let U : Set (B × I) := {q | (r q).2 = 0}
  let V : Set (B × I) := {q | (r q).1 ∈ range i}
  have hU : IsClosed U := isClosed_eq r.continuous.snd continuous_const
  have hV : IsClosed V := hi.isClosed_range.preimage r.continuous.fst
  have hUV : U ∪ V = univ := Set.eq_univ_of_forall hr
  let pv : C(V, Y) := ⟨fun q => p (e.symm ⟨(r q.val).1, q.property⟩, (r q.val).2),
    p.continuous.comp ((e.symm.continuous.comp
      ((r.continuous.comp continuous_subtype_val).fst.subtype_mk _)).prodMk
      (r.continuous.comp continuous_subtype_val).snd)⟩
  let F : B × I → Y := fun q => if h : q ∈ V then pv ⟨q, h⟩ else f (r q).1
  have hv : ContinuousOn F V := continuousOn_iff_continuous_restrict.mpr
    (pv.continuous.congr (by intro q; dsimp [F]; rw [dif_pos q.property]))
  have hu : ContinuousOn F U :=
    (f.continuous.comp r.continuous.fst).continuousOn.congr (by
      intro q hq
      dsimp only [F]
      split_ifs with h
      · change p (e.symm ⟨(r q).1, h⟩, (r q).2) = f (r q).1
        rw [show (r q).2 = 0 from hq, hp]
        exact congrArg f (congrArg Subtype.val (e.apply_symm_apply ⟨(r q).1, h⟩))
      · rfl)
  refine ⟨⟨F, continuousOn_univ.mp (hUV ▸ hu.union_of_isClosed hv hU hV)⟩, ?_, ?_⟩
  · intro b
    change F (b, 0) = f b
    dsimp only [F]
    split_ifs with h
    · change p (e.symm ⟨(r (b, 0)).1, h⟩, (r (b, 0)).2) = f b
      have ht : (r (b, 0)).2 = 0 := congrArg Prod.snd (hzero b)
      rw [ht, hp]
      apply congrArg f
      exact (congrArg Subtype.val (e.apply_symm_apply ⟨(r (b, 0)).1, h⟩)).trans
        (congrArg Prod.fst (hzero b))
    · exact congrArg f (congrArg Prod.fst (hzero b))
  · intro a t
    have hv' : (i a, t) ∈ V := by
      change (r (i a, t)).1 ∈ range i
      rw [hside]
      exact ⟨a, rfl⟩
    change F (i a, t) = p (a, t)
    rw [show F (i a, t) = pv ⟨(i a, t), hv'⟩ from dif_pos hv']
    change p (e.symm ⟨(r (i a, t)).1, hv'⟩, (r (i a, t)).2) = p (a, t)
    have he : e.symm ⟨(r (i a, t)).1, hv'⟩ = a := by
      apply e.injective
      rw [e.apply_symm_apply]
      apply Subtype.ext
      exact congrArg Prod.fst (hside a t)
    rw [he, hside]

/-- The actual one-dimensional cubical horn retraction, written in the
coordinate order convenient for cylinder constructions. -/
theorem exists_interval_boundary_retraction :
    ∃ r : C(I × I, I × I),
      (∀ t, r (t, 0) = (t, 0)) ∧
      (∀ s, r (0, s) = (0, s)) ∧
      (∀ s, r (1, s) = (1, s)) ∧
      (∀ q, (r q).2 = 0 ∨ (r q).1 = 0 ∨ (r q).1 = 1) := by
  let H := HomotopyLifting.cubeHornRetraction 1
  let a : C(I × I, I × (Fin 1 → I)) :=
    ⟨fun q => (q.2, fun _ => q.1), continuous_snd.prodMk
      (continuous_pi (fun _ => continuous_fst))⟩
  let r : C(I × I, I × I) := ⟨fun q => ((H (a q)).val.2 0, (H (a q)).val.1),
    ((continuous_apply 0).comp (H.continuous.comp a.continuous).subtype_val.snd).prodMk
      (H.continuous.comp a.continuous).subtype_val.fst⟩
  have he (q : I × I) (hq : q.2 = 0 ∨ q.1 = 0 ∨ q.1 = 1) : r q = q := by
    have hh : (a q).1 = 0 ∨ (a q).2 ∈ _root_.Cube.boundary (Fin 1) := by
      rcases hq with h | h | h
      · exact Or.inl h
      · exact Or.inr ⟨0, Or.inl h⟩
      · exact Or.inr ⟨0, Or.inr h⟩
    have hr := HomotopyLifting.cubeHornRetraction_restrict 1 ⟨a q, hh⟩
    exact congrArg (fun z => (z.val.2 0, z.val.1)) hr
  refine ⟨r, fun t => he (t, 0) (Or.inl rfl),
    fun s => he (0, s) (Or.inr (Or.inl rfl)),
    fun s => he (1, s) (Or.inr (Or.inr rfl)), ?_⟩
  intro q
  rcases (H (a q)).property with ht | ⟨j, hj⟩
  · exact Or.inl ht
  · have hj0 : j = 0 := Subsingleton.elim _ _
    subst j
    exact Or.inr hj

end KIP126.Topology.HomotopyExtension
