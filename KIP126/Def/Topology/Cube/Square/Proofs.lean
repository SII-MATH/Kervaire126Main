module

public import KIP126.Def.Topology.Cube.Square.Data

@[expose] public section

namespace KIP126.Topology.Cube

open scoped unitInterval

@[continuity, fun_prop] theorem continuous_delayedCoordinate : Continuous delayedCoordinate :=
  continuous_projIcc.comp ((continuous_const.mul continuous_subtype_val).sub continuous_const)

@[continuity, fun_prop] theorem continuous_advancedCoordinate : Continuous advancedCoordinate :=
  continuous_projIcc.comp (continuous_const.mul continuous_subtype_val)

@[simp] theorem delayedCoordinate_zero : delayedCoordinate 0 = 0 := by
  apply Set.projIcc_of_le_left
  norm_num

@[simp] theorem delayedCoordinate_one : delayedCoordinate 1 = 1 := by
  apply Set.projIcc_of_right_le
  norm_num

@[simp] theorem advancedCoordinate_zero : advancedCoordinate 0 = 0 := by
  apply Set.projIcc_of_le_left
  norm_num

@[simp] theorem advancedCoordinate_one : advancedCoordinate 1 = 1 := by
  apply Set.projIcc_of_right_le
  norm_num

theorem delayedCoordinate_eq_zero {t : I} (ht : (t : ℝ) ≤ 1 / 2) :
    delayedCoordinate t = 0 :=
  Set.projIcc_of_le_left zero_le_one (by linarith)

theorem advancedCoordinate_eq_one {t : I} (ht : 1 / 2 ≤ (t : ℝ)) :
    advancedCoordinate t = 1 :=
  Set.projIcc_of_right_le zero_le_one (by linarith)

universe u v
variable {Z : Type u} {Y : Type v} [TopologicalSpace Z] [TopologicalSpace Y] {b : Y}

/-- Reparametrization of a continuous family of based loops is homotopic
relative to every parameter where the family is the constant loop. -/
theorem path_family_reparam_homotopicRel
    (p q : C(Z, Path b b)) (S : Set Z) (hp : ∀ z ∈ S, p z = Path.refl b)
    (φ : C(I,I)) (hφ0 : φ 0 = 0) (hφ1 : φ 1 = 1)
    (he : ∀ z t, q z t = p z (φ t)) : p.HomotopicRel q S := by
  refine ⟨{
    toFun := fun z => {
      toFun := fun t => p z.2 (Set.Icc.convexComb t (φ t) z.1)
      continuous_toFun := by fun_prop
      source' := by simp [hφ0]
      target' := by simp [hφ1] }
    continuous_toFun := Path.continuous_uncurry_iff.mp (by
      change Continuous (fun z : (I × Z) × I =>
        p z.1.2 (Set.Icc.convexComb z.2 (φ z.2) z.1.1))
      fun_prop)
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }⟩
  · intro z
    apply Path.ext
    funext t
    simp
  · intro z
    apply Path.ext
    funext t
    simpa using (he z t).symm
  · intro s z hz
    apply Path.ext
    funext t
    simp [hp z hz]

/-- A continuous square whose left and bottom edges are constant gives a
homotopy from its top edge to its right edge. The construction is continuous
in every hopfAndDetector parameter and fixes parameters where the square is constant. -/
theorem square_edges_homotopicRel
    (F : C((I × I) × Z,Y)) (p q : C(Z, Path b b)) (S : Set Z)
    (hleft : ∀ t z, F ((0,t),z) = b)
    (hbottom : ∀ t z, F ((t,0),z) = b)
    (htop : ∀ t z, F ((t,1),z) = p z t)
    (hright : ∀ t z, F ((1,t),z) = q z t)
    (hS : ∀ s t z, z ∈ S → F ((s,t),z) = b) : p.HomotopicRel q S := by
  have hp (z : Z) (hz : z ∈ S) : p z = Path.refl b := by
    apply Path.ext
    funext t
    exact (htop t z).symm.trans (hS t 1 z hz)
  have hq (z : Z) (hz : z ∈ S) : q z = Path.refl b := by
    apply Path.ext
    funext t
    exact (hright t z).symm.trans (hS 1 t z hz)
  let delay : C(I,I) := ⟨delayedCoordinate,continuous_delayedCoordinate⟩
  let pd : C(Z,Path b b) := {
    toFun := fun z => (p z).reparam delayedCoordinate continuous_delayedCoordinate
      delayedCoordinate_zero delayedCoordinate_one
    continuous_toFun := Path.continuous_uncurry_iff.mp (by
      change Continuous (fun z : Z × I => p z.1 (delayedCoordinate z.2))
      fun_prop) }
  let qd : C(Z,Path b b) := {
    toFun := fun z => (q z).reparam delayedCoordinate continuous_delayedCoordinate
      delayedCoordinate_zero delayedCoordinate_one
    continuous_toFun := Path.continuous_uncurry_iff.mp (by
      change Continuous (fun z : Z × I => q z.1 (delayedCoordinate z.2))
      fun_prop) }
  have hpd : p.HomotopicRel pd S :=
    path_family_reparam_homotopicRel p pd S hp delay delayedCoordinate_zero
      delayedCoordinate_one (fun _ _ => rfl)
  have hqd : q.HomotopicRel qd S :=
    path_family_reparam_homotopicRel q qd S hq delay delayedCoordinate_zero
      delayedCoordinate_one (fun _ _ => rfl)
  refine hpd.trans ((show pd.HomotopicRel qd S from ?_).trans hqd.symm)
  refine ⟨{
    toFun := fun z => {
      toFun := fun t => F ((
        Set.Icc.convexComb (delayedCoordinate t) (advancedCoordinate t) z.1,
        Set.Icc.convexComb (advancedCoordinate t) (delayedCoordinate t) z.1),z.2)
      continuous_toFun := by fun_prop
      source' := by simp [hleft]
      target' := by simpa [htop] using (p z.2).target }
    continuous_toFun := Path.continuous_uncurry_iff.mp (by
      change Continuous (fun z : (I × Z) × I => F ((
        Set.Icc.convexComb (delayedCoordinate z.2) (advancedCoordinate z.2) z.1.1,
        Set.Icc.convexComb (advancedCoordinate z.2) (delayedCoordinate z.2) z.1.1),z.1.2))
      fun_prop)
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }⟩
  · intro z
    apply Path.ext
    funext t
    change F ((Set.Icc.convexComb _ _ 0,Set.Icc.convexComb _ _ 0),z) =
      p z (delayedCoordinate t)
    simp only [Set.Icc.convexComb_zero]
    by_cases ht : (t : ℝ) ≤ 1 / 2
    · rw [delayedCoordinate_eq_zero ht,hleft,Path.source]
    · rw [advancedCoordinate_eq_one (le_of_lt (lt_of_not_ge ht)),htop]
  · intro z
    apply Path.ext
    funext t
    change F ((Set.Icc.convexComb _ _ 1,Set.Icc.convexComb _ _ 1),z) =
      q z (delayedCoordinate t)
    simp only [Set.Icc.convexComb_one]
    by_cases ht : (t : ℝ) ≤ 1 / 2
    · rw [delayedCoordinate_eq_zero ht,hbottom,Path.source]
    · rw [advancedCoordinate_eq_one (le_of_lt (lt_of_not_ge ht)),hright]
  · intro s z hz
    apply Path.ext
    funext t
    change F ((_,_),z) = p z (delayedCoordinate t)
    rw [hS _ _ z hz,hp z hz]
    rfl

end KIP126.Topology.Cube
