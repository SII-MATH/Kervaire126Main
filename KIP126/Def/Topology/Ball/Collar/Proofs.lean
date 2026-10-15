module

public import KIP126.Def.Topology.Ball.Collar.Data
public import KIP126.Def.Topology.Pushout.Neighborhood.Proofs

@[expose] public section

namespace KIP126.Topology.Ball

open Metric Set CategoryTheory CategoryTheory.Limits _root_.Topology

universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option backward.isDefEq.respectTransparency false

omit [NormedSpace ℝ E] in
/-- The radial collar is open in the actual closed ball. -/
theorem unitDiskCollar_isOpen : IsOpen (unitDiskCollar E) :=
  isOpen_lt continuous_const (continuous_norm.comp continuous_subtype_val)

omit [NormedSpace ℝ E] in
/-- Every boundary point lies in the radial collar. -/
theorem unitDiskBoundary_mem_collar (s : sphere (0 : E) 1) :
    unitDiskBoundary E s ∈ unitDiskCollar E := by
  have hs : ‖s.1‖ = 1 := mem_sphere_zero_iff_norm.mp s.2
  change (1:ℝ)/2 < ‖s.1‖
  rw [hs]
  norm_num

/-- The collar projection fixes each actual boundary point. -/
theorem unitDiskCollarProjection_boundary (s : sphere (0 : E) 1) :
    unitDiskCollarProjection E ⟨unitDiskBoundary E s,unitDiskBoundary_mem_collar s⟩ = s := by
  apply Subtype.ext
  have hs : ‖s.1‖ = 1 := mem_sphere_zero_iff_norm.mp s.2
  simp [unitDiskCollarProjection,unitDiskBoundary,hs]

omit [NormedSpace ℝ E] in
/-- The standard disk boundary map is a closed embedding, in every real
normed space, without requiring the disk to be compact. -/
theorem unitDiskBoundary_isClosedEmbedding : IsClosedEmbedding (unitDiskBoundary E) :=
  IsClosedEmbedding.inclusion sphere_subset_closedBall
    (isClosed_sphere.preimage continuous_subtype_val)

/-- Attaching a genuine closed disk gives an actual open neighborhood of
the old space with a continuous retraction onto it. -/
theorem exists_open_disk_attachment_retraction
    {B P : TopCat.{u}} (b₀ : B)
    {f : TopCat.of (sphere (0 : E) 1) ⟶ B}
    {a : TopCat.of (closedBall (0 : E) 1) ⟶ P} {b : B ⟶ P}
    (h : IsPushout (unitDiskBoundary E) f a b) :
    ∃ V : Set P, IsOpen V ∧ Set.range b ⊆ V ∧
      ∃ g : C(V,B), ∀ y (hy : b y ∈ V), g ⟨b y,hy⟩ = y := by
  classical
  let r : closedBall (0 : E) 1 → B := fun x =>
    if hx : x ∈ unitDiskCollar E then f (unitDiskCollarProjection E ⟨x,hx⟩) else b₀
  have hr : ContinuousOn r (unitDiskCollar E) := by
    apply continuousOn_iff_continuous_restrict.mpr
    have he : (fun x : unitDiskCollar E => r x.1) =
        fun x => f (unitDiskCollarProjection E x) := by
      funext x
      simp [r,x.2]
    change Continuous (fun x : unitDiskCollar E => r x.1)
    rw [he]
    exact f.hom.continuous.comp (unitDiskCollarProjection E).continuous
  have hri (s : sphere (0 : E) 1) : r (unitDiskBoundary E s) = f s := by
    dsimp only [r]
    rw [dif_pos (unitDiskBoundary_mem_collar s)]
    exact congrArg f (unitDiskCollarProjection_boundary s)
  obtain ⟨V,hV,hbV,g,hgb,_⟩ := exists_open_pushout_retraction h
    unitDiskBoundary_isClosedEmbedding (unitDiskCollar E) unitDiskCollar_isOpen
    (by rintro _ ⟨s,rfl⟩; exact unitDiskBoundary_mem_collar s) r hr hri
  exact ⟨V,hV,hbV,g,hgb⟩

end KIP126.Topology.Ball
