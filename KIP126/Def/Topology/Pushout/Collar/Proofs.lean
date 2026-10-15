module

public import KIP126.Def.Topology.Pushout.Collar.Data
public import KIP126.Def.Topology.Ball.Collar.Proofs

@[expose] public section

namespace KIP126.Topology

open CategoryTheory CategoryTheory.Limits _root_.Topology Set

universe u

set_option backward.isDefEq.respectTransparency false

/-- An actual retraction of the boundary collar constructs the full
attachment collar, including both exact preimages and descended formulas. -/
theorem exists_attachmentCollar
    {S A B P : TopCat.{u}} [NormalSpace A] [T1Space A]
    {i : S ⟶ A} {f : S ⟶ B} {a : A ⟶ P} {b : B ⟶ P}
    (h : IsPushout i f a b) (hi : IsClosedEmbedding i) (b₀ : B)
    (W : Set A) (hW : IsOpen W) (hiW : ∀ s, i s ∈ W)
    (r : C(W,S)) (hri : ∀ s, r ⟨i s,hiW s⟩ = s) :
    Nonempty (AttachmentCollar i f a b) := by
  classical
  let rA : A → B := fun x => if hx : x ∈ W then f (r ⟨x,hx⟩) else b₀
  have hrA : ContinuousOn rA W := by
    apply continuousOn_iff_continuous_restrict.mpr
    change Continuous (fun x : W => rA x.1)
    have he : (fun x : W => rA x.1) = fun x => f (r x) := by
      funext x
      simp [rA,x.2]
    rw [he]
    exact f.hom.continuous.comp r.continuous
  have hrAi (s : S) : rA (i s) = f s := by
    dsimp only [rA]
    rw [dif_pos (hiW s),hri]
  obtain ⟨V,hV,haV,hbV,g,hgb,hga⟩ :=
    exists_open_pushout_retraction_with_preimages h hi W hW
      (by rintro _ ⟨s,rfl⟩; exact hiW s) rA hrA hrAi
  refine ⟨⟨W,hW,hiW,r,hri,V,hV,haV,hbV,g,?_,hgb⟩⟩
  intro x hx
  rw [hga]
  dsimp only [rA]
  rw [dif_pos (by rw [← haV]; exact hx)]

/-- Every actual disk attachment carries the radial attachment collar.
Its existence has no additional collar or local-triviality premise. -/
theorem exists_disk_attachmentCollar
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {B P : TopCat.{u}} (b₀ : B)
    {f : TopCat.of (Metric.sphere (0 : E) 1) ⟶ B}
    {a : TopCat.of (Metric.closedBall (0 : E) 1) ⟶ P} {b : B ⟶ P}
    (h : IsPushout (Ball.unitDiskBoundary E) f a b) :
    Nonempty (AttachmentCollar (Ball.unitDiskBoundary E) f a b) :=
  exists_attachmentCollar h Ball.unitDiskBoundary_isClosedEmbedding b₀
    (Ball.unitDiskCollar E) Ball.unitDiskCollar_isOpen Ball.unitDiskBoundary_mem_collar
    (Ball.unitDiskCollarProjection E) Ball.unitDiskCollarProjection_boundary

end KIP126.Topology
