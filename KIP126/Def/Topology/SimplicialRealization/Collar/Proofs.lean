module

public import KIP126.Def.Topology.Pushout.Collar.Coproduct.Proofs
public import KIP126.Def.Topology.SimplicialRealization.Classical.Proofs
public import KIP126.Def.Topology.SimplicialRealization.DiskPair.Proofs

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory CategoryTheory.Limits Simplicial Opposite _root_.Topology

universe u

set_option backward.isDefEq.respectTransparency false

/-- The universe-lifted disk used by the actual cell complex has its
genuine radial boundary retraction on an open collar. -/
theorem exists_diskBoundary_open_retraction (n : ℕ) :
    ∃ W : Set (TopCat.disk.{u} n), ∃ _ : IsOpen W,
      ∃ hiW : ∀ s, TopCat.diskBoundaryInclusion n s ∈ W,
      ∃ r : C(W, TopCat.diskBoundary.{u} n),
        ∀ s, r ⟨TopCat.diskBoundaryInclusion n s, hiW s⟩ = s := by
  exact exists_open_boundary_retraction_of_homeomorph
    (TopCat.diskBoundaryInclusion.{u} n).hom
    (Ball.unitDiskBoundary (EuclideanSpace ℝ (Fin n))).hom
    Homeomorph.ulift Homeomorph.ulift (fun _ => rfl)
    (Ball.unitDiskCollar (EuclideanSpace ℝ (Fin n))) Ball.unitDiskCollar_isOpen
    Ball.unitDiskBoundary_mem_collar (Ball.unitDiskCollarProjection _)
    Ball.unitDiskCollarProjection_boundary

/-- The actual realized simplex boundary has an open neighborhood with
a continuous retraction fixing the entire realized boundary. -/
theorem exists_simplex_boundary_open_retraction (n : ℕ) :
    ∃ W : Set |(Δ[n] : SSet.{u})|, ∃ _ : IsOpen W,
      ∃ hiW : ∀ s, SSet.toTop.map (∂Δ[n].ι) s ∈ W,
      ∃ r : C(W, |(∂Δ[n] : SSet.{u})|),
        ∀ s, r ⟨SSet.toTop.map (∂Δ[n].ι) s, hiW s⟩ = s := by
  obtain ⟨q⟩ := nonempty_boundary_realization_disk_arrow_iso.{u} n
  obtain ⟨W, hW, hiW, r, hri⟩ := exists_diskBoundary_open_retraction.{u} n
  let eS := TopCat.homeoOfIso (Arrow.leftFunc.mapIso q)
  let eA := TopCat.homeoOfIso (Arrow.rightFunc.mapIso q)
  exact exists_open_boundary_retraction_of_homeomorph
    (SSet.toTop.map (∂Δ[n].ι)).hom (TopCat.diskBoundaryInclusion n).hom eS eA
    (fun s => (ConcreteCategory.congr_hom q.hom.w s).symm) W hW hiW r hri

/-- Each actual simplicial skeletal attachment has a descended open
collar of its old stage, constructed from radial simplex collars. -/
theorem cellComplex_attachmentCollar (X : SSet.{u}) (n : ℕ)
    (b₀ : (cellComplex X).F.obj n) :
    let a := (cellComplex X).attachCells n (by simp)
    Nonempty (AttachmentCollar a.m a.g₁ a.g₂
      ((cellComplex X).F.map (homOfLE (Nat.le_succ n)))) := by
  let a := (cellComplex X).attachCells n (by simp)
  letI : NormalSpace a.cofan₂.pt := (simplexCellCoproduct_separation X n).1
  letI : T2Space a.cofan₂.pt := (simplexCellCoproduct_separation X n).2
  obtain ⟨W, hW, hiW, r, hri⟩ := exists_simplex_boundary_open_retraction.{u} n
  obtain ⟨V, hV, hmV, q, hqm⟩ := exists_coproduct_open_boundary_retraction
    (fun _ : a.ι => SSet.toTop.map (∂Δ[n].ι)) a.cofan₁ a.cofan₂
    a.isColimit₁ a.isColimit₂ a.m a.hm (fun _ => W) (fun _ => hW)
    (fun _ => hiW) (fun _ => r) (fun _ => hri)
  have hm : IsClosedEmbedding a.m := isClosedEmbedding_of_coproduct
    (fun _ : a.ι => SSet.toTop.map (∂Δ[n].ι))
    (fun _ => realization_mono_isClosedEmbedding (∂Δ[n].ι))
    a.cofan₁ a.cofan₂ a.isColimit₁ a.isColimit₂ a.m a.hm
  exact exists_attachmentCollar a.isPushout.flip hm b₀ V hV hmV q hqm

end KIP126.Topology.SimplicialRealization
