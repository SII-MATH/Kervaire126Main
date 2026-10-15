module

public import KIP126.Def.Topology.SimplicialRealization.FiniteSkeleton.Proofs
public import KIP126.Def.Topology.SimplicialRealization.Collar.Proofs
public import KIP126.Def.Topology.FiberBundle.Attachment.Proofs
public import KIP126.Def.Topology.HomotopyLifting.Coproduct.Proofs

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory CategoryTheory.Limits Simplicial Opposite
universe u v w
set_option backward.isDefEq.respectTransparency false

/-- Actual product trivializations over all the original simplices of a
finite simplicial realization give actual open local trivializations. -/
theorem finite_realization_localTriviality_of_simplex_triviality
    (X : SSet.{u}) [X.Finite] {E : Type v} [TopologicalSpace E]
    {F : Type w} [TopologicalSpace F] [Nonempty F] (p : C(E,|X|))
    (hsimplex : ∀ (n : ℕ) (s : X.obj (op ⦋n⦌)),
      ∃ e : {z : E × |(Δ[n] : SSet.{u})| //
        p z.1 = SSet.toTop.map (SSet.yonedaEquiv.symm s) z.2} ≃ₜ (F × |(Δ[n] : SSet.{u})|),
        ∀ z, (e z).2 = z.val.2) :
    ∀ x, ∃ T : Bundle.Trivialization F p, x ∈ T.baseSet := by
  classical
  have hstage (n : ℕ) : ∀ x,
      ∃ T : Bundle.Trivialization F (pullbackSndMap p ((cellComplex X).incl.app n).hom),
        x ∈ T.baseSet := by
    induction n with
    | zero =>
      letI := cellComplex_stage_zero_isEmpty X
      exact fun x => isEmptyElim x
    | succ n ih =>
      let c := (cellComplex X).attachCells n (by simp)
      let a := ((cellComplex X).incl.app (n+1)).hom
      let q := pullbackSndMap p a
      let b := ((cellComplex X).F.map (homOfLE (Nat.le_succ n))).hom
      letI : CompactSpace c.cofan₂.pt := finite_cellComplex_cell_coproduct_compact X n
      letI : CompactSpace ((cellComplex X).F.obj n) := finite_cellComplex_stage_compact X n
      letI : T2Space ((cellComplex X).F.obj (n+1)) := cellComplex_stage_t2Space X (n+1)
      letI : T2Space ((cellComplex X).F.obj (Order.succ n)) := cellComplex_stage_t2Space X (n+1)
      letI : NormalSpace c.cofan₂.pt := (simplexCellCoproduct_separation X n).1
      letI : T2Space c.cofan₂.pt := (simplexCellCoproduct_separation X n).2
      have hcell (k : c.ι) : ∃ e :
          {z : {z : E × ((cellComplex X).F.obj (n+1)) // p z.1 = a z.2} × |(Δ[n] : SSet.{u})| //
            q z.1 = c.g₂ (c.cofan₂.inj k z.2)} ≃ₜ (F × |(Δ[n] : SSet.{u})|),
          ∀ z, (e z).2 = z.val.2 := by
        let t := (c.cell k).hom
        have ht : a.comp t = (SSet.toTop.map (SSet.yonedaEquiv.symm k.simplex)).hom := by
          ext x
          exact ConcreteCategory.congr_hom (cellComplex_cell_characteristic X n k) x
        have hd : ∃ e : {z : E × |(Δ[n] : SSet.{u})| // p z.1 = (a.comp t) z.2} ≃ₜ
            (F × |(Δ[n] : SSet.{u})|), ∀ z, (e z).2 = z.val.2 := by
          rw [ht]
          exact hsimplex n k.simplex
        obtain ⟨e,he⟩ := hd
        exact ⟨(iteratedPullbackHomeomorph p a t).trans e,fun z => he _⟩
      choose e he using hcell
      obtain ⟨eA,heA⟩ := HomotopyLifting.coproduct_pullback_product_homeomorph
        c.cofan₂ c.isColimit₂ q c.g₂ e he
      have hab : a.comp b = ((cellComplex X).incl.app n).hom := by
        ext x
        exact ConcreteCategory.congr_hom (cellComplex_step_inclusion X n) x
      have hB : ∀ x, ∃ T : Bundle.Trivialization F (pullbackSndMap q b), x ∈ T.baseSet := by
        have hh : ∀ x, ∃ T : Bundle.Trivialization F (pullbackSndMap p (a.comp b)),
            x ∈ T.baseSet := by
          rw [hab]
          exact ih
        exact localTriviality_of_total_homeomorph _ (pullbackSndMap q b)
          (iteratedPullbackHomeomorph p a b) (fun _ => rfl) hh
      exact localTriviality_of_attachment c.isPushout.flip
        (cellComplex_boundary_coproduct_isClosedEmbedding X n)
        (fun y => cellComplex_attachmentCollar X n y) q eA heA hB
  obtain ⟨d,hd⟩ := finite_cellComplex_exists_terminal_stage X
  letI := hd
  exact localTriviality_of_pullback_base_homeomorph p
    (TopCat.homeoOfIso (asIso ((cellComplex X).incl.app d))) (hstage d)

end KIP126.Topology.SimplicialRealization
