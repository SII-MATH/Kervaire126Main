module

public import KIP126.Def.Topology.FiberBundle.Attachment.Equivalence.Data
public import KIP126.Def.Topology.FiberBundle.OpenEmbedding
public import KIP126.Def.Topology.FiberBundle.Pullback.Chart
public import KIP126.Def.Topology.FiberBundle.Pullback.Proofs
public import KIP126.Def.Topology.FiberBundle.Chart.Global

@[expose] public section

namespace KIP126.Topology

open CategoryTheory CategoryTheory.Limits _root_.Topology Set

universe u v w

set_option backward.isDefEq.respectTransparency false

/-- Local product charts extend across an actual compact cell attachment.
The proof constructs open collar charts at old points and uses the
actual open cell complement at new points. -/
theorem localTriviality_of_attachment
    {S A B P : TopCat.{u}} [CompactSpace A] [CompactSpace B] [T2Space P]
    [NormalSpace A] [T1Space A]
    {i : S ⟶ A} {f : S ⟶ B} {a : A ⟶ P} {b : B ⟶ P}
    (h : IsPushout i f a b) (hi : IsClosedEmbedding i)
    (hc : ∀ y : B, Nonempty (AttachmentCollar i f a b))
    {E : Type v} [TopologicalSpace E] {F : Type w} [TopologicalSpace F] [Nonempty F]
    (p : C(E,P)) (e : {z : E × A // p z.1 = a z.2} ≃ₜ (F × A))
    (he : ∀ z, (e z).2 = z.val.2)
    (hB : ∀ y, ∃ T : Bundle.Trivialization F (pullbackSndMap p b.hom), y ∈ T.baseSet) :
    ∀ x, ∃ T : Bundle.Trivialization F p, x ∈ T.baseSet := by
  intro x
  obtain (⟨y,rfl⟩ | ⟨x,rfl,hx⟩) := Types.eq_or_eq_of_isPushout' (h.flip.map (forget TopCat)) x
  · obtain ⟨c⟩ := hc y
    let j : C(c.V,P) := ⟨Subtype.val,continuous_subtype_val⟩
    let q : C(c.Target p,c.V) := pullbackSndMap p (b.hom.comp c.g)
    have hq : ∀ z, ∃ T : Bundle.Trivialization F q, z ∈ T.baseSet := by
      have hpb := localTriviality_pullback (pullbackSndMap p b.hom) c.g hB
      exact localTriviality_of_total_homeomorph _ q
        (iteratedPullbackHomeomorph p b.hom c.g).symm (fun _ => rfl) hpb
    have hj : ∀ z, ∃ T : Bundle.Trivialization F (pullbackSndMap p j), z ∈ T.baseSet :=
      localTriviality_of_total_homeomorph q (pullbackSndMap p j)
        (attachmentCollarHomeomorph h hi c p e he)
        (fun z => attachmentCollarForward_snd h c p e he z) hq
    have hy : b y ∈ c.V := (Set.eq_univ_iff_forall.mp c.preimage_b) y
    obtain ⟨T,hT⟩ := hj ⟨b y,hy⟩
    exact localTriviality_at_of_openEmbedding p j c.open_V.isOpenEmbedding_subtypeVal ⟨b y,hy⟩ T hT
  · let U : Set A := (Set.range i)ᶜ
    let j : C(U,A) := ⟨Subtype.val,continuous_subtype_val⟩
    let aj : C(U,P) := a.hom.comp j
    have hA : ∀ z, ∃ T : Bundle.Trivialization F (pullbackSndMap p a.hom), z ∈ T.baseSet :=
      FiberBundle.localTriviality_of_globalProduct _
        (e.trans (Homeomorph.prodComm F A)) he
    have hj : ∀ z, ∃ T : Bundle.Trivialization F (pullbackSndMap p aj), z ∈ T.baseSet := by
      have hpj := localTriviality_pullback (pullbackSndMap p a.hom) j hA
      exact localTriviality_of_total_homeomorph _ (pullbackSndMap p aj)
        (iteratedPullbackHomeomorph p a.hom j).symm (fun _ => rfl) hpj
    obtain ⟨T,hT⟩ := hj ⟨x,hx⟩
    exact localTriviality_at_of_openEmbedding p aj
      (isOpenEmbedding_pushout_boundary_complement h hi) ⟨x,hx⟩ T hT

end KIP126.Topology
