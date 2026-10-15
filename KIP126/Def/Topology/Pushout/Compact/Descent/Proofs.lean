module

public import KIP126.Def.Topology.Pushout.Compact.Proofs
public import KIP126.Def.Topology.Pushout.Cells.Proofs

@[expose] public section

namespace KIP126.Topology
open CategoryTheory CategoryTheory.Limits _root_.Topology
universe u v w
set_option backward.isDefEq.respectTransparency false

/-- Continuity after arbitrary base change of a finite compact attachment is
detected on its two actual pullback pieces. No local compactness of the
parameter space or of the target is required. -/
theorem continuous_of_compact_pushout_pullback
    {S A B P : TopCat.{u}} [CompactSpace A] [CompactSpace B] [T2Space P]
    {i : S ⟶ A} {f : S ⟶ B} {a : A ⟶ P} {b : B ⟶ P}
    (h : IsPushout i f a b)
    {T : Type v} [TopologicalSpace T] (k : C(T,P))
    {F : Type w} [TopologicalSpace F] (m : T → F)
    (ha : Continuous (fun x : {zt : A × T // a zt.1 = k zt.2} => m x.val.2))
    (hb : Continuous (fun x : {bt : B × T // b bt.1 = k bt.2} => m x.val.2)) :
    Continuous m := by
  let A' := {zt : A × T // a zt.1 = k zt.2}
  let B' := {bt : B × T // b bt.1 = k bt.2}
  let q : A' ⊕ B' → T := Sum.elim (fun x => x.val.2) (fun x => x.val.2)
  have hA := compact_pullback_snd_isProperMap a a.hom.continuous k k.continuous
  have hB := compact_pullback_snd_isProperMap b b.hom.continuous k k.continuous
  have hq : IsQuotientMap q := (hA.isClosedMap.sumElim hB.isClosedMap).isQuotientMap
    (hA.continuous.sumElim hB.continuous) (by
      intro t
      obtain ⟨x,hx⟩ | ⟨y,hy⟩ := Types.eq_or_eq_of_isPushout (h.map (forget TopCat)) (k t)
      · exact ⟨Sum.inl ⟨(x,t),hx⟩,rfl⟩
      · exact ⟨Sum.inr ⟨(y,t),hy⟩,rfl⟩)
  apply hq.continuous_iff.mpr
  exact continuous_sum_dom.mpr ⟨ha,hb⟩


end KIP126.Topology
