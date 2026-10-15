module

public import KIP126.Def.StableHomotopy.Spectra.BasedSpace.Suspension.Cell.Boundary

@[expose] public section

namespace KIP126.StableHomotopy.Spectra.BasedSpace

open CategoryTheory CategoryTheory.Limits KIP126.Topology.HomotopyLifting
open scoped unitInterval

universe u

set_option backward.isDefEq.respectTransparency false

/-- An actual based map obtained by attaching one ordinary cube remains an
ordinary single-cell attachment after reduced suspension. The cell dimension
increases by one and the old-space map is the original suspended based map. -/
theorem suspendMap_isPushout_of_cube_attachment (n : ℕ) {A B : BasedSpace.{u}}
    (a : cubeBoundaryObject n ⟶ A.space) (c : cubeObject n ⟶ B.space)
    (f : A ⟶ B) (h : IsPushout (cubeBoundaryInclusion n) a c (TopCat.ofHom f.map)) :
    IsPushout (cubeBoundaryInclusion (n+1)) (suspensionCellBoundary n A a)
      (suspensionCellCharacteristic n B c) (TopCat.ofHom (suspendMap f).map) := by
  let w := suspensionCell_square n a c f h.w
  suffices hl : ∀ s : PushoutCocone (cubeBoundaryInclusion (n+1))
      (suspensionCellBoundary n A a),
      ∃ d : B.suspension.space ⟶ s.pt,
        suspensionCellCharacteristic n B c ≫ d = s.inl ∧
        TopCat.ofHom (suspendMap f).map ≫ d = s.inr by
    classical
    apply IsPushout.of_isColimit (c := PushoutCocone.mk _ _ w)
    refine PushoutCocone.IsColimit.mk _ (fun s => (hl s).choose)
      (fun s => (hl s).choose_spec.1) (fun s => (hl s).choose_spec.2) ?_
    intro s m hm₁ hm₂
    ext z
    refine Quot.inductionOn z ?_
    rintro ⟨b,t⟩
    rcases Types.eq_or_eq_of_isPushout (h.map (forget TopCat)) b with ⟨x,rfl⟩ | ⟨x,rfl⟩
    · let q := (cubeObjectSuccHomeomorph n).symm (t,x)
      exact (ConcreteCategory.congr_hom hm₁ q).trans
        (ConcreteCategory.congr_hom (hl s).choose_spec.1 q).symm
    · exact (ConcreteCategory.congr_hom hm₂ (suspensionProjection A (x,t))).trans
        (ConcreteCategory.congr_hom (hl s).choose_spec.2
          (suspensionProjection A (x,t))).symm
  intro s
  let uA : C(A × I, s.pt) := s.inr.hom.comp (suspensionProjection A)
  let uC : C(cubeObject n × I, s.pt) := s.inl.hom.comp
    ⟨fun q => (cubeObjectSuccHomeomorph n).symm (q.2,q.1),
      (cubeObjectSuccHomeomorph n).symm.continuous.comp
        (continuous_snd.prodMk continuous_fst)⟩
  have hu : cubeBoundaryInclusion n ≫ TopCat.ofHom uC.curry =
      a ≫ TopCat.ofHom uA.curry := by
    ext x t
    have he := ConcreteCategory.congr_hom s.condition
      (cubeBoundaryProductSideInclusion n (t,x))
    change uC (cubeBoundaryInclusion n x,t) = _ at he
    exact he.trans (congrArg s.inr (suspensionCellBoundary_side n A a (t,x)))
  let v := h.desc (TopCat.ofHom uC.curry) (TopCat.ofHom uA.curry) hu
  let E : C(B × I, s.pt) := v.hom.uncurry
  have hC (x : cubeObject n) (t : I) : E (c x,t) = uC (x,t) :=
    congrArg (fun p : C(I,s.pt) => p t)
      (ConcreteCategory.congr_hom (h.inl_desc _ _ hu) x)
  have hA (x : A) (t : I) : E (f.map x,t) = uA (x,t) :=
    congrArg (fun p : C(I,s.pt) => p t)
      (ConcreteCategory.congr_hom (h.inr_desc _ _ hu) x)
  have hCe (x : cubeObject n) (t : I) (ht : t = 0 ∨ t = 1) :
      uC (x,t) = s.inr A.suspension.point := by
    have he := ConcreteCategory.congr_hom s.condition
      (cubeBoundaryProductEndInclusion n (⟨t,ht⟩,x))
    change uC (x,t) = _ at he
    exact he.trans (congrArg s.inr (suspensionCellBoundary_ends n A a (⟨t,ht⟩,x)))
  have hc (p : B × I) (hp : SuspensionCollapsed B p) :
      E p = s.inr A.suspension.point := by
    rcases hp with hp | hp
    · have he : p = (f.map A.point,p.2) := Prod.ext (hp.trans f.point.symm) rfl
      rw [he, hA]
      change s.inr (suspensionProjection A (A.point,p.2)) = _
      rw [suspensionProjection_collapsed A _ (Or.inl rfl)]
    · rcases Types.eq_or_eq_of_isPushout (h.map (forget TopCat)) p.1 with ⟨x,hx⟩ | ⟨x,hx⟩
      · have he : p = (c x,p.2) := Prod.ext hx.symm rfl
        rw [he,hC]
        exact hCe x p.2 hp
      · have he : p = (f.map x,p.2) := Prod.ext hx.symm rfl
        rw [he,hA]
        change s.inr (suspensionProjection A (x,p.2)) = _
        rw [suspensionProjection_collapsed A _ (Or.inr hp)]
  have hr : ∀ p q, SuspensionRelation B p q → E p = E q :=
    fun p q hpq => (hc p hpq.1).trans (hc q hpq.2).symm
  let d : B.suspension.space ⟶ s.pt := TopCat.ofHom
    ⟨Quot.lift E hr, continuous_quot_lift hr E.continuous⟩
  refine ⟨d, ?_, ?_⟩
  · ext x
    change E (c (cubeObjectSuccHomeomorph n x).2,
      (cubeObjectSuccHomeomorph n x).1) = s.inl x
    rw [hC]
    exact congrArg s.inl ((cubeObjectSuccHomeomorph n).symm_apply_apply x)
  · ext x
    refine Quot.inductionOn x ?_
    rintro ⟨a,t⟩
    exact hA a t

end KIP126.StableHomotopy.Spectra.BasedSpace
