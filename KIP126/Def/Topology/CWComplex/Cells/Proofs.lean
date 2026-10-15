module

public import KIP126.Def.Topology.Pushout.Cells.Proofs
public import KIP126.Def.Topology.CWComplex.ClosedEmbedding.Proofs

@[expose] public section

namespace KIP126.Topology

open CategoryTheory CategoryTheory.Limits _root_.Topology Set HomotopicalAlgebra

universe u

set_option backward.isDefEq.respectTransparency false

/-- Coproduct coordinates identify the attaching boundary componentwise. -/
theorem coproduct_inj_mem_range_iff
    {ι : Type u} {A B : ι → TopCat.{u}} (f : ∀ i, A i ⟶ B i)
    (cA : Cofan A) (cB : Cofan B) (hA : IsColimit cA) (hB : IsColimit cB)
    (m : cA.pt ⟶ cB.pt) (hm : ∀ i, cA.inj i ≫ m = f i ≫ cB.inj i)
    (k : ι) (x : B k) : cB.inj k x ∈ Set.range m ↔ x ∈ Set.range (f k) := by
  let eA := hA.coconePointUniqueUpToIso (TopCat.sigmaCofanIsColimit A)
  let eB := hB.coconePointUniqueUpToIso (TopCat.sigmaCofanIsColimit B)
  have hAinj (k : ι) (x : A k) : eA.hom (cA.inj k x) = Sigma.mk k x := by
    have h := IsColimit.comp_coconePointUniqueUpToIso_hom hA
      (TopCat.sigmaCofanIsColimit A) (Discrete.mk k)
    exact ConcreteCategory.congr_hom h x
  have hBinj (k : ι) (x : B k) : eB.hom (cB.inj k x) = Sigma.mk k x := by
    have h := IsColimit.comp_coconePointUniqueUpToIso_hom hB
      (TopCat.sigmaCofanIsColimit B) (Discrete.mk k)
    exact ConcreteCategory.congr_hom h x
  constructor
  · rintro ⟨y,hy⟩
    obtain ⟨j,z,hz⟩ : ∃ j z, cA.inj j z = y := by
      obtain ⟨j,z,hjz⟩ : ∃ j z, eA.hom y = (⟨j,z⟩ : Σ i, A i) := by
        exact ⟨(eA.hom y).1,(eA.hom y).2,rfl⟩
      refine ⟨j,z,?_⟩
      apply (TopCat.homeoOfIso eA).injective
      exact (hAinj j z).trans hjz.symm
    rw [← hz] at hy
    have h := ConcreteCategory.congr_hom (hm j) z
    have he : (⟨j,f j z⟩ : Σ i, B i) = ⟨k,x⟩ := by
      rw [← hBinj,← hBinj]
      exact congrArg eB.hom (h.symm.trans hy)
    have hj : j = k := congrArg Sigma.fst he
    subst j
    exact ⟨z,@sigma_mk_injective ι (fun i => B i) k _ _ he⟩
  · rintro ⟨y,rfl⟩
    exact ⟨cA.inj k y,ConcreteCategory.congr_hom (hm k) y⟩

/-- Each coproduct summand carries its usual open embedding. -/
theorem isOpenEmbedding_coproduct_inj
    {ι : Type u} {A : ι → TopCat.{u}} (c : Cofan A) (hc : IsColimit c) (k : ι) :
    IsOpenEmbedding (c.inj k) := by
  let e := hc.coconePointUniqueUpToIso (TopCat.sigmaCofanIsColimit A)
  have he : (c.inj k : A k → c.pt) = (TopCat.homeoOfIso e).symm ∘ Sigma.mk k := by
    funext x
    apply (TopCat.homeoOfIso e).injective
    exact (ConcreteCategory.congr_hom
      (IsColimit.comp_coconePointUniqueUpToIso_hom hc
        (TopCat.sigmaCofanIsColimit A) (Discrete.mk k)) x).trans
      ((TopCat.homeoOfIso e).apply_symm_apply _).symm
  rw [he]
  exact (TopCat.homeoOfIso e).symm.isOpenEmbedding.comp IsOpenEmbedding.sigmaMk

/-- Coproduct summands have disjoint images, including their point coordinates. -/
theorem coproduct_inj_eq_iff
    {ι : Type u} {A : ι → TopCat.{u}} (c : Cofan A) (hc : IsColimit c)
    {k l : ι} {x : A k} {y : A l} :
    c.inj k x = c.inj l y ↔ (⟨k,x⟩ : Σ i, A i) = ⟨l,y⟩ := by
  let e := hc.coconePointUniqueUpToIso (TopCat.sigmaCofanIsColimit A)
  have he (i : ι) (z : A i) : e.hom (c.inj i z) = Sigma.mk i z :=
    ConcreteCategory.congr_hom
      (IsColimit.comp_coconePointUniqueUpToIso_hom hc
        (TopCat.sigmaCofanIsColimit A) (Discrete.mk i)) z
  constructor
  · intro h
    exact (he k x).symm.trans ((congrArg e.hom h).trans (he l y))
  · intro h
    apply (TopCat.homeoOfIso e).injective
    exact (he k x).trans (h.trans (he l y).symm)

/-- An interior point of an attached cell can only equal the same point
in the same cell; no other cell acquires an interior identification. -/
theorem attachCells_interior_eq_iff
    {α : Type*} {A B : α → TopCat.{u}} {g : ∀ i, A i ⟶ B i}
    {X Y : TopCat.{u}} {f : X ⟶ Y} (c : AttachCells.{u} g f)
    [NormalSpace c.cofan₂.pt] [T1Space c.cofan₂.pt]
    (hg : ∀ i, IsClosedEmbedding (g i))
    {k l : c.ι} {x : B (c.π k)} {y : B (c.π l)} (hx : x ∉ Set.range (g (c.π k))) :
    c.cell k x = c.cell l y ↔ (⟨k,x⟩ : Σ i, B (c.π i)) = ⟨l,y⟩ := by
  have hm := isClosedEmbedding_of_coproduct (fun i => g (c.π i))
    (fun i => hg (c.π i)) c.cofan₁ c.cofan₂ c.isColimit₁ c.isColimit₂ c.m c.hm
  have hx' : c.cofan₂.inj k x ∉ Set.range c.m := by
    simpa only [coproduct_inj_mem_range_iff _ _ _ c.isColimit₁ c.isColimit₂ c.m c.hm] using hx
  constructor
  · intro h
    apply (coproduct_inj_eq_iff c.cofan₂ c.isColimit₂).mp
    exact pushout_cell_eq_of_outside_boundary c.isPushout.flip hm hx' h
  · intro h
    exact congrArg c.g₂ ((coproduct_inj_eq_iff c.cofan₂ c.isColimit₂).mpr h)

/-- An interior point in a newly attached cell is outside the previous stage. -/
theorem attachCells_interior_not_mem_range
    {α : Type*} {A B : α → TopCat.{u}} {g : ∀ i, A i ⟶ B i}
    {X Y : TopCat.{u}} {f : X ⟶ Y} (c : AttachCells.{u} g f)
    (hg : ∀ i, IsClosedEmbedding (g i))
    (k : c.ι) (x : B (c.π k)) (hx : x ∉ Set.range (g (c.π k))) :
    c.cell k x ∉ Set.range f := by
  have hm := isClosedEmbedding_of_coproduct (fun i => g (c.π i))
    (fun i => hg (c.π i)) c.cofan₁ c.cofan₂ c.isColimit₁ c.isColimit₂ c.m c.hm
  rintro ⟨y,hy⟩
  obtain ⟨s,hs,_⟩ :=
    (Types.pushoutCocone_inl_eq_inr_iff_of_isColimit
      (c.isPushout.flip.map (forget TopCat)).isColimit hm.injective
      (c.cofan₂.inj k x) y).mp hy.symm
  exact hx ((coproduct_inj_mem_range_iff _ _ _ c.isColimit₁ c.isColimit₂ c.m c.hm k x).mp ⟨s,hs⟩)

/-- The interior of every attached cell is open embedded in the successor
stage; the statement uses the actual boundary complement. -/
theorem isOpenEmbedding_attachCells_boundary_complement
    {α : Type*} {A B : α → TopCat.{u}} {g : ∀ i, A i ⟶ B i}
    {X Y : TopCat.{u}} {f : X ⟶ Y} (c : AttachCells.{u} g f)
    [NormalSpace c.cofan₂.pt] [T1Space c.cofan₂.pt]
    (hg : ∀ i, IsClosedEmbedding (g i)) (k : c.ι) :
    IsOpenEmbedding (fun x : {x : B (c.π k) // x ∉ Set.range (g (c.π k))} =>
      c.cell k x.1) := by
  have hm := isClosedEmbedding_of_coproduct (fun i => g (c.π i))
    (fun i => hg (c.π i)) c.cofan₁ c.cofan₂ c.isColimit₁ c.isColimit₂ c.m c.hm
  have havoid (x : {x : B (c.π k) // x ∉ Set.range (g (c.π k))}) :
      c.cofan₂.inj k x.1 ∉ Set.range c.m := by
    simpa only [coproduct_inj_mem_range_iff _ _ _ c.isColimit₁ c.isColimit₂ c.m c.hm] using x.2
  have hinc : IsOpenEmbedding
      (fun x : {x : B (c.π k) // x ∉ Set.range (g (c.π k))} => c.cofan₂.inj k x.1) :=
    (isOpenEmbedding_coproduct_inj c.cofan₂ c.isColimit₂ k).comp
      (hg (c.π k)).isClosed_range.isOpen_compl.isOpenEmbedding_subtypeVal
  have hlift : IsOpenEmbedding
      (fun x : {x : B (c.π k) // x ∉ Set.range (g (c.π k))} =>
        (⟨c.cofan₂.inj k x.1,havoid x⟩ : {x : c.cofan₂.pt // x ∉ Set.range c.m})) :=
    IsOpenEmbedding.of_continuous_injective_isOpenMap
      (hinc.continuous.subtype_mk havoid)
      (fun x y h => hinc.injective (congrArg Subtype.val h))
      (hinc.isOpenMap.codRestrict havoid)
  exact (isOpenEmbedding_pushout_boundary_complement c.isPushout.flip hm).comp hlift

end KIP126.Topology
