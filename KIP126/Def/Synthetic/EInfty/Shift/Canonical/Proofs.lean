module

public import KIP126.Def.Synthetic.EInfty.Shift.Canonical.Predicates
public import KIP126.Def.Synthetic.EInfty.Shift.Predicates
public import KIP126.Def.ClassicalAdams.TowerNaturality.Morphism.Proofs
public import KIP126.Def.ClassicalAdams.TowerNaturality.Isomorphism.Proofs
public import KIP126.Def.SpectralSequence.ModuleQuotient.Proofs

@[expose] public section

/-! Internal construction obligations for weight reindexing. These are
properties of the actual tower maps, not statements supplied by BHS. -/
private theorem weight_shift_page_eq_of_boundary : (
∀ (D : KIP126.SpectralSequence.SSData (ModuleCat.{_} ℤ)) (a b : (CategoryTheory.Subobject.underlying.obj (D.Z ⊤) : ModuleCat ℤ)), (D.Z ⊤).arrow a - (D.Z ⊤).arrow b ∈ (ModuleCat.subobjectModule D.V) (D.B 0) → D.pageπ ⊤ a = D.pageπ ⊤ b
) := (
open CategoryTheory CategoryTheory.Limits KIP126.SpectralSequence in
by
    intro D a b h
    obtain ⟨c, hc⟩ := h
    let j := Subobject.ofLE (D.B 0) (D.B ⊤) (D.B_mono le_top)
    let i := Subobject.ofLE (D.B ⊤) (D.Z ⊤) (D.B_le_Z ⊤)
    have hab : a - b = i (j c) := by
      apply (ModuleCat.mono_iff_injective (D.Z ⊤).arrow).mp inferInstance
      rw [map_sub]
      have hi := congrArg (fun f => f.hom (j c)) (Subobject.ofLE_arrow (D.B_le_Z ⊤))
      have hj := congrArg (fun f => f.hom c) (Subobject.ofLE_arrow (D.B_mono (show (0 : WithTop ℕ) ≤ ⊤ from le_top)))
      exact hc.symm.trans (hj.symm.trans hi.symm)
    apply sub_eq_zero.mp
    rw [← map_sub, hab]
    exact congrArg (fun f => f.hom (j c)) (cokernel.condition i)
)

private theorem weight_shift_natural_of_ambient_boundary : (
open CategoryTheory in
∀ {Syn : Type _} [KIP126.Synthetic.Context.SyntheticCategory.{_, _} Syn] [KIP126.StableHomotopy.HasFunctorialCofiber (C := Syn)] {H : Syn} {unit : KIP126.Synthetic.Context.S_0_0 ⟶ H} {F : KIP126.Synthetic.SpectralSequence.SyntheticAdamsFamily Syn} (P : KIP126.Synthetic.SpectralSequence.TowerPresentation unit F) (S : KIP126.Synthetic.SpectralSequence.EInftyWeightShift F), KIP126.Synthetic.SpectralSequence.CanonicalWeightShift P S → (∀ {A B : Syn} (g : A ⟶ B) (k : ℤ) (p : ℤ × ℤ) (w : ℤ) (x : ((F.obj ((KIP126.Synthetic.Context.SyntheticCategory.biShift (0, k)).obj A)).sequence.ssData (p.1, p.2, w + k)).V), KIP126.Synthetic.SpectralSequence.canonicalWeightShiftAmbient unit P B k p w ((F.functor.map ((KIP126.Synthetic.Context.SyntheticCategory.biShift (0, k)).map g)).φ (p.1, p.2, w + k) x) - (show ((F.obj B).sequence.ssData (p.1, p.2, w)).V from (F.functor.map g).φ (p.1, p.2, w) (KIP126.Synthetic.SpectralSequence.canonicalWeightShiftAmbient unit P A k p w x)) ∈ (ModuleCat.subobjectModule ((F.obj B).sequence.ssData (p.1, p.2, w)).V) (((F.obj B).sequence.ssData (p.1, p.2, w)).B 0)) → KIP126.Synthetic.SpectralSequence.EInftyWeightShift.Natural S
) := (
fun {Syn} [instSyn : _] [instCof : _] {H} {unit} {F} P S canonical boundary {A} {B} g k p w x =>
open CategoryTheory CategoryTheory.Limits KIP126.SpectralSequence KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence in
by
    let DA := (F.obj ((SyntheticCategory.biShift (0, k)).obj A)).sequence.ssData (p.1, p.2, w + k)
    let DB := (F.obj B).sequence.ssData (p.1, p.2, w)
    let f := (F.functor.map ((SyntheticCategory.biShift (0, k)).map g)).toSSDataMorphism
    let h := (F.functor.map g).toSSDataMorphism
    obtain ⟨a, rfl⟩ := (ModuleCat.epi_iff_surjective (DA.pageπ ⊤)).mp (by exact coequalizer.π_epi) x
    obtain ⟨bA, hbA, hqA⟩ := canonical A k p w a
    obtain ⟨bB, hbB, hqB⟩ := canonical B k p w (f.cycleMap (p.1, p.2, w + k) ⊤ a)
    have hf := congrArg (fun z => z.hom a) (f.pageπ_pageMap (p.1, p.2, w + k) ⊤)
    have hh := congrArg (fun z => z.hom bA) (h.pageπ_pageMap (p.1, p.2, w) ⊤)
    change S.iso B k p w (f.pageMap (p.1, p.2, w + k) ⊤ (DA.pageπ ⊤ a)) = h.pageMap (p.1, p.2, w) ⊤ (S.iso A k p w (DA.pageπ ⊤ a))
    change f.pageMap (p.1, p.2, w + k) ⊤ (DA.pageπ ⊤ a) = ((F.obj ((SyntheticCategory.biShift (0, k)).obj B)).sequence.ssData (p.1, p.2, w + k)).pageπ ⊤ (f.cycleMap (p.1, p.2, w + k) ⊤ a) at hf
    change h.pageMap (p.1, p.2, w) ⊤ _ = DB.pageπ ⊤ (h.cycleMap (p.1, p.2, w) ⊤ bA) at hh
    have hfa := congrArg (fun z => z.hom a) (f.cycleMap_arrow (p.1, p.2, w + k) ⊤)
    have hha := congrArg (fun z => z.hom bA) (h.cycleMap_arrow (p.1, p.2, w) ⊤)
    have left : (DB.Z ⊤).arrow bB = canonicalWeightShiftAmbient unit P B k p w (f.φ (p.1, p.2, w + k) ((DA.Z ⊤).arrow a)) := hbB.trans (congrArg (canonicalWeightShiftAmbient unit P B k p w).hom hfa)
    have right : (DB.Z ⊤).arrow (h.cycleMap (p.1, p.2, w) ⊤ bA) = h.φ (p.1, p.2, w) (canonicalWeightShiftAmbient unit P A k p w ((DA.Z ⊤).arrow a)) := hha.trans (congrArg (h.φ (p.1, p.2, w)).hom hbA)
    have diff := boundary g k p w ((DA.Z ⊤).arrow a)
    have heq : (DB.Z ⊤).arrow bB - (DB.Z ⊤).arrow (h.cycleMap (p.1, p.2, w) ⊤ bA) = canonicalWeightShiftAmbient unit P B k p w (f.φ (p.1, p.2, w + k) ((DA.Z ⊤).arrow a)) - (show DB.V from h.φ (p.1, p.2, w) (canonicalWeightShiftAmbient unit P A k p w ((DA.Z ⊤).arrow a))) := congrArg₂ (fun x y : DB.V => x - y) left right
    have heq_page : DB.pageπ ⊤ bB = DB.pageπ ⊤ (h.cycleMap (p.1, p.2, w) ⊤ bA) := weight_shift_page_eq_of_boundary DB _ _ (heq.symm ▸ diff)
    exact (congrArg (S.iso B k p w) hf).trans (hqB.trans (heq_page.trans (hh.symm.trans (congrArg (h.pageMap (p.1, p.2, w) ⊤).hom hqA.symm))))
)

section WeightNaturality

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open KIP126.SpectralSequence KIP126.Classical.Adams KIP126.StableHomotopy
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
universe u v
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

private theorem weight_shift_boundary_of_page_eq
    (D : SSData (ModuleCat.{u} ℤ)) (r : WithTop ℕ)
    (a b : (Subobject.underlying.obj (D.Z r) : ModuleCat ℤ))
    (h : D.pageπ r a = D.pageπ r b) :
    (D.Z r).arrow a - (D.Z r).arrow b ∈ (ModuleCat.subobjectModule D.V) (D.B r) := by
  let i := Subobject.ofLE (D.B r) (D.Z r) (D.B_le_Z r)
  have hp := congrArg (fun x => (ModuleCat.cokernelIsoRangeQuotient i).hom x) h
  have hc := ModuleCat.cokernel_π_cokernelIsoRangeQuotient_hom i
  have ha := congrArg (fun f => f.hom a) hc
  have hb := congrArg (fun f => f.hom b) hc
  change (ModuleCat.cokernelIsoRangeQuotient i).hom (D.pageπ r a) =
    i.hom.range.mkQ a at ha
  change (ModuleCat.cokernelIsoRangeQuotient i).hom (D.pageπ r b) =
    i.hom.range.mkQ b at hb
  rw [ha, hb] at hp
  obtain ⟨c, hc⟩ := (Submodule.Quotient.eq i.hom.range).mp hp
  refine ⟨c, ?_⟩
  have hh := congrArg (fun f => f.hom c) (Subobject.ofLE_arrow (D.B_le_Z r))
  change (D.Z r).arrow (i c) = (D.B r).arrow c at hh
  rw [hc, map_sub] at hh
  exact hh.symm

private theorem weight_shift_map_boundary
    {ι : Type*} [AddCommGroup ι] [DecidableEq ι]
    {D E : ι → SSData (ModuleCat.{u} ℤ)}
    (f : SSDataMorphism ι D E) (p : ι) (r : WithTop ℕ)
    {x : (D p).V} (hx : x ∈ (ModuleCat.subobjectModule (D p).V) ((D p).B r)) :
    f.φ p x ∈ (ModuleCat.subobjectModule (E p).V) ((E p).B r) := by
  obtain ⟨b, rfl⟩ := hx
  obtain ⟨l, hl⟩ := f.preserves_B p r
  exact ⟨l b, congrArg (fun k => k.hom b) hl⟩

private theorem weight_shift_ambient_diff_of_page_eq
    {ι : Type*} [AddCommGroup ι] [DecidableEq ι]
    {D E : ι → SSData (ModuleCat.{u} ℤ)}
    (f g : SSDataMorphism ι D E) (p : ι)
    (h : f.pageMap p 0 = g.pageMap p 0) (x : (D p).V) :
    f.φ p x - g.φ p x ∈ (ModuleCat.subobjectModule (E p).V) ((E p).B 0) := by
  haveI : IsIso ((D p).Z 0).arrow := (Subobject.isIso_arrow_iff_eq_top _).mpr (D p).Z_zero
  obtain ⟨a, rfl⟩ := (ModuleCat.epi_iff_surjective ((D p).Z 0).arrow).mp inferInstance x
  have hf := congrArg (fun z => z.hom a) (f.cycleMap_arrow p 0)
  have hg := congrArg (fun z => z.hom a) (g.cycleMap_arrow p 0)
  have hqf := congrArg (fun z => z.hom a) (f.pageπ_pageMap p 0)
  have hqg := congrArg (fun z => z.hom a) (g.pageπ_pageMap p 0)
  have hq : (E p).pageπ 0 (f.cycleMap p 0 a) =
      (E p).pageπ 0 (g.cycleMap p 0 a) := hqf.symm.trans ((congrArg (fun z => z.hom ((D p).pageπ 0 a)) h).trans hqg)
  have hb := weight_shift_boundary_of_page_eq (E p) 0 _ _ hq
  exact (congrArg₂ (fun a b : (E p).V => a-b) hf hg) ▸ hb

private theorem weight_shift_forward_naturality_boundary
    {Syn : Type u} [SyntheticCategory.{u,v} Syn] [HasFunctorialCofiber (C := Syn)]
    {H : Syn} {unit : 𝟙_ Syn ⟶ H} {F : SyntheticAdamsFamily Syn}
    (P : TowerPresentation unit F) {A B : Syn} (g : A ⟶ B) (w : ℤ) (p : ℤ × ℤ)
    (x : ((F.obj A).sequence.ssData (p.1,p.2,w)).V) :
    (show adamsCycleAmbient unit ((SyntheticCategory.biShift (0,-w)).obj B) p.1 p.2 from
      (P.forward B w).φ p ((F.functor.map g).φ (p.1,p.2,w) x)) -
      adamsCycleInduced unit ((SyntheticCategory.biShift (0,-w)).map g) 2 (Nat.le_succ 1) p.1 p.2
        ((P.forward A w).φ p x) ∈
      adamsBoundarySubmodule unit ((SyntheticCategory.biShift (0,-w)).obj B) p.1 p.2 0 := by
  let f : SSDataMorphism (ℤ × ℤ)
      (fun p => (F.obj A).sequence.ssData (p.1,p.2,w))
      (fun p => (F.obj B).sequence.ssData (p.1,p.2,w)) :=
    { φ := fun p => (F.functor.map g).φ (p.1,p.2,w)
      preserves_Z := fun p => (F.functor.map g).preserves_Z (p.1,p.2,w)
      preserves_B := fun p => (F.functor.map g).preserves_B (p.1,p.2,w) }
  obtain ⟨T, hT⟩ := adamsTowerSSDataMorphism_exists unit
    ((SyntheticCategory.biShift (0,-w)).map g)
  have hpage : T.pageMap p 0 = weightTowerE2Map unit g w p := by
    apply (cancel_mono (adamsTowerSSDataPageIso unit
      ((SyntheticCategory.biShift (0,-w)).obj B) p.1 p.2 0).hom).mp
    erw [adamsTowerSSDataMorphism_page_comparison unit _ T hT p 0]
    change _ = ((adamsTowerSSDataPageIso unit
      ((SyntheticCategory.biShift (0,-w)).obj A) p.1 p.2 0).hom ≫
      ModuleCat.ofHom (adamsPageInduced unit ((SyntheticCategory.biShift (0,-w)).map g)
        2 (Nat.le_succ 1) p.1 p.2) ≫
      (adamsTowerSSDataPageIso unit ((SyntheticCategory.biShift (0,-w)).obj B) p.1 p.2 0).inv) ≫ _
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hn : (f.comp (P.forward B w)).pageMap p 0 =
      ((P.forward A w).comp T).pageMap p 0 := by
    rw [SSDataMorphism.pageMap_comp, SSDataMorphism.pageMap_comp, hpage]
    exact P.natural_e2 g w p
  have hb := weight_shift_ambient_diff_of_page_eq (f.comp (P.forward B w)) ((P.forward A w).comp T) p hn x
  have hbound : (ModuleCat.subobjectModule ((weightTower unit B w).ssData p).V)
      (((weightTower unit B w).ssData p).B 0) =
      adamsBoundarySubmodule unit ((SyntheticCategory.biShift (0,-w)).obj B) p.1 p.2 0 :=
    (ModuleCat.subobjectModule _).apply_symm_apply _
  have hb' := (le_of_eq hbound) hb
  have ht := congrArg (fun m => m.hom ((P.forward A w).φ p x)) (hT p)
  change T.φ p ((P.forward A w).φ p x) =
    adamsCycleInduced unit ((SyntheticCategory.biShift (0,-w)).map g) 2 (Nat.le_succ 1) p.1 p.2
      ((P.forward A w).φ p x) at ht
  change (show adamsCycleAmbient unit ((SyntheticCategory.biShift (0,-w)).obj B) p.1 p.2 from
    (P.forward B w).φ p ((F.functor.map g).φ (p.1,p.2,w) x)) -
    (show adamsCycleAmbient unit ((SyntheticCategory.biShift (0,-w)).obj B) p.1 p.2 from
      T.φ p ((P.forward A w).φ p x)) ∈ _ at hb'
  exact (congrArg (fun z : adamsCycleAmbient unit ((SyntheticCategory.biShift (0,-w)).obj B) p.1 p.2 =>
    (show adamsCycleAmbient unit ((SyntheticCategory.biShift (0,-w)).obj B) p.1 p.2 from
      (P.forward B w).φ p ((F.functor.map g).φ (p.1,p.2,w) x)) - z) ht) ▸ hb'


end WeightNaturality

namespace KIP126.Synthetic.SpectralSequence

open CategoryTheory KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.SpectralSequence
set_option backward.isDefEq.respectTransparency false
universe u v
variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  {H : Syn} {unit : S_0_0 ⟶ H}
  {F : SyntheticAdamsFamily Syn}

/-- Prove preservation of the cycle and boundary towers, descend the actual
weight-shift map and its inverse to E∞, and verify their inverse equations.
Full-category naturality is a separate external hypothesis in
`KIP126.Literature.Background.WeightShift`. -/
theorem canonicalWeightShift_exists (P : TowerPresentation unit F) :
    ∃ S : EInftyWeightShift F, CanonicalWeightShift P S := by
  classical
  have all (A : Syn) (k : ℤ) (p : ℤ × ℤ) (w : ℤ) :
      ∃ q : ((F.obj ((SyntheticCategory.biShift (0, k)).obj A)).sequence.ssData
          (p.1, p.2, w + k)).eInfty ≅ ((F.obj A).sequence.ssData (p.1, p.2, w)).eInfty,
        ∀ a : (Subobject.underlying.obj (((F.obj ((SyntheticCategory.biShift (0, k)).obj A)).sequence.ssData
          (p.1, p.2, w + k)).Z ⊤) : ModuleCat ℤ),
          ∃ b : (Subobject.underlying.obj (((F.obj A).sequence.ssData (p.1, p.2, w)).Z ⊤) : ModuleCat ℤ),
            (((F.obj A).sequence.ssData (p.1, p.2, w)).Z ⊤).arrow b =
              canonicalWeightShiftAmbient unit P A k p w
                ((((F.obj ((SyntheticCategory.biShift (0, k)).obj A)).sequence.ssData (p.1, p.2, w + k)).Z ⊤).arrow a) ∧
            q.hom ((((F.obj ((SyntheticCategory.biShift (0, k)).obj A)).sequence.ssData
              (p.1, p.2, w + k)).pageπ ⊤ a)) =
              ((F.obj A).sequence.ssData (p.1, p.2, w)).pageπ ⊤ b := by
    let X := (SyntheticCategory.biShift (0, k)).obj A
    let U := (SyntheticCategory.biShift (0, -(w + k))).obj X
    let V := (SyntheticCategory.biShift (0, -w)).obj A
    let eF : ((F.obj X).sequence.ssData (p.1, p.2, w + k)).V ≅
        ((weightTower unit X (w + k)).ssData p).V :=
      { hom := (P.forward X (w + k)).φ p
        inv := (P.inverse X (w + k)).φ p
        hom_inv_id := P.left_inv X (w + k) p
        inv_hom_id := P.right_inv X (w + k) p }
    let eI : ((weightTower unit A w).ssData p).V ≅
        ((F.obj A).sequence.ssData (p.1, p.2, w)).V :=
      { hom := (P.inverse A w).φ p
        inv := (P.forward A w).φ p
        hom_inv_id := P.right_inv A w p
        inv_hom_id := P.left_inv A w p }
    let eT := LinearEquiv.ofBijective
      (KIP126.Classical.Adams.adamsCycleInduced unit (weightShiftObjectIso A k w).hom 2 (Nat.le_succ 1) p.1 p.2)
      (KIP126.Classical.Adams.adamsCycleInduced_bijective unit (weightShiftObjectIso A k w).hom 2 (Nat.le_succ 1) p.1 p.2)
    let e := (eF.toLinearEquiv.trans eT).trans eI.toLinearEquiv
    have htZ (x : KIP126.Classical.Adams.adamsCycleAmbient unit U p.1 p.2) :
        eT x ∈ (ModuleCat.subobjectModule _) (((weightTower unit A w).ssData p).Z ⊤) ↔
          x ∈ (ModuleCat.subobjectModule _) (((weightTower unit X (w + k)).ssData p).Z ⊤) := by
      change eT x ∈ (ModuleCat.subobjectModule (ModuleCat.of ℤ (KIP126.Classical.Adams.adamsCycleAmbient unit V p.1 p.2)))
          ((ModuleCat.subobjectModule _).symm (KIP126.Classical.Adams.adamsCycleSubmodule unit V p.1 p.2 ⊤)) ↔
        x ∈ (ModuleCat.subobjectModule (ModuleCat.of ℤ (KIP126.Classical.Adams.adamsCycleAmbient unit U p.1 p.2)))
          ((ModuleCat.subobjectModule _).symm (KIP126.Classical.Adams.adamsCycleSubmodule unit U p.1 p.2 ⊤))
      rw [OrderIso.apply_symm_apply, OrderIso.apply_symm_apply]
      exact KIP126.Classical.Adams.adamsCycleInduced_mem_cycleSubmodule_iff unit
        (weightShiftObjectIso A k w).hom p.1 p.2 ⊤ x
    have htB (x : KIP126.Classical.Adams.adamsCycleAmbient unit U p.1 p.2) :
        eT x ∈ (ModuleCat.subobjectModule _) (((weightTower unit A w).ssData p).B ⊤) ↔
          x ∈ (ModuleCat.subobjectModule _) (((weightTower unit X (w + k)).ssData p).B ⊤) := by
      change eT x ∈ (ModuleCat.subobjectModule (ModuleCat.of ℤ (KIP126.Classical.Adams.adamsCycleAmbient unit V p.1 p.2)))
          ((ModuleCat.subobjectModule _).symm (KIP126.Classical.Adams.adamsBoundarySubmodule unit V p.1 p.2 ⊤)) ↔
        x ∈ (ModuleCat.subobjectModule (ModuleCat.of ℤ (KIP126.Classical.Adams.adamsCycleAmbient unit U p.1 p.2)))
          ((ModuleCat.subobjectModule _).symm (KIP126.Classical.Adams.adamsBoundarySubmodule unit U p.1 p.2 ⊤))
      rw [OrderIso.apply_symm_apply, OrderIso.apply_symm_apply]
      exact KIP126.Classical.Adams.adamsCycleInduced_mem_boundarySubmodule_iff unit
        (weightShiftObjectIso A k w).hom p.1 p.2 ⊤ x
    have hZ x := (subobject_mem_iff_of_inverse eI.toLinearEquiv _ _
      ((P.inverse A w).preserves_Z p ⊤) ((P.forward A w).preserves_Z p ⊤) (eT (eF.hom x))).trans
      ((htZ (eF.hom x)).trans (subobject_mem_iff_of_inverse eF.toLinearEquiv _ _
        ((P.forward X (w + k)).preserves_Z p ⊤) ((P.inverse X (w + k)).preserves_Z p ⊤) x))
    have hB x := (subobject_mem_iff_of_inverse eI.toLinearEquiv _ _
      ((P.inverse A w).preserves_B p ⊤) ((P.forward A w).preserves_B p ⊤) (eT (eF.hom x))).trans
      ((htB (eF.hom x)).trans (subobject_mem_iff_of_inverse eF.toLinearEquiv _ _
        ((P.forward X (w + k)).preserves_B p ⊤) ((P.inverse X (w + k)).preserves_B p ⊤) x))
    obtain ⟨q, hq⟩ := subobject_quotient_iso_of_linearEquiv
      (((F.obj X).sequence.ssData (p.1, p.2, w + k)).B ⊤)
      (((F.obj X).sequence.ssData (p.1, p.2, w + k)).Z ⊤)
      (((F.obj A).sequence.ssData (p.1, p.2, w)).B ⊤)
      (((F.obj A).sequence.ssData (p.1, p.2, w)).Z ⊤)
      (((F.obj X).sequence.ssData (p.1, p.2, w + k)).B_le_Z ⊤)
      (((F.obj A).sequence.ssData (p.1, p.2, w)).B_le_Z ⊤) e hB hZ
    exact ⟨q, hq⟩
  refine ⟨{ iso := fun A k p w => (all A k p w).choose.toLinearEquiv }, ?_⟩
  intro A k p w
  dsimp only
  intro a
  exact (all A k p w).choose_spec a

end KIP126.Synthetic.SpectralSequence
