module

public import KIP126.Def.SpectralSequence.Basic.Category.Proofs
public import KIP126.Def.ClassicalAdams.PageRepresentatives.Predicates
public import KIP126.Def.AdamsSynthetic.Extensions.Predicates
public import KIP126.Literature.AdamsSynthetic.ComparisonTheorems
public import KIP126.Def.SpectralSequence.BoundedExtension.UnderlyingComplex.Proofs
public import KIP126.Def.Synthetic.EInfty.Shift.Canonical.Proofs
public import KIP126.Def.Synthetic.Context.Coherence.Proofs

@[expose] public section

/-! The finite extension stretching law, proved from the stated
classical/synthetic comparisons on the same Adams towers. All finite quotient
representatives and filtration corrections refer to those comparisons. -/
namespace KIP126.Main.ExtensionLaws

open CategoryTheory
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Synthetic.Context KIP126.AdamsSynthetic KIP126.Classical.Adams
open KIP126.Literature.AdamsSynthetic

universe u v w
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H}
  (D : AdamsComparison H M Syn)

open CategoryTheory.Limits KIP126.SpectralSequence
open KIP126.Synthetic.SpectralSequence KIP126.Synthetic.PageExtension

open KIP126.Algebra KIP126.Classical.Adams.PageRepresentatives

section ShiftedRepresentatives

open CategoryTheory.Functor CategoryTheory.Pretriangulated

set_option maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
private theorem quotient_shift_exists (coh : BiShiftCoherence Syn)
    (a : ℤ × ℤ) (q : ℕ) (X : Syn)
    [cs : (SyntheticCategory.biShift (Syn := Syn) a).CommShift ℤ]
    [(SyntheticCategory.biShift (Syn := Syn) a).IsTriangulated] :
    ∃ e : XModLambdaN ((SyntheticCategory.biShift a).obj X) q ≅
      (SyntheticCategory.biShift a).obj (XModLambdaN X q),
      XModLambdaN.incl ((SyntheticCategory.biShift a).obj X) q ≫ e.hom =
        (SyntheticCategory.biShift a).map (XModLambdaN.incl X q) := by
  let oneComm (a : ℤ × ℤ) :
      SyntheticCategory.biShift (Syn := Syn) a ⋙ SyntheticCategory.biShift (lambdaDegree 1) ≅
        SyntheticCategory.biShift (lambdaDegree 1) ⋙ SyntheticCategory.biShift a :=
    biShiftAddIso a (0,-1) (a+(0,-1)) rfl ≪≫
      (biShiftAddIso (0,-1) a (a+(0,-1)) (add_comm _ _)).symm

  let powerComm (a : ℤ × ℤ) : (q : ℕ) →
      SyntheticCategory.biShift (Syn := Syn) a ⋙ SyntheticCategory.biShift (lambdaDegree q) ≅
        SyntheticCategory.biShift (lambdaDegree q) ⋙ SyntheticCategory.biShift a := fun q =>
    Nat.rec (motive := fun q =>
      SyntheticCategory.biShift (Syn := Syn) a ⋙ SyntheticCategory.biShift (lambdaDegree q) ≅
        SyntheticCategory.biShift (lambdaDegree q) ⋙ SyntheticCategory.biShift a)
      (isoWhiskerLeft _ SyntheticCategory.biShift_zero ≪≫
        Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm ≪≫
        (isoWhiskerRight SyntheticCategory.biShift_zero _).symm)
      (fun q ih =>
        isoWhiskerLeft _ (lambdaShiftAddIso 1 q (q+1) (by omega)).symm ≪≫
        (Functor.associator _ _ _).symm ≪≫
        isoWhiskerRight (oneComm a) _ ≪≫ Functor.associator _ _ _ ≪≫
        isoWhiskerLeft _ ih ≪≫
        (Functor.associator _ _ _).symm ≪≫
        isoWhiskerRight (lambdaShiftAddIso 1 q (q+1) (by omega)) _) q

  have powerComm_square (coh : BiShiftCoherence Syn) (a : ℤ × ℤ)
      (q : ℕ) (X : Syn) :
      lambdaPow q ((SyntheticCategory.biShift a).obj X) =
        (powerComm a q).hom.app X ≫ (SyntheticCategory.biShift a).map (lambdaPow q X) := by
    induction q generalizing X with
    | zero =>
      simp [powerComm, lambdaPow, ← Functor.map_comp]
      exact (Category.comp_id _).symm
    | succ q ih =>
      have h1 : (oneComm a).hom.app X ≫
          (SyntheticCategory.biShift a).map (SyntheticCategory.lam.app X) =
          SyntheticCategory.lam.app ((SyntheticCategory.biShift a).obj X) := by
        simpa [oneComm, Category.assoc] using (coh.lambda_comm a X).symm
      apply (cancel_epi ((lambdaShiftAddIso 1 q (q+1) (by omega)).hom.app
        ((SyntheticCategory.biShift a).obj X))).mp
      rw [lambdaPow_succ_comparison]
      simp only [powerComm, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
        isoWhiskerLeft_hom, isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app,
        Functor.associator_inv_app, Functor.associator_hom_app, Category.id_comp, Category.assoc]
      rw [Iso.hom_inv_id_app_assoc]
      rw [← Functor.map_comp, lambdaPow_succ_comparison, Functor.map_comp]
      have hn := (powerComm a q).hom.naturality (SyntheticCategory.lam.app X)
      have hn' := congrArg (fun h => h ≫ (SyntheticCategory.biShift a).map (lambdaPow q X)) hn
      simp only [Functor.comp_map, Category.assoc] at hn'
      dsimp only [KIP126.Synthetic.Context.lambdaDegree, Functor.id_obj] at hn' ⊢
      erw [← hn']
      rw [← Category.assoc, ← Functor.map_comp, h1, ih]

  let F := SyntheticCategory.biShift (Syn := Syn) a
  let T := Triangle.mk (lambdaPow q X) (XModLambdaN.incl X q) (XModLambdaN.proj X q)
  let T' := Triangle.mk (lambdaPow q (F.obj X))
    (XModLambdaN.incl (F.obj X) q) (XModLambdaN.proj (F.obj X) q)
  have hT : T ∈ distTriang Syn := HasFunctorialCofiber.cofib_distinguished _
  have hT' : T' ∈ distTriang Syn := HasFunctorialCofiber.cofib_distinguished _
  let e := isoTriangleOfIso₁₂ T' (F.mapTriangle.obj T) hT'
    (F.map_distinguished T hT) ((powerComm a q).app X) (Iso.refl _) (by
      change lambdaPow q (F.obj X) ≫ 𝟙 _ =
        (powerComm a q).hom.app X ≫ F.map (lambdaPow q X)
      simpa only [Category.comp_id] using powerComm_square coh a q X)
  refine ⟨Triangle.π₃.mapIso e, ?_⟩
  have h := e.hom.comm₂
  change XModLambdaN.incl (F.obj X) q ≫ e.hom.hom₃ =
    e.hom.hom₂ ≫ F.map (XModLambdaN.incl X q) at h
  change XModLambdaN.incl (F.obj X) q ≫ e.hom.hom₃ =
    F.map (XModLambdaN.incl X q)
  simpa only [e, isoTriangleOfIso₁₂_hom_hom₂, Iso.refl_hom, Category.id_comp] using h

set_option maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
private theorem shifted_finite_source_exists (D : AdamsComparison H M Syn)
    (synthetic : SyntheticComparisonTheorems D) (X : ClassicalObject) (q : ℕ) (hq : 0 < q)
    (a s t : ℤ) (x : E2 H (X.obj D.hopfAndDetector) s t)
    (hx : x ∈ cycles H (X.obj D.hopfAndDetector) q (s,t)) :
    ∃ e : ((D.family.obj ((SyntheticObject.quotient q (.shift (0,a) (.nu X))).obj D.nu D.hopfAndDetector)).sequence.ssData (s,t,t+a-(0:ℕ))).eInfty,
      HasInfinityRepresentative _ 2 (s,t,t+a-(0:ℕ)) (finiteNuLabel D X q a s t 0 x) e := by
  have weightPageShift_exists {K : Syn} {unit : S_0_0 ⟶ K}
      {F : SyntheticAdamsFamily Syn} (P : TowerPresentation unit F)
      (A : Syn) (k : ℤ) (p : ℤ × ℤ) (w : ℤ) (n : WithTop ℕ) :
      Nonempty (((F.obj ((SyntheticCategory.biShift (0,k)).obj A)).sequence.ssData
        (p.1,p.2,w+k)).page n ≅ ((F.obj A).sequence.ssData (p.1,p.2,w)).page n) := by
    classical
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
        eT x ∈ (ModuleCat.subobjectModule _) (((weightTower unit A w).ssData p).Z n) ↔
          x ∈ (ModuleCat.subobjectModule _) (((weightTower unit X (w + k)).ssData p).Z n) := by
      change eT x ∈ (ModuleCat.subobjectModule (ModuleCat.of ℤ (KIP126.Classical.Adams.adamsCycleAmbient unit V p.1 p.2)))
          ((ModuleCat.subobjectModule _).symm (KIP126.Classical.Adams.adamsCycleSubmodule unit V p.1 p.2 n)) ↔
        x ∈ (ModuleCat.subobjectModule (ModuleCat.of ℤ (KIP126.Classical.Adams.adamsCycleAmbient unit U p.1 p.2)))
          ((ModuleCat.subobjectModule _).symm (KIP126.Classical.Adams.adamsCycleSubmodule unit U p.1 p.2 n))
      rw [OrderIso.apply_symm_apply, OrderIso.apply_symm_apply]
      exact KIP126.Classical.Adams.adamsCycleInduced_mem_cycleSubmodule_iff unit
        (weightShiftObjectIso A k w).hom p.1 p.2 n x
    have htB (x : KIP126.Classical.Adams.adamsCycleAmbient unit U p.1 p.2) :
        eT x ∈ (ModuleCat.subobjectModule _) (((weightTower unit A w).ssData p).B n) ↔
          x ∈ (ModuleCat.subobjectModule _) (((weightTower unit X (w + k)).ssData p).B n) := by
      change eT x ∈ (ModuleCat.subobjectModule (ModuleCat.of ℤ (KIP126.Classical.Adams.adamsCycleAmbient unit V p.1 p.2)))
          ((ModuleCat.subobjectModule _).symm (KIP126.Classical.Adams.adamsBoundarySubmodule unit V p.1 p.2 n)) ↔
        x ∈ (ModuleCat.subobjectModule (ModuleCat.of ℤ (KIP126.Classical.Adams.adamsCycleAmbient unit U p.1 p.2)))
          ((ModuleCat.subobjectModule _).symm (KIP126.Classical.Adams.adamsBoundarySubmodule unit U p.1 p.2 n))
      rw [OrderIso.apply_symm_apply, OrderIso.apply_symm_apply]
      exact KIP126.Classical.Adams.adamsCycleInduced_mem_boundarySubmodule_iff unit
        (weightShiftObjectIso A k w).hom p.1 p.2 n x
    have hZ x := (subobject_mem_iff_of_inverse eI.toLinearEquiv _ _
      ((P.inverse A w).preserves_Z p n) ((P.forward A w).preserves_Z p n) (eT (eF.hom x))).trans
      ((htZ (eF.hom x)).trans (subobject_mem_iff_of_inverse eF.toLinearEquiv _ _
        ((P.forward X (w + k)).preserves_Z p n) ((P.inverse X (w + k)).preserves_Z p n) x))
    have hB x := (subobject_mem_iff_of_inverse eI.toLinearEquiv _ _
      ((P.inverse A w).preserves_B p n) ((P.forward A w).preserves_B p n) (eT (eF.hom x))).trans
      ((htB (eF.hom x)).trans (subobject_mem_iff_of_inverse eF.toLinearEquiv _ _
        ((P.forward X (w + k)).preserves_B p n) ((P.inverse X (w + k)).preserves_B p n) x))
    obtain ⟨q, hq⟩ := subobject_quotient_iso_of_linearEquiv
      (((F.obj X).sequence.ssData (p.1, p.2, w + k)).B n)
      (((F.obj X).sequence.ssData (p.1, p.2, w + k)).Z n)
      (((F.obj A).sequence.ssData (p.1, p.2, w)).B n)
      (((F.obj A).sequence.ssData (p.1, p.2, w)).Z n)
      (((F.obj X).sequence.ssData (p.1, p.2, w + k)).B_le_Z n)
      (((F.obj A).sequence.ssData (p.1, p.2, w)).B_le_Z n) e hB hZ
    exact ⟨q⟩

  have family_map_data (D : AdamsComparison H M Syn)  {X Y : Syn} (f : X ⟶ Y) (r : ℤ) (i : Tridegree) :
      familyPageMap D.family f r i = (D.family.functor.map f).toSSDataMorphism.pageMap i (↑(r-2).toNat) := by
    let F := (D.family.functor.map f).toSSDataMorphism
    let PX := (D.family.functor.obj X).ssData i
    let PY := (D.family.functor.obj Y).ssData i
    let nX : WithTop ℕ := ↑(r-(D.family.functor.obj X).r₀).toNat
    let nY : WithTop ℕ := ↑(r-(D.family.functor.obj Y).r₀).toNat
    change (@eqToHom (ModuleCat ℤ) _ (PX.page (↑(r-2).toNat)) (PX.page nX) _ ≫
      (F.pageMap i nX ≫ @eqToHom (ModuleCat ℤ) _ (PY.page nX) (PY.page nY) _) ≫
      @eqToHom (ModuleCat ℤ) _ (PY.page nY) (PY.page (↑(r-2).toNat)) _) = F.pageMap i (↑(r-2).toNat)
    have hX : nX=↑(r-2).toNat := by dsimp only [nX]; rw [D.family.firstPage X]
    have hY : nY=↑(r-2).toNat := by dsimp only [nY]; rw [D.family.firstPage Y]
    have normalize (A B : WithTop ℕ → ModuleCat.{v} ℤ) (j : ∀ n, A n ⟶ B n)
        (n m n0 : WithTop ℕ) (hn : n=n0) (hm : m=n0)
        (h1 : A n0=A n) (h2 : B n=B m) (h3 : B m=B n0) :
        eqToHom h1 ≫ (j n ≫ eqToHom h2) ≫ eqToHom h3 = j n0 := by
      subst n
      subst m
      simp only [eqToHom_refl,Category.id_comp,Category.comp_id]
    exact normalize PX.page PY.page (fun n => F.pageMap i n) nX nY (↑(r-2).toNat) hX hY _ _ _
  have family_page_comp (D : AdamsComparison H M Syn)  {X Y Z : Syn} (f : X ⟶ Y) (g : Y ⟶ Z) (r : ℤ) (i : Tridegree) :
      familyPageMap D.family f r i ≫ familyPageMap D.family g r i = familyPageMap D.family (f ≫ g) r i := by
    rw [family_map_data D,family_map_data D,family_map_data D,Functor.map_comp]
    exact (SSDataMorphism.pageMap_comp _ _ _ _).symm
  have family_page_id (D : AdamsComparison H M Syn) (X : Syn) (r : ℤ) (i : Tridegree) :
      familyPageMap D.family (𝟙 X) r i = 𝟙 _ := by
    rw [family_map_data, CategoryTheory.Functor.map_id]
    exact SSDataMorphism.pageMap_id _ _ _

  let familyPageIso (D : AdamsComparison H M Syn) {X Y : Syn} (e : X ≅ Y)
      (r : ℤ) (i : Tridegree) : (D.family.obj X).Page r i ≅ (D.family.obj Y).Page r i := {
    hom := familyPageMap D.family e.hom r i
    inv := familyPageMap D.family e.inv r i
    hom_inv_id := by rw [family_page_comp, e.hom_inv_id, family_page_id]
    inv_hom_id := by rw [family_page_comp, e.inv_hom_id, family_page_id] }

  have shiftedFinitePageVanishing (D : AdamsComparison H M Syn)
      (synthetic : SyntheticComparisonTheorems D) (X : ClassicalObject) (q : ℕ) (hq : 0 < q)
      (a r s t w : ℤ)
      (e : XModLambdaN ((SyntheticCategory.biShift (0,a)).obj (D.nu.functor.obj (X.obj D.hopfAndDetector))) q ≅
        (SyntheticCategory.biShift (0,a)).obj (XModLambdaN (D.nu.functor.obj (X.obj D.hopfAndDetector)) q))
      (hr : 2 ≤ r) (hw : t < w-a ∨ (q:ℤ) ≤ t-(w-a)) :
      Subsingleton ((D.family.obj (XModLambdaN ((SyntheticCategory.biShift (0,a)).obj
        (D.nu.functor.obj (X.obj D.hopfAndDetector))) q)).Page r (s,t,w)) := by
    haveI := synthetic.finite_quotient_page_vanishing X q hq r s t (w-a) hr hw
    obtain ⟨ew⟩ := weightPageShift_exists D.towerPresentation
      (XModLambdaN (D.nu.functor.obj (X.obj D.hopfAndDetector)) q) a (s,t) (w-a) (↑(r-2).toNat)
    have ew' : (D.family.obj ((SyntheticCategory.biShift (0,a)).obj
        (XModLambdaN (D.nu.functor.obj (X.obj D.hopfAndDetector)) q))).Page r (s,t,w) ≅
        (D.family.nuQuotient D.nu (X.obj D.hopfAndDetector) q).Page r (s,t,w-a) := by
      simpa only [sub_add_cancel, SyntheticAdamsSS.Page, SyntheticAdamsFamily.nuQuotient, SyntheticAdamsFamily.quotient] using ew
    exact ((familyPageIso D e r (s,t,w)) ≪≫ ew').toLinearEquiv.injective.subsingleton

  have syntheticRep_map (D : AdamsComparison H M Syn) {X Y : Syn}
      (f : X ⟶ Y) (r : ℤ) (i : Tridegree)
      (x : (D.family.obj X).E₂ i) (xr : (D.family.obj X).Page r i)
      (hx : KIP126.Synthetic.SpectralSequence.RepresentsOnPage (D.family.obj X) r i x xr) :
      KIP126.Synthetic.SpectralSequence.RepresentsOnPage (D.family.obj Y) r i
        (familyPageMap D.family f 2 i x) (familyPageMap D.family f r i xr) := by
    obtain ⟨hr,z,hz,he⟩ := hx
    change (Subobject.ofLE (((D.family.functor.obj X).ssData i).Z (↑(r-2).toNat)) (((D.family.functor.obj X).ssData i).Z 0) _ ≫
      ((D.family.functor.obj X).ssData i).pageπ 0) z=x at hz
    let F := (D.family.functor.map f).toSSDataMorphism
    refine ⟨hr,F.cycleMap i (↑(r-2).toNat) z,?_,?_⟩
    · rw [family_map_data D]
      have h := F.cycleMap_ofLE_assoc i (show (0:WithTop ℕ)≤↑(r-2).toNat from bot_le)
        (((D.family.obj Y).sequence.ssData i).pageπ 0)
      dsimp only [SyntheticAdamsFamily.obj] at h
      rw [← F.pageπ_pageMap] at h
      exact (congrArg (fun a => a z) h).symm.trans (by
        simpa only [ModuleCat.comp_apply,CategoryTheory.comp_apply] using congrArg (fun q => F.pageMap i 0 q) hz)
    · rw [family_map_data D]
      exact (congrArg (fun a => a z) (F.pageπ_pageMap i (↑(r-2).toNat))).symm.trans (by
        change F.pageMap i (↑(r-2).toNat) (((D.family.obj X).sequence.ssData i).pageπ (↑(r-2).toNat) z)=_
        rw [he])

  have syntheticRep_infty (A : SyntheticAdamsSS.{v})
      (r : ℤ) (i : Tridegree) (x : A.E₂ i) (xr : A.Page r i)
      (hx : KIP126.Synthetic.SpectralSequence.RepresentsOnPage A r i x xr)
      (hout : ∀ n : ℤ, r ≤ n → A.sequence.d n i = 0) :
      ∃ e : (A.sequence.ssData i).eInfty, HasInfinityRepresentative A 2 i x e := by
    obtain ⟨hr,z,hz,he⟩ := hx
    have hZ := cycles_top_eq_of_d_eq_zero A.sequence r (by rw [A.firstPage]; exact hr) i hout
    rw [A.firstPage] at hZ
    let zInf := (Subobject.ofLE _ _ hZ.ge) z
    refine ⟨_,by norm_num,zInf,?_,rfl⟩
    change (Subobject.ofLE _ _ _ ≫ (A.sequence.ssData i).pageπ 0)
      ((Subobject.ofLE _ _ hZ.ge) z)=x
    rw [←CategoryTheory.comp_apply,←Category.assoc,Subobject.ofLE_comp_ofLE]
    exact hz

  have page_has_initial_rep
      {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)}
      {r : ℤ} {p : ℤ × ℤ} (hr : 2 ≤ r) (a : E.Page r p) :
      ∃ x : E.Page 2 p, KIP126.SpectralSequence.RepresentsOnPage E r p x a := by
    haveI : Epi ((E.ssData p).pageπ ↑(r-E.r₀).toNat) := by
      change Epi (cokernel.π _)
      infer_instance
    obtain ⟨z,hz⟩ := (ModuleCat.epi_iff_surjective ((E.ssData p).pageπ ↑(r-E.r₀).toNat)).mp inferInstance a
    exact ⟨_,hr,z,rfl,hz⟩

  have shiftedFiniteSource_exists (D : AdamsComparison H M Syn)
      (synthetic : SyntheticComparisonTheorems D) (X : ClassicalObject) (q : ℕ) (hq : 0 < q)
      (a s t : ℤ)
      (eqs : XModLambdaN ((SyntheticCategory.biShift (0,a)).obj (D.nu.functor.obj (X.obj D.hopfAndDetector))) q ≅
        (SyntheticCategory.biShift (0,a)).obj (XModLambdaN (D.nu.functor.obj (X.obj D.hopfAndDetector)) q))
      (x : E2 H (X.obj D.hopfAndDetector) s t)
      (hx : x ∈ cycles H (X.obj D.hopfAndDetector) q (s,t)) :
      ∃ e : ((D.family.obj ((SyntheticObject.quotient q (.shift (0,a) (.nu X))).obj D.nu D.hopfAndDetector)).sequence.ssData (s,t,t+a-(0:ℕ))).eInfty,
        HasInfinityRepresentative _ 2 (s,t,t+a-(0:ℕ)) (finiteNuLabel D X q a s t 0 x) e := by
    let E := adamsTowerInternalSpectralSequence H.unit (X.obj D.hopfAndDetector)
    have hr : 2 ≤ (q+1:ℕ) := by omega
    have hx' : IsCycle H (X.obj D.hopfAndDetector) ((q+1:ℕ)-1:ℤ) (s,t) x := by
      refine ⟨by omega,?_⟩
      simpa only [Nat.cast_add,Nat.cast_one,add_sub_cancel_right] using hx
    obtain ⟨xr,hxr⟩ := (isCycle_iff_represents H (X.obj D.hopfAndDetector) (q+1:ℕ) (by omega) (s,t) x).mp hx'
    have hd : (s,t) + E.diffDeg (q+1:ℕ) = (s+(q+1:ℕ),t+(q+1:ℕ)-1) := by
      change (s+(q+1:ℕ),t+((q+1:ℕ)-1)) = _
      congr 1; omega
    let yr := (E.d (q+1:ℕ) (s,t) ≫ eqToHom (congrArg (E.Page (q+1:ℕ)) hd)) xr
    obtain ⟨y,hy⟩ := page_has_initial_rep (by omega : (2:ℤ)≤(q+1:ℕ)) yr
    have hc : KIP126.SpectralSequence.HasDifferential E (q+1:ℕ)
        (s,t) (s+(q+1:ℕ),t+(q+1:ℕ)-1) x y := ⟨hd,xr,yr,hxr,hy,rfl⟩
    have hs := (synthetic.differentials X a s t (q+1) 0 hr x y).mp hc
    obtain ⟨_,xs,ys,hxs,hys,hds⟩ := hs
    have hf := syntheticRep_map D (XModLambdaN.incl _ q) (q+1:ℕ)
      (s,t,t+a-(0:ℕ)) (D.nuE2 X a s t 0 x) xs hxs
    apply syntheticRep_infty _ (q+1:ℕ) (s,t,t+a-(0:ℕ)) _ _ hf
    intro n hn
    have hi : (s,t,t+a-(0:ℕ)) +
        (D.family.functor.obj (XModLambdaN ((SyntheticCategory.biShift (0,a)).obj
          (D.nu.functor.obj (X.obj D.hopfAndDetector))) q)).diffDeg n = (s+n,t+n-1,t+a) := by
      rw [D.family.differentialDegree]
      simp only [syntheticAdamsDifferentialDegree, Prod.mk_add_mk, Nat.cast_zero, sub_zero, add_zero]
      ext <;> dsimp; omega
    haveI := shiftedFinitePageVanishing D synthetic X q hq a n (s+n) (t+n-1) (t+a)
      eqs (by omega) (Or.inr (by omega))
    have hp : Subsingleton ((D.family.functor.obj (XModLambdaN ((SyntheticCategory.biShift (0,a)).obj
        (D.nu.functor.obj (X.obj D.hopfAndDetector))) q)).Page n
          ((s,t,t+a-(0:ℕ)) + (D.family.functor.obj (XModLambdaN ((SyntheticCategory.biShift (0,a)).obj
            (D.nu.functor.obj (X.obj D.hopfAndDetector))) q)).diffDeg n)) := by
      rw [hi]
      simpa only [KIP126.SpectralSequence.Page, D.family.firstPage, SyntheticAdamsSS.Page,
        SyntheticAdamsFamily.obj] using (inferInstance : Subsingleton
          ((D.family.obj (XModLambdaN ((SyntheticCategory.biShift (0,a)).obj
            (D.nu.functor.obj (X.obj D.hopfAndDetector))) q)).Page n (s+n,t+n-1,t+a)))
    letI := hp
    ext z
    exact @Subsingleton.elim _ hp _ _

  letI := D.shiftCommShift (0,a)
  letI := D.shiftExact (0,a)
  obtain ⟨eqs,heqs⟩ := quotient_shift_exists D.shiftCoherence (0,a) q (D.nu.functor.obj (X.obj D.hopfAndDetector))
  exact shiftedFiniteSource_exists D synthetic X q hq a s t eqs x hx

end ShiftedRepresentatives

end KIP126.Main.ExtensionLaws
