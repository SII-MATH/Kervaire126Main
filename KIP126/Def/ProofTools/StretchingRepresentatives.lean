module

public import KIP126.Def.ProofTools.Representatives

/-! Internal representative transport in the finite stretching proof.
Adapted from the proved source at bbac1fc05843 (MIT; retained source LICENSE).
The selected Literature and AdamsSynthetic interfaces are used directly. -/

@[expose] section
namespace KIP126.ProofTools.Internal
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open CategoryTheory.Pretriangulated KIP126.StableHomotopy
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.AdamsSynthetic.Standard
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

set_option maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
private theorem quotient_shift_exists (coh : BiShiftCoherence SyntheticSpectrum)
    (a : ℤ × ℤ) (q : ℕ) (X : SyntheticSpectrum)
    [cs : (SyntheticCategory.biShift (Syn := SyntheticSpectrum) a).CommShift ℤ]
    [(SyntheticCategory.biShift (Syn := SyntheticSpectrum) a).IsTriangulated] :
    ∃ e : XModLambdaN ((SyntheticCategory.biShift a).obj X) q ≅
      (SyntheticCategory.biShift a).obj (XModLambdaN X q),
      XModLambdaN.incl ((SyntheticCategory.biShift a).obj X) q ≫ e.hom =
        (SyntheticCategory.biShift a).map (XModLambdaN.incl X q) := by
  let oneComm (a : ℤ × ℤ) :
      SyntheticCategory.biShift (Syn := SyntheticSpectrum) a ⋙ SyntheticCategory.biShift (lambdaDegree 1) ≅
        SyntheticCategory.biShift (lambdaDegree 1) ⋙ SyntheticCategory.biShift a :=
    biShiftAddIso a (0,-1) (a+(0,-1)) rfl ≪≫
      (biShiftAddIso (0,-1) a (a+(0,-1)) (add_comm _ _)).symm

  let powerComm (a : ℤ × ℤ) : (q : ℕ) →
      SyntheticCategory.biShift (Syn := SyntheticSpectrum) a ⋙ SyntheticCategory.biShift (lambdaDegree q) ≅
        SyntheticCategory.biShift (lambdaDegree q) ⋙ SyntheticCategory.biShift a := fun q =>
    Nat.rec (motive := fun q =>
      SyntheticCategory.biShift (Syn := SyntheticSpectrum) a ⋙ SyntheticCategory.biShift (lambdaDegree q) ≅
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

  have powerComm_square (coh : BiShiftCoherence SyntheticSpectrum) (a : ℤ × ℤ)
      (q : ℕ) (X : SyntheticSpectrum) :
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

  let F := SyntheticCategory.biShift (Syn := SyntheticSpectrum) a
  let T := Triangle.mk (lambdaPow q X) (XModLambdaN.incl X q) (XModLambdaN.proj X q)
  let T' := Triangle.mk (lambdaPow q (F.obj X))
    (XModLambdaN.incl (F.obj X) q) (XModLambdaN.proj (F.obj X) q)
  have hT : T ∈ distTriang SyntheticSpectrum := HasFunctorialCofiber.cofib_distinguished _
  have hT' : T' ∈ distTriang SyntheticSpectrum := HasFunctorialCofiber.cofib_distinguished _
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


private def familyPageIso {X Y : SyntheticSpectrum} (e : X ≅ Y)
    (r : ℤ) (i : Tridegree) : (model.family.obj X).Page r i ≅ (model.family.obj Y).Page r i where
  hom := familyPageMap model.family e.hom r i
  inv := familyPageMap model.family e.inv r i
  hom_inv_id := by
    change (model.family.map e.hom).pageMap r i ≫ (model.family.map e.inv).pageMap r i = _
    rw [← SpectralSequenceMorphism.pageMap_comp, ← SyntheticAdamsFamily.map_comp,
      e.hom_inv_id, SyntheticAdamsFamily.map_id, SpectralSequenceMorphism.pageMap_id]
  inv_hom_id := by
    change (model.family.map e.inv).pageMap r i ≫ (model.family.map e.hom).pageMap r i = _
    rw [← SpectralSequenceMorphism.pageMap_comp, ← SyntheticAdamsFamily.map_comp,
      e.inv_hom_id, SyntheticAdamsFamily.map_id, SpectralSequenceMorphism.pageMap_id]

private def shiftedPageIso (X : SyntheticObject) (a r s t w : ℤ) (hr : 2 ≤ r) :
    (model.family.obj (X.obj model.nu model.auxiliary)).Page r (s,t,w-a) ≅
      (model.family.obj ((SyntheticObject.shift (0,a) X).obj model.nu model.auxiliary)).Page r (s,t,w) := by
  simpa using (essShift (0,a)).page X r hr (t-s,w-a) s

private def shiftedInfinityIso (X : SyntheticObject) (a s t w : ℤ) :
    ((model.family.obj (X.obj model.nu model.auxiliary)).sequence.ssData (s,t,w-a)).eInfty ≅
      ((model.family.obj ((SyntheticObject.shift (0,a) X).obj model.nu model.auxiliary)).sequence.ssData (s,t,w)).eInfty := by
  simpa using towerInfinityIso (model.convergence X) (model.convergence (.shift (0,a) X))
    ((essShift (0,a)).filtered X (t-s,w-a)) s

private theorem shiftedFinitePageVanishing (X : ClassicalObject) (q : ℕ) (hq : 0 < q)
    (a r s t w : ℤ) (hr : 2 ≤ r) (hw : t < w-a ∨ (q:ℤ) ≤ t-(w-a)) :
    Subsingleton ((model.family.obj (XModLambdaN ((SyntheticCategory.biShift (0,a)).obj
      (model.nu.functor.obj (X.obj model.auxiliary))) q)).Page r (s,t,w)) := by
  have hz := KIP126.Literature.Standard.finite_quotient_vanishing X q hq r hr s t (w-a)
    (by rcases hw with hw | hw; exact Or.inl (by omega); exact Or.inr hw)
  have hsub := ModuleCat.isZero_iff_subsingleton.mp hz
  letI := model.exactness.shiftCommShift (0,a)
  letI := model.exactness.shiftExact (0,a)
  obtain ⟨e,_⟩ := quotient_shift_exists model.quotients.coherence (0,a) q
    (model.nu.functor.obj (X.obj model.auxiliary))
  let iso := (familyPageIso e r (s,t,w)) ≪≫ (shiftedPageIso (.quotient q (.nu X)) a r s t w hr).symm
  refine ⟨fun x y => iso.toLinearEquiv.injective ?_⟩
  exact @Subsingleton.elim _ hsub _ _

private theorem shifted_quotient_eInfty_zero
    (X : ClassicalObject) (q : ℕ) (hq : 0 < q) (e s t w : ℤ)
    (hwindow : ¬ (0 ≤ t-(w-e) ∧ t-(w-e) < (q:ℤ))) :
    IsZero (((model.family.obj (XModLambdaN
      ((SyntheticCategory.biShift (0,e)).obj (model.nu.functor.obj (X.obj model.auxiliary))) q)).sequence.ssData
        (s,t,w)).eInfty) := by
  haveI : Subsingleton (KIP126.Literature.finiteEInftyModel model X q (s,t) (w-e)) := by
    simp only [KIP126.Literature.finiteEInftyModel, hwindow, ite_false]
    infer_instance
  have hsub : Subsingleton (((model.family.obj (XModLambdaN
      (model.nu.functor.obj (X.obj model.auxiliary)) q)).sequence.ssData (s,t,w-e)).eInfty) :=
    (KIP126.Literature.Standard.eInfinity_finite X q hq (s,t) (w-e)).injective.subsingleton
  haveI : Subsingleton (((model.family.obj ((SyntheticCategory.biShift (0,e)).obj (XModLambdaN
      (model.nu.functor.obj (X.obj model.auxiliary)) q))).sequence.ssData (s,t,w)).eInfty) := by
    refine ⟨fun x y => (shiftedInfinityIso (.quotient q (.nu X)) e s t w).symm.toLinearEquiv.injective ?_⟩
    exact @Subsingleton.elim _ hsub _ _
  have hz := ModuleCat.isZero_of_subsingleton (((model.family.obj
    ((SyntheticCategory.biShift (0,e)).obj (XModLambdaN
      (model.nu.functor.obj (X.obj model.auxiliary)) q))).sequence.ssData (s,t,w)).eInfty)
  letI := model.exactness.shiftCommShift (0,e)
  letI := model.exactness.shiftExact (0,e)
  obtain ⟨Q,_⟩ := quotient_shift_exists model.quotients.coherence (0,e) q
    (model.nu.functor.obj (X.obj model.auxiliary))
  let eval : KIP126.Core.SpectralSequence (ModuleCat ℤ) Tridegree ⥤ ModuleCat ℤ := {
    obj := fun E => (E.ssData (s,t,w)).eInfty
    map := fun f => f.eInftyMap (s,t,w)
    map_id := fun E => SpectralSequenceMorphism.eInftyMap_id E (s,t,w)
    map_comp := fun f g => SpectralSequenceMorphism.eInftyMap_comp f g (s,t,w) }
  exact hz.of_iso ((model.family.functor ⋙ eval).mapIso Q)

private theorem subquotientMap_injective {R : Type*} [Ring R] {A : Type*} [AddCommGroup A] [Module R A]
    {Z Z' B : Submodule R A} (hZ : Z ≤ Z') :
    Function.Injective (KIP126.Literature.subquotientMap hZ (le_rfl : B ≤ B)) := by
  apply (LinearMap.ker_eq_bot).mp
  apply le_antisymm
  · intro x hx
    obtain ⟨x,rfl⟩ := Submodule.Quotient.mk_surjective _ x
    change KIP126.Literature.subquotientMap hZ (le_rfl : B ≤ B) (Submodule.Quotient.mk x) = 0 at hx
    change Submodule.Quotient.mk (Submodule.inclusion hZ x) = 0 at hx
    have hxB := (Submodule.Quotient.mk_eq_zero _).mp hx
    change x.val ∈ B at hxB
    change Submodule.Quotient.mk x = 0
    exact (Submodule.Quotient.mk_eq_zero _).mpr hxB
  · exact bot_le

private theorem rho_infty_injective (Y : ClassicalObject) (i j : ℕ)
    (hi : 0 < i) (hij : i ≤ j) (s t w : ℤ) (hupper : t-w < i) :
    Function.Injective ((model.family.map
      ((model.quotients.tower (model.nu.functor.obj (Y.obj model.auxiliary))).rho i j hij)).eInftyMap (s,t,w)) := by
  by_cases hlow : 0 ≤ t-w
  · intro x y hxy
    apply (KIP126.Literature.Standard.infinityFiniteWindow Y j (by omega) (s,t) w
      (by constructor <;> omega)).injective
    apply subquotientMap_injective (KIP126.Literature.cycles_antitone model Y (s,t)
      (show (i:ℤ)-t+w ≤ (j:ℤ)-t+w by omega))
    have hx := KIP126.Literature.Standard.eInfinity_rho_finite Y i j hi hij (s,t) w ⟨hlow,hupper⟩ x
    have hy := KIP126.Literature.Standard.eInfinity_rho_finite Y i j hi hij (s,t) w ⟨hlow,hupper⟩ y
    rw [hxy] at hx
    exact hx.symm.trans hy
  · haveI : Subsingleton (KIP126.Literature.finiteEInftyModel model Y j (s,t) w) := by
      simp only [KIP126.Literature.finiteEInftyModel, show ¬ (0 ≤ t-w ∧ t-w < (j:ℤ)) by omega, ite_false]
      infer_instance
    haveI : Subsingleton (((model.family.quotient (model.nu.functor.obj (Y.obj model.auxiliary)) j).sequence.ssData (s,t,w)).eInfty) :=
      (KIP126.Literature.Standard.eInfinity_finite Y j (by omega) (s,t) w).injective.subsingleton
    intro x y _
    apply @Subsingleton.elim (((model.family.quotient (model.nu.functor.obj (Y.obj model.auxiliary)) j).sequence.ssData (s,t,w)).eInfty)
      inferInstance x y

private theorem syntheticRep_map {A B : SyntheticAdamsSS}
    (f : A.sequence ⟶ B.sequence) {r : ℤ} {i : Tridegree}
    {x : A.E₂ i} {xr : A.Page r i}
    (hx : SyntheticRepresentsOnPage A r i x xr) :
    SyntheticRepresentsOnPage B r i (f.pageMap 2 i x) (f.pageMap r i xr) := by
  have hstart := f.r₀_eq
  rcases A with ⟨⟨⟨r₀, D, δ, d⟩, dd, Zs, Bs⟩, hA, hDA⟩
  rcases B with ⟨⟨⟨r₀', D', δ', d'⟩, dd', Zs', Bs'⟩, hB, hDB⟩
  dsimp at hstart
  subst r₀'
  obtain ⟨hr,z,hz,he⟩ := hx
  let n : WithTop ℕ := ↑(2-r₀).toNat
  let m : WithTop ℕ := ↑(r-r₀).toNat
  let F := f.toSSDataMorphism
  have hnm : n ≤ m := by
    dsimp [n,m]
    exact_mod_cast (show (2-r₀).toNat ≤ (r-r₀).toNat by omega)
  refine ⟨hr,F.cycleMap i m z,?_,?_⟩
  · have hs := F.cycleMap_ofLE_assoc i hnm ((D' i).pageπ n)
    have hp := F.pageπ_pageMap i n
    have eqn : (Subobject.ofLE ((D i).Z m) ((D i).Z n) ((D i).Z_anti hnm) ≫
        (D i).pageπ n) ≫ F.pageMap i n =
      F.cycleMap i m ≫ Subobject.ofLE ((D' i).Z m) ((D' i).Z n) ((D' i).Z_anti hnm) ≫ (D' i).pageπ n := by
      rw [Category.assoc,hp]
      exact hs
    have hh := congrArg (fun a => a z) eqn
    simpa only [ModuleCat.comp_apply, hz, SpectralSequenceMorphism.pageMap,
      SpectralSequenceMorphism.toPreSSMorphism, PreSSMorphism.pageMap, SSDataMorphism.pageMapAt,
      eqToHom_refl, Category.comp_id, n, m, F] using hh.symm
  · have hh := congrArg (fun a => a z) (F.pageπ_pageMap i m)
    simpa only [ModuleCat.comp_apply, he, SpectralSequenceMorphism.pageMap,
      SpectralSequenceMorphism.toPreSSMorphism, PreSSMorphism.pageMap, SSDataMorphism.pageMapAt,
      eqToHom_refl, Category.comp_id, n, m, F] using hh.symm

private theorem family_infinity_representative_map {X Y : SyntheticSpectrum}
    (f : X ⟶ Y) (i : Tridegree)
    (x : (model.family.obj X).E₂ i) (e : ((model.family.obj X).sequence.ssData i).eInfty)
    (hx : HasInfinityRepresentative (model.family.obj X) 2 i x e) :
    HasInfinityRepresentative (model.family.obj Y) 2 i
      (familyPageMap model.family f 2 i x) ((model.family.map f).eInftyMap i e) := by
  have aux {A B : SyntheticAdamsSS} (f : A.sequence ⟶ B.sequence)
      (x : A.E₂ i) (e : (A.sequence.ssData i).eInfty)
      (hx : HasInfinityRepresentative A 2 i x e) :
      HasInfinityRepresentative B 2 i (f.pageMap 2 i x) (f.eInftyMap i e) := by
    have hstart := f.r₀_eq
    rcases A with ⟨⟨⟨r₀,D,δ,d⟩,dd,Zs,Bs⟩,hA,hDA⟩
    rcases B with ⟨⟨⟨r₀',D',δ',d'⟩,dd',Zs',Bs'⟩,hB,hDB⟩
    dsimp at hstart
    subst r₀'
    obtain ⟨hr,z,hz,he⟩ := hx
    let n : WithTop ℕ := ↑(2-r₀).toNat
    let F := f.toSSDataMorphism
    refine ⟨hr,F.cycleMap i ⊤ z,?_,?_⟩
    · have hs := F.cycleMap_ofLE_assoc i (show n ≤ ⊤ from le_top) ((D' i).pageπ n)
      rw [← F.pageπ_pageMap] at hs
      have hh := congrArg (fun a => a z) hs
      change (D' i).pageπ n ((Subobject.ofLE ((D' i).Z ⊤) ((D' i).Z n) ((D' i).Z_anti le_top)) (F.cycleMap i ⊤ z)) =
        F.pageMap i n x
      change (D i).pageπ n ((Subobject.ofLE ((D i).Z ⊤) ((D i).Z n) ((D i).Z_anti le_top)) z) = x at hz
      simpa only [ModuleCat.comp_apply, hz] using hh.symm
    · change (D' i).pageπ ⊤ (F.cycleMap i ⊤ z) = F.pageMap i ⊤ e
      exact (congrArg (fun a => a z) (F.pageπ_pageMap i ⊤)).symm.trans (by
        change F.pageMap i ⊤ ((D i).pageπ ⊤ z) = _
        rw [he])
  exact aux (model.family.map f) x e hx

private theorem syntheticRep_infty (A : SyntheticAdamsSS)
    (r : ℤ) (i : Tridegree) (x : A.E₂ i) (xr : A.Page r i)
    (hx : SyntheticRepresentsOnPage A r i x xr)
    (hout : ∀ n : ℤ, r ≤ n → A.sequence.d n i = 0) :
    ∃ e : (A.sequence.ssData i).eInfty, HasInfinityRepresentative A 2 i x e := by
  obtain ⟨hr,z,hz,he⟩ := hx
  have hZ := cycles_top_eq_of_d_eq_zero A.sequence r (by rw [A.firstPage]; exact hr) i hout
  let zInf := (Subobject.ofLE _ _ hZ.ge) z
  refine ⟨_,by norm_num,zInf,?_,rfl⟩
  change (Subobject.ofLE _ _ _ ≫ (A.sequence.ssData i).pageπ _)
    ((Subobject.ofLE _ _ hZ.ge) z)=x
  rw [←CategoryTheory.comp_apply,←Category.assoc,Subobject.ofLE_comp_ofLE]
  exact hz

private theorem shifted_finite_source_exists
    (X : ClassicalObject) (q : ℕ) (hq : 0 < q)
    (a s t : ℤ) (x : Ambient model X (s,t))
    (hx : x ∈ KIP126.Literature.cycles model X q (s,t)) :
    ∃ e : ((model.family.obj ((SyntheticObject.quotient q (.shift (0,a) (.nu X))).obj model.nu model.auxiliary)).sequence.ssData (s,t,t+a-(0:ℕ))).eInfty,
      HasInfinityRepresentative _ 2 (s,t,t+a-(0:ℕ)) (finiteNuLabel model X q a s t 0 x) e := by
  let E := model.classical.obj (X.obj model.auxiliary)
  have hr : 2 ≤ q+1 := by omega
  have hx' : ReachesPage E (q+1) (s,t) x := by
    apply (isCycle_iff_reaches model X (q+1) (by omega) (s,t) x).mp
    refine ⟨by omega,?_⟩
    simpa using hx
  obtain ⟨xr,hxr⟩ := hx'
  have hd : (s,t) + E.diffDeg (q+1:ℕ) = (s+(q+1:ℕ),t+(q+1:ℕ)-1) := by
    rw [model.classical.differentialDegree]
    ext <;> dsimp <;> omega
  let yr := (E.d (q+1:ℕ) (s,t) ≫ eqToHom (congrArg (E.Page (q+1:ℕ)) hd)) xr
  obtain ⟨y,hy⟩ := FinitePageCalculus.page_has_initial_representative (by omega : (2:ℤ)≤(q+1:ℕ)) yr
  have hc : HasDifferential E (q+1:ℕ)
      (s,t) (s+(q+1:ℕ),t+(q+1:ℕ)-1) x y := ⟨hd,xr,yr,hxr,hy,rfl⟩
  have hs := (KIP126.Literature.Standard.bhs_differentials X a s t (q+1) 0 hr x y).mp hc
  obtain ⟨_,xs,ys,hxs,hys,hds⟩ := hs
  have hf := syntheticRep_map (model.family.map (XModLambdaN.incl _ q)) hxs
  apply syntheticRep_infty _ (q+1:ℕ) (s,t,t+a-(0:ℕ)) _ _ hf
  intro n hn
  have hi : (s,t,t+a-(0:ℕ)) +
      (model.family.functor.obj (XModLambdaN ((SyntheticCategory.biShift (0,a)).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) q)).diffDeg n = (s+n,t+n-1,t+a) := by
    rw [model.family.differentialDegree]
    simp only [syntheticAdamsRawShift, Prod.mk_add_mk, Nat.cast_zero, sub_zero, add_zero]
    ext <;> dsimp <;> omega
  have hsub := shiftedFinitePageVanishing X q hq a n (s+n) (t+n-1) (t+a)
    (by omega) (Or.inr (by omega))
  have hp : Subsingleton ((model.family.functor.obj (XModLambdaN ((SyntheticCategory.biShift (0,a)).obj
      (model.nu.functor.obj (X.obj model.auxiliary))) q)).Page n
        ((s,t,t+a-(0:ℕ)) + (model.family.functor.obj (XModLambdaN ((SyntheticCategory.biShift (0,a)).obj
          (model.nu.functor.obj (X.obj model.auxiliary))) q)).diffDeg n)) := by
    rw [hi]
    exact hsub
  ext z
  exact @Subsingleton.elim _ hp _ _

private theorem family_page_comp {X Y Z : SyntheticSpectrum}
    (f : X ⟶ Y) (g : Y ⟶ Z) (r : ℤ) (i : Tridegree) :
    familyPageMap model.family f r i ≫ familyPageMap model.family g r i =
      familyPageMap model.family (f ≫ g) r i := by
  change (model.family.map f).pageMap r i ≫ (model.family.map g).pageMap r i = _
  rw [← SpectralSequenceMorphism.pageMap_comp, ← SyntheticAdamsFamily.map_comp]
  rfl

private theorem page_regrade {A B : SyntheticSpectrum} (f : A ⟶ B) {i j : Tridegree}
    (h : i = j) (z : (model.family.obj A).E₂ i) :
    regradeE2 h (familyPageMap model.family f 2 i z) =
      familyPageMap model.family f 2 j (regradeE2 h z) := by
  subst j
  rfl

private theorem finite_source_rho (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (i j : ℕ) (hij : i ≤ j) (s t : ℤ) (x : Ambient model X (s,t)) :
    familyPageMap model.family
      ((model.quotients.tower ((extensionSourceObject model X Y f).obj model.nu model.auxiliary)).rho i j hij) 2
      (s, (t-s)+s, t+normalizedExponent model.classicalTower f)
      (finiteSourceForExtension model X Y f j s t x) =
        finiteSourceForExtension model X Y f i s t x := by
  unfold finiteSourceForExtension
  rw [← page_regrade]
  congr 1
  unfold finiteNuLabel
  have hc := congrArg (fun g => familyPageMap model.family g 2
    (s,t,t+(normalizedExponent model.classicalTower f : ℤ)-(0:ℕ)))
    ((model.quotients.tower ((extensionSourceObject model X Y f).obj model.nu model.auxiliary)).rho_quotient hij)
  rw [← family_page_comp] at hc
  exact ConcreteCategory.congr_hom hc ((model.comparison.nuE2 X _ s t 0) x)

private theorem finite_target_rho (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (i j : ℕ) (hij : i ≤ j) (n s t : ℤ)
    (hn : (normalizedExponent model.classicalTower f : ℤ) ≤ n)
    (y : Ambient model Y ((s+n),(t+n))) :
    familyPageMap model.family ((model.quotients.tower (model.nu.functor.obj (Y.obj model.auxiliary))).rho i j hij) 2
      (s+n, (t-s)+(s+n), t+normalizedExponent model.classicalTower f)
      (finiteTargetForExtension model X Y f j n s t hn y) =
        finiteTargetForExtension model X Y f i n s t hn y := by
  unfold finiteTargetForExtension
  rw [← page_regrade]
  congr 1
  unfold finiteTargetLabel
  have hc := congrArg (fun g => familyPageMap model.family g 2
    (s+n,t+n,t+n-(n-normalizedExponent model.classicalTower f).toNat))
    ((model.quotients.tower (model.nu.functor.obj (Y.obj model.auxiliary))).rho_quotient hij)
  rw [← family_page_comp] at hc
  exact ConcreteCategory.congr_hom hc (targetNuLabel model Y (s+n) (t+n) _ y)


private theorem infinity_representative_regrade
    {A : SyntheticAdamsSS} {i j : Tridegree} (h : i = j)
    (x : A.E₂ i) (e : (A.sequence.ssData i).eInfty)
    (he : HasInfinityRepresentative A 2 i x e) :
    HasInfinityRepresentative A 2 j (regradeE2 h x)
      ((eqToHom (congrArg (fun p => (A.sequence.ssData p).eInfty) h)) e) := by
  subst j
  exact he

private theorem finite_target_infinity_exists (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (q : ℕ) (hq : 0 < q) (n s t : ℤ)
    (hn : (normalizedExponent model.classicalTower f : ℤ) ≤ n)
    (hk : n - normalizedExponent model.classicalTower f < q)
    (y : Ambient model Y ((s + n),(t + n)))
    (hy : y ∈ KIP126.Literature.cycles model Y
      ((q : ℤ) - n + normalizedExponent model.classicalTower f) (s + n, t + n)) :
    ∃ e : ((model.family.obj ((SyntheticObject.quotient q (.nu Y)).obj
        model.nu model.auxiliary)).sequence.ssData
          (s + n, (t - s) + (s + n), t + normalizedExponent model.classicalTower f)).eInfty,
      HasInfinityRepresentative _ 2 _ (finiteTargetForExtension model X Y f q n s t hn y) e := by
  let k := (n - normalizedExponent model.classicalTower f).toNat
  have hkZ : (k : ℤ) = n - normalizedExponent model.classicalTower f := Int.toNat_of_nonneg (by omega)
  let p : ℤ × ℤ := (s+n,t+n)
  have hw : 0 ≤ p.2-(p.2-k) ∧ p.2-(p.2-k) < q := by constructor <;> dsimp only [p] <;> omega
  let P := KIP126.Literature.Standard.infinityFiniteWindow Y q hq p (p.2-k) hw
  have hy' : y ∈ KIP126.Literature.cycles model Y (q-p.2+(p.2-k)) p := by
    have hlvl : (q:ℤ)-p.2+(p.2-k) = (q:ℤ)-n+normalizedExponent model.classicalTower f := by omega
    simpa only [hlvl] using hy
  let c := KIP126.Literature.subquotientClass
    (KIP126.Literature.cycles model Y (q-p.2+(p.2-k)) p)
    (KIP126.Literature.boundaries model Y (1+p.2-(p.2-k)) p) ⟨y,hy'⟩
  let e := P.symm c
  have hlabel : nuWeightLabel model Y p.1 p.2 (p.2-k) (by omega) y =
      targetNuLabel model Y p.1 p.2 k y := by
    have hk : (p.2-(p.2-k)).toNat = k := by omega
    have transport (a b : ℕ) (hab : a = b)
        (h : (p.1,p.2,p.2-a) = (p.1,p.2,p.2-b)) :
        regradeE2 h (targetNuLabel model Y p.1 p.2 a y) = targetNuLabel model Y p.1 p.2 b y := by
      subst b
      rfl
    exact transport _ k hk _
  have he : HasInfinityRepresentative (model.family.quotient
      (model.nu.functor.obj (Y.obj model.auxiliary)) q) 2 (p.1,p.2,p.2-k)
      (finiteTargetLabel model Y q p.1 p.2 k y) e := by
    have hh := (KIP126.Literature.Standard.eInfinity_finite_labels Y q hq p.1 p.2
      (p.2-k) hw y e).mpr ⟨hy',P.apply_symm_apply c⟩
    rw [hlabel] at hh
    exact hh
  have hi : (p.1,p.2,p.2-k) =
      (s+n,(t-s)+(s+n),t+normalizedExponent model.classicalTower f) := by
    dsimp only [p]
    ext <;> dsimp <;> omega
  refine ⟨(eqToHom (congrArg (fun p => ((model.family.quotient
    (model.nu.functor.obj (Y.obj model.auxiliary)) q).sequence.ssData p).eInfty) hi)) e,?_⟩
  exact infinity_representative_regrade hi _ _ he

private theorem finite_representatives_lift (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (rEarlier rLater : ℕ) (n s t : ℤ)
    (x : Ambient model X (s,t))
    (y : Ambient model Y ((s+n),(t+n)))
    (hr : 2 ≤ rEarlier) (hle : rEarlier ≤ rLater)
    (hn : (normalizedExponent model.classicalTower f : ℤ) ≤ n)
    (hnUpper : n ≤ (rEarlier:ℤ)-2+normalizedExponent model.classicalTower f)
    (hx : IsCycle model X ((rLater:ℤ)-1) (s,t) x)
    (hy : IsCycle model Y
      ((rLater:ℤ)-1-n+normalizedExponent model.classicalTower f) (s+n,t+n) y)
    (W : FiniteExtensionWitness model X Y f rEarlier n s t x y) :
    ∃ (xx : ((model.family.obj ((SyntheticObject.quotient (rLater-1)
        (extensionSourceObject model X Y f)).obj model.nu model.auxiliary)).sequence.ssData
        (s,(t-s)+s,t+normalizedExponent model.classicalTower f)).eInfty)
      (yy : ((model.family.obj ((SyntheticObject.quotient (rLater-1) (.nu Y)).obj
        model.nu model.auxiliary)).sequence.ssData
        (s+n,(t-s)+(s+n),t+normalizedExponent model.classicalTower f)).eInfty),
      HasInfinityRepresentative _ 2 _ (finiteSourceForExtension model X Y f (rLater-1) s t x) xx ∧
      HasInfinityRepresentative _ 2 _ (finiteTargetForExtension model X Y f (rLater-1) n s t hn y) yy ∧
      (model.family.functor.map ((model.quotients.tower ((extensionSourceObject model X Y f).obj model.nu model.auxiliary)).rho
        (rEarlier-1) (rLater-1) (Nat.sub_le_sub_right hle 1))).eInftyMap
        (s,(t-s)+s,t+normalizedExponent model.classicalTower f) xx = W.source ∧
      (model.family.functor.map ((model.quotients.tower (model.nu.functor.obj (Y.obj model.auxiliary))).rho
        (rEarlier-1) (rLater-1) (Nat.sub_le_sub_right hle 1))).eInftyMap
        (s+n,(t-s)+(s+n),t+normalizedExponent model.classicalTower f) yy = W.target := by



  have hq : 0 < rLater-1 := by omega
  have hij : rEarlier-1 ≤ rLater-1 := Nat.sub_le_sub_right hle 1
  obtain ⟨xs,hxs⟩ := shifted_finite_source_exists X (rLater-1) hq
    (normalizedExponent model.classicalTower f) s t x (by
      simpa only [Nat.cast_sub (show 1≤rLater by omega),Nat.cast_one] using hx.2)
  have hsgrade : (s,t,t+(normalizedExponent model.classicalTower f:ℤ)-(0:ℕ)) =
      (s,(t-s)+s,t+normalizedExponent model.classicalTower f) := by simp
  let xx := (eqToHom (congrArg (fun p => ((model.family.obj ((SyntheticObject.quotient (rLater-1)
    (extensionSourceObject model X Y f)).obj model.nu model.auxiliary)).sequence.ssData p).eInfty) hsgrade)) xs
  have hxx : HasInfinityRepresentative _ 2 _
      (finiteSourceForExtension model X Y f (rLater-1) s t x) xx :=
    infinity_representative_regrade hsgrade _ xs hxs
  obtain ⟨yy,hyy⟩ := finite_target_infinity_exists X Y f
    (rLater-1) hq n s t hn (by omega) y (by
      simpa only [Nat.cast_sub (show 1≤rLater by omega),Nat.cast_one] using hy.2)
  refine ⟨xx,yy,hxx,hyy,?_,?_⟩
  · have hh := family_infinity_representative_map
      ((model.quotients.tower ((extensionSourceObject model X Y f).obj model.nu model.auxiliary)).rho
        (rEarlier-1) (rLater-1) hij) _ _ xx hxx
    rw [finite_source_rho] at hh
    exact hh.unique W.source_rep
  · have hh := family_infinity_representative_map
      ((model.quotients.tower (model.nu.functor.obj (Y.obj model.auxiliary))).rho
        (rEarlier-1) (rLater-1) hij) _ _ yy hyy
    rw [finite_target_rho] at hh
    exact hh.unique W.target_rep


end
end KIP126.ProofTools.Internal
