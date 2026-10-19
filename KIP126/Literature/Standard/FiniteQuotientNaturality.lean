module

import all KIP126.Literature.Standard.FiniteQuotientTriangle

/-! Strict naturality of the actual first quotient coordinates under actual
shifted nu-images. Detection transport and finite-window arguments are
proved from the existing public inputs; no ProofTools import is used.
This file does not identify the action of a positive-exponent normalized lift.
-/

@[expose] section
namespace KIP126.Literature.Standard
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000

section Generic
universe u v
private theorem first_quotient_infinity_rep_morphism
    {E E' : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) Tridegree}
    (f : E ⟶ E') (i : Tridegree) {x : E.Page 2 i} {e : (E.ssData i).eInfty}
    (h : ∃ z : (Subobject.underlying.obj ((E.ssData i).Z ⊤) : ModuleCat ℤ),
      (Subobject.ofLE _ _ ((E.ssData i).Z_anti le_top) ≫
        (E.ssData i).pageπ (↑(2-E.r₀).toNat : WithTop ℕ)) z = x ∧
      (E.ssData i).pageπ ⊤ z = e) :
    ∃ z : (Subobject.underlying.obj ((E'.ssData i).Z ⊤) : ModuleCat ℤ),
      (Subobject.ofLE _ _ ((E'.ssData i).Z_anti le_top) ≫
        (E'.ssData i).pageπ (↑(2-E'.r₀).toNat : WithTop ℕ)) z = f.pageMap 2 i x ∧
      (E'.ssData i).pageπ ⊤ z = f.eInftyMap i e := by
  have hstart := f.r₀_eq
  rcases E with ⟨⟨r₀,D,δ,d⟩,dd,Zs,Bs⟩
  rcases E' with ⟨⟨r₀',D',δ',d'⟩,dd',Zs',Bs'⟩
  dsimp at hstart
  subst r₀'
  obtain ⟨z,hz,he⟩ := h
  let n : WithTop ℕ := ↑(2-r₀).toNat
  refine ⟨f.toSSDataMorphism.cycleMap i ⊤ z, ?_, ?_⟩
  · have hs := f.toSSDataMorphism.cycleMap_ofLE_assoc i
      (r := n) (s := ⊤) le_top ((D' i).pageπ n)
    have hp := f.toSSDataMorphism.pageπ_pageMap i n
    have hq : (Subobject.ofLE ((D i).Z ⊤) ((D i).Z n) ((D i).Z_anti le_top) ≫
        (D i).pageπ n) ≫ f.toSSDataMorphism.pageMap i n =
        f.toSSDataMorphism.cycleMap i ⊤ ≫
          Subobject.ofLE ((D' i).Z ⊤) ((D' i).Z n) ((D' i).Z_anti le_top) ≫ (D' i).pageπ n := by
      rw [Category.assoc,hp]
      exact hs
    change ((Subobject.ofLE _ _ _ ≫ (D' i).pageπ n)
      (f.toSSDataMorphism.cycleMap i ⊤ z)) =
      ((f.toSSDataMorphism.pageMap i n ≫ eqToHom _) x)
    simpa only [ModuleCat.comp_apply, hz, eqToHom_refl, Category.comp_id, n]
      using (ConcreteCategory.congr_hom hq z).symm
  · have hp := f.toSSDataMorphism.pageπ_pageMap i ⊤
    change (D' i).pageπ ⊤ (f.toSSDataMorphism.cycleMap i ⊤ z) =
      f.toSSDataMorphism.pageMap i ⊤ e
    simpa only [ModuleCat.comp_apply, he] using
      (ConcreteCategory.congr_hom hp z).symm

private theorem first_quotient_infinity_rep_map {Syn : Type u} [SyntheticCategory.{u,v} Syn]
    {F : SyntheticAdamsFamily Syn} {X Y : Syn} (g : X ⟶ Y)
    (i : Tridegree) {x : (F.obj X).Page 2 i}
    {e : ((F.obj X).sequence.ssData i).eInfty}
    (h : HasInfinityRepresentative (F.obj X) 2 i x e) :
    HasInfinityRepresentative (F.obj Y) 2 i (F.pageMap g 2 i x)
      ((F.map g).eInftyMap i e) := by
  obtain ⟨hr,z,hz,he⟩ := h
  obtain ⟨z',hz',he'⟩ := first_quotient_infinity_rep_morphism (F.map g) i ⟨z,hz,he⟩
  exact ⟨hr,z',hz',he'⟩

/-- Detection is natural for the prescribed homotopy and E∞ maps of one convergent map. -/
private theorem first_quotient_detects_map {Syn : Type u} [SyntheticCategory.{u,v} Syn]
    [HasFunctorialCofiber (C := Syn)] {H : Syn} {unit : S_0_0 ⟶ H}
    {F : SyntheticAdamsFamily Syn} {P : SyntheticTowerPresentation unit F}
    {X Y : Syn} {g : X ⟶ Y} {cx : SyntheticTowerConvergence P X}
    {cy : SyntheticTowerConvergence P Y}
    (M : ConvergentMap F g cx.toConvergence cy.toConvergence)
    (i : Tridegree) {x : (F.obj X).Page 2 i}
    {a : BiHom (i.2.1-i.1) i.2.2 X}
    (h : KIP126.AdamsSynthetic.Detects cx i x a) :
    KIP126.AdamsSynthetic.Detects cy i (F.pageMap g 2 i x) (a ≫ g) := by
  obtain ⟨e, he, b, hb, hgr⟩ := h
  let hc := M.comparison.filtration_compat i.1 (i.2.1-i.1,i.2.2)
  let b' := hc.choose b
  refine ⟨(F.map g).eInftyMap i e, first_quotient_infinity_rep_map g i he, b', ?_, ?_⟩
  · have hmap := ConcreteCategory.congr_hom hc.choose_spec b
    have heq := ConcreteCategory.congr_hom
      (congrFun M.abutment_eq (i.2.1-i.1,i.2.2))
      (((P.filtration X).F i.1 (i.2.1-i.1,i.2.2)).arrow b)
    change ((P.filtration Y).F i.1 (i.2.1-i.1,i.2.2)).arrow b' = _
    exact hmap.trans (heq.trans (congrArg (fun z => z ≫ g) hb))
  · have hm := M.comparison.iso_compat i
    simp only [SyntheticTowerConvergence.toConvergence, Filtration.transportGraded_self,
      Category.comp_id] at hm
    rw [M.infinity_eq] at hm
    have hm' := ConcreteCategory.congr_hom hm e
    change (cy.identification i).hom ((F.map g).eInftyMap i e) =
      Filtration.inducedAssocGradedMap M.comparison.aMap M.comparison.filtration_compat
        i.1 (i.2.1-i.1,i.2.2) ((cx.identification i).hom e) at hm'
    rw [hgr] at hm'
    have hg : (P.filtration X).toAssociatedGraded i.1 (i.2.1-i.1,i.2.2) ≫
        Filtration.inducedAssocGradedMap M.comparison.aMap M.comparison.filtration_compat
          i.1 (i.2.1-i.1,i.2.2) =
        hc.choose ≫ (P.filtration Y).toAssociatedGraded i.1 (i.2.1-i.1,i.2.2) := by
      exact cokernel.π_desc _ _ _
    exact hm'.trans (ConcreteCategory.congr_hom hg b)

private theorem first_quotient_familyPageMap_comp {Syn : Type u} [SyntheticCategory.{u,v} Syn]
    (F : SyntheticAdamsFamily Syn) {X Y Z : Syn} (f : X ⟶ Y) (g : Y ⟶ Z)
    (r : ℤ) (i : Tridegree) :
    F.pageMap (f ≫ g) r i = F.pageMap f r i ≫ F.pageMap g r i := by
  change (F.map (f ≫ g)).pageMap r i =
    (F.map f).pageMap r i ≫ (F.map g).pageMap r i
  rw [F.map_comp, SpectralSequenceMorphism.pageMap_comp]


variable {Syn : Type u} [SyntheticCategory.{u,v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  {H : Syn} {unit : S_0_0 ⟶ H} {F : SyntheticAdamsFamily Syn}
  {P : SyntheticTowerPresentation unit F} {X : Syn}

private theorem first_quotient_filtration_iff_of_infinity_zero (c : SyntheticTowerConvergence P X)
    (s t m w : ℤ) (hst : s ≤ t)
    (hz : ∀ j, s ≤ j → j < t → IsZero (((F.obj X).sequence.ssData (j,m+j,w)).eInfty))
    (a : BiHom m w X) : FiltrationAtLeast P s a ↔ FiltrationAtLeast P t a := by
  have hgraded (j : ℤ) (hj : s ≤ j) (hjt : j < t) :
      IsZero ((P.filtration X).associatedGraded j (m,w)) :=
    (hz j hj hjt).of_iso (towerGradedIso c (m,w) j).symm
  have he := (P.filtration X).eq_of_associatedGraded_isZero s t (m,w) hst hgraded
  have he' := congrArg (fun Q => a ∈ (ModuleCat.subobjectModule (syntheticHomotopy X (m,w))) Q) he
  simpa only [SyntheticTowerPresentation.filtration, OrderIso.apply_symm_apply,
    FiltrationAtLeast] using Iff.of_eq he'
private theorem first_quotient_filtration_map
    {Y : Syn} (f : X ⟶ Y) (s : ℤ) (p : ℤ × ℤ)
    (a : BiHom p.1 p.2 X) (ha : FiltrationAtLeast P s a) :
    FiltrationAtLeast P s (a ≫ f) := by
  obtain ⟨b,hb⟩ := ha
  refine ⟨b ≫ (P.map f).stage s.toNat,?_⟩
  change (b ≫ (P.map f).stage s.toNat) ≫ (P.tower Y).projection s = a ≫ f
  rw [Category.assoc,(P.map f).projection,←Category.assoc]
  exact congrArg (fun z => z ≫ f) hb

end Generic

private theorem first_quotient_finite_infinity_zero_outside (X : ClassicalObject) (q : ℕ) (hq : 0 < q)
    (s t w : ℤ) (hw : ¬ (0 ≤ t-w ∧ t-w < q)) :
    IsZero (((model.family.quotient (model.nu.functor.obj (X.obj model.auxiliary)) q).sequence.ssData
      (s,t,w)).eInfty) := by
  haveI : Subsingleton (KIP126.Literature.finiteEInftyModel model X q (s,t) w) := by
    simp only [KIP126.Literature.finiteEInftyModel, hw, ite_false]
    infer_instance
  haveI : Subsingleton (((model.family.quotient
      (model.nu.functor.obj (X.obj model.auxiliary)) q).sequence.ssData (s,t,w)).eInfty) :=
    (KIP126.Literature.Standard.eInfinity_finite X q hq (s,t) w).injective.subsingleton
  exact ModuleCat.isZero_of_subsingleton _

private theorem first_quotient_finite_high_filtration_zero (X : ClassicalObject) (q : ℕ) (hq : 0 < q)
    (m w s : ℤ) (hs : (q:ℤ) ≤ m+s-w)
    (a : BiHom m w (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
    (ha : FiltrationAtLeast model.syntheticTower s a) : a = 0 := by
  apply synthetic_homotopy_separated (.nu X) q m w a
  intro j
  by_cases hj : s ≤ (j:ℤ)
  · exact (first_quotient_filtration_iff_of_infinity_zero (model.convergence (.quotient q (.nu X)))
      s j m w hj (fun k hk _ => first_quotient_finite_infinity_zero_outside X q hq k (m+k) w (by omega)) a).mp ha
  · exact model.syntheticTower.filtrationSubmodule_antitone _ (m,w) (by omega) ha

/-- At the first quotient's upper filtration edge, the actual class is zero.
The quotient is taken after the given weight shift, exactly as in firstQuotient. -/
private theorem first_quotient_shifted_high_filtration_zero
    (Y : ClassicalObject) (a s t : ℤ)
    (d : BiHom (t-s) (t+a)
      (XModLambdaN ((SyntheticCategory.biShift (0,a)).obj
        (model.nu.functor.obj (Y.obj model.auxiliary))) 1))
    (hd : FiltrationAtLeast model.syntheticTower (s+1) d) : d = 0 := by
  letI := model.exactness.shiftCommShift (0,a)
  letI := model.exactness.shiftExact (0,a)
  let V := model.nu.functor.obj (Y.obj model.auxiliary)
  let A : SyntheticObject := .quotient 1 (.shift (0,a) (.nu Y))
  let B : SyntheticObject := .shift (0,a) (.quotient 1 (.nu Y))
  obtain ⟨e,_⟩ := finite_quotient_shift_comparison model.quotients.coherence
    (0,a) 1 V
  have hde : FiltrationAtLeast model.syntheticTower (s+1) (d ≫ e.hom) :=
    first_quotient_filtration_map e.hom (s+1) (t-s,t+a) d hd
  let E : FilteredPieceIso (model.convergence (.quotient 1 (.nu Y))).filtration
      (model.convergence B).filtration (t-s,t) (t-s,t+a) := by
    have hp : (t-s,t)+(0,a) = (t-s,t+a) := by ext <;> simp
    exact hp ▸ (essShift (0,a)).filtered (.quotient 1 (.nu Y)) (t-s,t)
  have hmem : d ≫ e.hom ∈ ModuleCat.subobjectModule _
      ((model.convergence B).filtration.F (s+1) (t-s,t+a)) := by
    simpa only [SyntheticTowerConvergence.filtration,SyntheticTowerPresentation.filtration,
      OrderIso.apply_symm_apply,FiltrationAtLeast,B,V,SyntheticObject.obj,
      syntheticHomotopy] using hde
  obtain ⟨b,hb⟩ := hmem
  have hcomm := ConcreteCategory.congr_hom (E.symm.level_arrow (s+1)) b
  simp only [ModuleCat.comp_apply,FilteredPieceIso.symm] at hcomm
  have hbase : FiltrationAtLeast model.syntheticTower (s+1)
      (E.ambient.inv (d ≫ e.hom)) := by
    have hbase' : E.ambient.inv (d ≫ e.hom) ∈ ModuleCat.subobjectModule _
        ((model.convergence (.quotient 1 (.nu Y))).filtration.F (s+1) (t-s,t)) := by
      refine ⟨(E.level (s+1)).inv b,?_⟩
      change ((model.convergence (.quotient 1 (.nu Y))).filtration.F
        (s+1) (t-s,t)).arrow ((E.level (s+1)).inv b) = E.ambient.inv (d ≫ e.hom)
      simpa only [hb,Iso.symm_hom] using hcomm
    simpa only [SyntheticTowerConvergence.filtration,SyntheticTowerPresentation.filtration,
      OrderIso.apply_symm_apply,FiltrationAtLeast] using hbase'
  have hzero := first_quotient_finite_high_filtration_zero Y 1 (by decide)
    (t-s) t (s+1) (by omega) (E.ambient.inv (d ≫ e.hom)) hbase
  have hdzero : d ≫ e.hom = 0 := by
    apply (ModuleCat.mono_iff_injective E.ambient.inv).mp inferInstance
    simpa only [map_zero] using hzero
  apply (cancel_mono e.hom).mp
  simpa only [zero_comp] using hdzero

private def first_quotient_nu_label
    (X : ClassicalObject) (a s t : ℤ)
    (x : (model.classical.obj (X.obj model.auxiliary)).Page 2 (s,t)) :
    (model.family.obj ((SyntheticCategory.biShift (0,a)).obj
      (model.nu.functor.obj (X.obj model.auxiliary)))).Page 2 (s,t,t+a) := by
  simpa only [Nat.cast_zero,sub_zero] using model.comparison.nuE2 X a s t 0 x

private theorem first_quotient_nu_label_natural
    (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary) (a s t : ℤ)
    (x : (model.classical.obj (X.obj model.auxiliary)).Page 2 (s,t)) :
    model.family.pageMap ((SyntheticCategory.biShift (0,a)).map
      (model.nu.functor.map f)) 2 (s,t,t+a) (first_quotient_nu_label X a s t x) =
      first_quotient_nu_label Y a s t
        ((model.classical.functor.map f).pageMap 2 (s,t) x) := by
  have regrade (w w' : ℤ) (hw : w=w')
      (g : ((SyntheticCategory.biShift (0,a)).obj
          (model.nu.functor.obj (X.obj model.auxiliary))) ⟶
        ((SyntheticCategory.biShift (0,a)).obj
          (model.nu.functor.obj (Y.obj model.auxiliary))))
      (b : (model.family.obj ((SyntheticCategory.biShift (0,a)).obj
        (model.nu.functor.obj (X.obj model.auxiliary)))).Page 2 (s,t,w))
      (c : (model.family.obj ((SyntheticCategory.biShift (0,a)).obj
        (model.nu.functor.obj (Y.obj model.auxiliary)))).Page 2 (s,t,w))
      (h : model.family.pageMap g 2 (s,t,w) b = c) :
      model.family.pageMap g 2 (s,t,w')
        (Eq.mp (congrArg (fun w => ↥((model.family.obj
          ((SyntheticCategory.biShift (0,a)).obj
            (model.nu.functor.obj (X.obj model.auxiliary)))).Page 2 (s,t,w))) hw) b) =
      Eq.mp (congrArg (fun w => ↥((model.family.obj
        ((SyntheticCategory.biShift (0,a)).obj
          (model.nu.functor.obj (Y.obj model.auxiliary)))).Page 2 (s,t,w))) hw) c := by
    subst w'
    exact h
  exact regrade (t+a-(0:ℕ)) (t+a) (by simp)
    _ _ _ (model.comparison.nu_natural X Y f a s t 0 x)

/-- Before finite-window vanishing, naturality already holds modulo precisely
one next filtration step, with the same x and the actual Q_1(nu f). -/
private theorem first_quotient_nu_naturality_next_filtration
    (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary) (a s t : ℤ)
    (x : (model.classical.obj (X.obj model.auxiliary)).Page 2 (s,t)) :
    FiltrationAtLeast model.syntheticTower (s+1)
      ((model.firstQuotient X a s t).symm x ≫
        XModLambdaN.map ((SyntheticCategory.biShift (0,a)).map (model.nu.functor.map f)) 1 -
      (model.firstQuotient Y a s t).symm
        ((model.classical.functor.map f).pageMap 2 (s,t) x)) := by
  let VX := (SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,a)).obj
    (model.nu.functor.obj (X.obj model.auxiliary))
  let VY := (SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,a)).obj
    (model.nu.functor.obj (Y.obj model.auxiliary))
  let g : VX ⟶ VY := (SyntheticCategory.biShift (0,a)).map (model.nu.functor.map f)
  let qg := XModLambdaN.map g 1
  let AX : SyntheticObject := .quotient 1 (.shift (0,a) (.nu X))
  let AY : SyntheticObject := .quotient 1 (.shift (0,a) (.nu Y))
  have hdX := model.comparisonCompatible.first_quotient X a s t x
  have hdY := model.comparisonCompatible.first_quotient Y a s t
    ((model.classical.functor.map f).pageMap 2 (s,t) x)
  have hdMap := first_quotient_detects_map (model.convergentMap AX AY qg) (s,t,t+a) hdX
  have hlabels : model.family.pageMap qg 2 (s,t,t+a)
      (model.family.pageMap (XModLambdaN.incl VX 1) 2 (s,t,t+a)
        (first_quotient_nu_label X a s t x)) =
    model.family.pageMap (XModLambdaN.incl VY 1) 2 (s,t,t+a)
      (first_quotient_nu_label Y a s t
        ((model.classical.functor.map f).pageMap 2 (s,t) x)) := by
    rw [←ModuleCat.comp_apply,←first_quotient_familyPageMap_comp,
      ←XModLambdaN.incl_naturality,first_quotient_familyPageMap_comp,ModuleCat.comp_apply]
    rw [first_quotient_nu_label_natural X Y f a s t x]
  have hdMap' : Detects (model.convergence AY) (s,t,t+a)
      (model.family.pageMap (XModLambdaN.incl VY 1) 2 (s,t,t+a)
        (first_quotient_nu_label Y a s t
          ((model.classical.functor.map f).pageMap 2 (s,t) x)))
      ((model.firstQuotient X a s t).symm x ≫ qg) := by
    rw [←hlabels]
    exact hdMap
  exact detects_sub_filtration (model.convergence AY) (s,t,t+a) hdMap' hdY

/-- Strict naturality of the specified first-quotient coordinates for actual
weight-shifted nu-images of classical maps. This is not an assertion about
positive-exponent normalized lifts. -/
private theorem first_quotient_nu_naturality
    (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary) (a s t : ℤ)
    (x : (model.classical.obj (X.obj model.auxiliary)).Page 2 (s,t)) :
    (model.firstQuotient X a s t).symm x ≫
        XModLambdaN.map ((SyntheticCategory.biShift (0,a)).map (model.nu.functor.map f)) 1 =
      (model.firstQuotient Y a s t).symm
        ((model.classical.functor.map f).pageMap 2 (s,t) x) := by
  apply sub_eq_zero.mp
  exact first_quotient_shifted_high_filtration_zero Y a s t _
    (first_quotient_nu_naturality_next_filtration X Y f a s t x)


/-- Zero positive lambda power is exactly the existing inverse zero shift.
This uses the unit coherence of the given bigraded action. -/
private theorem normalized_zero_positive_power (A : SyntheticSpectrum) :
    lambdaToPositivePow 0 A = SyntheticCategory.biShift_zero.inv.app A := by
  have hu := model.quotients.coherence.right_unit (0,0) A
  dsimp only [biShiftAddIso] at hu
  simp only [eqToIso_refl,Iso.trans_refl] at hu
  unfold lambdaToPositivePow
  norm_num only
  simp only [eqToHom_refl,Category.id_comp]
  change SyntheticCategory.biShift_zero.inv.app A ≫
    ((SyntheticCategory.biShift_comp (0,0) (0,0)).inv.app A ≫
      SyntheticCategory.biShift_zero.hom.app ((SyntheticCategory.biShift (0,0)).obj A)) = _
  erw [←hu,Iso.inv_hom_id_app,Category.comp_id]

private theorem normalized_zero_factorization_form {A B : SyntheticSpectrum} {k : ℕ}
    (hk : k=0) (M : (SyntheticCategory.biShift (0,(k:ℤ))).obj A ⟶ B)
    (g : A ⟶ B) (hM : lambdaToPositivePow k A ≫ M = g) :
    M = eqToHom (congrArg (fun j : ℕ =>
      (SyntheticCategory.biShift (0,(j:ℤ))).obj A) hk) ≫
        SyntheticCategory.biShift_zero.hom.app A ≫ g := by
  subst k
  rw [normalized_zero_positive_power] at hM
  have h := congrArg (fun z => SyntheticCategory.biShift_zero.hom.app A ≫ z) hM
  erw [←Category.assoc,Iso.hom_inv_id_app,Category.id_comp] at h
  simpa only [eqToHom_refl,Category.id_comp] using h

/-- The explicit source comparison to F_(0,0) nu X; its only transport is
exactly the given equality of the actual normalization exponent with zero. -/
private def normalized_zero_source_iso (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (h0 : normalizedExponent model.classicalTower f = 0) :
    (SyntheticCategory.biShift (0,(normalizedExponent model.classicalTower f:ℤ))).obj
        (model.nu.functor.obj (X.obj model.auxiliary)) ≅
      (SyntheticCategory.biShift (0,0)).obj
        (model.nu.functor.obj (X.obj model.auxiliary)) :=
  eqToIso (congrArg (fun k : ℕ => (SyntheticCategory.biShift (0,(k:ℤ))).obj
    (model.nu.functor.obj (X.obj model.auxiliary))) h0)

/-- A selected normalized map of exponent zero is strictly the nu-image
through the displayed source comparison and the existing zero-shift iso. -/
private theorem normalized_map_at_zero (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (h0 : normalizedExponent model.classicalTower f = 0) :
    (model.normalizedMap X Y f).map =
      (normalized_zero_source_iso X Y f h0).hom ≫
        SyntheticCategory.biShift_zero.hom.app _ ≫ model.nu.functor.map f := by
  exact normalized_zero_factorization_form h0 _ _ (model.normalizedMap X Y f).factorization

/-- The same first-quotient coordinates calibrate the actual selected
normalized map when its exponent is zero. The source class is transported
by the inverse of the explicit F_(0,0) comparison, through the actual Q_1. -/
private theorem first_quotient_normalized_map_at_zero
    (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (h0 : normalizedExponent model.classicalTower f = 0) (s t : ℤ)
    (x : (model.classical.obj (X.obj model.auxiliary)).Page 2 (s,t)) :
    (model.firstQuotient X 0 s t).symm x ≫
        XModLambdaN.map (normalized_zero_source_iso X Y f h0).inv 1 ≫
        XModLambdaN.map (model.normalizedMap X Y f).map 1 =
      (model.firstQuotient Y 0 s t).symm
          ((model.classical.functor.map f).pageMap 2 (s,t) x) ≫
        XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1 := by
  have hM := normalized_map_at_zero X Y f h0
  have hzero := SyntheticCategory.biShift_zero.hom.naturality (model.nu.functor.map f)
  dsimp only [Functor.id_map] at hzero
  calc
    _ = (model.firstQuotient X 0 s t).symm x ≫
        XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _ ≫
          model.nu.functor.map f) 1 := by
      rw [hM,model.quotients.functoriality.map_comp]
      rw [←Category.assoc (XModLambdaN.map _ _),
        ←model.quotients.functoriality.map_comp]
      simp only [Iso.inv_hom_id,model.quotients.functoriality.map_id,Category.id_comp]
    _ = (model.firstQuotient X 0 s t).symm x ≫
        XModLambdaN.map ((SyntheticCategory.biShift (0,0)).map (model.nu.functor.map f) ≫
          SyntheticCategory.biShift_zero.hom.app _) 1 := by rw [hzero]
    _ = ((model.firstQuotient X 0 s t).symm x ≫
        XModLambdaN.map ((SyntheticCategory.biShift (0,0)).map (model.nu.functor.map f)) 1) ≫
        XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1 := by
      rw [model.quotients.functoriality.map_comp,Category.assoc]
    _ = _ := by rw [first_quotient_nu_naturality X Y f 0 s t x]


/-- At exponent zero the negative-target version is the original map
followed by the explicit inverse zero shift and the same index transport. -/
private theorem normalized_negative_lift_at_zero {A B : SyntheticSpectrum} {k : ℕ}
    (h0 : k=0) (M : (SyntheticCategory.biShift (0,(k:ℤ))).obj A ⟶ B)
    (g : A ⟶ B) (hM : lambdaToPositivePow k A ≫ M = g) :
    negativeLift k M = g ≫ SyntheticCategory.biShift_zero.inv.app B ≫
      eqToHom (congrArg (fun j : ℕ =>
        (SyntheticCategory.biShift (0,-(j:ℤ))).obj B) h0).symm := by
  subst k
  simp only [eqToHom_refl,Category.comp_id]
  apply ((SyntheticCategory.biShift_zero.app B).eq_comp_inv).mpr
  have hnegative : negativeLift 0 M ≫ lambdaPow 0 B = lambdaToPositivePow 0 A ≫ M := by
    simp only [negativeLift,lambdaToPositivePow,Category.assoc]
    rw [lambdaPow_naturality]
  exact hnegative.trans hM


/-- Direct first-quotient calibration of the literal negative-target
normalized map of exponent zero. The target comparison to F_(0,0) is
explicit and retains the original dependent exponent transport. -/
private theorem first_quotient_normalized_negative_lift_at_zero
    (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (h0 : normalizedExponent model.classicalTower f = 0) (s t : ℤ)
    (x : (model.classical.obj (X.obj model.auxiliary)).Page 2 (s,t)) :
    let eNeg : (SyntheticCategory.biShift
          (0,-(normalizedExponent model.classicalTower f:ℤ))).obj
          (model.nu.functor.obj (Y.obj model.auxiliary)) ≅
        (SyntheticCategory.biShift (0,0)).obj
          (model.nu.functor.obj (Y.obj model.auxiliary)) :=
      eqToIso (congrArg (fun k : ℕ => (SyntheticCategory.biShift (0,-(k:ℤ))).obj
        (model.nu.functor.obj (Y.obj model.auxiliary))) h0)
    (model.firstQuotient X 0 s t).symm x ≫
        XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1 ≫
        XModLambdaN.map (negativeLift (normalizedExponent model.classicalTower f)
          (model.normalizedMap X Y f).map) 1 =
      (model.firstQuotient Y 0 s t).symm
          ((model.classical.functor.map f).pageMap 2 (s,t) x) ≫
        XModLambdaN.map eNeg.inv 1 := by
  dsimp only
  let eNeg : (SyntheticCategory.biShift
        (0,-(normalizedExponent model.classicalTower f:ℤ))).obj
        (model.nu.functor.obj (Y.obj model.auxiliary)) ≅
      (SyntheticCategory.biShift (0,0)).obj
        (model.nu.functor.obj (Y.obj model.auxiliary)) :=
    eqToIso (congrArg (fun k : ℕ => (SyntheticCategory.biShift (0,-(k:ℤ))).obj
      (model.nu.functor.obj (Y.obj model.auxiliary))) h0)
  have hneg := normalized_negative_lift_at_zero h0 (model.normalizedMap X Y f).map
    (model.nu.functor.map f) (model.normalizedMap X Y f).factorization
  have hzero := SyntheticCategory.biShift_zero.hom.naturality (model.nu.functor.map f)
  dsimp only [Functor.id_map] at hzero
  have hcomp : SyntheticCategory.biShift_zero.hom.app _ ≫
      negativeLift (normalizedExponent model.classicalTower f)
        (model.normalizedMap X Y f).map =
    (SyntheticCategory.biShift (0,0)).map (model.nu.functor.map f) ≫ eNeg.inv := by
    rw [hneg,←Category.assoc _ (model.nu.functor.map f),←hzero]
    simp only [Category.assoc,←Category.assoc (SyntheticCategory.biShift_zero.hom.app _),
      Iso.hom_inv_id_app,Category.id_comp]
    rfl
  calc
    _ = (model.firstQuotient X 0 s t).symm x ≫
        XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _ ≫
          negativeLift (normalizedExponent model.classicalTower f)
            (model.normalizedMap X Y f).map) 1 := by
      rw [model.quotients.functoriality.map_comp]
    _ = (model.firstQuotient X 0 s t).symm x ≫
        XModLambdaN.map ((SyntheticCategory.biShift (0,0)).map (model.nu.functor.map f) ≫
          eNeg.inv) 1 := by rw [hcomp]
    _ = ((model.firstQuotient X 0 s t).symm x ≫
        XModLambdaN.map ((SyntheticCategory.biShift (0,0)).map (model.nu.functor.map f)) 1) ≫
        XModLambdaN.map eNeg.inv 1 := by
      rw [model.quotients.functoriality.map_comp,Category.assoc]
    _ = _ := by rw [first_quotient_nu_naturality X Y f 0 s t x]

end
end KIP126.Literature.Standard
