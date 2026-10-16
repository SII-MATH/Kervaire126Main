module
import all KIP126.Def.ProofTools.GeneralizedLeibniz.CrossingFinite
import all KIP126.Def.ProofTools.GeneralizedLeibniz.CrossingLabels
import all KIP126.Def.ProofTools.GeneralizedLeibniz.DivisionLabels
import all KIP126.Def.ProofTools.GeneralizedLeibniz.RightEdge
import all KIP126.Def.ProofTools.GeneralizedMahowald.MinimalSource
import all KIP126.Def.ProofTools.GeneralizedMahowald.SuspensionDetection

@[expose] section
namespace KIP126.ProofTools.Internal.Leibniz
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Standard
open KIP126.ProofTools.Internal.Mahowald
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 200000
set_option Elab.async false

section General
universe u v
variable {Syn : Type u} [SyntheticCategory.{u,v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  {H : Syn} {unit : S_0_0 ⟶ H} {E : SyntheticAdamsFamily Syn}
  {P : SyntheticTowerPresentation unit E} {X Y : Syn} {g : X ⟶ Y}
  {cx : SyntheticTowerConvergence P X} {cy : SyntheticTowerConvergence P Y}

/-- Once higher-source crossings are excluded, a fixed nonzero target grade
makes every actual extension to that grade essential. -/
private theorem tower_essential_iff_target_nonzero_of_no_crossing
    (M : ConvergentMap E g cx.toConvergence cy.toConvergence)
    (p : ℤ × ℤ) (s n : ℤ)
    (x : ((E.obj X).sequence.ssData (s,p.1+s,p.2)).eInfty)
    (y : ((E.obj Y).sequence.ssData (s+n,p.1+(s+n),p.2)).eInfty)
    (he : TowerExtensionEquation M p s n x y)
    (hnc : TowerNoCrossing M p s n) :
    TowerEssentialExtension M p s n x y ↔ y ≠ 0 := by
  constructor
  · intro hess hy
    exact ((tower_essential_iff_no_zero M p s n x y he).mp hess) (by rwa [←hy])
  · intro hy
    apply (tower_essential_iff_no_zero M p s n x y he).mpr
    intro he0
    obtain ⟨hn,ar,br,hab,hax,hby⟩ := (tower_extension_iff M p s n x y).mp he
    obtain ⟨br0,hab0,hb0⟩ := tower_target_of_any_source_frame M p s n x 0 he0 hnc ar hax
    have hbr : br = br0 :=
      (ModuleCat.mono_iff_injective ((P.filtration Y).F (s+n) p).arrow).mp inferInstance
        (hab.symm.trans hab0)
    apply hy
    apply (infinityGradedIso cy p (s+n)).toLinearEquiv.injective
    change (infinityGradedIso cy p (s+n)).hom y =
      (infinityGradedIso cy p (s+n)).hom 0
    rw [←hby,←hb0,hbr]

end General

/-- At the normalization length, the finite ESS has no higher-source
indeterminacy, so essentiality is precisely a nonzero target grade. -/
private theorem minimal_length_finite_essential_iff_target_nonzero
    (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (q : ℕ) (hq : 0 < q) (s t : ℤ)
    (x : ((model.family.obj ((SyntheticObject.quotient q
      (extensionSourceObject model X Y f)).obj model.nu model.auxiliary)).sequence.ssData
      (s,(t-s)+s,t+normalizedExponent model.classicalTower f)).eInfty)
    (y : ((model.family.obj ((SyntheticObject.quotient q (.nu Y)).obj
      model.nu model.auxiliary)).sequence.ssData
      (s+normalizedExponent model.classicalTower f,
        (t-s)+(s+normalizedExponent model.classicalTower f),
        t+normalizedExponent model.classicalTower f)).eInfty)
    (he : TowerExtensionEquation (model.convergentMap
      (.quotient q (extensionSourceObject model X Y f)) (.quotient q (.nu Y))
      (finiteExtensionMap model X Y f q))
      (t-s,t+normalizedExponent model.classicalTower f)
      s (normalizedExponent model.classicalTower f) x y) :
    TowerEssentialExtension (model.convergentMap
      (.quotient q (extensionSourceObject model X Y f)) (.quotient q (.nu Y))
      (finiteExtensionMap model X Y f q))
      (t-s,t+normalizedExponent model.classicalTower f)
      s (normalizedExponent model.classicalTower f) x y ↔ y ≠ 0 := by
  exact tower_essential_iff_target_nonzero_of_no_crossing _ _ _ _ _ _ he
    (minimal_length_finite_tower_no_crossing X Y f q hq s t _ le_rfl)

/-- In the first nontrivial short position, the definition of a paper crossing
has exactly displacement one and no target setback. In particular its required
boundary exclusion is B₂, independently of the normalization exponent. -/
private theorem short_finite_has_crossing_iff
    (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (r : ℕ) (s t : ℤ) :
    FiniteHasCrossing model X Y f r
      ((normalizedExponent model.classicalTower f:ℤ)+1) s t ↔
    3 ≤ r ∧ ∃ (x : Ambient model X (s+1,t+1))
      (y : Ambient model Y
        (s+1+normalizedExponent model.classicalTower f,
          t+1+normalizedExponent model.classicalTower f)),
      ∃ W : FiniteExtensionWitness model X Y f (r-1)
        (normalizedExponent model.classicalTower f) (s+1) (t+1) x y,
        W.Essential ∧ y ∉ boundaries model Y 2
          (s+1+normalizedExponent model.classicalTower f,
            t+1+normalizedExponent model.classicalTower f) := by
  constructor
  · rintro ⟨a,b,ha,har,hb,H⟩
    have hlen : (normalizedExponent model.classicalTower f:ℤ) ≤
        (normalizedExponent model.classicalTower f:ℤ)+1-a-b := by
      obtain ⟨x,y,W,_,_⟩ := H
      exact W.length_lower
    have ha1 : a=1 := by omega
    have hb0 : b=0 := by omega
    subst a; subst b
    refine ⟨by omega,?_⟩
    have he : (normalizedExponent model.classicalTower f:ℤ)+1-(1:ℕ)-(0:ℕ) =
        normalizedExponent model.classicalTower f := by omega
    have hB : 1+((normalizedExponent model.classicalTower f:ℤ)+1)-(0:ℕ)-
        normalizedExponent model.classicalTower f=2 := by omega
    rw [he,hB] at H
    exact H
  · rintro ⟨hr,x,y,W,hess,hy⟩
    refine ⟨1,0,by omega,by omega,by omega,?_⟩
    have he : (normalizedExponent model.classicalTower f:ℤ)+1-(1:ℕ)-(0:ℕ) =
        normalizedExponent model.classicalTower f := by omega
    have hB : 1+((normalizedExponent model.classicalTower f:ℤ)+1)-(0:ℕ)-
        normalizedExponent model.classicalTower f=2 := by omega
    rw [he,hB]
    exact ⟨x,y,W,hess,hy⟩

/-- The kernel of restriction to the first quotient lies one source
filtration higher, including arbitrary vertical normalization shifts. -/
private theorem shifted_finite_first_kernel_filtration (X : ClassicalObject)
    (q : ℕ) (hq : 0 < q) (e s t : ℤ)
    (a : BiHom (t-s) (t+e)
      (XModLambdaN ((SyntheticCategory.biShift (0,e)).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) q))
    (ha : a ≫ (model.quotients.tower _).rho 1 q hq = 0) :
    FiltrationAtLeast model.syntheticTower (s+1) a := by
  let A := model.nu.functor.obj (X.obj model.auxiliary)
  by_cases hq1 : q=1
  · subst q
    have hz : a=0 := by
      simpa only [(model.quotients.tower _).rho_id,Category.comp_id] using ha
    rw [hz]
    exact Submodule.zero_mem _
  have h1q : 1<q := by omega
  let T := (model.quotients.tower ((SyntheticCategory.biShift (0,e)).obj A)).triangle
    (show 0<1 by decide) h1q
  have haz : a≫T.rho=0 := by
    simpa only [T,(model.quotients.tower _).triangle_rho] using ha
  obtain ⟨b,hb⟩ := (Triangle.mk T.lambdaMap T.rho T.delta).coyoneda_exact₂
    T.distinguished a haz
  change BiHom (t-s) (t+e) ((SyntheticCategory.biShift (0,-(1:ℤ))).obj
    (XModLambdaN ((SyntheticCategory.biShift (0,e)).obj A) (q-1))) at b
  change a = b≫T.lambdaMap at hb
  letI := model.exactness.shiftCommShift (0,e)
  letI := model.exactness.shiftExact (0,e)
  obtain ⟨ε,_,_⟩ := quotient_shift_exists model.quotients.coherence (0,e) (q-1) A
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(1:ℤ))
  let I : F.obj (XModLambdaN ((SyntheticCategory.biShift (0,e)).obj A) (q-1)) ≅
      (SyntheticCategory.biShift (0,e-1)).obj (XModLambdaN A (q-1)) :=
    F.mapIso ε ≪≫
      (SyntheticCategory.biShift_comp (0,e) (0,-(1:ℤ))).app _ ≪≫
      eqToIso (congrArg (fun p => (SyntheticCategory.biShift p).obj (XModLambdaN A (q-1)))
        (by ext <;> simp [sub_eq_add_neg]))
  have hbottom := shifted_quotient_bottom_filtration X (q-1) (by omega) (e-1)
    (t-s) (t+e) (b≫I.hom)
  have hbottom' : FiltrationAtLeast model.syntheticTower (s+1) (b≫I.hom) := by
    convert hbottom using 1; omega
  have hbf := map_preserves_filtration (model.convergentMap
    (.shift (0,e-1) (.quotient (q-1) (.nu X)))
    (.shift (0,-(1:ℤ)) (.quotient (q-1) (.shift (0,e) (.nu X)))) I.inv)
    (t-s,t+e) (s+1) (b≫I.hom) hbottom'
  have hbfil : FiltrationAtLeast model.syntheticTower (s+1) b := by
    change FiltrationAtLeast model.syntheticTower (s+1) ((b≫I.hom)≫I.inv) at hbf
    simpa only [FiltrationAtLeast,Category.assoc,Iso.hom_inv_id,Category.comp_id] using hbf
  have hmap := map_preserves_filtration (model.convergentMap
    (.shift (0,-(1:ℤ)) (.quotient (q-1) (.shift (0,e) (.nu X))))
    (.quotient q (.shift (0,e) (.nu X))) T.lambdaMap)
    (t-s,t+e) (s+1) b hbfil
  rwa [←hb] at hmap

/-- Conversely, the actual first-quotient equation and the original cycle
condition determine detection of the normalized finite source. -/
private theorem shifted_finite_source_detects_of_first
    (X : ClassicalObject) (q : ℕ) (hq : 0 < q) (e s t : ℤ)
    (x : Ambient model X (s,t)) (hx : x ∈ cycles model X q (s,t))
    (a : BiHom (t-s) (t+e)
      (XModLambdaN ((SyntheticCategory.biShift (0,e)).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) q))
    (ha : a≫(model.quotients.tower _).rho 1 q hq =
      (model.firstQuotient X e s t).symm x) :
    Detects (model.convergence (.quotient q (.shift (0,e) (.nu X))))
      (s,t,t+e) (regradeE2 (by simp) (finiteNuLabel model X q e s t 0 x)) a := by
  obtain ⟨v,hv⟩ := shifted_finite_source_exists X q hq e s t x hx
  have hv := representative_transport (show (s,t,t+e-(0:ℕ))=(s,t,t+e) by simp) _ _ hv
  let A := (SyntheticObject.quotient q (.shift (0,e) (.nu X))).obj model.nu model.auxiliary
  let F := model.syntheticTower.filtration A
  haveI : Epi (F.toAssociatedGraded s (t-s,t+e)) := inferInstanceAs (Epi (cokernel.π _))
  obtain ⟨ar,har⟩ := (ModuleCat.epi_iff_surjective (F.toAssociatedGraded s (t-s,t+e))).mp
    inferInstance (((model.convergence (.quotient q (.shift (0,e) (.nu X)))).identification
      (s,t,t+e)).hom _)
  let a0 : BiHom (t-s) (t+e) (XModLambdaN
      ((SyntheticCategory.biShift (0,e)).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) q) :=
    (F.F s (t-s,t+e)).arrow ar
  have ha0 : Detects (model.convergence (.quotient q (.shift (0,e) (.nu X))))
      (s,t,t+e) (regradeE2 (by simp) (finiteNuLabel model X q e s t 0 x)) a0 := by
    exact ⟨_,hv,ar,rfl,har.symm⟩
  have hfirst := shifted_finite_source_first X q hq e s t x a0 ha0
  have hd := shifted_finite_first_kernel_filtration X q hq e s t (a-a0) (by
    rw [Preadditive.sub_comp,ha,hfirst,sub_self])
  exact detects_of_high_difference (.quotient q (.shift (0,e) (.nu X)))
    (s,t,t+e) _ a0 a ha0 hd

/-- Every bottom-weight representative in a positively normalized finite
source has an actual classical cycle label, with no representative assumption. -/
private theorem positive_finite_source_label_exists
    (X : ClassicalObject) (q : ℕ) (hq : 0 < q) (s t : ℤ)
    (a : BiHom (t-s) (t+1)
      (XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) q)) :
    ∃ x : Ambient model X (s,t), x ∈ cycles model X q (s,t) ∧
      Detects (model.convergence (.quotient q (.shift (0,1) (.nu X))))
        (s,t,t+1) (regradeE2 (by simp) (finiteNuLabel model X q 1 s t 0 x)) a := by
  letI := model.exactness.shiftCommShift (0,1)
  letI := model.exactness.shiftExact (0,1)
  let A := model.nu.functor.obj (X.obj model.auxiliary)
  obtain ⟨ε₁,hε₁,_⟩ := quotient_shift_exists model.quotients.coherence (0,1) 1 A
  obtain ⟨εq,hεq,_⟩ := quotient_shift_exists model.quotients.coherence (0,1) q A
  let a0 := quotientUnshift X (0,1) (t-s,t) q εq (homotopyRegrade (by simp) rfl a)
  obtain ⟨x,hx⟩ := quotient_first_label_exists X q hq s t a0
  have hcycles := first_label_lift_cycles X q hq s t x a0 hx
  refine ⟨x,hcycles,shifted_finite_source_detects_of_first X q hq 1 s t x hcycles a ?_⟩
  have hunshift : quotientUnshift X (0,1) (t-s,t) 1 ε₁
      (homotopyRegrade (by simp) rfl (a≫(model.quotients.tower _).rho 1 q hq)) =
      quotientUnshift X (0,1) (t-s,t) 1 ε₁
        (homotopyRegrade (by simp) rfl ((model.firstQuotient X 1 s t).symm x)) := by
    rw [positive_first_desuspend X s t x ε₁ hε₁]
    rw [regrade_comp,←quotient_unshift_restriction X (0,1) (t-s,t) 1 q
      (by decide) hq ε₁ εq hε₁ hεq]
    exact hx
  have hh := congrArg (fun z => shiftHomotopyClass (0,1) (t-s,t) z≫ε₁.inv) hunshift
  simp only [shift_quotient_unshift] at hh
  have hinj : Function.Injective (homotopyRegrade
      (show t-s=((t-s,t)+(0,1)).1 by simp) (rfl : t+1=t+1)
      (X:=XModLambdaN ((SyntheticCategory.biShift (0,1)).obj A) 1)) := by
    intro a b hab
    have h := congrArg (homotopyRegrade (show ((t-s,t)+(0,1)).1=t-s by simp)
      (rfl : t+1=t+1)) hab
    simpa only [homotopy_regrade_inverse] using h
  exact hinj hh

private theorem zero_finite_source_label_exists
    (X : ClassicalObject) (q : ℕ) (hq : 0 < q) (s t : ℤ)
    (a : BiHom (t-s) (t+0)
      (XModLambdaN ((SyntheticCategory.biShift (0,0)).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) q)) :
    ∃ x : Ambient model X (s,t), x ∈ cycles model X q (s,t) ∧
      Detects (model.convergence (.quotient q (.shift (0,0) (.nu X))))
        (s,t,t+0) (regradeE2 (by simp) (finiteNuLabel model X q 0 s t 0 x)) a := by
  let x := (model.firstQuotient X 0 s t)
    (a≫(model.quotients.tower _).rho 1 q hq)
  have hfirst : a≫(model.quotients.tower _).rho 1 q hq =
      (model.firstQuotient X 0 s t).symm x :=
    ((model.firstQuotient X 0 s t).symm_apply_apply _).symm
  have hfirst0 : homotopyRegrade rfl (show t+0=t by simp) a≫
      (model.quotients.tower _).rho 1 q hq=firstLabel model X s t x := by
    have hh := congrArg (homotopyRegrade rfl (show t+0=t by simp)) hfirst
    rw [regrade_comp] at hh
    have hl : homotopyRegrade rfl (show t+0=t by simp)
        ((model.firstQuotient X 0 s t).symm x)=firstLabel model X s t x := by
      have cast (m w w' : ℤ) (h : w=w') (A : SyntheticSpectrum) (z : BiHom m w A) :
          homotopyRegrade rfl h z=(congrArg (fun v => BiHom m v A) h).mp z := by
        subst w'; rfl
      unfold firstLabel
      exact cast _ _ _ _ _ _
    exact hh.trans hl
  have hreach := (KIP126.Literature.Standard.bhs_finite_lift X q hq s t x).mpr
    ⟨homotopyRegrade rfl (by simp) a,hfirst0⟩
  have hcycle : x ∈ cycles model X q (s,t) := by
    have hh := ((isCycle_iff_reaches model X (q+1) (by omega) (s,t) x).mpr hreach).2
    simpa only [add_sub_cancel_right] using hh
  exact ⟨x,hcycle,shifted_finite_source_detects_of_first X q hq 0 s t x hcycle a hfirst⟩

/-- A normalized finite source has a classical bottom label. This consumes
only the existing normalization bound e≤1 and the fixed first-quotient
comparison; no no-crossing or survival assumption is added. -/
private theorem normalized_finite_source_label_exists
    (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (q : ℕ) (hq : 0 < q) (s t : ℤ)
    (a : BiHom (t-s) (t+normalizedExponent model.classicalTower f)
      (XModLambdaN ((extensionSourceObject model X Y f).obj model.nu model.auxiliary) q)) :
    ∃ x : Ambient model X (s,t), x ∈ cycles model X q (s,t) ∧
      Detects (model.convergence (.quotient q (extensionSourceObject model X Y f)))
        (s,t,t+normalizedExponent model.classicalTower f)
        (regradeE2 (by simp) (finiteNuLabel model X q
          (normalizedExponent model.classicalTower f) s t 0 x)) a := by
  have core (e : ℤ) (he : e=0 ∨ e=1)
      (a : BiHom (t-s) (t+e) (XModLambdaN ((SyntheticCategory.biShift (0,e)).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) q)) :
      ∃ x : Ambient model X (s,t), x ∈ cycles model X q (s,t) ∧
        Detects (model.convergence (.quotient q (.shift (0,e) (.nu X))))
          (s,t,t+e) (regradeE2 (by simp) (finiteNuLabel model X q e s t 0 x)) a := by
    rcases he with rfl | rfl
    · exact zero_finite_source_label_exists X q hq s t a
    · exact positive_finite_source_label_exists X q hq s t a
  exact core (normalizedExponent model.classicalTower f)
    (by have := normalizedExponent_le_one model.classicalTower f; omega) a

private theorem e2_regrade_trans {A : SyntheticAdamsSS} {i j k : Tridegree}
    (hij : i=j) (hjk : j=k) (z : A.E₂ i) :
    regradeE2 hjk (regradeE2 hij z)=regradeE2 (hij.trans hjk) z := by
  subst j; subst k; rfl

private theorem minimal_finite_witness_of_detected_source
    (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (q : ℕ) (hq : 0 < q) (s t : ℤ)
    (a : BiHom (t-s) (t+normalizedExponent model.classicalTower f)
      (XModLambdaN ((extensionSourceObject model X Y f).obj model.nu model.auxiliary) q))
    (x : Ambient model X (s,t)) (hx : x∈cycles model X q (s,t))
    (hax : Detects (model.convergence (.quotient q (extensionSourceObject model X Y f)))
      (s,t,t+normalizedExponent model.classicalTower f)
      (regradeE2 (by simp) (finiteNuLabel model X q
        (normalizedExponent model.classicalTower f) s t 0 x)) a) :
    ∃ (y : Ambient model Y (s+normalizedExponent model.classicalTower f,
        t+normalizedExponent model.classicalTower f)),
      ∃ _W : FiniteExtensionWitness model X Y f (q+1)
        (normalizedExponent model.classicalTower f) s t x y,
        Detects (model.convergence (.quotient q (extensionSourceObject model X Y f)))
          (s,t,t+normalizedExponent model.classicalTower f)
          (regradeE2 (by simp) (finiteNuLabel model X q
            (normalizedExponent model.classicalTower f) s t 0 x)) a ∧
        (homotopyRegrade
          (m' := (t+normalizedExponent model.classicalTower f)-(s+normalizedExponent model.classicalTower f))
          (w' := t+normalizedExponent model.classicalTower f)
          (by omega) rfl (a≫finiteExtensionMap model X Y f q))≫
            (model.quotients.tower _).rho 1 q hq =
          firstLabel model Y (s+normalizedExponent model.classicalTower f)
            (t+normalizedExponent model.classicalTower f) y≫
            XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1 := by
  let e : ℤ := normalizedExponent model.classicalTower f
  let b : BiHom ((t+e)-(s+e)) (t+e)
      (XModLambdaN (model.nu.functor.obj (Y.obj model.auxiliary)) q) :=
    homotopyRegrade (by omega) rfl (a≫finiteExtensionMap model X Y f q)
  obtain ⟨y,hy⟩ := quotient_first_label_exists Y q hq (s+e) (t+e) b
  have hycycle := first_label_lift_cycles Y q hq (s+e) (t+e) y b hy
  have hby := first_label_detects_unshifted Y q hq (s+e) (t+e) y b hy
  have hsource' : Detects (model.convergence (.quotient q (extensionSourceObject model X Y f)))
      (s,(t-s)+s,t+e) (finiteSourceForExtension model X Y f q s t x)
      (homotopyRegrade (by dsimp; omega) rfl a) :=
    source_detects_reindex X q e s t x a hax
  have htarget := detects_transport
    (show (s+e,t+e,t+e)=(s+e,(t-s)+(s+e),t+e) by ext <;> (dsimp; all_goals omega)) _ _ hby
  have label_eq : finiteTargetForExtension model X Y f q e s t le_rfl y =
      regradeE2 (show (s+e,t+e,t+e)=(s+e,(t-s)+(s+e),t+e) by ext <;> (dsimp; all_goals omega))
        (regradeE2 (by simp) (finiteTargetLabel model Y q (s+e) (t+e) 0 y)) := by
    unfold finiteTargetForExtension
    rw [e2_regrade_trans]
    have labels (k k' : ℕ) (hk : k=k') (p : Tridegree)
        (h₁ : (s+e,t+e,t+e-k)=p) (h₂ : (s+e,t+e,t+e-k')=p) :
        regradeE2 h₁ (finiteTargetLabel model Y q (s+e) (t+e) k y)=
          regradeE2 h₂ (finiteTargetLabel model Y q (s+e) (t+e) k' y) := by
      subst k'; rfl
    exact labels _ _ (by dsimp [e]; omega) _ _ _
  have htarget' : Detects (model.convergence (.quotient q (.nu Y)))
      (s+e,(t-s)+(s+e),t+e)
      (finiteTargetForExtension model X Y f q e s t le_rfl y)
      (homotopyRegrade (by dsimp; omega) rfl (a≫finiteExtensionMap model X Y f q)) := by
    rw [label_eq]
    dsimp only [b] at htarget
    have comp {U : SyntheticSpectrum} {u v z w : ℤ}
        (huv : u=v) (hvz : v=z) (a : BiHom u w U) :
        homotopyRegrade hvz rfl (homotopyRegrade huv rfl a)=
          homotopyRegrade (huv.trans hvz) rfl a := by
      subst v; subst z; rfl
    rw [comp] at htarget
    exact htarget
  obtain ⟨xx,yy,hxx,hyy,heq⟩ := extension_equation_of_detected_pair
    (model.convergentMap (.quotient q (extensionSourceObject model X Y f))
      (.quotient q (.nu Y)) (finiteExtensionMap model X Y f q))
      (t-s,t+e) s e (by dsimp [e]; omega) _ _ a
      (a≫finiteExtensionMap model X Y f q) hsource' htarget' rfl
  have hxreach : ReachesPage (model.classical.obj (X.obj model.auxiliary)) (q+1:ℕ) (s,t) x :=
    (isCycle_iff_reaches model X (q+1:ℕ) (by omega) (s,t) x).mp
      ⟨by omega,by simpa only [Nat.cast_add,Nat.cast_one,add_sub_cancel_right] using hx⟩
  have hyreach : ReachesPage (model.classical.obj (Y.obj model.auxiliary)) (q+1:ℕ) (s+e,t+e) y :=
    (isCycle_iff_reaches model Y (q+1:ℕ) (by omega) (s+e,t+e) y).mp
      ⟨by omega,by simpa only [Nat.cast_add,Nat.cast_one,add_sub_cancel_right] using hycycle⟩
  have hyreach' : ReachesPage (model.classical.obj (Y.obj model.auxiliary))
      ((q+1:ℕ)-e+normalizedExponent model.classicalTower f) (s+e,t+e) y := by
    have hpage : (q+1:ℕ)=((q+1:ℕ)-e+normalizedExponent model.classicalTower f : ℤ) := by
      dsimp [e]; omega
    exact hpage ▸ hyreach
  refine ⟨y,?_,hax,hy⟩
  exact {
    page_ge_two := by omega
    length_lower := le_rfl
    length_upper := by omega
    source_cycle := hxreach
    target_cycle := hyreach'
    source := xx
    target := yy
    source_rep := hxx
    target_rep := hyy
    equation := heq }

private theorem minimal_finite_witness_of_source
    (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (q : ℕ) (hq : 0 < q) (s t : ℤ)
    (a : BiHom (t-s) (t+normalizedExponent model.classicalTower f)
      (XModLambdaN ((extensionSourceObject model X Y f).obj model.nu model.auxiliary) q)) :
    ∃ (x : Ambient model X (s,t))
      (y : Ambient model Y (s+normalizedExponent model.classicalTower f,
        t+normalizedExponent model.classicalTower f)),
      ∃ _W : FiniteExtensionWitness model X Y f (q+1)
        (normalizedExponent model.classicalTower f) s t x y,
        Detects (model.convergence (.quotient q (extensionSourceObject model X Y f)))
          (s,t,t+normalizedExponent model.classicalTower f)
          (regradeE2 (by simp) (finiteNuLabel model X q
            (normalizedExponent model.classicalTower f) s t 0 x)) a ∧
        (homotopyRegrade
          (m' := (t+normalizedExponent model.classicalTower f)-(s+normalizedExponent model.classicalTower f))
          (w' := t+normalizedExponent model.classicalTower f)
          (by omega) rfl (a≫finiteExtensionMap model X Y f q))≫
            (model.quotients.tower _).rho 1 q hq =
          firstLabel model Y (s+normalizedExponent model.classicalTower f)
            (t+normalizedExponent model.classicalTower f) y≫
            XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1 := by
  obtain ⟨x,hx,hax⟩ := normalized_finite_source_label_exists X Y f q hq s t a
  obtain ⟨y,W,hs,hfirst⟩ := minimal_finite_witness_of_detected_source X Y f q hq s t a x hx hax
  exact ⟨x,y,W,hs,hfirst⟩

private theorem finite_lambda_target_not_boundary
    (X : ClassicalObject) (q : ℕ) (hq : 1<q) (s t : ℤ)
    (x : Ambient model X (s,t))
    (b : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (q-1)))
    (hb : b≫(model.quotients.tower _).rho 1 (q-1) (by omega)=
      firstLabel model X s t x≫XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1)
    (hnot : ¬FiltrationAtLeast model.syntheticTower (s+1)
      (finiteLambdaClass X q 1 (by decide) hq s t b)) :
    x ∉ boundaries model X 2 (s,t) := by
  intro hxB
  have hx := first_label_lift_cycles X (q-1) (by omega) s t x b hb
  have hx' : x∈cycles model X ((q:ℤ)-t+(t-(1:ℕ))) (s,t) := by
    convert hx using 1; congr 1; omega
  have h0 : HasInfinityRepresentative _ 2 (s,t,t-(1:ℕ))
      (finiteTargetLabel model X q s t 1 x) 0 := by
    apply (finite_target_label_iff X q (by omega) s t 1 hq ⟨x,hx'⟩ 0).mpr
    rw [map_zero]
    symm
    apply (CrossingLabels.subquotient_zero_iff _ _ _).mpr
    convert hxB using 1; congr 1; omega
  exact hnot (detects_zero_infinity_filtration (model.convergence (.quotient q (.nu X)))
    (s,t,t-(1:ℕ)) (finite_quotient_lambda_detects X q 1 (by decide) hq s t x b hb) h0)

private theorem minimal_finite_witness_essential_of_target_not_boundary
    (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (r : ℕ) (s t : ℤ) (x : Ambient model X (s,t))
    (y : Ambient model Y (s+normalizedExponent model.classicalTower f,
      t+normalizedExponent model.classicalTower f))
    (W : FiniteExtensionWitness model X Y f r
      (normalizedExponent model.classicalTower f) s t x y)
    (hy : y∉boundaries model Y 2
      (s+normalizedExponent model.classicalTower f,t+normalizedExponent model.classicalTower f)) :
    W.Essential := by
  let e : ℤ := normalizedExponent model.classicalTower f
  have hq : 0<r-1 := by have := W.page_ge_two; omega
  apply (minimal_length_finite_essential_iff_target_nonzero X Y f (r-1) hq
    s t W.source W.target W.equation).mpr
  intro hz
  have hrep := representative_transport
    (show (s+e,(t-s)+(s+e),t+e)=(s+e,t+e,t+e) by ext <;> (dsimp; all_goals omega))
    _ _ W.target_rep
  rw [finite_extension_target_weight_label] at hrep
  have hlabel := (KIP126.Literature.Standard.eInfinity_finite_labels Y (r-1) hq
    (s+e) (t+e) (t+e) (by omega) y _).mp hrep
  have hB1 : y∈boundaries model Y 1 (s+e,t+e) := by
    have heq := hlabel.2
    simp only [hz,map_zero] at heq
    have hB := (CrossingLabels.subquotient_zero_iff _ _ ⟨y,hlabel.1⟩).mp heq.symm
    convert hB using 1; congr 1; omega
  exact hy (boundaries_monotone model Y (s+e,t+e) (by omega : (1:ℤ)≤2) hB1)

/-- An actual divided source whose one-lambda image has a nonzero target
grade produces the precise paper crossing, including essentiality and B₂. -/
private theorem short_crossing_of_lambda_target_not_high
    (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (q : ℕ) (hq : 1<q) (s t : ℤ)
    (b : BiHom ((t+1)-(s+1)) ((t+1)+normalizedExponent model.classicalTower f)
      (XModLambdaN ((extensionSourceObject model X Y f).obj model.nu model.auxiliary) (q-1)))
    (hnot : ¬FiltrationAtLeast model.syntheticTower
      (s+1+normalizedExponent model.classicalTower f+1)
      (finiteLambdaClass Y q 1 (by decide) hq
        (s+1+normalizedExponent model.classicalTower f)
        (t+1+normalizedExponent model.classicalTower f)
        (homotopyRegrade
          (m' := (t+1+normalizedExponent model.classicalTower f)-
            (s+1+normalizedExponent model.classicalTower f))
          (w' := t+1+normalizedExponent model.classicalTower f)
          (by omega) rfl (b≫finiteExtensionMap model X Y f (q-1))))) :
    FiniteHasCrossing model X Y f (q+1)
      ((normalizedExponent model.classicalTower f:ℤ)+1) s t := by
  obtain ⟨x,y,W,_,hfirst⟩ := minimal_finite_witness_of_source X Y f (q-1) (by omega)
    (s+1) (t+1) b
  have hy := finite_lambda_target_not_boundary Y q hq
    (s+1+normalizedExponent model.classicalTower f)
    (t+1+normalizedExponent model.classicalTower f) y _ hfirst hnot
  have hess := minimal_finite_witness_essential_of_target_not_boundary X Y f
    (q-1+1) (s+1) (t+1) x y W hy
  apply (short_finite_has_crossing_iff X Y f (q+1) s t).mpr
  refine ⟨by omega,x,y,?_⟩
  have H : ∃ W : FiniteExtensionWitness model X Y f (q-1+1)
      (normalizedExponent model.classicalTower f) (s+1) (t+1) x y,
      W.Essential ∧ y∉boundaries model Y 2
        (s+1+normalizedExponent model.classicalTower f,t+1+normalizedExponent model.classicalTower f) :=
    ⟨W,hess,hy⟩
  have heq : q-1+1=q := by omega
  rw [heq] at H
  rw [show q+1-1=q by omega]
  exact H

private theorem homotopy_regrade_comp {A : SyntheticSpectrum} {m m' m'' w w' w'' : ℤ}
    (hm : m=m') (hw : w=w') (hm' : m'=m'') (hw' : w'=w'') (a : BiHom m w A) :
    homotopyRegrade hm' hw' (homotopyRegrade hm hw a)=
      homotopyRegrade (hm.trans hm') (hw.trans hw') a := by
  subst m'; subst m''; subst w'; subst w''; rfl

private theorem vertical_shift_regrade (A : SyntheticSpectrum) (i : ℕ)
    (m m' w w' : ℤ) (hm : m=m') (hw : w=w') (a : BiHom m (w+i) A) :
    verticalShiftEquiv A i m' w'
        (homotopyRegrade hm (congrArg (fun z : ℤ => z+i) hw) a)=
      homotopyRegrade hm hw (verticalShiftEquiv A i m w a) := by
  subst m'; subst w'; rfl

/-- In the first short length, every essential actual-tower crossing gives
the paper's shorter finite crossing. Lambda is not cancelled through a
filtration: its nonzero target grade supplies the exact B₂ exclusion. -/
private theorem short_finite_noCrossing_tower
    (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (q : ℕ) (hq : 0<q) (s t n : ℤ)
    (hn : n ≤ (normalizedExponent model.classicalTower f:ℤ)+1)
    (hnc : FiniteNoCrossing model X Y f (q+1) n s t) :
    TowerNoCrossing (model.convergentMap
      (.quotient q (extensionSourceObject model X Y f)) (.quotient q (.nu Y))
      (finiteExtensionMap model X Y f q))
      (t-s,t+normalizedExponent model.classicalTower f) s n := by
  intro u v hsu huv hvs x y hess
  have hposition := short_finite_crossing_position X Y f q hq s t n u v hn hsu huv hvs x y hess
  rcases hposition with ⟨hu,hv,hnEq⟩
  subst u; subst v; subst n
  have h1q : 1<q := by
    have H := finite_crossing_source_bound X Y f q hq s t (s+1)
      (s+normalizedExponent model.classicalTower f+1) huv x y hess
    omega
  let e : ℤ := normalizedExponent model.classicalTower f
  let A := (extensionSourceObject model X Y f).obj model.nu model.auxiliary
  let B := model.nu.functor.obj (Y.obj model.auxiliary)
  let p := (t-s,t+e)
  let M := model.convergentMap (.quotient q (extensionSourceObject model X Y f))
    (.quotient q (.nu Y)) (finiteExtensionMap model X Y f q)
  have hrel : TowerExtensionEquation M p (s+1)
      ((s+e+1)-(s+1)) x y := hess.1
  obtain ⟨_,ar,br,hab,hax,hby⟩ := (tower_extension_iff M p (s+1)
    ((s+e+1)-(s+1)) x y).mp hrel
  let a : BiHom (t-s) (t+e) (XModLambdaN A q) :=
    ((model.syntheticTower.filtration (XModLambdaN A q)).F (s+1) p).arrow ar
  have ha : FiltrationAtLeast model.syntheticTower (s+1) a := by
    have H : a∈ModuleCat.subobjectModule _
      ((model.syntheticTower.filtration (XModLambdaN A q)).F (s+1) p) := ⟨ar,rfl⟩
    simpa only [SyntheticTowerPresentation.filtration,OrderIso.apply_symm_apply,FiltrationAtLeast] using H
  have hnot : ¬FiltrationAtLeast model.syntheticTower (s+e+1+1)
      (a≫finiteExtensionMap model X Y f q) := by
    intro hhigh
    have hzero : y=0 := by
      apply (infinityGradedIso (model.convergence (.quotient q (.nu Y)))
        p ((s+1)+((s+e+1)-(s+1)))).toLinearEquiv.injective
      change (infinityGradedIso (model.convergence (.quotient q (.nu Y)))
          p ((s+1)+((s+e+1)-(s+1)))).hom y =
        (infinityGradedIso (model.convergence (.quotient q (.nu Y)))
          p ((s+1)+((s+e+1)-(s+1)))).hom 0
      rw [←hby,map_zero]
      apply ((model.syntheticTower.filtration
        ((SyntheticObject.quotient q (.nu Y)).obj model.nu model.auxiliary)).toAssociatedGraded_eq_zero_iff
        ((s+1)+((s+e+1)-(s+1))) p br).mpr
      rw [←hab]
      have hhigh' : FiltrationAtLeast model.syntheticTower
          ((s+1)+((s+e+1)-(s+1))+1) (a≫finiteExtensionMap model X Y f q) := by
        convert hhigh using 1; omega
      simpa only [a,p,A,B,extensionSourceObject,SyntheticObject.obj,
        SyntheticTowerPresentation.filtration,OrderIso.apply_symm_apply,FiltrationAtLeast]
        using hhigh'
    exact ((tower_essential_iff_no_zero M p (s+1) ((s+e+1)-(s+1)) x y hrel).mp hess)
      (by rwa [←hzero])
  obtain ⟨bS,hbS⟩ := normalized_finite_source_division X e 1 q (by decide) h1q
    (t-s) (t+e) (s+1) (by omega) a ha
  let E := verticalShiftEquiv (XModLambdaN A (q-1)) 1 (t-s) (t+e)
  let b0 := E.symm bS
  let b : BiHom ((t+1)-(s+1)) ((t+1)+e) (XModLambdaN A (q-1)) :=
    homotopyRegrade (by omega) (by omega) b0
  let c0 := b0≫finiteExtensionMap model X Y f (q-1)
  let c : BiHom ((t+1+e)-(s+1+e)) (t+1+e) (XModLambdaN B (q-1)) :=
    homotopyRegrade (by omega) rfl (b≫finiteExtensionMap model X Y f (q-1))
  have hcomm := (model.quotients.natural (model.normalizedMap X Y f).map).lambda_naturality
    (show 0<1 by decide) h1q
  change (SyntheticCategory.biShift (0,-(1:ℤ))).map (finiteExtensionMap model X Y f (q-1))≫
      ((model.quotients.tower B).triangle (show 0<1 by decide) h1q).lambdaMap =
    ((model.quotients.tower A).triangle (show 0<1 by decide) h1q).lambdaMap≫
      finiteExtensionMap model X Y f q at hcomm
  have hactual : verticalShiftEquiv (XModLambdaN B (q-1)) 1 (t-s) (t+e) c0≫
      ((model.quotients.tower B).triangle (show 0<1 by decide) h1q).lambdaMap =
      a≫finiteExtensionMap model X Y f q := by
    let LA := ((model.quotients.tower A).triangle (show 0<1 by decide) h1q).lambdaMap
    let LB := ((model.quotients.tower B).triangle (show 0<1 by decide) h1q).lambdaMap
    let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(1:ℤ))
    have hcomm' : F.map (finiteExtensionMap model X Y f (q-1))≫LB =
        LA≫finiteExtensionMap model X Y f q := hcomm
    have hm := congrArg (fun z =>
      verticalShiftEquiv (XModLambdaN A (q-1)) 1 (t-s) (t+e) b0≫z) hcomm'
    have hm' : (verticalShiftEquiv (XModLambdaN A (q-1)) 1 (t-s) (t+e) b0≫
        F.map (finiteExtensionMap model X Y f (q-1)))≫LB =
      (verticalShiftEquiv (XModLambdaN A (q-1)) 1 (t-s) (t+e) b0≫LA)≫
        finiteExtensionMap model X Y f q := by
      simpa only [Category.assoc] using hm
    have hbSame : bS≫LA=a := hbS
    calc
      _ = (verticalShiftEquiv (XModLambdaN A (q-1)) 1 (t-s) (t+e) b0≫
          F.map (finiteExtensionMap model X Y f (q-1)))≫LB :=
        congrArg (fun z => z≫LB) (vertical_shift_comp (XModLambdaN A (q-1))
          (XModLambdaN B (q-1)) (finiteExtensionMap model X Y f (q-1))
          1 (t-s) (t+e) b0).symm
      _ = (verticalShiftEquiv (XModLambdaN A (q-1)) 1 (t-s) (t+e) b0≫LA)≫
          finiteExtensionMap model X Y f q := hm'
      _ = a≫finiteExtensionMap model X Y f q :=
        (congrArg (fun z => (z≫LA)≫finiteExtensionMap model X Y f q)
          (E.apply_symm_apply bS)).trans
          (congrArg (fun z => z≫finiteExtensionMap model X Y f q) hbSame)
  have hclass : finiteLambdaClass Y q 1 (by decide) h1q (s+1+e) (t+1+e) c =
      homotopyRegrade (m' := (t+1+e)-(s+1+e)) (w' := (t+1+e)-(1:ℕ))
        (by omega) (by omega) (a≫finiteExtensionMap model X Y f q) := by
    rw [finiteLambdaClass_vertical]
    dsimp only [c,b,A,B]
    rw [regrade_comp,homotopy_regrade_comp,←regrade_comp,homotopy_regrade_comp]
    change verticalShiftEquiv (XModLambdaN B (q-1)) 1
        ((t+1+e)-(s+1+e)) ((t+1+e)-(1:ℕ))
        (homotopyRegrade (show t-s=(t+1+e)-(s+1+e) by omega)
          (congrArg (fun z : ℤ => z+(1:ℕ)) (show t+e=(t+1+e)-(1:ℕ) by omega)) c0)≫
        ((model.quotients.tower B).triangle (show 0<1 by decide) h1q).lambdaMap = _
    rw [vertical_shift_regrade,←regrade_comp,hactual]
  apply hnc
  apply short_crossing_of_lambda_target_not_high X Y f q h1q s t b
  intro hhigh
  change FiltrationAtLeast model.syntheticTower (s+1+e+1)
    (finiteLambdaClass Y q 1 (by decide) h1q (s+1+e) (t+1+e) c) at hhigh
  rw [hclass] at hhigh
  apply hnot
  have H := (regrade_filtration_iff _ _ (s+1+e+1) (a≫finiteExtensionMap model X Y f q)).mp hhigh
  convert H using 1; omega

private theorem source_detects_native (X : ClassicalObject) (q : ℕ) (e s t : ℤ)
    (x : Ambient model X (s,t))
    (a : BiHom (t-s) (t+e) (XModLambdaN ((SyntheticCategory.biShift (0,e)).obj
      (model.nu.functor.obj (X.obj model.auxiliary))) q))
    (ha : Detects (model.convergence (.quotient q (.shift (0,e) (.nu X))))
      (s,(t-s)+s,t+e) (regradeE2 (by simp) (finiteNuLabel model X q e s t 0 x))
      (homotopyRegrade (by dsimp; omega) rfl a)) :
    Detects (model.convergence (.quotient q (.shift (0,e) (.nu X))))
      (s,t,t+e) (regradeE2 (by simp) (finiteNuLabel model X q e s t 0 x)) a := by
  have H := detects_transport (show (s,(t-s)+s,t+e)=(s,t,t+e) by simp) _ _ ha
  rw [e2_regrade_trans,homotopy_regrade_comp] at H
  exact H

/-- The complete first-short-length synchronization needed by MH2. The
specified target belongs to the original W, and the actual source remains aZ. -/
private theorem finite_extension_at_source_short
    (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (r : ℕ) (n s t : ℤ) (x : Ambient model X (s,t)) (y : Ambient model Y (s+n,t+n))
    (W : FiniteExtensionWitness model X Y f r n s t x y)
    (hn : n≤(normalizedExponent model.classicalTower f:ℤ)+1)
    (hnc : FiniteNoCrossing model X Y f r n s t)
    (aZ : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (r-1)))
    (haZ : Detects (model.convergence (.quotient (r-1) (.nu X))) (s,t,t)
      (regradeE2 (by simp) (finiteTargetLabel model X (r-1) s t 0 x)) aZ) :
    FiniteExtensionAtSource X Y f r n s t x y W aZ := by
  let q : ℕ := r-1
  let e : ℤ := normalizedExponent model.classicalTower f
  have hq : 0<q := by dsimp [q]; have := W.page_ge_two; omega
  have hpage : q+1=r := by dsimp [q]; have := W.page_ge_two; omega
  have hFinite : FiniteNoCrossing model X Y f (q+1) n s t := by
    simpa only [hpage] using hnc
  have hTower := short_finite_noCrossing_tower X Y f q hq s t n hn hFinite
  let p := (t-s,t+e)
  obtain ⟨_,ar,br,hab,hax,hby⟩ := (tower_extension_iff _ p s n W.source W.target).mp W.equation
  let ah : BiHom (t-s) (t+e)
      ((SyntheticObject.quotient q (extensionSourceObject model X Y f)).obj model.nu model.auxiliary) :=
    ((model.syntheticTower.filtration
      ((SyntheticObject.quotient q (extensionSourceObject model X Y f)).obj model.nu model.auxiliary)).F s p).arrow ar
  have hs := source_frame_detects (model.convergence (.quotient q (extensionSourceObject model X Y f)))
    p s W.source _ W.source_rep ar hax
  have hsNative := source_detects_native X q e s t x ah hs
  have hx : x∈cycles model X q (s,t) := by
    have H := ((isCycle_iff_reaches model X r (by have := W.page_ge_two; omega) (s,t) x).mpr
      W.source_cycle).2
    have hlevel : (q:ℤ)=(r:ℤ)-1 := by dsimp [q]; have := W.page_ge_two; omega
    rw [hlevel]
    exact H
  obtain ⟨y0,Wmin,_,_⟩ := minimal_finite_witness_of_detected_source X Y f q hq s t ah x hx hsNative
  obtain ⟨ahNew,hsNew,_,huNew⟩ := finite_extension_at_source_minimal X Y f (q+1)
    e s t x y0 Wmin le_rfl aZ haZ
  exact extension_at_source_of_normalized_source X Y f r n s t x y W aZ ahNew hsNew huNew hTower

end
end KIP126.ProofTools.Internal.Leibniz
