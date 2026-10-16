module
import all KIP126.ProofTools.GeneralizedMahowald.SphereMayCorrection
import KIP126.Literature.Standard

@[expose] section
namespace KIP126.ProofTools.Internal.Mahowald
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard KIP126.Literature
open KIP126.Literature.Standard
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2000000

private theorem sphere_shifted_nu_high_target_map_zero
    (Y X : ClassicalObject) (n w₀ : ℤ) (δ ε : ℤ×ℤ) (r : ℕ) (hr : 0<r)
    (hgap : (r:ℤ)≤δ.1-δ.2-(ε.1-ε.2))
    (eY : model.nu.functor.obj (Y.obj model.auxiliary) ≅ Smn n w₀)
    (d : (SyntheticCategory.biShift δ).obj
        (model.nu.functor.obj (Y.obj model.auxiliary)) ⟶
      (SyntheticCategory.biShift ε).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) r)) : d=0 := by
  let e : (SyntheticCategory.biShift δ).obj
      (model.nu.functor.obj (Y.obj model.auxiliary)) ≅ Smn (n+δ.1) (w₀+δ.2) :=
    (SyntheticCategory.biShift δ).mapIso eY ≪≫
      (SyntheticCategory.biShift_comp (n,w₀) δ).app S_0_0 ≪≫
      eqToIso (by cases δ; rfl)
  apply (cancel_epi e.inv).mp
  simpa only [comp_zero] using shifted_nu_to_shifted_finite_no_return Y X r hr δ ε
    hgap (n+δ.1) (w₀+δ.2) e.inv d

private theorem shifted_nuCofiber_high_target_map_zero
    (X : ClassicalObject) (δ ε : ℤ×ℤ) (r : ℕ) (hr : 0<r)
    (hgap : (r:ℤ)≤δ.1-δ.2-(ε.1-ε.2))
    (d : (SyntheticCategory.biShift δ).obj
        (model.nu.functor.obj (ClassicalObject.nuCofiber.obj model.auxiliary)) ⟶
      (SyntheticCategory.biShift ε).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) r)) : d=0 := by
  let T := normalizedTriangle model model.auxiliary.nuRouteTriangle nuCofiber_exponent_sum
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) δ
  letI := model.exactness.shiftCommShift δ
  letI := model.exactness.shiftExact δ
  let U := F.mapTriangle.obj T
  have hU : U ∈ distTriang SyntheticSpectrum := F.map_distinguished T nuCofiber_distinguished
  let V := model.nu.functor.obj (ClassicalObject.nuCofiber.obj model.auxiliary)
  let W := model.nu.functor.obj ((ClassicalObject.shift 3 .sphere).obj model.auxiliary)
  let e₃ : U.obj₃ ≅ F.obj V := by
    change F.obj ((SyntheticCategory.biShift
      (0,-(normalizedExponent model.classicalTower model.auxiliary.nuRouteTriangle.g:ℤ))).obj V) ≅ _
    rw [nuCofiber_bottom_exponent]
    exact F.mapIso (SyntheticCategory.biShift_zero.app V)
  let dT : U.obj₃ ⟶ _ := e₃.hom ≫ d
  have hbottom : U.mor₂ ≫ dT=0 := by
    exact sphere_shifted_nu_high_target_map_zero .sphere X 0 0 δ ε r hr
      hgap
      (model.nu.unitIso ≪≫ (SyntheticCategory.biShift_zero.app S_0_0).symm) _
  obtain ⟨z,hz⟩ := U.yoneda_exact₃ hU dT hbottom
  have htopiso : U.obj₁⟦(1:ℤ)⟧ ≅ (SyntheticCategory.biShift (δ.1+1,δ.2+1)).obj W := by
    change (F.obj ((SyntheticCategory.biShift
      (0,(normalizedExponent model.classicalTower model.auxiliary.nuRouteTriangle.f:ℤ))).obj W))⟦(1:ℤ)⟧ ≅ _
    change (F.obj ((SyntheticCategory.biShift
      (0,(normalizedExponent model.classicalTower model.auxiliary.nuMap:ℤ))).obj W))⟦(1:ℤ)⟧ ≅ _
    rw [nuCofiber_nu_exponent]
    exact (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).symm.app _ ≪≫
      (SyntheticCategory.biShift (1,0)).mapIso
        ((SyntheticCategory.biShift_comp (0,1) δ).app W) ≪≫
      (SyntheticCategory.biShift_comp ((0,1)+δ) (1,0)).app W ≪≫
      eqToIso (by cases δ; simp [add_comm])
  have hz0 : z=0 := by
    apply (cancel_epi htopiso.inv).mp
    have hh := sphere_shifted_nu_high_target_map_zero (.shift 3 .sphere) X 3 3
      (δ.1+1,δ.2+1) ε r hr (by dsimp; omega) (nuSphereThree model) (htopiso.inv≫z)
    simpa only [comp_zero] using hh
  apply (cancel_epi e₃.hom).mp
  rw [comp_zero]
  change dT=0
  rw [hz,hz0,comp_zero]


private theorem nuCofiber_high_target_map_zero
    (X : ClassicalObject) (a b : ℤ) (r : ℕ) (hr : 0<r)
    (hgap : (r:ℤ)≤b-a)
    (d : (SyntheticCategory.biShift (0,a)).obj
        (model.nu.functor.obj (ClassicalObject.nuCofiber.obj model.auxiliary)) ⟶
      (SyntheticCategory.biShift (0,b)).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) r)) : d=0 := by
  exact shifted_nuCofiber_high_target_map_zero X (0,a) (0,b) r hr (by dsimp; omega) d

private theorem nuCofiber_high_target_extension
    (X : ClassicalObject) (a b : ℤ) (q r : ℕ) (hr : 0<r)
    (hgap : (r:ℤ)≤q+b-a)
    (d : (SyntheticCategory.biShift (0,a)).obj
        (model.nu.functor.obj (ClassicalObject.nuCofiber.obj model.auxiliary)) ⟶
      (SyntheticCategory.biShift (0,b)).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) r)) :
    ∃ dQ : XModLambdaN ((SyntheticCategory.biShift (0,a)).obj
        (model.nu.functor.obj (ClassicalObject.nuCofiber.obj model.auxiliary))) q ⟶
      (SyntheticCategory.biShift (0,b)).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) r),
      XModLambdaN.incl _ q≫dQ=d := by
  let V := model.nu.functor.obj (ClassicalObject.nuCofiber.obj model.auxiliary)
  let A := (SyntheticCategory.biShift (0,a)).obj V
  let e : (SyntheticCategory.biShift (0,-(q:ℤ))).obj A ≅
      (SyntheticCategory.biShift (0,a-q)).obj V :=
    (SyntheticCategory.biShift_comp (0,a) (0,-(q:ℤ))).app V ≪≫
      eqToIso (by simp [sub_eq_add_neg])
  have hz := nuCofiber_high_target_map_zero X (a-q) b r hr (by omega)
    (e.inv≫lambdaPow q A≫d)
  have hzero : lambdaPow q A≫d=0 := by
    apply (cancel_epi e.inv).mp
    simpa only [comp_zero] using hz
  obtain ⟨dQ,hdQ⟩ := (XModLambdaN.cofiberTriangle A q).yoneda_exact₂
    (XModLambdaN.cofiberTriangle_distinguished A q) d hzero
  exact ⟨dQ,hdQ.symm⟩

private theorem actual_edge_correction_of_extensions
    (Y X Z : ClassicalObject) (a b cWeight : ℤ)
    (q r i : ℕ) (hr : 0 < r) (hi : 0 < i)
    (hcompareC : (i:ℤ)≤q+b-a+1) (hcompareD : (r:ℤ)≤q+cWeight-a+1)
    (A C D : SyntheticObject)
    (hA : A=.shift (0,a) (.nu Y))
    (hC : C=.shift (0,b) (.quotient r (.nu X)))
    (hD : D=.shift (0,cWeight) (.quotient r (.nu Z)))
    (d : A.obj model.nu model.auxiliary ⟶ C.obj model.nu model.auxiliary)
    (h : C.obj model.nu model.auxiliary ⟶ D.obj model.nu model.auxiliary)
    (R : A.obj model.nu model.auxiliary ⟶ D.obj model.nu model.auxiliary)
    (K J : (SyntheticObject.quotient q A).obj model.nu model.auxiliary ⟶ D.obj model.nu model.auxiliary)
    (rho : C.obj model.nu model.auxiliary ⟶ (SyntheticCategory.biShift (0,b)).obj
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) i))
    (hextC : ∃ dQ : (SyntheticObject.quotient q A).obj model.nu model.auxiliary ⟶
        C.obj model.nu model.auxiliary, XModLambdaN.incl _ q≫dQ=d)
    (hextR : ∃ RQ : (SyntheticObject.quotient q A).obj model.nu model.auxiliary ⟶
        D.obj model.nu model.auxiliary, XModLambdaN.incl _ q≫RQ=R)
    (hkill : d≫rho=0)
    (hedge : XModLambdaN.incl (A.obj model.nu model.auxiliary) q≫K-
      XModLambdaN.incl (A.obj model.nu model.auxiliary) q≫J=d≫h-R)
    (p : Tridegree) (x : (model.family.obj (A.obj model.nu model.auxiliary)).E₂ p)
    (alpha : BiHom (p.2.1-p.1) p.2.2 ((SyntheticObject.quotient q A).obj model.nu model.auxiliary))
    (v : BiHom (p.2.1-p.1) p.2.2 (C.obj model.nu model.auxiliary))
    (halpha : Detects (model.convergence (SyntheticObject.quotient q A)) p
      (familyPageMap model.family (XModLambdaN.incl (A.obj model.nu model.auxiliary) q) 2 p x) alpha)
    (hv : v≫h=alpha≫K)
    (hRzero : Detects (model.convergence D) p (familyPageMap model.family R 2 p x) 0) :
    ∃ (dQ : (SyntheticObject.quotient q A).obj model.nu model.auxiliary ⟶ C.obj model.nu model.auxiliary)
      (v' : BiHom (p.2.1-p.1) p.2.2 (C.obj model.nu model.auxiliary)),
      XModLambdaN.incl (A.obj model.nu model.auxiliary) q≫dQ=d ∧ v'=v-alpha≫dQ ∧
      Detects (model.convergence C) p (familyPageMap model.family d 2 p x) (alpha≫dQ) ∧
      v'≫rho=v≫rho ∧
      Detects (model.convergence D) p
        (familyPageMap model.family J 2 p
          (familyPageMap model.family (XModLambdaN.incl (A.obj model.nu model.auxiliary) q) 2 p x)) (v'≫h) := by
  subst A
  subst C
  subst D
  dsimp only [SyntheticObject.obj] at d h R K J rho x alpha v halpha hv hedge hRzero hextC hextR hkill ⊢
  obtain ⟨dQ,hdQ⟩ := hextC
  obtain ⟨RQ,hRQ⟩ := hextR
  have hdRho : d≫rho=0 := hkill
  have hincRho : XModLambdaN.incl _ q≫(dQ≫rho)=XModLambdaN.incl _ q≫0 := by
    rw [←Category.assoc,hdQ,hdRho,comp_zero]
  have hcdRho : (alpha≫dQ)≫rho=0 := by
    have heq := finite_source_high_target_extensions_equal Y X q i hi a b
      hcompareC (dQ≫rho) 0 hincRho (p.2.1-p.1) p.2.2 alpha
    simpa only [Category.assoc,comp_zero] using heq
  have hinc : XModLambdaN.incl _ q≫(K-J) = XModLambdaN.incl _ q≫(dQ≫h-RQ) := by
    simp only [Preadditive.comp_sub,←Category.assoc,hdQ,hRQ]
    exact hedge
  have heq := finite_source_high_target_extensions_equal Y Z q r hr a cWeight
    hcompareD (K-J) (dQ≫h-RQ) hinc (p.2.1-p.1) p.2.2 alpha
  have heq' : alpha≫K-alpha≫J=(alpha≫dQ)≫h-alpha≫RQ := by
    simpa only [Preadditive.comp_sub,Category.assoc] using heq
  have hmath : (v-alpha≫dQ)≫h=alpha≫J-alpha≫RQ := by
    rw [Preadditive.sub_comp,hv]
    calc
      alpha≫K-(alpha≫dQ)≫h = (alpha≫K-alpha≫J)+alpha≫J-(alpha≫dQ)≫h := by abel
      _ = ((alpha≫dQ)≫h-alpha≫RQ)+alpha≫J-(alpha≫dQ)≫h := by rw [heq']
      _ = alpha≫J-alpha≫RQ := by abel
  have hdLabel : familyPageMap model.family dQ 2 p
      (familyPageMap model.family (XModLambdaN.incl _ q) 2 p x) =
      familyPageMap model.family d 2 p x := by
    rw [←ModuleCat.comp_apply,family_page_comp,hdQ]
  have hRLabel : familyPageMap model.family RQ 2 p
      (familyPageMap model.family (XModLambdaN.incl _ q) 2 p x) =
      familyPageMap model.family R 2 p x := by
    rw [←ModuleCat.comp_apply,family_page_comp,hRQ]
  have hcd := detects_map (.quotient q (.shift (0,a) (.nu Y)))
    (.shift (0,b) (.quotient r (.nu X))) dQ p _ alpha halpha
  have hcd := (congrArg (fun z => Detects
    (model.convergence (.shift (0,b) (.quotient r (.nu X)))) p z (alpha≫dQ)) hdLabel).mp hcd
  have hres := detects_map (.quotient q (.shift (0,a) (.nu Y)))
    (.shift (0,cWeight) (.quotient r (.nu Z))) RQ p _ alpha halpha
  have hres := (congrArg (fun z => Detects
    (model.convergence (.shift (0,cWeight) (.quotient r (.nu Z)))) p z (alpha≫RQ)) hRLabel).mp hres
  have hres0 := detects_zero_of_detects_same_label_zero
    (.shift (0,cWeight) (.quotient r (.nu Z))) p _ _ hres hRzero
  have hJ := detects_map (.quotient q (.shift (0,a) (.nu Y)))
    (.shift (0,cWeight) (.quotient r (.nu Z))) J p _ alpha halpha
  have htarget := detects_add (model.convergence (.shift (0,cWeight) (.quotient r (.nu Z))))
    p hJ (detects_neg hres0)
  refine ⟨dQ,v-alpha≫dQ,hdQ,rfl,hcd,?_,?_⟩
  · rw [Preadditive.sub_comp,hcdRho,sub_zero]
  · rw [hmath]
    simpa only [SyntheticObject.obj,neg_zero,add_zero,sub_eq_add_neg] using htarget


private theorem nuCofiber_source_actual_edge_correction
    (X Z : ClassicalObject) (a b cWeight : ℤ)
    (q r i : ℕ) (hr : 0 < r) (hi : 0 < i)
    (hgapC : (r:ℤ)≤q+b-a) (hgapD : (r:ℤ)≤q+cWeight-a)
    (hkill : (i:ℤ)≤b-a)
    (A C D : SyntheticObject)
    (hA : A=.shift (0,a) (.nu .nuCofiber))
    (hC : C=.shift (0,b) (.quotient r (.nu X)))
    (hD : D=.shift (0,cWeight) (.quotient r (.nu Z)))
    (d : A.obj model.nu model.auxiliary ⟶ C.obj model.nu model.auxiliary)
    (h : C.obj model.nu model.auxiliary ⟶ D.obj model.nu model.auxiliary)
    (R : A.obj model.nu model.auxiliary ⟶ D.obj model.nu model.auxiliary)
    (K J : (SyntheticObject.quotient q A).obj model.nu model.auxiliary ⟶ D.obj model.nu model.auxiliary)
    (rho : C.obj model.nu model.auxiliary ⟶ (SyntheticCategory.biShift (0,b)).obj
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) i))
    (hedge : XModLambdaN.incl (A.obj model.nu model.auxiliary) q≫K-
      XModLambdaN.incl (A.obj model.nu model.auxiliary) q≫J=d≫h-R)
    (p : Tridegree) (x : (model.family.obj (A.obj model.nu model.auxiliary)).E₂ p)
    (alpha : BiHom (p.2.1-p.1) p.2.2 ((SyntheticObject.quotient q A).obj model.nu model.auxiliary))
    (v : BiHom (p.2.1-p.1) p.2.2 (C.obj model.nu model.auxiliary))
    (halpha : Detects (model.convergence (SyntheticObject.quotient q A)) p
      (familyPageMap model.family (XModLambdaN.incl (A.obj model.nu model.auxiliary) q) 2 p x) alpha)
    (hv : v≫h=alpha≫K)
    (hRzero : Detects (model.convergence D) p (familyPageMap model.family R 2 p x) 0) :
    ∃ (dQ : (SyntheticObject.quotient q A).obj model.nu model.auxiliary ⟶ C.obj model.nu model.auxiliary)
      (v' : BiHom (p.2.1-p.1) p.2.2 (C.obj model.nu model.auxiliary)),
      XModLambdaN.incl (A.obj model.nu model.auxiliary) q≫dQ=d ∧ v'=v-alpha≫dQ ∧
      Detects (model.convergence C) p (familyPageMap model.family d 2 p x) (alpha≫dQ) ∧
      v'≫rho=v≫rho ∧
      Detects (model.convergence D) p
        (familyPageMap model.family J 2 p
          (familyPageMap model.family (XModLambdaN.incl (A.obj model.nu model.auxiliary) q) 2 p x)) (v'≫h) := by
  have hextC : ∃ dQ : (SyntheticObject.quotient q A).obj model.nu model.auxiliary ⟶
      C.obj model.nu model.auxiliary, XModLambdaN.incl _ q≫dQ=d := by
    subst A
    subst C
    exact nuCofiber_high_target_extension X a b q r hr hgapC d
  have hextR : ∃ RQ : (SyntheticObject.quotient q A).obj model.nu model.auxiliary ⟶
      D.obj model.nu model.auxiliary, XModLambdaN.incl _ q≫RQ=R := by
    subst A
    subst D
    exact nuCofiber_high_target_extension Z a cWeight q r hr hgapD R
  have hkill' : d≫rho=0 := by
    subst A
    subst C
    exact nuCofiber_high_target_map_zero X a b i hi hkill (d≫rho)
  exact actual_edge_correction_of_extensions .nuCofiber X Z a b cWeight q r i hr hi
    (by omega) (by omega) A C D hA hC hD d h R K J rho hextC hextR hkill'
    hedge p x alpha v halpha hv hRzero


private theorem nu_classical_shift_iso_exists (Y : ClassicalObject) (p : ℤ) :
    Nonempty (model.nu.functor.obj ((ClassicalObject.shift p Y).obj model.auxiliary) ≅
      (SyntheticCategory.biShift (p,p)).obj (model.nu.functor.obj (Y.obj model.auxiliary))) := by
  induction p using Int.induction_on with
  | zero =>
    exact ⟨model.nu.functor.mapIso ((shiftFunctorZero Spectrum ℤ).app (Y.obj model.auxiliary)) ≪≫
      (SyntheticCategory.biShift_zero.app _).symm⟩
  | succ i ih =>
    obtain ⟨e⟩ := ih
    exact ⟨model.nu.functor.mapIso
        ((shiftFunctorAdd' Spectrum (i:ℤ) 1 ((i:ℤ)+1) rfl).app (Y.obj model.auxiliary)) ≪≫
      model.nu.suspensionIso ((ClassicalObject.shift i Y).obj model.auxiliary) ≪≫
      (SyntheticCategory.biShift (1,1)).mapIso e ≪≫
      (SyntheticCategory.biShift_comp ((i:ℤ),(i:ℤ)) (1,1)).app _⟩
  | pred i ih =>
    obtain ⟨e⟩ := ih
    let A := model.nu.functor.obj ((ClassicalObject.shift (-((i:ℤ))-1) Y).obj model.auxiliary)
    let eStep : model.nu.functor.obj ((ClassicalObject.shift (-((i:ℤ))) Y).obj model.auxiliary) ≅
        (SyntheticCategory.biShift (1,1)).obj A :=
      model.nu.functor.mapIso
        ((shiftFunctorAdd' Spectrum (-((i:ℤ))-1) 1 (-((i:ℤ))) (by omega)).app
          (Y.obj model.auxiliary)) ≪≫ model.nu.suspensionIso _
    refine ⟨(SyntheticCategory.biShift_zero.app A).symm ≪≫
      eqToIso (congrArg (fun δ => (SyntheticCategory.biShift δ).obj A)
        (show (0,0)=(1,1)+(-1,-1) by ext <;> norm_num)) ≪≫
      (SyntheticCategory.biShift_comp (1,1) (-1,-1)).symm.app A ≪≫
      (SyntheticCategory.biShift (-1,-1)).mapIso eStep.symm ≪≫
      (SyntheticCategory.biShift (-1,-1)).mapIso e ≪≫
      (SyntheticCategory.biShift_comp (-((i:ℤ)),-((i:ℤ))) (-1,-1)).app _ ≪≫ ?_⟩
    exact eqToIso (by simp [sub_eq_add_neg])

private theorem shifted_classical_nuCofiber_high_target_map_zero
    (X : ClassicalObject) (p a b : ℤ) (r : ℕ) (hr : 0<r)
    (hgap : (r:ℤ)≤b-a)
    (d : (SyntheticCategory.biShift (0,a)).obj
        (model.nu.functor.obj ((ClassicalObject.shift p .nuCofiber).obj model.auxiliary)) ⟶
      (SyntheticCategory.biShift (0,b)).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) r)) : d=0 := by
  obtain ⟨eY⟩ := nu_classical_shift_iso_exists .nuCofiber p
  let e : (SyntheticCategory.biShift (0,a)).obj
      (model.nu.functor.obj ((ClassicalObject.shift p .nuCofiber).obj model.auxiliary)) ≅
      (SyntheticCategory.biShift (p,p+a)).obj
        (model.nu.functor.obj (ClassicalObject.nuCofiber.obj model.auxiliary)) :=
    (SyntheticCategory.biShift (0,a)).mapIso eY ≪≫
      (SyntheticCategory.biShift_comp (p,p) (0,a)).app _ ≪≫ eqToIso (by simp)
  apply (cancel_epi e.inv).mp
  have hh := shifted_nuCofiber_high_target_map_zero X (p,p+a) (0,b) r hr
    (by dsimp; omega) (e.inv≫d)
  simpa only [comp_zero] using hh

private theorem shifted_classical_nuCofiber_high_target_extension
    (X : ClassicalObject) (p a b : ℤ) (q r : ℕ) (hr : 0<r)
    (hgap : (r:ℤ)≤q+b-a)
    (d : (SyntheticCategory.biShift (0,a)).obj
        (model.nu.functor.obj ((ClassicalObject.shift p .nuCofiber).obj model.auxiliary)) ⟶
      (SyntheticCategory.biShift (0,b)).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) r)) :
    ∃ dQ : XModLambdaN ((SyntheticCategory.biShift (0,a)).obj
        (model.nu.functor.obj ((ClassicalObject.shift p .nuCofiber).obj model.auxiliary))) q ⟶
      (SyntheticCategory.biShift (0,b)).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) r),
      XModLambdaN.incl _ q≫dQ=d := by
  let V := model.nu.functor.obj ((ClassicalObject.shift p .nuCofiber).obj model.auxiliary)
  let A := (SyntheticCategory.biShift (0,a)).obj V
  let e : (SyntheticCategory.biShift (0,-(q:ℤ))).obj A ≅
      (SyntheticCategory.biShift (0,a-q)).obj V :=
    (SyntheticCategory.biShift_comp (0,a) (0,-(q:ℤ))).app V ≪≫
      eqToIso (by simp [sub_eq_add_neg])
  have hz := shifted_classical_nuCofiber_high_target_map_zero X p (a-q) b r hr (by omega)
    (e.inv≫lambdaPow q A≫d)
  have hzero : lambdaPow q A≫d=0 := by
    apply (cancel_epi e.inv).mp
    simpa only [comp_zero] using hz
  obtain ⟨dQ,hdQ⟩ := (XModLambdaN.cofiberTriangle A q).yoneda_exact₂
    (XModLambdaN.cofiberTriangle_distinguished A q) d hzero
  exact ⟨dQ,hdQ.symm⟩

private theorem shifted_classical_nuCofiber_source_actual_edge_correction
    (X Z : ClassicalObject) (j a b cWeight : ℤ)
    (q r i : ℕ) (hr : 0 < r) (hi : 0 < i)
    (hgapC : (r:ℤ)≤q+b-a) (hgapD : (r:ℤ)≤q+cWeight-a)
    (hkill : (i:ℤ)≤b-a)
    (A C D : SyntheticObject)
    (hA : A=.shift (0,a) (.nu (.shift j .nuCofiber)))
    (hC : C=.shift (0,b) (.quotient r (.nu X)))
    (hD : D=.shift (0,cWeight) (.quotient r (.nu Z)))
    (d : A.obj model.nu model.auxiliary ⟶ C.obj model.nu model.auxiliary)
    (h : C.obj model.nu model.auxiliary ⟶ D.obj model.nu model.auxiliary)
    (R : A.obj model.nu model.auxiliary ⟶ D.obj model.nu model.auxiliary)
    (K J : (SyntheticObject.quotient q A).obj model.nu model.auxiliary ⟶ D.obj model.nu model.auxiliary)
    (rho : C.obj model.nu model.auxiliary ⟶ (SyntheticCategory.biShift (0,b)).obj
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) i))
    (hedge : XModLambdaN.incl (A.obj model.nu model.auxiliary) q≫K-
      XModLambdaN.incl (A.obj model.nu model.auxiliary) q≫J=d≫h-R)
    (p : Tridegree) (x : (model.family.obj (A.obj model.nu model.auxiliary)).E₂ p)
    (alpha : BiHom (p.2.1-p.1) p.2.2 ((SyntheticObject.quotient q A).obj model.nu model.auxiliary))
    (v : BiHom (p.2.1-p.1) p.2.2 (C.obj model.nu model.auxiliary))
    (halpha : Detects (model.convergence (SyntheticObject.quotient q A)) p
      (familyPageMap model.family (XModLambdaN.incl (A.obj model.nu model.auxiliary) q) 2 p x) alpha)
    (hv : v≫h=alpha≫K)
    (hRzero : Detects (model.convergence D) p (familyPageMap model.family R 2 p x) 0) :
    ∃ (dQ : (SyntheticObject.quotient q A).obj model.nu model.auxiliary ⟶ C.obj model.nu model.auxiliary)
      (v' : BiHom (p.2.1-p.1) p.2.2 (C.obj model.nu model.auxiliary)),
      XModLambdaN.incl (A.obj model.nu model.auxiliary) q≫dQ=d ∧ v'=v-alpha≫dQ ∧
      Detects (model.convergence C) p (familyPageMap model.family d 2 p x) (alpha≫dQ) ∧
      v'≫rho=v≫rho ∧
      Detects (model.convergence D) p
        (familyPageMap model.family J 2 p
          (familyPageMap model.family (XModLambdaN.incl (A.obj model.nu model.auxiliary) q) 2 p x)) (v'≫h) := by
  have hextC : ∃ dQ : (SyntheticObject.quotient q A).obj model.nu model.auxiliary ⟶
      C.obj model.nu model.auxiliary, XModLambdaN.incl _ q≫dQ=d := by
    subst A
    subst C
    exact shifted_classical_nuCofiber_high_target_extension X j a b q r hr hgapC d
  have hextR : ∃ RQ : (SyntheticObject.quotient q A).obj model.nu model.auxiliary ⟶
      D.obj model.nu model.auxiliary, XModLambdaN.incl _ q≫RQ=R := by
    subst A
    subst D
    exact shifted_classical_nuCofiber_high_target_extension Z j a cWeight q r hr hgapD R
  have hkill' : d≫rho=0 := by
    subst A
    subst C
    exact shifted_classical_nuCofiber_high_target_map_zero X j a b i hi hkill (d≫rho)
  exact actual_edge_correction_of_extensions (.shift j .nuCofiber) X Z a b cWeight q r i hr hi
    (by omega) (by omega) A C D hA hC hD d h R K J rho hextC hextR hkill'
    hedge p x alpha v halpha hv hRzero


end
end KIP126.ProofTools.Internal.Mahowald
