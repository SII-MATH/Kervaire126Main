module
public import KIP126.ProofTools.Operations
public import KIP126.ProofTools.Representatives
import all KIP126.Main.Internal.DetectionLabels
/-! The normalized exponent-zero label and representative calculation from
NuFifth:317–446,583–790 (bbac1fc05843, MIT), using the same fixed maps. -/
@[expose] section
namespace KIP126.Main.Internal.NuThree
open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence KIP126.AdamsSynthetic
open KIP126.Core.SpectralSequence KIP126.Kervaire.Route KIP126.Literature
open KIP126.AdamsSynthetic.Standard (model SyntheticSpectrum)
open KIP126.ProofTools KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald KIP126.Main.Internal
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
private theorem zero_shift_quotient_label_8
    (X : ClassicalObject) (q : ℕ) (x : (model.classical.obj (X.obj model.auxiliary)).Page 2 (8,134)) :
    familyPageMap model.family
      (XModLambdaN.map (show (SyntheticCategory.biShift (0,0)).obj (model.nu.functor.obj (X.obj model.auxiliary)) ⟶ model.nu.functor.obj (X.obj model.auxiliary) from SyntheticCategory.biShift_zero.hom.app _) q)
      2 (8,134,134-(0:ℕ))
      (by simpa only [add_zero,SyntheticObject.obj,SyntheticAdamsSS.E₂] using finiteNuLabel model X q 0 8 134 0 x) =
    (by simpa only [SyntheticObject.obj,SyntheticAdamsSS.E₂,SyntheticAdamsFamily.quotient] using finiteTargetLabel model X q 8 134 0 x) := by
  let A := model.nu.functor.obj (X.obj model.auxiliary)
  let a : (model.family.obj ((SyntheticCategory.biShift (0,0)).obj A)).E₂ (8,134,134-(0:ℕ)) := by
    simpa only [add_zero,SyntheticObject.obj,SyntheticAdamsSS.E₂] using model.comparison.nuE2 X 0 8 134 0 x
  change familyPageMap model.family (XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app A) q) 2 (8,134,134-(0:ℕ))
    (familyPageMap model.family (XModLambdaN.incl _ q) 2 (8,134,134-(0:ℕ)) a) =
      familyPageMap model.family (XModLambdaN.incl _ q) 2 (8,134,134-(0:ℕ))
        (familyPageMap model.family (SyntheticCategory.biShift_zero.hom.app A) 2 (8,134,134-(0:ℕ)) a)
  calc
    _ = familyPageMap model.family
        (XModLambdaN.incl _ q≫XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app A) q) 2 (8,134,134-(0:ℕ)) a :=
      ConcreteCategory.congr_hom (family_page_comp _ _ 2 (8,134,134-(0:ℕ))) a
    _ = familyPageMap model.family
        (SyntheticCategory.biShift_zero.hom.app A≫XModLambdaN.incl _ q) 2 (8,134,134-(0:ℕ)) a := by
      rw [XModLambdaN.incl_naturality]
    _ = _ := (ConcreteCategory.congr_hom (family_page_comp _ _ 2 (8,134,134-(0:ℕ))) a).symm
private theorem zero_shift_quotient_label_inverse_8
    (X : ClassicalObject) (q : ℕ) (x : (model.classical.obj (X.obj model.auxiliary)).Page 2 (8,134)) :
    familyPageMap model.family
      (XModLambdaN.map (show model.nu.functor.obj (X.obj model.auxiliary) ⟶ (SyntheticCategory.biShift (0,0)).obj (model.nu.functor.obj (X.obj model.auxiliary)) from SyntheticCategory.biShift_zero.inv.app _) q)
      2 (8,134,134-(0:ℕ))
      (by simpa only [SyntheticObject.obj,SyntheticAdamsSS.E₂,SyntheticAdamsFamily.quotient] using finiteTargetLabel model X q 8 134 0 x) =
    (by simpa only [add_zero,SyntheticObject.obj,SyntheticAdamsSS.E₂] using finiteNuLabel model X q 0 8 134 0 x) := by
  let A := model.nu.functor.obj (X.obj model.auxiliary)
  let f := XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app A) q
  let g := XModLambdaN.map (SyntheticCategory.biShift_zero.inv.app A) q
  have hfg : f≫g=𝟙 _ := by
    dsimp only [f,g]
    rw [←model.quotients.functoriality.map_comp,Iso.hom_inv_id_app,model.quotients.functoriality.map_id]
  rw [←zero_shift_quotient_label_8 X q x]
  change familyPageMap model.family g 2 (8,134,134-(0:ℕ))
    (familyPageMap model.family f 2 (8,134,134-(0:ℕ)) _) = _
  rw [←ConcreteCategory.comp_apply]
  rw [family_page_comp f g 2 (8,134,134-(0:ℕ)),hfg,family_page_id]
  rfl
private theorem zero_shift_finite_infinity_exists_8
    (X : ClassicalObject) (q : ℕ) (hq : 0<q)
    (x : (model.classical.obj (X.obj model.auxiliary)).Page 2 (8,134))
    (hx : x∈cycles model X q (8,134)) :
    ∃ e : ((model.family.obj ((SyntheticObject.quotient q (.shift (0,0) (.nu X))).obj model.nu model.auxiliary)).sequence.ssData (8,134,134-(0:ℕ))).eInfty,
      HasInfinityRepresentative _ 2 (8,134,134-(0:ℕ))
        (by simpa only [add_zero,SyntheticObject.obj,SyntheticAdamsSS.E₂] using finiteNuLabel model X q 0 8 134 0 x) e := by
  let P := KIP126.Literature.Standard.infinityFiniteWindow X q hq (8,134) (134-(0:ℕ)) (by constructor <;> omega)
  let c : cycles model X ((q:ℤ)-134+(134-(0:ℕ))) (8,134) :=
    ⟨x,by simpa only [Nat.cast_zero,sub_zero,sub_add_cancel] using hx⟩
  let en := P.symm (subquotientClass _ _ c)
  have hen : HasInfinityRepresentative (model.family.quotient (model.nu.functor.obj (X.obj model.auxiliary)) q)
      2 (8,134,134-(0:ℕ)) (by simpa only [SyntheticObject.obj,SyntheticAdamsSS.E₂,SyntheticAdamsFamily.quotient] using finiteTargetLabel model X q 8 134 0 x) en := by
    exact (finite_target_label_iff X q hq 8 134 0 hq c en).mpr (P.apply_symm_apply _)
  let g := XModLambdaN.map (SyntheticCategory.biShift_zero.inv.app (model.nu.functor.obj (X.obj model.auxiliary))) q
  refine ⟨(model.family.functor.map g).eInftyMap (8,134,134-(0:ℕ)) en,?_⟩
  have he := family_infinity_representative_map g (8,134,134-(0:ℕ)) _ en hen
  dsimp only [g,id] at he
  have hl := zero_shift_quotient_label_inverse_8 X q x
  convert he using 1
  · rfl
  · exact hl.symm
  · rfl
private theorem lambda_to_positive_zero (A : SyntheticSpectrum) :
    lambdaToPositivePow 0 A = SyntheticCategory.biShift_zero.inv.app A := by
  have hc := model.quotients.coherence.right_unit (0,0) A
  have he : (SyntheticCategory.biShift_comp (0,0) (0,0)).hom.app A =
      SyntheticCategory.biShift_zero.hom.app ((SyntheticCategory.biShift (0,0)).obj A) := by
    change (biShiftAddIso (0,0) (0,0) (0,0) (by decide)).hom.app _=_ at hc
    simpa only [biShiftAddIso,Iso.trans_hom,NatTrans.comp_app,eqToIso.hom,
      eqToHom_app,eqToHom_refl,Category.comp_id] using hc
  dsimp only [lambdaToPositivePow,lambdaPow]
  simp only [eqToHom_refl,Category.id_comp]
  change SyntheticCategory.biShift_zero.inv.app A ≫
    (SyntheticCategory.biShift_comp (0,0) (0,0)).inv.app A ≫
      SyntheticCategory.biShift_zero.hom.app ((SyntheticCategory.biShift (0,0)).obj A)=_
  calc
    _ = SyntheticCategory.biShift_zero.inv.app A ≫
        (SyntheticCategory.biShift_comp (0,0) (0,0)).inv.app A ≫
          (SyntheticCategory.biShift_comp (0,0) (0,0)).hom.app A := by
      exact congrArg (fun k => SyntheticCategory.biShift_zero.inv.app A ≫
        (SyntheticCategory.biShift_comp (0,0) (0,0)).inv.app A ≫ k) he.symm
    _ = SyntheticCategory.biShift_zero.inv.app A := by
      rw [Iso.inv_hom_id_app]
      exact Category.comp_id _
private theorem target_nu_natural_8
    (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (x : (model.classical.obj (X.obj model.auxiliary)).Page 2 (8,134)) :
    familyPageMap model.family (model.nu.functor.map f) 2 (8,134,134) (targetNuLabel model X 8 134 0 x) =
      targetNuLabel model Y 8 134 0 (model.classical.pageMap f 2 (8,134) x) := by
  have h := model.comparison.nu_natural X Y f 0 8 134 0 x
  change familyPageMap model.family (model.nu.functor.map f) 2 (8,134,134)
    (familyPageMap model.family (SyntheticCategory.biShift_zero.hom.app _) 2 (8,134,134) (model.comparison.nuE2 X 0 8 134 0 x)) = _
  calc
    _ = familyPageMap model.family (SyntheticCategory.biShift_zero.hom.app _≫model.nu.functor.map f) 2 (8,134,134) (model.comparison.nuE2 X 0 8 134 0 x) :=
      ConcreteCategory.congr_hom (family_page_comp _ _ 2 (8,134,134)) _
    _ = familyPageMap model.family ((SyntheticCategory.biShift (0,0)).map (model.nu.functor.map f)≫SyntheticCategory.biShift_zero.hom.app _) 2 (8,134,134) (model.comparison.nuE2 X 0 8 134 0 x) := by
      exact congrArg (fun g => familyPageMap model.family g 2 (8,134,134) (model.comparison.nuE2 X 0 8 134 0 x)) (SyntheticCategory.biShift_zero.hom.naturality (model.nu.functor.map f)).symm
    _ = familyPageMap model.family (SyntheticCategory.biShift_zero.hom.app _) 2 (8,134,134)
        (familyPageMap model.family ((SyntheticCategory.biShift (0,0)).map (model.nu.functor.map f)) 2 (8,134,134) (model.comparison.nuE2 X 0 8 134 0 x)) :=
      (ConcreteCategory.congr_hom (family_page_comp _ _ 2 (8,134,134)) _).symm
    _ = _ := congrArg (fun y => familyPageMap model.family (SyntheticCategory.biShift_zero.hom.app _) 2 (8,134,134) y) h
private theorem finite_target_natural_8
    (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (q : ℕ) (x : (model.classical.obj (X.obj model.auxiliary)).Page 2 (8,134)) :
    familyPageMap model.family (XModLambdaN.map (model.nu.functor.map f) q) 2 (8,134,134)
      (finiteTargetLabel model X q 8 134 0 x) =
      finiteTargetLabel model Y q 8 134 0 (model.classical.pageMap f 2 (8,134) x) := by
  change familyPageMap model.family (XModLambdaN.map (model.nu.functor.map f) q) 2 (8,134,134)
    (familyPageMap model.family (XModLambdaN.incl _ q) 2 (8,134,134) (targetNuLabel model X 8 134 0 x)) = _
  calc
    _ = familyPageMap model.family (XModLambdaN.incl _ q≫XModLambdaN.map (model.nu.functor.map f) q) 2 (8,134,134) (targetNuLabel model X 8 134 0 x) :=
      ConcreteCategory.congr_hom (family_page_comp _ _ 2 (8,134,134)) _
    _ = familyPageMap model.family (model.nu.functor.map f≫XModLambdaN.incl _ q) 2 (8,134,134) (targetNuLabel model X 8 134 0 x) :=
      congrArg (fun g => familyPageMap model.family g 2 (8,134,134) (targetNuLabel model X 8 134 0 x)) (XModLambdaN.incl_naturality (model.nu.functor.map f) q).symm
    _ = familyPageMap model.family (XModLambdaN.incl _ q) 2 (8,134,134)
        (familyPageMap model.family (model.nu.functor.map f) 2 (8,134,134) (targetNuLabel model X 8 134 0 x)) :=
      (ConcreteCategory.congr_hom (family_page_comp _ _ 2 (8,134,134)) _).symm
    _ = _ := congrArg (fun y => familyPageMap model.family (XModLambdaN.incl _ q) 2 (8,134,134) y) (target_nu_natural_8 X Y f x)
private theorem zero_exponent_source_infinity_8
    (X : ClassicalObject) (n : ℕ) (hn : n=0)
    (q : ℕ) (hq : 0<q) (x : (model.classical.obj (X.obj model.auxiliary)).Page 2 (8,134))
    (hx : x∈cycles model X q (8,134)) :
    ∃ e : ((model.family.obj ((SyntheticObject.quotient q (.shift (0,n) (.nu X))).obj model.nu model.auxiliary)).sequence.ssData (8,(134-8)+8,134+n)).eInfty,
      HasInfinityRepresentative _ 2 (8,(134-8)+8,134+n)
        (regradeE2 (A:=model.family.obj ((SyntheticObject.quotient q (.shift (0,n) (.nu X))).obj model.nu model.auxiliary)) (i:=(8,134,134+(n:ℤ)-(0:ℕ))) (j:=(8,134,134+(n:ℤ))) (by ext <;> simp) (finiteNuLabel model X q n 8 134 0 x)) e := by
  subst n
  exact zero_shift_finite_infinity_exists_8 X q hq x hx
private theorem normalized_zero_source_infinity_8
    (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary) (he : normalizedExponent model.classicalTower f=0)
    (q : ℕ) (hq : 0<q) (x : (model.classical.obj (X.obj model.auxiliary)).Page 2 (8,134))
    (hx : x∈cycles model X q (8,134)) :
    ∃ e : ((model.family.obj ((SyntheticObject.quotient q (extensionSourceObject model X Y f)).obj model.nu model.auxiliary)).sequence.ssData (8,(134-8)+8,134+normalizedExponent model.classicalTower f)).eInfty,
      HasInfinityRepresentative _ 2 (8,(134-8)+8,134+normalizedExponent model.classicalTower f)
        (finiteSourceForExtension model X Y f q 8 134 x) e := by
  exact zero_exponent_source_infinity_8 X _ he q hq x hx
private theorem zero_exponent_map_label_8
    (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (n : ℕ) (hn : n=0)
    (g : (SyntheticCategory.biShift (0,n)).obj (model.nu.functor.obj (X.obj model.auxiliary)) ⟶ model.nu.functor.obj (Y.obj model.auxiliary))
    (hf : lambdaToPositivePow n (model.nu.functor.obj (X.obj model.auxiliary))≫g=model.nu.functor.map f)
    (q : ℕ) (x : (model.classical.obj (X.obj model.auxiliary)).Page 2 (8,134)) :
    HEq (familyPageMap model.family (XModLambdaN.map g q) 2 (8,(134-8)+8,134+n)
      (regradeE2 (A:=model.family.obj ((SyntheticObject.quotient q (.shift (0,n) (.nu X))).obj model.nu model.auxiliary)) (i:=(8,134,134+(n:ℤ)-(0:ℕ))) (j:=(8,134,134+(n:ℤ))) (by ext <;> simp) (finiteNuLabel model X q n 8 134 0 x)))
      (finiteTargetLabel model Y q 8 134 0 (model.classical.pageMap f 2 (8,134) x)) := by
  subst n
  have hfact : SyntheticCategory.biShift_zero.inv.app (model.nu.functor.obj (X.obj model.auxiliary))≫g=model.nu.functor.map f :=
    (congrArg (fun u => u≫g) (lambda_to_positive_zero _)).symm.trans hf
  have hg : g=SyntheticCategory.biShift_zero.hom.app (model.nu.functor.obj (X.obj model.auxiliary))≫model.nu.functor.map f := by
    calc
      _ = SyntheticCategory.biShift_zero.hom.app (model.nu.functor.obj (X.obj model.auxiliary))≫
        SyntheticCategory.biShift_zero.inv.app (model.nu.functor.obj (X.obj model.auxiliary))≫g := by simp
      _ = _ := congrArg (fun u => SyntheticCategory.biShift_zero.hom.app (model.nu.functor.obj (X.obj model.auxiliary))≫u) hfact
  apply heq_of_eq
  change familyPageMap model.family (XModLambdaN.map g q) 2 (8,134,134) (finiteNuLabel model X q 0 8 134 0 x) = _
  calc
    _ = familyPageMap model.family (XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app (model.nu.functor.obj (X.obj model.auxiliary))≫model.nu.functor.map f) q) 2 (8,134,134) (finiteNuLabel model X q 0 8 134 0 x) :=
      congrArg (fun u => familyPageMap model.family (XModLambdaN.map u q) 2 (8,134,134) (finiteNuLabel model X q 0 8 134 0 x)) hg
    _ = familyPageMap model.family (XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app (model.nu.functor.obj (X.obj model.auxiliary))) q≫XModLambdaN.map (model.nu.functor.map f) q) 2 (8,134,134) (finiteNuLabel model X q 0 8 134 0 x) :=
      congrArg (fun u => familyPageMap model.family u 2 (8,134,134) (finiteNuLabel model X q 0 8 134 0 x)) (model.quotients.functoriality.map_comp _ _ q)
    _ = familyPageMap model.family (XModLambdaN.map (model.nu.functor.map f) q) 2 (8,134,134)
        (familyPageMap model.family (XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app (model.nu.functor.obj (X.obj model.auxiliary))) q) 2 (8,134,134) (finiteNuLabel model X q 0 8 134 0 x)) :=
      (ConcreteCategory.congr_hom (family_page_comp _ _ 2 (8,134,134)) _).symm
    _ = familyPageMap model.family (XModLambdaN.map (model.nu.functor.map f) q) 2 (8,134,134) (finiteTargetLabel model X q 8 134 0 x) :=
      congrArg (fun z => familyPageMap model.family (XModLambdaN.map (model.nu.functor.map f) q) 2 (8,134,134) z) (zero_shift_quotient_label_8 X q x)
    _ = _ := finite_target_natural_8 X Y f q x
private theorem normalized_zero_map_label_8
    (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (he : normalizedExponent model.classicalTower f=0) (q : ℕ) (x : (model.classical.obj (X.obj model.auxiliary)).Page 2 (8,134)) :
    HEq (familyPageMap model.family (finiteExtensionMap model X Y f q) 2 (8,(134-8)+8,134+normalizedExponent model.classicalTower f)
      (finiteSourceForExtension model X Y f q 8 134 x))
      (finiteTargetLabel model Y q 8 134 0 (model.classical.pageMap f 2 (8,134) x)) := by
  exact zero_exponent_map_label_8 X Y f _ he (model.normalizedMap X Y f).map (model.normalizedMap X Y f).factorization q x
private theorem zero_exponent_target_label_8
    (Y : ClassicalObject) (q n : ℕ) (hn : n=0) (y : (model.classical.obj (Y.obj model.auxiliary)).Page 2 (8,134)) :
    HEq (regradeE2 (A:=model.family.obj ((SyntheticObject.quotient q (.nu Y)).obj model.nu model.auxiliary))
      (i:=(8+0,134+0,(134+0)-((0-(n:ℤ)).toNat:ℤ)))
      (j:=(8+0,(134-8)+(8+0),134+n))
      (by subst n; decide) (finiteTargetLabel model Y q (8+0) (134+0) (0-(n:ℤ)).toNat y))
      (finiteTargetLabel model Y q 8 134 0 y) := by
  subst n
  rfl

private theorem zero_shift_quotient_label_11
    (X : ClassicalObject) (q : ℕ) (x : (model.classical.obj (X.obj model.auxiliary)).Page 2 (11,136)) :
    familyPageMap model.family
      (XModLambdaN.map (show (SyntheticCategory.biShift (0,0)).obj (model.nu.functor.obj (X.obj model.auxiliary)) ⟶ model.nu.functor.obj (X.obj model.auxiliary) from SyntheticCategory.biShift_zero.hom.app _) q)
      2 (11,136,136-(0:ℕ))
      (by simpa only [add_zero,SyntheticObject.obj,SyntheticAdamsSS.E₂] using finiteNuLabel model X q 0 11 136 0 x) =
    (by simpa only [SyntheticObject.obj,SyntheticAdamsSS.E₂,SyntheticAdamsFamily.quotient] using finiteTargetLabel model X q 11 136 0 x) := by
  let A := model.nu.functor.obj (X.obj model.auxiliary)
  let a : (model.family.obj ((SyntheticCategory.biShift (0,0)).obj A)).E₂ (11,136,136-(0:ℕ)) := by
    simpa only [add_zero,SyntheticObject.obj,SyntheticAdamsSS.E₂] using model.comparison.nuE2 X 0 11 136 0 x
  change familyPageMap model.family (XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app A) q) 2 (11,136,136-(0:ℕ))
    (familyPageMap model.family (XModLambdaN.incl _ q) 2 (11,136,136-(0:ℕ)) a) =
      familyPageMap model.family (XModLambdaN.incl _ q) 2 (11,136,136-(0:ℕ))
        (familyPageMap model.family (SyntheticCategory.biShift_zero.hom.app A) 2 (11,136,136-(0:ℕ)) a)
  calc
    _ = familyPageMap model.family
        (XModLambdaN.incl _ q≫XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app A) q) 2 (11,136,136-(0:ℕ)) a :=
      ConcreteCategory.congr_hom (family_page_comp _ _ 2 (11,136,136-(0:ℕ))) a
    _ = familyPageMap model.family
        (SyntheticCategory.biShift_zero.hom.app A≫XModLambdaN.incl _ q) 2 (11,136,136-(0:ℕ)) a := by
      rw [XModLambdaN.incl_naturality]
    _ = _ := (ConcreteCategory.congr_hom (family_page_comp _ _ 2 (11,136,136-(0:ℕ))) a).symm
private theorem zero_shift_quotient_label_inverse_11
    (X : ClassicalObject) (q : ℕ) (x : (model.classical.obj (X.obj model.auxiliary)).Page 2 (11,136)) :
    familyPageMap model.family
      (XModLambdaN.map (show model.nu.functor.obj (X.obj model.auxiliary) ⟶ (SyntheticCategory.biShift (0,0)).obj (model.nu.functor.obj (X.obj model.auxiliary)) from SyntheticCategory.biShift_zero.inv.app _) q)
      2 (11,136,136-(0:ℕ))
      (by simpa only [SyntheticObject.obj,SyntheticAdamsSS.E₂,SyntheticAdamsFamily.quotient] using finiteTargetLabel model X q 11 136 0 x) =
    (by simpa only [add_zero,SyntheticObject.obj,SyntheticAdamsSS.E₂] using finiteNuLabel model X q 0 11 136 0 x) := by
  let A := model.nu.functor.obj (X.obj model.auxiliary)
  let f := XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app A) q
  let g := XModLambdaN.map (SyntheticCategory.biShift_zero.inv.app A) q
  have hfg : f≫g=𝟙 _ := by
    dsimp only [f,g]
    rw [←model.quotients.functoriality.map_comp,Iso.hom_inv_id_app,model.quotients.functoriality.map_id]
  rw [←zero_shift_quotient_label_11 X q x]
  change familyPageMap model.family g 2 (11,136,136-(0:ℕ))
    (familyPageMap model.family f 2 (11,136,136-(0:ℕ)) _) = _
  rw [←ConcreteCategory.comp_apply]
  rw [family_page_comp f g 2 (11,136,136-(0:ℕ)),hfg,family_page_id]
  rfl
private theorem zero_shift_finite_infinity_exists_11
    (X : ClassicalObject) (q : ℕ) (hq : 0<q)
    (x : (model.classical.obj (X.obj model.auxiliary)).Page 2 (11,136))
    (hx : x∈cycles model X q (11,136)) :
    ∃ e : ((model.family.obj ((SyntheticObject.quotient q (.shift (0,0) (.nu X))).obj model.nu model.auxiliary)).sequence.ssData (11,136,136-(0:ℕ))).eInfty,
      HasInfinityRepresentative _ 2 (11,136,136-(0:ℕ))
        (by simpa only [add_zero,SyntheticObject.obj,SyntheticAdamsSS.E₂] using finiteNuLabel model X q 0 11 136 0 x) e := by
  let P := KIP126.Literature.Standard.infinityFiniteWindow X q hq (11,136) (136-(0:ℕ)) (by constructor <;> omega)
  let c : cycles model X ((q:ℤ)-136+(136-(0:ℕ))) (11,136) :=
    ⟨x,by simpa only [Nat.cast_zero,sub_zero,sub_add_cancel] using hx⟩
  let en := P.symm (subquotientClass _ _ c)
  have hen : HasInfinityRepresentative (model.family.quotient (model.nu.functor.obj (X.obj model.auxiliary)) q)
      2 (11,136,136-(0:ℕ)) (by simpa only [SyntheticObject.obj,SyntheticAdamsSS.E₂,SyntheticAdamsFamily.quotient] using finiteTargetLabel model X q 11 136 0 x) en := by
    exact (finite_target_label_iff X q hq 11 136 0 hq c en).mpr (P.apply_symm_apply _)
  let g := XModLambdaN.map (SyntheticCategory.biShift_zero.inv.app (model.nu.functor.obj (X.obj model.auxiliary))) q
  refine ⟨(model.family.functor.map g).eInftyMap (11,136,136-(0:ℕ)) en,?_⟩
  have he := family_infinity_representative_map g (11,136,136-(0:ℕ)) _ en hen
  dsimp only [g,id] at he
  have hl := zero_shift_quotient_label_inverse_11 X q x
  convert he using 1
  · rfl
  · exact hl.symm
  · rfl
private theorem target_nu_natural_11
    (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (x : (model.classical.obj (X.obj model.auxiliary)).Page 2 (11,136)) :
    familyPageMap model.family (model.nu.functor.map f) 2 (11,136,136) (targetNuLabel model X 11 136 0 x) =
      targetNuLabel model Y 11 136 0 (model.classical.pageMap f 2 (11,136) x) := by
  have h := model.comparison.nu_natural X Y f 0 11 136 0 x
  change familyPageMap model.family (model.nu.functor.map f) 2 (11,136,136)
    (familyPageMap model.family (SyntheticCategory.biShift_zero.hom.app _) 2 (11,136,136) (model.comparison.nuE2 X 0 11 136 0 x)) = _
  calc
    _ = familyPageMap model.family (SyntheticCategory.biShift_zero.hom.app _≫model.nu.functor.map f) 2 (11,136,136) (model.comparison.nuE2 X 0 11 136 0 x) :=
      ConcreteCategory.congr_hom (family_page_comp _ _ 2 (11,136,136)) _
    _ = familyPageMap model.family ((SyntheticCategory.biShift (0,0)).map (model.nu.functor.map f)≫SyntheticCategory.biShift_zero.hom.app _) 2 (11,136,136) (model.comparison.nuE2 X 0 11 136 0 x) := by
      exact congrArg (fun g => familyPageMap model.family g 2 (11,136,136) (model.comparison.nuE2 X 0 11 136 0 x)) (SyntheticCategory.biShift_zero.hom.naturality (model.nu.functor.map f)).symm
    _ = familyPageMap model.family (SyntheticCategory.biShift_zero.hom.app _) 2 (11,136,136)
        (familyPageMap model.family ((SyntheticCategory.biShift (0,0)).map (model.nu.functor.map f)) 2 (11,136,136) (model.comparison.nuE2 X 0 11 136 0 x)) :=
      (ConcreteCategory.congr_hom (family_page_comp _ _ 2 (11,136,136)) _).symm
    _ = _ := congrArg (fun y => familyPageMap model.family (SyntheticCategory.biShift_zero.hom.app _) 2 (11,136,136) y) h
private theorem finite_target_natural_11
    (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (q : ℕ) (x : (model.classical.obj (X.obj model.auxiliary)).Page 2 (11,136)) :
    familyPageMap model.family (XModLambdaN.map (model.nu.functor.map f) q) 2 (11,136,136)
      (finiteTargetLabel model X q 11 136 0 x) =
      finiteTargetLabel model Y q 11 136 0 (model.classical.pageMap f 2 (11,136) x) := by
  change familyPageMap model.family (XModLambdaN.map (model.nu.functor.map f) q) 2 (11,136,136)
    (familyPageMap model.family (XModLambdaN.incl _ q) 2 (11,136,136) (targetNuLabel model X 11 136 0 x)) = _
  calc
    _ = familyPageMap model.family (XModLambdaN.incl _ q≫XModLambdaN.map (model.nu.functor.map f) q) 2 (11,136,136) (targetNuLabel model X 11 136 0 x) :=
      ConcreteCategory.congr_hom (family_page_comp _ _ 2 (11,136,136)) _
    _ = familyPageMap model.family (model.nu.functor.map f≫XModLambdaN.incl _ q) 2 (11,136,136) (targetNuLabel model X 11 136 0 x) :=
      congrArg (fun g => familyPageMap model.family g 2 (11,136,136) (targetNuLabel model X 11 136 0 x)) (XModLambdaN.incl_naturality (model.nu.functor.map f) q).symm
    _ = familyPageMap model.family (XModLambdaN.incl _ q) 2 (11,136,136)
        (familyPageMap model.family (model.nu.functor.map f) 2 (11,136,136) (targetNuLabel model X 11 136 0 x)) :=
      (ConcreteCategory.congr_hom (family_page_comp _ _ 2 (11,136,136)) _).symm
    _ = _ := congrArg (fun y => familyPageMap model.family (XModLambdaN.incl _ q) 2 (11,136,136) y) (target_nu_natural_11 X Y f x)
private theorem zero_exponent_source_infinity_11
    (X : ClassicalObject) (n : ℕ) (hn : n=0)
    (q : ℕ) (hq : 0<q) (x : (model.classical.obj (X.obj model.auxiliary)).Page 2 (11,136))
    (hx : x∈cycles model X q (11,136)) :
    ∃ e : ((model.family.obj ((SyntheticObject.quotient q (.shift (0,n) (.nu X))).obj model.nu model.auxiliary)).sequence.ssData (11,(136-11)+11,136+n)).eInfty,
      HasInfinityRepresentative _ 2 (11,(136-11)+11,136+n)
        (regradeE2 (A:=model.family.obj ((SyntheticObject.quotient q (.shift (0,n) (.nu X))).obj model.nu model.auxiliary)) (i:=(11,136,136+(n:ℤ)-(0:ℕ))) (j:=(11,136,136+(n:ℤ))) (by ext <;> simp) (finiteNuLabel model X q n 11 136 0 x)) e := by
  subst n
  exact zero_shift_finite_infinity_exists_11 X q hq x hx
private theorem normalized_zero_source_infinity_11
    (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary) (he : normalizedExponent model.classicalTower f=0)
    (q : ℕ) (hq : 0<q) (x : (model.classical.obj (X.obj model.auxiliary)).Page 2 (11,136))
    (hx : x∈cycles model X q (11,136)) :
    ∃ e : ((model.family.obj ((SyntheticObject.quotient q (extensionSourceObject model X Y f)).obj model.nu model.auxiliary)).sequence.ssData (11,(136-11)+11,136+normalizedExponent model.classicalTower f)).eInfty,
      HasInfinityRepresentative _ 2 (11,(136-11)+11,136+normalizedExponent model.classicalTower f)
        (finiteSourceForExtension model X Y f q 11 136 x) e := by
  exact zero_exponent_source_infinity_11 X _ he q hq x hx
private theorem zero_exponent_map_label_11
    (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (n : ℕ) (hn : n=0)
    (g : (SyntheticCategory.biShift (0,n)).obj (model.nu.functor.obj (X.obj model.auxiliary)) ⟶ model.nu.functor.obj (Y.obj model.auxiliary))
    (hf : lambdaToPositivePow n (model.nu.functor.obj (X.obj model.auxiliary))≫g=model.nu.functor.map f)
    (q : ℕ) (x : (model.classical.obj (X.obj model.auxiliary)).Page 2 (11,136)) :
    HEq (familyPageMap model.family (XModLambdaN.map g q) 2 (11,(136-11)+11,136+n)
      (regradeE2 (A:=model.family.obj ((SyntheticObject.quotient q (.shift (0,n) (.nu X))).obj model.nu model.auxiliary)) (i:=(11,136,136+(n:ℤ)-(0:ℕ))) (j:=(11,136,136+(n:ℤ))) (by ext <;> simp) (finiteNuLabel model X q n 11 136 0 x)))
      (finiteTargetLabel model Y q 11 136 0 (model.classical.pageMap f 2 (11,136) x)) := by
  subst n
  have hfact : SyntheticCategory.biShift_zero.inv.app (model.nu.functor.obj (X.obj model.auxiliary))≫g=model.nu.functor.map f :=
    (congrArg (fun u => u≫g) (lambda_to_positive_zero _)).symm.trans hf
  have hg : g=SyntheticCategory.biShift_zero.hom.app (model.nu.functor.obj (X.obj model.auxiliary))≫model.nu.functor.map f := by
    calc
      _ = SyntheticCategory.biShift_zero.hom.app (model.nu.functor.obj (X.obj model.auxiliary))≫
        SyntheticCategory.biShift_zero.inv.app (model.nu.functor.obj (X.obj model.auxiliary))≫g := by simp
      _ = _ := congrArg (fun u => SyntheticCategory.biShift_zero.hom.app (model.nu.functor.obj (X.obj model.auxiliary))≫u) hfact
  apply heq_of_eq
  change familyPageMap model.family (XModLambdaN.map g q) 2 (11,136,136) (finiteNuLabel model X q 0 11 136 0 x) = _
  calc
    _ = familyPageMap model.family (XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app (model.nu.functor.obj (X.obj model.auxiliary))≫model.nu.functor.map f) q) 2 (11,136,136) (finiteNuLabel model X q 0 11 136 0 x) :=
      congrArg (fun u => familyPageMap model.family (XModLambdaN.map u q) 2 (11,136,136) (finiteNuLabel model X q 0 11 136 0 x)) hg
    _ = familyPageMap model.family (XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app (model.nu.functor.obj (X.obj model.auxiliary))) q≫XModLambdaN.map (model.nu.functor.map f) q) 2 (11,136,136) (finiteNuLabel model X q 0 11 136 0 x) :=
      congrArg (fun u => familyPageMap model.family u 2 (11,136,136) (finiteNuLabel model X q 0 11 136 0 x)) (model.quotients.functoriality.map_comp _ _ q)
    _ = familyPageMap model.family (XModLambdaN.map (model.nu.functor.map f) q) 2 (11,136,136)
        (familyPageMap model.family (XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app (model.nu.functor.obj (X.obj model.auxiliary))) q) 2 (11,136,136) (finiteNuLabel model X q 0 11 136 0 x)) :=
      (ConcreteCategory.congr_hom (family_page_comp _ _ 2 (11,136,136)) _).symm
    _ = familyPageMap model.family (XModLambdaN.map (model.nu.functor.map f) q) 2 (11,136,136) (finiteTargetLabel model X q 11 136 0 x) :=
      congrArg (fun z => familyPageMap model.family (XModLambdaN.map (model.nu.functor.map f) q) 2 (11,136,136) z) (zero_shift_quotient_label_11 X q x)
    _ = _ := finite_target_natural_11 X Y f q x
private theorem normalized_zero_map_label_11
    (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (he : normalizedExponent model.classicalTower f=0) (q : ℕ) (x : (model.classical.obj (X.obj model.auxiliary)).Page 2 (11,136)) :
    HEq (familyPageMap model.family (finiteExtensionMap model X Y f q) 2 (11,(136-11)+11,136+normalizedExponent model.classicalTower f)
      (finiteSourceForExtension model X Y f q 11 136 x))
      (finiteTargetLabel model Y q 11 136 0 (model.classical.pageMap f 2 (11,136) x)) := by
  exact zero_exponent_map_label_11 X Y f _ he (model.normalizedMap X Y f).map (model.normalizedMap X Y f).factorization q x
private theorem zero_exponent_target_label_11
    (Y : ClassicalObject) (q n : ℕ) (hn : n=0) (y : (model.classical.obj (Y.obj model.auxiliary)).Page 2 (11,136)) :
    HEq (regradeE2 (A:=model.family.obj ((SyntheticObject.quotient q (.nu Y)).obj model.nu model.auxiliary))
      (i:=(11+0,136+0,(136+0)-((0-(n:ℤ)).toNat:ℤ)))
      (j:=(11+0,(136-11)+(11+0),136+n))
      (by subst n; decide) (finiteTargetLabel model Y q (11+0) (136+0) (0-(n:ℤ)).toNat y))
      (finiteTargetLabel model Y q 11 136 0 y) := by
  subst n
  rfl

end
end KIP126.Main.Internal.NuThree
