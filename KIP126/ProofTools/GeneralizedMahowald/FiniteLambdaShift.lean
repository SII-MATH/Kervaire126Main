module
import all KIP126.ProofTools.GeneralizedMahowald.HSource
import all KIP126.ProofTools.GeneralizedLeibniz.DivisionLabels

/-!
# Finite λ classes under suspension

These private lemmas compare quotient shift isomorphisms on actual sphere
representatives. Agreement on the quotient inclusion suffices: the remaining
cofiber boundary has weight −q−1 and vanishes in the target q-window. This gives
compatibility of finite λ classes with inverse suspension without requiring a
new compatibility assumption for the quotient shift isomorphisms.
-/

@[expose] section
namespace KIP126.ProofTools.Internal.Mahowald
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard KIP126.Literature
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Leibniz
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 3000000

private def shiftCommIso (a b : ℤ × ℤ) :
    SyntheticCategory.biShift (Syn:=SyntheticSpectrum) a ⋙ SyntheticCategory.biShift b ≅
      SyntheticCategory.biShift b ⋙ SyntheticCategory.biShift a :=
  biShiftAddIso a b (a+b) rfl ≪≫ (biShiftAddIso b a (a+b) (add_comm b a)).symm

private theorem shiftCommIso_eq (a b c : ℤ × ℤ) (h : a+b=c) :
    shiftCommIso a b = biShiftAddIso a b c h ≪≫
      (biShiftAddIso b a c ((add_comm b a).trans h)).symm := by
  subst c
  rfl

private theorem shift_comm_add (a b c d : ℤ × ℤ) (hbc : b+c=d) (X : SyntheticSpectrum) :
    (shiftCommIso a d).hom.app X =
      (biShiftAddIso b c d hbc).inv.app ((SyntheticCategory.biShift a).obj X) ≫
        (SyntheticCategory.biShift c).map ((shiftCommIso a b).hom.app X) ≫
        (shiftCommIso a c).hom.app ((SyntheticCategory.biShift b).obj X) ≫
        (SyntheticCategory.biShift a).map ((biShiftAddIso b c d hbc).hom.app X) := by
  let coh := model.quotients.coherence
  apply (cancel_mono ((biShiftAddIso d a (a+d) (add_comm d a)).hom.app X)).mp
  simp only [shiftCommIso,Iso.trans_hom,Iso.symm_hom,NatTrans.comp_app,Category.assoc]
  have h₁ := coh.associativity b c a d (a+c) (a+d) hbc (add_comm c a)
    (add_comm d a) (by rw [←hbc]; abel) X
  have h₂ := coh.associativity b a c (a+b) (a+c) (a+d) (add_comm b a) rfl
    (by rw [←hbc]; abel) (by rw [←hbc]; abel) X
  have h₃ := coh.associativity a b c (a+b) d (a+d) rfl hbc
    (by rw [←hbc]; abel) rfl X
  rw [h₁]
  simp only [Functor.map_comp,Category.assoc,Iso.inv_hom_id_app_assoc]
  rw [←h₂]
  rw [←Category.assoc ((SyntheticCategory.biShift c).map ((biShiftAddIso b a (a+b) (add_comm b a)).inv.app X)),
    ←Functor.map_comp,Iso.inv_hom_id_app (biShiftAddIso b a (a+b) (add_comm b a)) X,
    CategoryTheory.Functor.map_id,Category.id_comp]
  rw [h₃]
  simp

private theorem lambdaPow_shift_comm (a : ℤ × ℤ) (n : ℕ) (X : SyntheticSpectrum) :
    lambdaPow n ((SyntheticCategory.biShift a).obj X) =
      (shiftCommIso a (lambdaDegree n)).hom.app X ≫
        (SyntheticCategory.biShift a).map (lambdaPow n X) := by
  induction n generalizing X with
  | zero =>
    change SyntheticCategory.biShift_zero.hom.app ((SyntheticCategory.biShift a).obj X) =
      (shiftCommIso a 0).hom.app X ≫
        (SyntheticCategory.biShift a).map (SyntheticCategory.biShift_zero.hom.app X)
    rw [shiftCommIso_eq a 0 a (add_zero a)]
    simp only [Iso.trans_hom,Iso.symm_hom,NatTrans.comp_app]
    rw [model.quotients.coherence.right_unit]
    have hl := model.quotients.coherence.left_unit a X
    rw [←hl]
    simp
  | succ n ih =>
    have h1 : (shiftCommIso a (0,-1)).hom.app X ≫
        (SyntheticCategory.biShift a).map (SyntheticCategory.lam.app X) =
        SyntheticCategory.lam.app ((SyntheticCategory.biShift a).obj X) := by
      simpa [shiftCommIso,Category.assoc] using (model.quotients.coherence.lambda_comm a X).symm
    apply (cancel_epi ((lambdaShiftAddIso 1 n (n+1) (by omega)).hom.app
      ((SyntheticCategory.biShift a).obj X))).mp
    rw [lambdaPow_succ_comparison]
    rw [shift_comm_add a (lambdaDegree 1) (lambdaDegree n) (lambdaDegree (n+1))
      (by ext <;> simp [lambdaDegree,Nat.cast_add]) X]
    simp only [lambdaShiftAddIso,Category.assoc,Iso.hom_inv_id_app_assoc]
    rw [←Functor.map_comp]
    erw [lambdaPow_succ_comparison]
    rw [Functor.map_comp]
    have hn := (shiftCommIso a (lambdaDegree n)).hom.naturality (SyntheticCategory.lam.app X)
    have hn' := congrArg (fun h => h ≫ (SyntheticCategory.biShift a).map (lambdaPow n X)) hn
    simp only [Functor.comp_map,Category.assoc] at hn'
    dsimp only [lambdaDegree,Functor.id_obj] at hn' ⊢
    erw [←hn']
    rw [←Category.assoc,←Functor.map_comp]
    erw [h1,ih]
    rfl

private theorem finite_lambda_maps_equal_on_spheres
    (X Y : ClassicalObject) (q d : ℕ) (hdq : d < q)
    (f g : (SyntheticCategory.biShift (0,-(d:ℤ))).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (q-d)) ⟶
      XModLambdaN (model.nu.functor.obj (Y.obj model.auxiliary)) q)
    (hfg : (SyntheticCategory.biShift (0,-(d:ℤ))).map (XModLambdaN.incl _ (q-d)) ≫ f =
      (SyntheticCategory.biShift (0,-(d:ℤ))).map (XModLambdaN.incl _ (q-d)) ≫ g) :
    ∀ (m w : ℤ) (c : BiHom m w ((SyntheticCategory.biShift (0,-(d:ℤ))).obj
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (q-d)))), c ≫ f = c ≫ g := by
  letI := model.exactness.shiftCommShift (0,-(d:ℤ))
  letI := model.exactness.shiftExact (0,-(d:ℤ))
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(d:ℤ))
  let V := model.nu.functor.obj (X.obj model.auxiliary)
  let T := XModLambdaN.cofiberTriangle V (q-d)
  have hzero : (F.mapTriangle.obj T).mor₂ ≫ (f-g) = 0 := by
    change F.map (XModLambdaN.incl V (q-d)) ≫ (f-g) = 0
    rw [Preadditive.comp_sub,hfg,sub_self]
  obtain ⟨z,hz⟩ := Triangle.yoneda_exact₃ (F.mapTriangle.obj T)
    (F.map_distinguished T (XModLambdaN.cofiberTriangle_distinguished V (q-d))) (f-g) hzero
  intro m w c
  let ε : (F.obj ((SyntheticCategory.biShift (0,-((q-d:ℕ):ℤ))).obj V))⟦(1:ℤ)⟧ ≅
      (SyntheticCategory.biShift (0,-(q:ℤ)-1)).obj
        (model.nu.functor.obj ((ClassicalObject.shift 1 X).obj model.auxiliary)) :=
    (shiftFunctor SyntheticSpectrum (1:ℤ)).mapIso
      ((lambdaShiftAddIso (q-d) d q (Nat.sub_add_cancel (by omega))).app V) ≪≫
      (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).symm.app _ ≪≫
      (SyntheticCategory.biShift_comp (0,-(q:ℤ)) (1,0)).app V ≪≫
      eqToIso (congrArg (fun p => (SyntheticCategory.biShift p).obj V)
        (show (0,-(q:ℤ))+(1,0)=(1,1)+(0,-(q:ℤ)-1) by ext <;> simp)) ≪≫
      (SyntheticCategory.biShift_comp (1,1) (0,-(q:ℤ)-1)).symm.app V ≪≫
      (SyntheticCategory.biShift (0,-(q:ℤ)-1)).mapIso (model.nu.suspensionIso _).symm
  have h := negative_shift_nu_to_quotient_zero (.shift 1 X) Y q (by omega) m w
    ((c ≫ (F.mapTriangle.obj T).mor₃) ≫ ε.hom) (ε.inv ≫ z)
  have hcz : (c ≫ (F.mapTriangle.obj T).mor₃) ≫ z = 0 := by
    simpa only [Category.assoc,Iso.hom_inv_id_assoc] using h
  apply sub_eq_zero.mp
  rw [←Preadditive.comp_sub,hz,←Category.assoc]
  exact hcz

private theorem quotient_shift_lambda_on_spheres
    (X : ClassicalObject) (δ : ℤ × ℤ) (q d : ℕ) (hd : 0 < d) (hdq : d < q)
    (εn : XModLambdaN ((SyntheticCategory.biShift δ).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) (q-d) ≅
      (SyntheticCategory.biShift δ).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (q-d)))
    (εq : XModLambdaN ((SyntheticCategory.biShift δ).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) q ≅
      (SyntheticCategory.biShift δ).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
    (hεn : XModLambdaN.incl _ (q-d) ≫ εn.hom =
      (SyntheticCategory.biShift δ).map (XModLambdaN.incl _ (q-d)))
    (hεq : XModLambdaN.incl _ q ≫ εq.hom =
      (SyntheticCategory.biShift δ).map (XModLambdaN.incl _ q))
    (m w : ℤ) (c : BiHom m w ((SyntheticCategory.biShift (0,-(d:ℤ))).obj
      ((SyntheticCategory.biShift δ).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (q-d))))) :
    c ≫ (SyntheticCategory.biShift (0,-(d:ℤ))).map εn.inv ≫
        ((model.quotients.tower _).triangle hd hdq).lambdaMap ≫ εq.hom =
      c ≫ (shiftCommIso δ (0,-(d:ℤ))).hom.app _ ≫
        (SyntheticCategory.biShift δ).map ((model.quotients.tower _).triangle hd hdq).lambdaMap := by
  let A := model.nu.functor.obj (X.obj model.auxiliary)
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) δ
  let K := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(d:ℤ))
  let L := ((model.quotients.tower A).triangle hd hdq).lambdaMap
  let L' := ((model.quotients.tower (F.obj A)).triangle hd hdq).lambdaMap
  let ff := SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) δ
  let C := shiftCommIso δ (0,-(d:ℤ))
  let v : K.obj (XModLambdaN A (q-d)) ⟶ XModLambdaN A q :=
    ff.preimage (C.inv.app _ ≫ K.map εn.inv ≫ L' ≫ εq.hom)
  have hv : F.map v = C.inv.app _ ≫ K.map εn.inv ≫ L' ≫ εq.hom := ff.map_preimage _
  have hbase : K.map (XModLambdaN.incl A (q-d)) ≫ v =
      K.map (XModLambdaN.incl A (q-d)) ≫ L := by
    apply ff.map_injective
    rw [Functor.map_comp,Functor.map_comp,hv]
    have hn := C.inv.naturality (XModLambdaN.incl A (q-d))
    change F.map (K.map (XModLambdaN.incl A (q-d))) ≫ C.inv.app _ =
      C.inv.app A ≫ K.map (F.map (XModLambdaN.incl A (q-d))) at hn
    rw [←Category.assoc,hn,Category.assoc,←hεn,Functor.map_comp,Category.assoc]
    rw [←Category.assoc (K.map εn.hom),←Functor.map_comp,Iso.hom_inv_id,
      CategoryTheory.Functor.map_id,Category.id_comp]
    rw [←Category.assoc (K.map (XModLambdaN.incl (F.obj A) (q-d))),
      ((model.quotients.tower (F.obj A)).triangle hd hdq).lambda_quotient,
      Category.assoc,hεq]
    have hc := lambdaPow_shift_comm δ d A
    change lambdaPow d (F.obj A) = C.hom.app A ≫ F.map (lambdaPow d A) at hc
    rw [←Category.assoc,hc]
    simp only [Iso.inv_hom_id_app_assoc]
    rw [←Functor.map_comp,←Functor.map_comp]
    exact congrArg F.map (((model.quotients.tower A).triangle hd hdq).lambda_quotient.symm)
  have hb := finite_lambda_maps_equal_on_spheres X X q d hdq v L hbase
  have hh := shift_preserves_sphere_congruence _ _ δ v L hb m w (c ≫ C.hom.app _)
  rw [hv] at hh
  simpa only [C,F,K,L,L',Category.assoc,Iso.hom_inv_id_app_assoc] using hh

private theorem shift_hom_swap (p b c pb pc total : ℤ × ℤ)
    (hpb : p+b=pb) (hpc : p+c=pc) (hbc : pb+c=total) (hcb : pc+b=total)
    {A : SyntheticSpectrum} (α : BiHom p.1 p.2 A) :
    (biShiftAddIso pb c total hbc).inv.app S_0_0 ≫
        (SyntheticCategory.biShift c).map
          ((biShiftAddIso p b pb hpb).inv.app S_0_0 ≫ (SyntheticCategory.biShift b).map α) ≫
        (shiftCommIso b c).hom.app A =
      (biShiftAddIso pc b total hcb).inv.app S_0_0 ≫
        (SyntheticCategory.biShift b).map
          ((biShiftAddIso p c pc hpc).inv.app S_0_0 ≫ (SyntheticCategory.biShift c).map α) := by
  have ht : p+(b+c)=total := by rw [←add_assoc,hpb,hbc]
  have hL := shift_hom_associativity model.quotients.coherence p b c pb (b+c) total
    hpb rfl hbc ht α
  have hR := shift_hom_associativity model.quotients.coherence p c b pc (b+c) total
    hpc (add_comm c b) hcb ht α
  rw [←Category.assoc,←hL]
  simp only [shiftCommIso,Iso.trans_hom,Iso.symm_hom,NatTrans.comp_app,Category.assoc,
    Iso.inv_hom_id_app_assoc]
  exact hR

private theorem shift_hom_comp (δ p : ℤ × ℤ) {A B : SyntheticSpectrum}
    (a : BiHom p.1 p.2 A) (f : A ⟶ B) :
    shiftHomotopyClass δ p (a≫f) =
      shiftHomotopyClass δ p a ≫ (SyntheticCategory.biShift δ).map f := by
  simp [shiftHomotopyClass,Functor.map_comp,Category.assoc]

private theorem shift_regrade (n u k l m w : ℤ) (hm : n+k=m) (hw : u+l=w)
    (A : SyntheticSpectrum) (a : BiHom n u A) :
    homotopyRegrade hm hw (shiftHomotopyClass (k,l) (n,u) a) =
      (biShiftAddIso (n,u) (k,l) (m,w) (Prod.ext hm hw)).inv.app S_0_0 ≫
        (SyntheticCategory.biShift (k,l)).map a := by
  subst m
  subst w
  simp [homotopyRegrade,shiftHomotopyClass,biShiftAddIso]

private theorem shifted_finite_lambda_class
    (X : ClassicalObject) (q d : ℕ) (hd : 0 < d) (hdq : d < q) (s t : ℤ)
    (εn : XModLambdaN ((SyntheticCategory.biShift (1,1)).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) (q-d) ≅
      (SyntheticCategory.biShift (1,1)).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (q-d)))
    (εq : XModLambdaN ((SyntheticCategory.biShift (1,1)).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) q ≅
      (SyntheticCategory.biShift (1,1)).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
    (hεn : XModLambdaN.incl _ (q-d) ≫ εn.hom =
      (SyntheticCategory.biShift (1,1)).map (XModLambdaN.incl _ (q-d)))
    (hεq : XModLambdaN.incl _ q ≫ εq.hom =
      (SyntheticCategory.biShift (1,1)).map (XModLambdaN.incl _ q))
    (b : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (q-d))) :
    homotopyRegrade (m' := t+1-s) (w' := t+1-d) (by simp; omega) (by simp; omega)
        (shiftHomotopyClass (1,1) (t-s,t-d) (finiteLambdaClass X q d hd hdq s t b)) ≫ εq.inv =
      homotopyRegrade (by simp) (by simp [sub_eq_add_neg])
          (shiftHomotopyClass (0,-(d:ℤ)) (t+1-s,t+1)
            (homotopyRegrade (by simp; omega) rfl (shiftHomotopyClass (1,1) (t-s,t) b) ≫ εn.inv)) ≫
        ((model.quotients.tower _).triangle hd hdq).lambdaMap := by
  apply (cancel_mono εq.hom).mp
  simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id]
  unfold finiteLambdaClass
  rw [shift_hom_comp,regrade_comp,shift_hom_comp,regrade_comp]
  simp only [Category.assoc]
  rw [quotient_shift_lambda_on_spheres X (1,1) q d hd hdq εn εq hεn hεq]
  rw [shift_regrade,shift_regrade,shift_regrade,shift_regrade]
  rw [←Category.assoc]
  apply congrArg (fun z => z ≫ (SyntheticCategory.biShift (1,1)).map
    ((model.quotients.tower _).triangle hd hdq).lambdaMap)
  simpa only [Category.assoc] using (shift_hom_swap (t-s,t) (1,1) (0,-(d:ℤ)) (t+1-s,t+1) (t-s,t-d) (t+1-s,t+1-d)
    (by ext <;> dsimp; omega) (by ext <;> dsimp <;> omega)
    (by ext <;> dsimp <;> omega) (by ext <;> dsimp <;> omega) b).symm

private theorem suspension_finite_lambda_unshift
    (X : ClassicalObject) (q d : ℕ) (hd : 0 < d) (hdq : d < q) (s t : ℤ)
    (εn : XModLambdaN ((SyntheticCategory.biShift (1,1)).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) (q-d) ≅
      (SyntheticCategory.biShift (1,1)).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (q-d)))
    (εq : XModLambdaN ((SyntheticCategory.biShift (1,1)).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) q ≅
      (SyntheticCategory.biShift (1,1)).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
    (hεn : XModLambdaN.incl _ (q-d) ≫ εn.hom =
      (SyntheticCategory.biShift (1,1)).map (XModLambdaN.incl _ (q-d)))
    (hεq : XModLambdaN.incl _ q ≫ εq.hom =
      (SyntheticCategory.biShift (1,1)).map (XModLambdaN.incl _ q))
    (a : BiHom (t+1-s) (t+1)
      (XModLambdaN (model.nu.functor.obj ((ClassicalObject.shift 1 X).obj model.auxiliary)) (q-d))) :
    quotientUnshift X (1,1) (t-s,t-d) q εq
      (homotopyRegrade (by simp; omega) (by simp; omega)
        (finiteLambdaClass (.shift 1 X) q d hd hdq s (t+1) a ≫
          XModLambdaN.map (model.nu.suspensionIso (X.obj model.auxiliary)).hom q)) =
      finiteLambdaClass X q d hd hdq s t
        (quotientUnshift X (1,1) (t-s,t) (q-d) εn
          (homotopyRegrade (by simp; omega) rfl
            (a ≫ XModLambdaN.map (model.nu.suspensionIso (X.obj model.auxiliary)).hom (q-d)))) := by
  let b := quotientUnshift X (1,1) (t-s,t) (q-d) εn
    (homotopyRegrade (by simp; omega) rfl
      (a ≫ XModLambdaN.map (model.nu.suspensionIso (X.obj model.auxiliary)).hom (q-d)))
  have hb : homotopyRegrade (m' := t+1-s) (by simp; omega) rfl
      (shiftHomotopyClass (1,1) (t-s,t) b) ≫ εn.inv =
      a ≫ XModLambdaN.map (model.nu.suspensionIso (X.obj model.auxiliary)).hom (q-d) := by
    dsimp only [b]
    rw [←regrade_comp,shift_quotient_unshift,homotopy_regrade_inverse]
  have hnatural : finiteLambdaClass (.shift 1 X) q d hd hdq s (t+1) a ≫
        XModLambdaN.map (model.nu.suspensionIso (X.obj model.auxiliary)).hom q =
      homotopyRegrade (m' := t+1-s) (w' := t+1-d) (by simp) (by simp [sub_eq_add_neg])
        (shiftHomotopyClass (0,-(d:ℤ)) (t+1-s,t+1)
          (a ≫ XModLambdaN.map (model.nu.suspensionIso (X.obj model.auxiliary)).hom (q-d))) ≫
        ((model.quotients.tower _).triangle hd hdq).lambdaMap := by
    unfold finiteLambdaClass
    rw [shift_hom_comp,regrade_comp]
    simp only [Category.assoc]
    erw [←(model.quotients.natural (model.nu.suspensionIso (X.obj model.auxiliary)).hom).lambda_naturality hd hdq]
  have hshift := shifted_finite_lambda_class X q d hd hdq s t εn εq hεn hεq b
  rw [hb] at hshift
  change quotientUnshift X (1,1) (t-s,t-d) q εq _ = finiteLambdaClass X q d hd hdq s t b
  rw [hnatural,←hshift,regrade_comp,homotopy_regrade_inverse,quotient_unshift_shift]

end
end KIP126.ProofTools.Internal.Mahowald
