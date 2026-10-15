module
public import KIP126.Main.SectionSeven.AlphaOne
import all KIP126.Main.Internal.Selected.LambdaOperations

/-! Shift coherence and lambda composition in AlphaOne/Existence.lean:
1493–1677,1816–1948, bbac1fc05843 (MIT). -/
@[expose] section
namespace KIP126.Main.Internal.AlphaOne
open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence KIP126.AdamsSynthetic
open KIP126.Core.SpectralSequence KIP126.Main.SectionSeven KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard (model SyntheticSpectrum)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
private def shiftSwap (a b : ℤ × ℤ) (A : SyntheticSpectrum) :
    (SyntheticCategory.biShift b).obj ((SyntheticCategory.biShift a).obj A) ≅
    (SyntheticCategory.biShift a).obj ((SyntheticCategory.biShift b).obj A) :=
  (biShiftAddIso a b (a+b) rfl).app A ≪≫
    ((biShiftAddIso b a (a+b) (add_comm _ _)).app A).symm


private theorem shiftSwap_add (coh : BiShiftCoherence SyntheticSpectrum)
    (a b c : ℤ × ℤ) (A : SyntheticSpectrum) :
    (shiftSwap a (b+c) A).hom ≫
      (SyntheticCategory.biShift a).map ((biShiftAddIso b c (b+c) rfl).inv.app A) =
    (biShiftAddIso b c (b+c) rfl).inv.app ((SyntheticCategory.biShift a).obj A) ≫
      (SyntheticCategory.biShift c).map (shiftSwap a b A).hom ≫
      (shiftSwap a c ((SyntheticCategory.biShift b).obj A)).hom := by
  classical
  let habc : (a+b)+c=a+(b+c) := add_assoc a b c
  let hbac : b+(a+c)=a+(b+c) := by abel
  have h₁ := coh.associativity a b c (a+b) (b+c) (a+(b+c)) rfl rfl habc rfl A
  have h₂ := coh.associativity b a c (a+b) (a+c) (a+(b+c))
    (add_comm _ _) rfl habc hbac A
  have h₃ := coh.associativity b c a (b+c) (a+c) (a+(b+c))
    rfl (add_comm _ _) (add_comm _ _) hbac A
  simp only [shiftSwap,Iso.trans_hom,Iso.symm_hom,Iso.app_hom,Iso.app_inv]
  rw [Functor.map_comp]
  apply (cancel_epi ((biShiftAddIso b c (b+c) rfl).hom.app
    ((SyntheticCategory.biShift a).obj A))).mp
  simp only [Category.assoc,Iso.hom_inv_id_app_assoc]
  rw [← Category.assoc,← h₁]
  simp only [Category.assoc]
  apply (cancel_epi ((SyntheticCategory.biShift c).map
    ((biShiftAddIso a b (a+b) rfl).hom.app A))).mpr
  -- Cancel the common left factor introduced by the first associativity square.
  apply (cancel_epi ((SyntheticCategory.biShift c).map
    ((biShiftAddIso b a (a+b) (add_comm _ _)).hom.app A))).mp
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app,CategoryTheory.Functor.map_id,Category.id_comp]
  rw [← Category.assoc,h₂]
  simp only [Category.assoc]
  apply (cancel_epi ((biShiftAddIso a c (a+c) rfl).hom.app
    ((SyntheticCategory.biShift b).obj A))).mpr
  apply (cancel_epi ((biShiftAddIso c a (a+c) (add_comm _ _)).hom.app
    ((SyntheticCategory.biShift b).obj A))).mp
  rw [← Category.assoc,← Category.assoc,← h₃]
  simp only [Category.assoc,
    Iso.hom_inv_id_app]
  erw [CategoryTheory.Category.id_comp,←Functor.map_comp,Iso.hom_inv_id_app,CategoryTheory.Functor.map_id]
  rfl


private theorem shiftSwap_add_eq (coh : BiShiftCoherence SyntheticSpectrum)
    (a b c d : ℤ × ℤ) (h : b+c=d) (A : SyntheticSpectrum) :
    (shiftSwap a d A).hom ≫
      (SyntheticCategory.biShift a).map ((biShiftAddIso b c d h).inv.app A) =
    (biShiftAddIso b c d h).inv.app ((SyntheticCategory.biShift a).obj A) ≫
      (SyntheticCategory.biShift c).map (shiftSwap a b A).hom ≫
      (shiftSwap a c ((SyntheticCategory.biShift b).obj A)).hom := by
  classical
  subst d
  exact shiftSwap_add coh a b c A


private theorem shiftSwap_natural (a b : ℤ × ℤ) {A B : SyntheticSpectrum} (f : A ⟶ B) :
    (SyntheticCategory.biShift b).map ((SyntheticCategory.biShift a).map f) ≫
      (shiftSwap a b B).hom =
    (shiftSwap a b A).hom ≫
      (SyntheticCategory.biShift a).map ((SyntheticCategory.biShift b).map f) := by
  classical
  exact ((biShiftAddIso a b (a+b) rfl) ≪≫
    (biShiftAddIso b a (a+b) (add_comm _ _)).symm).hom.naturality f


private theorem shiftSwap_hom_eq (a b d : ℤ × ℤ)
    (hab : a+b=d) (hba : b+a=d) (A : SyntheticSpectrum) :
    (shiftSwap a b A).hom =
      (biShiftAddIso a b d hab).hom.app A ≫ (biShiftAddIso b a d hba).inv.app A := by
  classical
  subst d
  rfl


private theorem lambda_pow_shift (coh : BiShiftCoherence SyntheticSpectrum)
    (n : ℕ) (a : ℤ × ℤ) (A : SyntheticSpectrum) :
    lambdaPow n ((SyntheticCategory.biShift a).obj A) =
      (shiftSwap a (KIP126.Synthetic.Context.lambdaDegree n) A).hom ≫
        (SyntheticCategory.biShift a).map (lambdaPow n A) := by
  classical
  induction n generalizing A with
  | zero =>
    change SyntheticCategory.biShift_zero.hom.app ((SyntheticCategory.biShift a).obj A) =
      (shiftSwap a 0 A).hom ≫
        (SyntheticCategory.biShift a).map (SyntheticCategory.biShift_zero.hom.app A)
    have h : SyntheticCategory.biShift_zero.hom.app ((SyntheticCategory.biShift a).obj A) =
        (biShiftAddIso a 0 a (add_zero a)).hom.app A ≫
          (biShiftAddIso 0 a a (zero_add a)).inv.app A ≫
            (SyntheticCategory.biShift a).map (SyntheticCategory.biShift_zero.hom.app A) := by
      rw [←coh.left_unit a A,Iso.inv_hom_id_app,Category.comp_id]
      exact (coh.right_unit a A).symm
    rw [shiftSwap_hom_eq a 0 a (add_zero a) (zero_add a),Category.assoc]
    exact h
  | succ n ih =>
    have h1 : lambdaPow 1 ((SyntheticCategory.biShift a).obj A) =
        (shiftSwap a (KIP126.Synthetic.Context.lambdaDegree 1) A).hom ≫
          (SyntheticCategory.biShift a).map (lambdaPow 1 A) := by
      rw [lambdaPow_one coh,lambdaPow_one coh]
      change SyntheticCategory.lam.app ((SyntheticCategory.biShift a).obj A) =
        (shiftSwap a (0,-1) A).hom ≫ (SyntheticCategory.biShift a).map (SyntheticCategory.lam.app A)
      rw [shiftSwap_hom_eq a (0,-1) (a+(0,-1)) rfl (add_comm _ _),Category.assoc]
      exact coh.lambda_comm a A
    have hn := shiftSwap_natural a (KIP126.Synthetic.Context.lambdaDegree n) (lambdaPow 1 A)
    have hh := shiftSwap_add_eq coh a (KIP126.Synthetic.Context.lambdaDegree 1) (KIP126.Synthetic.Context.lambdaDegree n)
      (KIP126.Synthetic.Context.lambdaDegree (n+1)) (by ext <;> simp [KIP126.Synthetic.Context.lambdaDegree]) A
    change (shiftSwap a (KIP126.Synthetic.Context.lambdaDegree (n+1)) A).hom ≫
        (SyntheticCategory.biShift a).map ((lambdaShiftAddIso 1 n (n+1) (by omega)).inv.app A) =
      (lambdaShiftAddIso 1 n (n+1) (by omega)).inv.app ((SyntheticCategory.biShift a).obj A) ≫
        (SyntheticCategory.biShift (KIP126.Synthetic.Context.lambdaDegree n)).map (shiftSwap a (KIP126.Synthetic.Context.lambdaDegree 1) A).hom ≫
        (shiftSwap a (KIP126.Synthetic.Context.lambdaDegree n) ((SyntheticCategory.biShift (KIP126.Synthetic.Context.lambdaDegree 1)).obj A)).hom at hh
    rw [lambdaPow_add coh 1 n (n+1) (by omega) ((SyntheticCategory.biShift a).obj A),
      lambdaPow_add coh 1 n (n+1) (by omega) A,h1,ih]
    simp only [Functor.map_comp,Category.assoc]
    rw [reassoc_of% hn]
    rw [reassoc_of% hh]
    rfl


private theorem shift_assoc_inv (coh : BiShiftCoherence SyntheticSpectrum)
    (a b c ab bc total : ℤ × ℤ) (hab : a+b=ab) (hbc : b+c=bc)
    (habc : ab+c=total) (habc' : a+bc=total) (A : SyntheticSpectrum) :
    (biShiftAddIso ab c total habc).inv.app A ≫
      (SyntheticCategory.biShift c).map ((biShiftAddIso a b ab hab).inv.app A) =
    (biShiftAddIso a bc total habc').inv.app A ≫
      (biShiftAddIso b c bc hbc).inv.app ((SyntheticCategory.biShift a).obj A) := by
  classical
  have he : ((SyntheticCategory.biShift c).mapIso ((biShiftAddIso a b ab hab).app A) ≪≫
      (biShiftAddIso ab c total habc).app A) =
    ((biShiftAddIso b c bc hbc).app ((SyntheticCategory.biShift a).obj A) ≪≫
      (biShiftAddIso a bc total habc').app A) :=
    Iso.ext (coh.associativity a b c ab bc total hab hbc habc habc' A)
  have hi := congrArg Iso.inv he
  exact hi


private theorem sphere_action_lambda_three
    (η : BiHom 1 2 (S_0_0 : SyntheticSpectrum))
    (a : BiHom 123 132 (XModLambdaN (S_0_0 : SyntheticSpectrum) 11)) :
    sphereAction (lambdaMultiply 3 η) a = lambdaMultiply 3 (sphereAction η a) := by
  classical
  let S := (S_0_0 : SyntheticSpectrum)
  have h₁ := shift_assoc_inv model.quotients.coherence (1,2) (123,132) (0,-3)
    (124,134) (123,129) (124,131) (by decide) (by decide) (by decide) (by decide) S
  have h₂ := shift_assoc_inv model.quotients.coherence (1,2) (0,-3) (123,132)
    (1,-1) (123,129) (124,131) (by decide) (by decide) (by decide) (by decide) S
  simp only [biShiftAddIso,Iso.trans_inv,eqToIso.inv,
    eqToHom_refl,Category.id_comp] at h₁ h₂
  have hp :
    (SyntheticCategory.biShift_comp (124,134) (0,-3)).inv.app S ≫
      lambdaPow 3 (Smn 124 134) ≫
      (SyntheticCategory.biShift_comp (1,2) (123,132)).inv.app S =
    (SyntheticCategory.biShift_comp (1,-1) (123,132)).inv.app S ≫
      (SyntheticCategory.biShift (123,132)).map
        ((SyntheticCategory.biShift_comp (1,2) (0,-3)).inv.app S) ≫
      (SyntheticCategory.biShift (123,132)).map (lambdaPow 3 (Smn 1 2)) := by
    rw [←lambdaPow_naturality]
    change (SyntheticCategory.biShift_comp (124,134) (0,-3)).inv.app S ≫
      (SyntheticCategory.biShift (0,-3)).map ((SyntheticCategory.biShift_comp (1,2) (123,132)).inv.app S) ≫
      lambdaPow 3 ((SyntheticCategory.biShift (123,132)).obj (Smn 1 2)) = _
    rw [lambda_pow_shift model.quotients.coherence 3 (123,132) (Smn 1 2)]
    dsimp only [shiftSwap,KIP126.Synthetic.Context.lambdaDegree]
    simp only [Iso.trans_hom,Iso.trans_inv,Iso.symm_hom,Iso.app_hom,Iso.app_inv,biShiftAddIso,eqToIso.hom,eqToIso.inv,eqToHom_refl,
      Category.comp_id,Category.id_comp]
    simp only [Category.assoc]
    erw [←Category.assoc ((SyntheticCategory.biShift_comp (124,134) (0,-3)).inv.app S)]
    erw [h₁]
    simp only [Category.assoc,Smn,S,Nat.cast_ofNat,Iso.inv_hom_id_app_assoc]
    simpa only [Category.assoc,Smn,S,Nat.cast_ofNat] using
      (congrArg (fun z => z ≫ (SyntheticCategory.biShift (123,132)).map (lambdaPow 3 (Smn 1 2))) h₂.symm)
  unfold sphereAction lambdaMultiply
  simp only [eqToHom_refl,Category.id_comp,Functor.map_comp,Category.assoc]
  simpa only [Category.assoc,S,Smn,Int.reduceAdd,Int.reduceSub,Nat.cast_ofNat] using
    (congrArg (fun z => z ≫ (SyntheticCategory.biShift (123,132)).map η ≫ a) hp).symm



private theorem lambda_six_one
    (c : BiHom 124 138 (S_0_0 : SyntheticSpectrum)) :
    lambdaMultiply 6 (lambdaMultiply 1 c) = lambdaMultiply 7 c := by
  classical
  have ha := shift_assoc_inv model.quotients.coherence (124,138) (0,-1) (0,-6)
    (124,137) (0,-7) (124,131) (by decide) (by decide) (by decide) (by decide) (S_0_0 : SyntheticSpectrum)
  simp only [biShiftAddIso, Iso.trans_inv, eqToIso.inv, eqToHom_refl, Category.id_comp] at ha
  unfold lambdaMultiply
  simp only [eqToHom_refl, Category.id_comp, Nat.cast_ofNat, Int.reduceSub]
  erw [← reassoc_of% (lambdaPow_naturality 6
    ((SyntheticCategory.biShift_comp (124,138) (0,-1)).inv.app (S_0_0 : SyntheticSpectrum)))]
  erw [← reassoc_of% (lambdaPow_naturality 6 (lambdaPow 1 (Smn 124 138)))]
  erw [← Category.assoc, ha]
  erw [lambdaPow_add model.quotients.coherence 1 6 7 (by decide) (Smn 124 138)]
  simp only [lambdaShiftAddIso, biShiftAddIso, KIP126.Synthetic.Context.lambdaDegree,
    Iso.trans_inv, eqToIso.inv, eqToHom_refl,
    Category.id_comp, Category.assoc]
  rfl


private theorem lambda_six_two
    (c : BiHom 124 139 (S_0_0 : SyntheticSpectrum)) :
    lambdaMultiply 6 (lambdaMultiply 2 c) = lambdaMultiply 8 c := by
  classical
  have ha := shift_assoc_inv model.quotients.coherence (124,139) (0,-2) (0,-6)
    (124,137) (0,-8) (124,131) (by decide) (by decide) (by decide) (by decide) (S_0_0 : SyntheticSpectrum)
  simp only [biShiftAddIso, Iso.trans_inv, eqToIso.inv, eqToHom_refl, Category.id_comp] at ha
  unfold lambdaMultiply
  simp only [eqToHom_refl, Category.id_comp, Nat.cast_ofNat, Int.reduceSub]
  erw [← reassoc_of% (lambdaPow_naturality 6
    ((SyntheticCategory.biShift_comp (124,139) (0,-2)).inv.app (S_0_0 : SyntheticSpectrum)))]
  erw [← reassoc_of% (lambdaPow_naturality 6 (lambdaPow 2 (Smn 124 139)))]
  erw [← Category.assoc, ha]
  erw [lambdaPow_add model.quotients.coherence 2 6 8 (by decide) (Smn 124 139)]
  simp only [lambdaShiftAddIso, biShiftAddIso, KIP126.Synthetic.Context.lambdaDegree,
    Iso.trans_inv, eqToIso.inv, eqToHom_refl,
    Category.id_comp, Category.assoc]
  rfl


private theorem lambda_one_one
    (c : BiHom 125 141 (S_0_0 : SyntheticSpectrum)) :
    lambdaMultiply 1 (lambdaMultiply 1 c) = lambdaMultiply 2 c := by
  classical
  have ha := shift_assoc_inv model.quotients.coherence (125,141) (0,-1) (0,-1)
    (125,140) (0,-2) (125,139) (by decide) (by decide) (by decide) (by decide) (S_0_0 : SyntheticSpectrum)
  simp only [biShiftAddIso, Iso.trans_inv, eqToIso.inv, eqToHom_refl, Category.id_comp] at ha
  unfold lambdaMultiply
  simp only [eqToHom_refl, Category.id_comp, Nat.cast_ofNat, Int.reduceSub]
  erw [← reassoc_of% (lambdaPow_naturality 1
    ((SyntheticCategory.biShift_comp (125,141) (0,-1)).inv.app (S_0_0 : SyntheticSpectrum)))]
  erw [← reassoc_of% (lambdaPow_naturality 1 (lambdaPow 1 (Smn 125 141)))]
  erw [← Category.assoc, ha]
  erw [lambdaPow_add model.quotients.coherence 1 1 2 (by decide) (Smn 125 141)]
  simp only [lambdaShiftAddIso, biShiftAddIso, KIP126.Synthetic.Context.lambdaDegree,
    Iso.trans_inv, eqToIso.inv, eqToHom_refl,
    Category.id_comp, Category.assoc]
  rfl


private theorem sphere_action_right_one
    (η : BiHom 1 2 (S_0_0 : SyntheticSpectrum))
    (c : BiHom 124 138 (S_0_0 : SyntheticSpectrum)) :
    sphereAction η (lambdaMultiply 1 c) = lambdaMultiply 1 (sphereAction η c) := by
  classical
  have ha := shift_assoc_inv model.quotients.coherence (1,2) (124,138) (0,-1)
    (125,140) (124,137) (125,139) (by decide) (by decide) (by decide) (by decide) (S_0_0 : SyntheticSpectrum)
  simp only [biShiftAddIso, Iso.trans_inv, eqToIso.inv, eqToHom_refl, Category.id_comp] at ha
  unfold sphereAction lambdaMultiply
  simp only [eqToHom_refl, Category.id_comp, Int.reduceAdd]
  erw [← reassoc_of% (lambdaPow_naturality 1
    ((SyntheticCategory.biShift_comp (1,2) (124,138)).inv.app (S_0_0 : SyntheticSpectrum)))]
  erw [← reassoc_of% (lambdaPow_naturality 1
    ((SyntheticCategory.biShift (124,138)).map η))]
  erw [reassoc_of% ha]
  erw [← reassoc_of% ((SyntheticCategory.biShift_comp (124,138) (0,-1)).inv.naturality η)]
  rfl


private theorem sphere_action_right_two
    (η : BiHom 1 2 (S_0_0 : SyntheticSpectrum))
    (c : BiHom 124 139 (S_0_0 : SyntheticSpectrum)) :
    sphereAction η (lambdaMultiply 2 c) = lambdaMultiply 2 (sphereAction η c) := by
  classical
  have ha := shift_assoc_inv model.quotients.coherence (1,2) (124,139) (0,-2)
    (125,141) (124,137) (125,139) (by decide) (by decide) (by decide) (by decide) (S_0_0 : SyntheticSpectrum)
  simp only [biShiftAddIso, Iso.trans_inv, eqToIso.inv, eqToHom_refl, Category.id_comp] at ha
  unfold sphereAction lambdaMultiply
  simp only [eqToHom_refl, Category.id_comp, Nat.cast_ofNat,
    Int.reduceSub, Int.reduceAdd]
  erw [← reassoc_of% (lambdaPow_naturality 2
    ((SyntheticCategory.biShift_comp (1,2) (124,139)).inv.app (S_0_0 : SyntheticSpectrum)))]
  erw [← reassoc_of% (lambdaPow_naturality 2
    ((SyntheticCategory.biShift (124,139)).map η))]
  erw [reassoc_of% ha]
  erw [← reassoc_of% ((SyntheticCategory.biShift_comp (124,139) (0,-2)).inv.naturality η)]
  rfl


private theorem sphere_action_right_two_as_ones
    (η : BiHom 1 2 (S_0_0 : SyntheticSpectrum)) (c : BiHom 124 139 (S_0_0 : SyntheticSpectrum)) :
    sphereAction η (lambdaMultiply 2 c) = lambdaMultiply 1 (lambdaMultiply 1 (sphereAction η c)) := by
  classical
  exact (sphere_action_right_two η c).trans (lambda_one_one (sphereAction η c)).symm


private theorem lambda_one_division_of_quotient_zero
    {X : SyntheticSpectrum} (m w : ℤ) (z : BiHom m (w-1) X) (hz : quotientClass 1 z=0) :
    ∃ b : BiHom m w X, lambdaMultiply 1 b=z := by
  classical
  obtain ⟨a,ha⟩ := (KIP126.Main.Internal.Selected.vanishesModLambda_iff_factors 1 z).mp hz
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-1)
  let e : F.obj (Smn m w : SyntheticSpectrum) ≅ Smn m (w-1) :=
    (SyntheticCategory.biShift_comp (m,w) (0,-1)).app S_0_0 ≪≫
      eqToIso (by congr 1; simp [sub_eq_add_neg])
  let b := (SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) (0,-1)).preimage (e.hom≫a)
  have hb : F.map b=e.hom≫a :=
    (SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) (0,-1)).map_preimage _
  refine ⟨b,?_⟩
  have he : lambdaMultiply 1 b=e.inv≫lambdaPow 1 (Smn m w)≫b := by
    unfold lambdaMultiply
    change eqToHom (by congr 1; simp) ≫ (SyntheticCategory.biShift_comp (m,w) (0,-1)).inv.app S_0_0 ≫
      lambdaPow 1 (Smn m w) ≫ b =
      (eqToHom (by congr 1; simp) ≫ (SyntheticCategory.biShift_comp (m,w) (0,-1)).inv.app S_0_0) ≫
      lambdaPow 1 (Smn m w) ≫ b
    exact (Category.assoc _ _ _).symm
  rw [he]
  rw [←lambdaPow_naturality 1 b]
  change e.inv≫F.map b≫lambdaPow 1 X=z
  rw [hb]
  simp only [Category.assoc,e.inv_hom_id_assoc]
  exact ha



end
end KIP126.Main.Internal.AlphaOne
end
