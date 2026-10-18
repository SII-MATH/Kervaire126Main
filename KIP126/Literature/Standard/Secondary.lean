module

public import KIP126.Literature.Standard
import KIP126.AdamsSynthetic.Standard.ClassicalSupport

/-! The two source-to-synthetic secondary-operation comparisons previously
left unfinished in Kervaire126 bbac1fc05843,
Main/Solution/StageInput.lean:281 and :289 (MIT; see the retained source LICENSE).
They are upstream Literature responsibilities, not proof obligations of the
paper's Main module. The second comparison retains the actual order-two
hypothesis for every theta, not just the selected theta_5. -/

@[expose] section
namespace KIP126.Literature.Standard
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.AdamsSynthetic
universe u w v
variable {Syn : Type w} [SyntheticCategory.{w,v} Syn]
open KIP126.AdamsSynthetic.Standard (SyntheticSpectrum model)
noncomputable section

/- a48 Main/AdamsSynthetic/Toda/Product.lean:23–183; MIT.
The existing coherent shifts suffice for the actual λ² product comparison. -/
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
private theorem secondary_star_product (coh : BiShiftCoherence Syn)
    (eta : BiHom 1 2 (S_0_0 : Syn)) (theta : BiHom 62 64 (S_0_0 : Syn)) :
    sphereProduct (lambdaMultiply 2 eta) theta = lambdaMultiply 2 (sphereProduct eta theta) := by
  let shiftSwap (a b : ℤ × ℤ) (A : Syn) :
      (SyntheticCategory.biShift b).obj ((SyntheticCategory.biShift a).obj A) ≅
      (SyntheticCategory.biShift a).obj ((SyntheticCategory.biShift b).obj A) :=
    (biShiftAddIso a b (a+b) rfl).app A ≪≫
      ((biShiftAddIso b a (a+b) (add_comm _ _)).app A).symm
  have shiftSwap_add (coh : BiShiftCoherence Syn)
      (a b c : ℤ × ℤ) (A : Syn) :
      (shiftSwap a (b+c) A).hom ≫
        (SyntheticCategory.biShift a).map ((biShiftAddIso b c (b+c) rfl).inv.app A) =
      (biShiftAddIso b c (b+c) rfl).inv.app ((SyntheticCategory.biShift a).obj A) ≫
        (SyntheticCategory.biShift c).map (shiftSwap a b A).hom ≫
        (shiftSwap a c ((SyntheticCategory.biShift b).obj A)).hom := by
    let habc : (a+b)+c=a+(b+c) := add_assoc a b c
    let hbac : b+(a+c)=a+(b+c) := by abel
    have h₁ := coh.associativity a b c (a+b) (b+c) (a+(b+c)) rfl rfl habc rfl A
    have h₂ := coh.associativity b a c (a+b) (a+c) (a+(b+c))
      (add_comm _ _) rfl habc hbac A
    have h₃ := coh.associativity b c a (b+c) (a+c) (a+(b+c))
      rfl (add_comm _ _) (add_comm _ _) hbac A
    simp (config := { congrConsts := false }) only [shiftSwap,Iso.trans_hom,Iso.symm_hom,Iso.app_hom,Iso.app_inv]
    rw [Functor.map_comp]
    apply (cancel_epi ((biShiftAddIso b c (b+c) rfl).hom.app
      ((SyntheticCategory.biShift a).obj A))).mp
    simp (config := { congrConsts := false }) only [Category.assoc,Iso.hom_inv_id_app_assoc]
    rw [← Category.assoc,← h₁]
    simp (config := { congrConsts := false }) only [Category.assoc]
    apply (cancel_epi ((SyntheticCategory.biShift c).map
      ((biShiftAddIso a b (a+b) rfl).hom.app A))).mpr
    -- Cancel the common left factor introduced by the first associativity square.
    apply (cancel_epi ((SyntheticCategory.biShift c).map
      ((biShiftAddIso b a (a+b) (add_comm _ _)).hom.app A))).mp
    simp (config := { congrConsts := false }) only [← Functor.map_comp_assoc, Iso.hom_inv_id_app,CategoryTheory.Functor.map_id,Category.id_comp]
    rw [← Category.assoc,h₂]
    simp (config := { congrConsts := false }) only [Category.assoc]
    apply (cancel_epi ((biShiftAddIso a c (a+c) rfl).hom.app
      ((SyntheticCategory.biShift b).obj A))).mpr
    apply (cancel_epi ((biShiftAddIso c a (a+c) (add_comm _ _)).hom.app
      ((SyntheticCategory.biShift b).obj A))).mp
    rw [← Category.assoc,← Category.assoc,← h₃]
    simp (config := { congrConsts := false }) only [Category.assoc,
      Iso.hom_inv_id_app]
    erw [CategoryTheory.Category.id_comp,←Functor.map_comp,Iso.hom_inv_id_app,CategoryTheory.Functor.map_id]
    rfl
  have shiftSwap_add_eq (coh : BiShiftCoherence Syn)
      (a b c d : ℤ × ℤ) (h : b+c=d) (A : Syn) :
      (shiftSwap a d A).hom ≫
        (SyntheticCategory.biShift a).map ((biShiftAddIso b c d h).inv.app A) =
      (biShiftAddIso b c d h).inv.app ((SyntheticCategory.biShift a).obj A) ≫
        (SyntheticCategory.biShift c).map (shiftSwap a b A).hom ≫
        (shiftSwap a c ((SyntheticCategory.biShift b).obj A)).hom := by
    subst d
    exact shiftSwap_add coh a b c A
  have shiftSwap_natural (a b : ℤ × ℤ) {A B : Syn} (f : A ⟶ B) :
      (SyntheticCategory.biShift b).map ((SyntheticCategory.biShift a).map f) ≫
        (shiftSwap a b B).hom =
      (shiftSwap a b A).hom ≫
        (SyntheticCategory.biShift a).map ((SyntheticCategory.biShift b).map f) := by
    exact ((biShiftAddIso a b (a+b) rfl) ≪≫
      (biShiftAddIso b a (a+b) (add_comm _ _)).symm).hom.naturality f
  have shiftSwap_hom_eq (a b d : ℤ × ℤ)
      (hab : a+b=d) (hba : b+a=d) (A : Syn) :
      (shiftSwap a b A).hom =
        (biShiftAddIso a b d hab).hom.app A ≫ (biShiftAddIso b a d hba).inv.app A := by
    subst d
    rfl
  have lambda_pow_shift (coh : BiShiftCoherence Syn)
      (n : ℕ) (a : ℤ × ℤ) (A : Syn) :
      lambdaPow n ((SyntheticCategory.biShift a).obj A) =
        (shiftSwap a (KIP126.Synthetic.Context.lambdaDegree n) A).hom ≫
          (SyntheticCategory.biShift a).map (lambdaPow n A) := by
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
      simp (config := { congrConsts := false }) only [Functor.map_comp,Category.assoc]
      rw [reassoc_of% hn]
      rw [reassoc_of% hh]
      rfl
  have shift_assoc_inv (coh : BiShiftCoherence Syn)
      (a b c ab bc total : ℤ × ℤ) (hab : a+b=ab) (hbc : b+c=bc)
      (habc : ab+c=total) (habc' : a+bc=total) (A : Syn) :
      (biShiftAddIso ab c total habc).inv.app A ≫
        (SyntheticCategory.biShift c).map ((biShiftAddIso a b ab hab).inv.app A) =
      (biShiftAddIso a bc total habc').inv.app A ≫
        (biShiftAddIso b c bc hbc).inv.app ((SyntheticCategory.biShift a).obj A) := by
    have he : ((SyntheticCategory.biShift c).mapIso ((biShiftAddIso a b ab hab).app A) ≪≫
        (biShiftAddIso ab c total habc).app A) =
      ((biShiftAddIso b c bc hbc).app ((SyntheticCategory.biShift a).obj A) ≪≫
        (biShiftAddIso a bc total habc').app A) :=
      Iso.ext (coh.associativity a b c ab bc total hab hbc habc habc' A)
    have hi := congrArg Iso.inv he
    exact hi
  have shuffle_lambda_left_two (coh : BiShiftCoherence Syn)
      (etaShuffle : BiHom 1 2 (S_0_0 : Syn))
      (a : BiHom 62 64 (S_0_0 : Syn)) :
      sphereAction (lambdaMultiply 2 etaShuffle) a = lambdaMultiply 2 (sphereAction etaShuffle a) := by
    let S := (S_0_0 : Syn)
    have h₁ := shift_assoc_inv coh (1,2) (62,64) (0,-2)
      (63,66) (62,62) (63,64) (by decide) (by decide) (by decide) (by decide) S
    have h₂ := shift_assoc_inv coh (1,2) (0,-2) (62,64)
      (1,0) (62,62) (63,64) (by decide) (by decide) (by decide) (by decide) S
    simp (config := { congrConsts := false }) only [biShiftAddIso,Iso.trans_inv,eqToIso.inv,
      eqToHom_refl,Category.id_comp] at h₁ h₂
    have hp :
      (SyntheticCategory.biShift_comp (63,66) (0,-2)).inv.app S ≫
        lambdaPow 2 (Smn 63 66) ≫
        (SyntheticCategory.biShift_comp (1,2) (62,64)).inv.app S =
      (SyntheticCategory.biShift_comp (1,0) (62,64)).inv.app S ≫
        (SyntheticCategory.biShift (62,64)).map
          ((SyntheticCategory.biShift_comp (1,2) (0,-2)).inv.app S) ≫
        (SyntheticCategory.biShift (62,64)).map (lambdaPow 2 (Smn 1 2)) := by
      rw [←lambdaPow_naturality]
      change (SyntheticCategory.biShift_comp (63,66) (0,-2)).inv.app S ≫
        (SyntheticCategory.biShift (0,-2)).map ((SyntheticCategory.biShift_comp (1,2) (62,64)).inv.app S) ≫
        lambdaPow 2 ((SyntheticCategory.biShift (62,64)).obj (Smn 1 2)) = _
      rw [lambda_pow_shift coh 2 (62,64) (Smn 1 2)]
      dsimp only [shiftSwap,KIP126.Synthetic.Context.lambdaDegree]
      simp (config := { congrConsts := false }) only [Iso.trans_hom,Iso.trans_inv,Iso.symm_hom,Iso.app_hom,Iso.app_inv,biShiftAddIso,eqToIso.hom,eqToIso.inv,eqToHom_refl,
        Category.comp_id,Category.id_comp]
      simp (config := { congrConsts := false }) only [Category.assoc]
      erw [←Category.assoc ((SyntheticCategory.biShift_comp (63,66) (0,-2)).inv.app S)]
      erw [h₁]
      simp (config := { congrConsts := false }) only [Category.assoc,Smn,S,Nat.cast_ofNat,Iso.inv_hom_id_app_assoc]
      simpa (config := { congrConsts := false }) only [Category.assoc,Smn,S,Nat.cast_ofNat,Nat.cast_one,Int.natCast_one] using
        (congrArg (fun z => z ≫ (SyntheticCategory.biShift (62,64)).map (lambdaPow 2 (Smn 1 2))) h₂.symm)
    delta sphereAction lambdaMultiply
    simp (config := { congrConsts := false }) only [eqToHom_refl,Category.id_comp,Functor.map_comp,Category.assoc]
    simpa (config := { congrConsts := false }) only [Category.assoc,S,Smn,Int.reduceAdd,Int.reduceSub,Nat.cast_ofNat,Nat.cast_one,Int.natCast_one] using
      (congrArg (fun z => z ≫ (SyntheticCategory.biShift (62,64)).map etaShuffle ≫ a) hp).symm
  change sphereAction (lambdaMultiply 2 eta) theta = lambdaMultiply 2 (sphereAction eta theta)
  exact shuffle_lambda_left_two coh eta theta


/- Actual private source adaptations; public specified-value obligations remain pending. -/
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
private theorem secondary_lambda_precomp_injective_at_degree (m : ℕ) (wt : ℤ) (hw : wt ≤ (m:ℤ)+2) :
    Function.Injective (fun a : BiHom (m:ℤ) wt (S_0_0 : SyntheticSpectrum) =>
      SyntheticCategory.lam.app (Smn (m:ℤ) wt) ≫ a) := by
  letI := model.exactness.shiftAdditive (0,-1)
  letI := (SyntheticCategory.biShift_fullyFaithful (Syn := SyntheticSpectrum) (0,-1)).faithful
  let U := (SyntheticCategory.biShift (0,-1)).obj (Smn (Syn := SyntheticSpectrum) (m:ℤ) wt)
  let T := XModLambdaN.cofiberTriangle (S_0_0 : SyntheticSpectrum) 1
  let e₀ : U ≅ Smn (Syn := SyntheticSpectrum) (m:ℤ) (wt-1) :=
    (SyntheticCategory.biShift_comp ((m:ℤ),wt) (0,-1)).app S_0_0 ≪≫
      eqToIso (by congr 1 <;> simp (config := { congrConsts := false }) [sub_eq_add_neg])
  let e₁ : U⟦(1 : ℤ)⟧ ≅ Smn (Syn := SyntheticSpectrum) ((m:ℤ)+1) (wt-1) :=
    (shiftFunctor SyntheticSpectrum (1 : ℤ)).mapIso e₀ ≪≫
      (SyntheticCategory.biShift_compat (Syn := SyntheticSpectrum) 1).symm.app _ ≪≫
      (SyntheticCategory.biShift_comp ((m:ℤ),wt-1) (1,0)).app S_0_0 ≪≫
      eqToIso (by congr 1 <;> simp (config := { congrConsts := false }))
  have hQ : ∀ q : U⟦(1 : ℤ)⟧ ⟶ T.obj₃, q = 0 := by
    intro q
    haveI : Subsingleton (model.classical.sphere.Page 2 (wt-(m:ℤ)-2,wt-1)) := by
      by_cases he : wt = (m:ℤ)+2
      · subst wt
        have hp : (m:ℤ)+2-(m:ℤ)-2=0 := by omega
        have ht : (m:ℤ)+2-1=((m+1:ℕ):ℤ) := by omega
        rw [hp,ht]
        exact KIP126.AdamsSynthetic.Standard.sphere_page_filtration_zero 2 (m+1) (by omega)
      · exact KIP126.AdamsSynthetic.Standard.classical_page_negative .sphere
          2 (wt-(m:ℤ)-2) (wt-1) (by omega)
    have hz : ∀ a : BiHom ((m:ℤ)+1) (wt-1) (XModLambdaN (S_0_0 : SyntheticSpectrum) 1), a = 0 := by
      intro a
      have hp : wt-1-(wt-(m:ℤ)-2)= (m:ℤ)+1 := by omega
      have hsub : Subsingleton (BiHom (wt-1-(wt-(m:ℤ)-2)) (wt-1)
          (XModLambdaN (S_0_0 : SyntheticSpectrum) 1)) :=
        (KIP126.Literature.sphereFirstQuotient model (wt-(m:ℤ)-2) (wt-1)).injective.subsingleton
      rw [hp] at hsub
      exact @Subsingleton.elim _ hsub a 0
    apply (cancel_epi e₁.inv).mp
    simpa (config := { congrConsts := false }) only [comp_zero] using hz (e₁.inv ≫ q)
  intro a b hab
  dsimp only at hab
  have hpre : SyntheticCategory.lam.app (Smn (Syn := SyntheticSpectrum) (m:ℤ) wt) ≫ (a-b)=0 := by
    rw [Preadditive.comp_sub, hab, sub_self]
  have hf : (SyntheticCategory.biShift (0,-1)).map (a-b) ≫ T.mor₁=0 := by
    change (SyntheticCategory.biShift (0,-1)).map (a-b) ≫ lambdaPow 1 S_0_0=0
    rw [lambdaPow_one model.quotients.coherence, SyntheticCategory.lam.naturality]
    exact hpre
  have hfs : ((SyntheticCategory.biShift (0,-1)).map (a-b))⟦(1 : ℤ)⟧' ≫
      T.mor₁⟦(1 : ℤ)⟧'=0 := by
    rw [← Functor.map_comp, hf, Functor.map_zero]
  obtain ⟨q,hq⟩ := T.coyoneda_exact₁ (HasFunctorialCofiber.cofib_distinguished _) _ hfs
  have hz : ((SyntheticCategory.biShift (0,-1)).map (a-b))⟦(1 : ℤ)⟧'=0 := by
    rw [hq, hQ q, zero_comp]
  have hz' : (SyntheticCategory.biShift (0,-1)).map (a-b)=0 := by
    apply (shiftFunctor SyntheticSpectrum (1 : ℤ)).map_injective
    simpa (config := { congrConsts := false }) only [Functor.map_zero] using hz
  apply sub_eq_zero.mp
  apply (SyntheticCategory.biShift (0,-1)).map_injective
  simpa (config := { congrConsts := false }) only [Functor.map_zero] using hz'

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
private theorem secondary_lambda_powers_injective_at_degree (m : ℕ) (wt : ℤ) (hw : wt ≤ (m:ℤ)+2) :
    ∀ k : ℕ, Function.Injective (fun a : BiHom (m:ℤ) wt (S_0_0 : SyntheticSpectrum) => lambdaMultiply k a) := by
  let Syn := SyntheticSpectrum
  let X := (S_0_0 : Syn)
  let coh := model.quotients.coherence
  have one (k : ℕ) : Function.Injective (fun a :
      (SyntheticCategory.biShift (0,-(k : ℤ))).obj (Smn (Syn := Syn) (m:ℤ) wt) ⟶ X =>
      SyntheticCategory.lam.app _ ≫ a) := by
    let e : Smn (Syn := Syn) (m:ℤ) (wt-k) ≅
        (SyntheticCategory.biShift (0,-(k : ℤ))).obj (Smn (m:ℤ) wt) :=
      eqToIso (by dsimp only [Smn]; congr 1 <;> simp (config := { congrConsts := false }) [sub_eq_add_neg]) ≪≫
        ((SyntheticCategory.biShift_comp ((m:ℤ),wt) (0,-(k : ℤ))).app S_0_0).symm
    intro a b hab
    apply (cancel_epi e.hom).mp
    apply secondary_lambda_precomp_injective_at_degree m (wt-k) (by omega)
    dsimp only
    dsimp only at hab
    have hn := SyntheticCategory.lam.naturality e.hom
    dsimp only [Functor.id_map] at hn
    rw [← Category.assoc, ← Category.assoc, ← hn]
    simpa (config := { congrConsts := false }) only [Category.assoc] using
      congrArg (fun z => (SyntheticCategory.biShift (0,-1)).map e.hom ≫ z) hab
  have powers (k : ℕ) : Function.Injective (fun a : BiHom (m:ℤ) wt X => lambdaPow k (Smn (m:ℤ) wt) ≫ a) := by
    induction k with
    | zero =>
      intro a b hab
      exact (cancel_epi (SyntheticCategory.biShift_zero.hom.app (Smn (m:ℤ) wt))).mp hab
    | succ k ih =>
      intro a b hab
      apply ih
      apply one k
      rw [lambdaPow_add coh k 1 (k+1) rfl, lambdaPow_one coh] at hab
      have hc := (cancel_epi ((lambdaShiftAddIso k 1 (k+1) rfl).inv.app (Smn (Syn := Syn) (m:ℤ) wt))).mp
        (by simpa (config := { congrConsts := false }) only [Category.assoc] using hab)
      have hn := SyntheticCategory.lam.naturality (lambdaPow k (Smn (Syn := Syn) (m:ℤ) wt))
      dsimp only [Functor.id_map] at hn
      change (SyntheticCategory.biShift (0,-1)).map (lambdaPow k (Smn (m:ℤ) wt)) ≫
        (SyntheticCategory.lam.app (Smn (m:ℤ) wt) ≫ a) =
        (SyntheticCategory.biShift (0,-1)).map (lambdaPow k (Smn (m:ℤ) wt)) ≫
        (SyntheticCategory.lam.app (Smn (m:ℤ) wt) ≫ b) at hc
      rw [← Category.assoc, ← Category.assoc, hn] at hc
      simpa (config := { congrConsts := false }) only [Category.assoc] using hc
  intro k a b hab
  apply powers k
  dsimp only [lambdaMultiply] at hab
  have hc := (cancel_epi (eqToHom (by congr 1 <;> simp (config := { congrConsts := false })))).mp hab
  exact (cancel_epi ((SyntheticCategory.biShift_comp ((m:ℤ),wt) (0,-(k : ℤ))).inv.app S_0_0)).mp
    (by simpa (config := { congrConsts := false }) only [Category.assoc] using hc)


private theorem secondary_lambda_precomp_injective (wt : ℤ) (hw : wt ≤ 4) :
    Function.Injective (fun a : BiHom 2 wt (S_0_0 : SyntheticSpectrum) =>
      SyntheticCategory.lam.app (Smn 2 wt) ≫ a) :=
  secondary_lambda_precomp_injective_at_degree 2 wt (by omega)

private theorem secondary_lambda_powers_injective (wt : ℤ) (hw : wt ≤ 4) :
    ∀ k : ℕ, Function.Injective (fun a : BiHom 2 wt (S_0_0 : SyntheticSpectrum) => lambdaMultiply k a) :=
  secondary_lambda_powers_injective_at_degree 2 wt (by omega)

set_option backward.isDefEq.respectTransparency false in
private theorem secondary_realization_injective :
    Function.Injective (fun a : BiHom 2 4 (S_0_0 : SyntheticSpectrum) => model.recovery.realization.map a) := by
  letI := realization_additive
  intro a b hab
  dsimp only at hab
  have hz : model.recovery.realization.map (a-b)=0 := by rw [Functor.map_sub, hab, sub_self]
  obtain ⟨k,hk⟩ := (selected_realization_kernel .sphere 2 4 (a-b)).mp hz
  apply sub_eq_zero.mp
  apply secondary_lambda_powers_injective 4 (by omega) k
  dsimp only [lambdaMultiply] at hk ⊢
  simpa (config := { congrConsts := false }) only [comp_zero] using hk

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
private theorem secondary_low_nonempty :
    ∃ value : BiHom 2 4 (S_0_0 : SyntheticSpectrum),
      Route.TripleToda syntheticH0 eta syntheticH0 value := by
  let h := syntheticH0
  have hh : sphereProduct h eta = 0 := toda_h0_eta
  have heh : sphereProduct eta h = 0 := by
    rw [model.sphereProductCommutative 1 2 0 1 eta h]
    simp (config := { congrConsts := false }) only
      [mul_zero, Int.natAbs_zero, pow_zero, one_smul, hh]
    rfl
  letI := model.exactness.shiftAdditive (0,1)
  let f := (SyntheticCategory.biShift (1,3)).map h
  let g := (SyntheticCategory.biShift_comp (1,2) (0,1)).inv.app
    (S_0_0 : SyntheticSpectrum) ≫ (SyntheticCategory.biShift (0,1)).map eta
  have hraw : (SyntheticCategory.biShift (1,2)).map h ≫ eta = 0 := by
    apply (cancel_epi ((SyntheticCategory.biShift_comp (0,1) (1,2)).inv.app
      (S_0_0 : SyntheticSpectrum))).mp
    dsimp only [sphereProduct] at hh
    simpa (config := { congrConsts := false }) only
      [Category.assoc, comp_zero] using hh
  have hfg : f ≫ g = 0 := by
    dsimp only [f,g]
    erw [← Category.assoc, (SyntheticCategory.biShift_comp (1,2) (0,1)).inv.naturality]
    dsimp only [Functor.comp_map]
    rw [Category.assoc, ← Functor.map_comp, hraw, Functor.map_zero, comp_zero]
  have hgh : g ≫ h = 0 := by
    dsimp only [g, sphereProduct] at heh ⊢
    simpa (config := { congrConsts := false }) only [Category.assoc] using heh
  obtain ⟨x,hx⟩ := KIP126.StableHomotopy.Toda.exists_relation f g h hfg hgh
  refine ⟨(Route.tripleTodaSource 0 1 1 2 0 1).hom ≫ x, ?_⟩
  change KIP126.StableHomotopy.Toda.Relation
    ((Route.tripleTodaSource 0 1 1 2 0 1).inv ≫
      ((Route.tripleTodaSource 0 1 1 2 0 1).hom ≫ x)) f g h
  simpa (config := { congrConsts := false }) only [Iso.inv_hom_id_assoc] using hx

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
private theorem secondary_symmetric_nonempty
    (theta : BiHom 62 64 (S_0_0 : SyntheticSpectrum)) (htheta : theta+theta=0) :
    ∃ value : BiHom 63 64 (S_0_0 : SyntheticSpectrum),
      Route.TripleToda Route.syntheticTwo theta Route.syntheticTwo value := by
  let S := (S_0_0 : SyntheticSpectrum)
  let F := SyntheticCategory.biShift (Syn := SyntheticSpectrum) (62,64)
  let F0 := SyntheticCategory.biShift (Syn := SyntheticSpectrum) (0,0)
  letI : F.Additive := model.exactness.shiftAdditive (62,64)
  let A := F.obj S
  let Z := F0.obj S
  let u : Z ≅ S := SyntheticCategory.biShift_zero.app S
  let f := F.map Route.syntheticTwo
  let g : A ⟶ Z := (SyntheticCategory.biShift_comp (62,64) (0,0)).inv.app S ≫ F0.map theta
  have hright : (SyntheticCategory.biShift_comp (62,64) (0,0)).hom.app S =
      SyntheticCategory.biShift_zero.hom.app A := by
    have hh := model.quotients.coherence.right_unit (62,64) S
    simp (config := { congrConsts := false }) only [biShiftAddIso, Iso.trans_hom,
      NatTrans.comp_app, eqToIso.hom, eqToHom_app, eqToHom_refl, Category.comp_id] at hh
    exact hh
  have hgu : g ≫ u.hom = theta := by
    calc
      g ≫ u.hom = (SyntheticCategory.biShift_comp (62,64) (0,0)).inv.app S ≫
          (F0.map theta ≫ SyntheticCategory.biShift_zero.hom.app S) := Category.assoc _ _ _
      _ = (SyntheticCategory.biShift_comp (62,64) (0,0)).inv.app S ≫
          (SyntheticCategory.biShift_zero.hom.app A ≫ theta) :=
        congrArg (fun z => (SyntheticCategory.biShift_comp (62,64) (0,0)).inv.app S ≫ z)
          (SyntheticCategory.biShift_zero.hom.naturality theta)
      _ = (SyntheticCategory.biShift_comp (62,64) (0,0)).inv.app S ≫
          ((SyntheticCategory.biShift_comp (62,64) (0,0)).hom.app S ≫ theta) := by rw [hright]
      _ = theta := ((SyntheticCategory.biShift_comp (62,64) (0,0)).app S).inv_hom_id_assoc theta
  have hg2 : (2:ℕ) • g = 0 := by
    apply (cancel_mono u.hom).mp
    simpa (config := { congrConsts := false }) only
      [Preadditive.nsmul_comp, hgu, two_nsmul, Preadditive.add_comp, zero_comp] using htheta
  have hf : f = (2:ℕ) • F.map (SyntheticCategory.biShift_zero.hom.app S) := by
    dsimp only [f, S, Route.syntheticTwo]
    simp (config := { congrConsts := false }) only
      [Functor.map_comp, Functor.map_nsmul, Functor.map_id,
        Preadditive.comp_nsmul, Category.comp_id]
  have hfg : f ≫ g = 0 := by
    rw [hf, Preadditive.nsmul_comp, ← Preadditive.comp_nsmul, hg2, comp_zero]
  have hgh : g ≫ Route.syntheticTwo = 0 := by
    change g ≫ (u.hom ≫ ((2:ℕ) • 𝟙 S)) = 0
    rw [← Category.assoc, Preadditive.comp_nsmul, Category.comp_id,
      ← Preadditive.nsmul_comp, hg2, zero_comp]
  obtain ⟨x,hx⟩ := KIP126.StableHomotopy.Toda.exists_relation f g Route.syntheticTwo hfg hgh
  refine ⟨(Route.tripleTodaSource 0 0 62 64 0 0).hom ≫ x, ?_⟩
  change KIP126.StableHomotopy.Toda.Relation
    ((Route.tripleTodaSource 0 0 62 64 0 0).inv ≫
      ((Route.tripleTodaSource 0 0 62 64 0 0).hom ≫ x)) f g Route.syntheticTwo
  simpa (config := { congrConsts := false }) only [Iso.inv_hom_id_assoc] using hx

section Moore

variable {C : Type u} [StableHomotopyCategory.{u,v} C]

/-- The source's factorization on any *given* distinguished Moore triangle.
The same `M`, `i`, and `p` occur throughout the conclusion. -/
private theorem moore_factor_on_triangle
    {S M : C} (i : S ⟶ M) (p : M ⟶ S⟦(1 : ℤ)⟧)
    (hT : Triangle.mk ((2 : ℕ) • 𝟙 S) i p ∈ distTriang C)
    (htf : ∀ a : S ⟶ S, a + a = 0 → a = 0) :
    ∃ ε : S⟦(1 : ℤ)⟧ ⟶ S, (2 : ℕ) • 𝟙 M = p ≫ ε ≫ i := by
  let T := Triangle.mk ((2 : ℕ) • 𝟙 S) i p
  have hp : (2 : ℕ) • p = 0 := by
    have h := comp_distTriang_mor_zero₃₁ T hT
    change p ≫ ((2 : ℕ) • 𝟙 S)⟦(1 : ℤ)⟧' = 0 at h
    simpa (config := { congrConsts := false }) only
      [Functor.map_nsmul, CategoryTheory.Functor.map_id,
        Preadditive.comp_nsmul, Category.comp_id] using h
  have hp' : ((2 : ℕ) • 𝟙 M) ≫ p = 0 := by
    simpa (config := { congrConsts := false }) only
      [Preadditive.nsmul_comp, Category.id_comp] using hp
  obtain ⟨a, ha⟩ := T.coyoneda_exact₃ hT ((2 : ℕ) • 𝟙 M) hp'
  change M ⟶ S at a
  change (2 : ℕ) • 𝟙 M = a ≫ i at ha
  have hi : (2 : ℕ) • i = 0 := by
    have h := comp_distTriang_mor_zero₁₂ T hT
    change ((2 : ℕ) • 𝟙 S) ≫ i = 0 at h
    simpa (config := { congrConsts := false }) only
      [Preadditive.nsmul_comp, Category.id_comp] using h
  have hai : i ≫ a = 0 := by
    apply htf
    have h : (2 : ℕ) • (i ≫ a) = 0 := by
      rw [← Preadditive.nsmul_comp, hi, zero_comp]
    simpa (config := { congrConsts := false }) only [two_nsmul] using h
  obtain ⟨ε, hε⟩ := T.yoneda_exact₃ hT a hai
  change S⟦(1 : ℤ)⟧ ⟶ S at ε
  change a = p ≫ ε at hε
  exact ⟨ε, by rw [ha, hε, Category.assoc] <;> rfl⟩

/-- The source's existential statement, with no source result package. -/
private theorem moore_factor
    (S : C) (htf : ∀ a : S ⟶ S, a + a = 0 → a = 0) :
    ∃ (M : C) (i : S ⟶ M) (p : M ⟶ S⟦(1 : ℤ)⟧)
      (ε : S⟦(1 : ℤ)⟧ ⟶ S),
      Triangle.mk ((2 : ℕ) • 𝟙 S) i p ∈ distTriang C ∧
        (2 : ℕ) • 𝟙 M = p ≫ ε ≫ i := by
  obtain ⟨M, i, p, hT⟩ := distinguished_cocone_triangle ((2 : ℕ) • 𝟙 S)
  obtain ⟨ε, hε⟩ := moore_factor_on_triangle i p hT htf
  exact ⟨M, i, p, ε, hT, hε⟩

/-- A specialization preserving the registered *chosen* cofiber object and
both of its actual structure maps. -/
private theorem moore_factor_chosen [HasFunctorialCofiber (C := C)]
    (S : C) (htf : ∀ a : S ⟶ S, a + a = 0 → a = 0) :
    ∃ ε : S⟦(1 : ℤ)⟧ ⟶ S,
      (2 : ℕ) • 𝟙 (HasFunctorialCofiber.cofib ((2 : ℕ) • 𝟙 S)) =
        HasFunctorialCofiber.cofibδ ((2 : ℕ) • 𝟙 S) ≫ ε ≫
          HasFunctorialCofiber.cofibι ((2 : ℕ) • 𝟙 S) :=
  moore_factor_on_triangle
    (HasFunctorialCofiber.cofibι ((2 : ℕ) • 𝟙 S))
    (HasFunctorialCofiber.cofibδ ((2 : ℕ) • 𝟙 S))
    (HasFunctorialCofiber.cofib_distinguished ((2 : ℕ) • 𝟙 S)) htf

/-- This equivalence isolates the actual lifting obstruction; it does not
assume or claim that the obstruction always vanishes. -/
private theorem moore_factor_iff_lift
    {S M : C} (i : S ⟶ M) (p : M ⟶ S⟦(1 : ℤ)⟧)
    (hT : Triangle.mk ((2 : ℕ) • 𝟙 S) i p ∈ distTriang C) :
    (∃ ε : S⟦(1 : ℤ)⟧ ⟶ S, (2 : ℕ) • 𝟙 M = p ≫ ε ≫ i) ↔
      ∃ a : M ⟶ S, (2 : ℕ) • 𝟙 M = a ≫ i ∧ i ≫ a = 0 := by
  let T := Triangle.mk ((2 : ℕ) • 𝟙 S) i p
  constructor
  · rintro ⟨ε, hε⟩
    refine ⟨p ≫ ε, ?_, ?_⟩
    · simpa (config := { congrConsts := false }) only [Category.assoc] using hε
    · have hip := comp_distTriang_mor_zero₂₃ T hT
      change i ≫ p = 0 at hip
      rw [← Category.assoc, hip, zero_comp]
  · rintro ⟨a, ha, hai⟩
    obtain ⟨ε, hε⟩ := T.yoneda_exact₃ hT a hai
    change S⟦(1 : ℤ)⟧ ⟶ S at ε
    change a = p ≫ ε at hε
    exact ⟨ε, by rw [ha, hε, Category.assoc] <;> rfl⟩

end Moore

section ScalarToda

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor C n)] [Pretriangulated C]

/-- The actual scalar defect on the *same* cone yields the Toda witness.
No separate cone, comparison object, or externally supplied bracket value is
introduced. `j` only identifies the doubled first map's two objects. -/
private theorem scalar_defect_to_toda
    {X A Q Z W : C} (j : X ≅ A) (f : X ⟶ A)
    (hf : f = (2 : ℕ) • j.hom)
    (i : A ⟶ Q) (p : Q ⟶ X⟦(1 : ℤ)⟧)
    (hT : Triangle.mk f i p ∈ distTriang C)
    (b : X⟦(1 : ℤ)⟧ ⟶ A)
    (hQ : (2 : ℕ) • 𝟙 Q = p ≫ b ≫ i)
    (g : A ⟶ Z) (hg : (2 : ℕ) • g = 0) (u : Z ⟶ W) :
    Toda.Relation (b ≫ g ≫ u) f g ((2 : ℕ) • u) := by
  let T := Triangle.mk f i p
  have hfg : f ≫ g = 0 := by
    rw [hf, Preadditive.nsmul_comp, ← Preadditive.comp_nsmul, hg, comp_zero]
  obtain ⟨gbar, hgbar⟩ := T.yoneda_exact₂ hT g hfg
  change g = i ≫ gbar at hgbar
  have hibar : i ≫ gbar = g := hgbar.symm
  refine ⟨Q, i, p, hT, gbar, hibar, ?_⟩
  calc
    p ≫ (b ≫ g ≫ u) = (p ≫ b ≫ i) ≫ gbar ≫ u := by
      rw [← hibar]
      simp (config := { congrConsts := false }) only [Category.assoc]
    _ = ((2 : ℕ) • 𝟙 Q) ≫ gbar ≫ u := by rw [hQ]
    _ = gbar ≫ ((2 : ℕ) • u) := by
      simp (config := { congrConsts := false }) only
        [Preadditive.nsmul_comp, Preadditive.comp_nsmul, Category.id_comp] <;> rfl

end ScalarToda

/- a48 Symmetric.lean:4745–4894; actual same-object Moore/Toda construction. -/
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
private theorem secondary_symmetric_from_moore
      (hs1 : ∀ a b : BiHom 1 0 (S_0_0 : SyntheticSpectrum), a ≠ 0 → b ≠ 0 → a = b)
      (he : lambdaMultiply 2 eta ≠ 0)
      (M : SyntheticSpectrum) (i : (S_0_0 : SyntheticSpectrum) ⟶ M)
      (p : M ⟶ (S_0_0 : SyntheticSpectrum)⟦(1 : ℤ)⟧)
      (ε : (S_0_0 : SyntheticSpectrum)⟦(1 : ℤ)⟧ ⟶ (S_0_0 : SyntheticSpectrum))
      (hT : Triangle.mk ((2 : ℕ) • 𝟙 (S_0_0 : SyntheticSpectrum)) i p ∈ distTriang SyntheticSpectrum)
      (hMoore : (2 : ℕ) • 𝟙 M = p ≫ ε ≫ i)
      (hM : (2 : ℕ) • 𝟙 M ≠ 0) :
      ∀ θ : BiHom 62 64 (S_0_0 : SyntheticSpectrum), θ + θ = 0 →
        Route.TripleToda Route.syntheticTwo θ Route.syntheticTwo
          (lambdaMultiply 2 (sphereProduct eta θ)) := by
    let Syn := SyntheticSpectrum
    have hproduct : ∀ θ : BiHom 62 64 (S_0_0 : Syn),
        sphereProduct (lambdaMultiply 2 eta) θ = lambdaMultiply 2 (sphereProduct eta θ) :=
      secondary_star_product model.quotients.coherence eta
    let S := (S_0_0 : Syn)
    let F := SyntheticCategory.biShift (Syn := Syn) (62,64)
    let F0 := SyntheticCategory.biShift (Syn := Syn) (0,0)
    let Fs := SyntheticCategory.biShift (Syn := Syn) (1,0)
    let FF := SyntheticCategory.biShift_fullyFaithful (Syn := Syn) (62,64)
    letI : F.Additive := model.exactness.shiftAdditive (62,64)
    letI : F.CommShift ℤ := model.exactness.shiftCommShift (62,64)
    letI : F.IsTriangulated := model.exactness.shiftExact (62,64)
    let X := F.obj (F0.obj S)
    let A := F.obj S
    let Q := F.obj M
    let e0 : F0.obj S ≅ S := SyntheticCategory.biShift_zero.app S
    let j : X ≅ A := F.mapIso e0
    let js : X⟦(1 : ℤ)⟧ ≅ A⟦(1 : ℤ)⟧ :=
      (shiftFunctor Syn (1 : ℤ)).mapIso j
    let γ : F.obj (S⟦(1 : ℤ)⟧) ≅ A⟦(1 : ℤ)⟧ :=
      (F.commShiftIso (1 : ℤ)).app S
    let f : X ⟶ A := F.map Route.syntheticTwo
    let ir : A ⟶ Q := F.map i
    let px : Q ⟶ X⟦(1 : ℤ)⟧ := F.map p ≫ γ.hom ≫ js.inv
    let b : X⟦(1 : ℤ)⟧ ⟶ A := js.hom ≫ γ.inv ≫ F.map ε
    let T := Triangle.mk ((2 : ℕ) • 𝟙 S) i p
    let TX := Triangle.mk f ir px
    have hTX : TX ∈ distTriang Syn := by
      apply isomorphic_distinguished _ (F.map_distinguished T hT)
      refine Triangle.isoMk TX (F.mapTriangle.obj T) j (Iso.refl _) (Iso.refl _)
        ?_ ?_ ?_
      · dsimp only [Syn, S, TX, T, f, j, e0, Route.syntheticTwo, Functor.mapTriangle]
        dsimp only [Smn]
        simp (config := { congrConsts := false }) [Functor.map_comp, F.map_id S]
        erw [CategoryTheory.Functor.map_id, Category.comp_id]
      · dsimp only [Syn, S, TX, T, ir, Functor.mapTriangle]
        simp (config := { congrConsts := false })
      · change (F.map p ≫ γ.hom ≫ js.inv) ≫ js.hom =
          𝟙 Q ≫ (F.map p ≫ γ.hom)
        simp (config := { congrConsts := false }) only [Syn, S, Category.assoc, Iso.inv_hom_id,
          Category.comp_id, Category.id_comp]
    have hQ : (2 : ℕ) • 𝟙 Q = px ≫ b ≫ ir := by
      have h := congrArg F.map hMoore
      simpa only [Syn, S, Functor.map_nsmul, CategoryTheory.Functor.map_id, Functor.map_comp,
        Q, px, b, ir, Category.assoc, Iso.inv_hom_id_assoc,
        Iso.hom_inv_id_assoc] using h

    have hε : ε ≠ 0 := by
      intro hz
      apply hM
      simpa only [Syn, S, hz, zero_comp, comp_zero] using hMoore
    have hFε : F.map ε ≠ 0 := by
      intro hz
      apply hε
      exact FF.map_injective (by simpa only [Syn, S, Functor.map_zero] using hz)
    have hbne : b ≠ 0 := by
      intro hz
      apply hFε
      apply (cancel_epi γ.inv).mp
      apply (cancel_epi js.hom).mp
      simpa only [Syn, S, b, Category.assoc, comp_zero] using hz

    let t : Smn (Syn := Syn) 63 64 ≅ X⟦(1 : ℤ)⟧ :=
      Route.tripleTodaSource 0 0 62 64 0 0
    let μ : F.obj (Fs.obj S) ≅ Smn (Syn := Syn) 63 64 :=
      (SyntheticCategory.biShift_comp (1,0) (62,64)).app S
    let κ : F.obj (Fs.obj S) ≅ X⟦(1 : ℤ)⟧ := μ ≪≫ t
    let e : BiHom 1 0 S := lambdaMultiply 2 eta
    let σ : Smn (Syn := Syn) 63 64 ⟶ A := μ.inv ≫ F.map e
    let b0 : BiHom 1 0 S := FF.preimage (κ.hom ≫ b)
    have hb0map : F.map b0 = κ.hom ≫ b := FF.map_preimage _
    have hb0ne : b0 ≠ 0 := by
      intro hz
      apply hbne
      apply (cancel_epi κ.hom).mp
      have hh := hb0map.symm
      simpa only [Syn, S, hz, Functor.map_zero, comp_zero] using hh
    have hb0 : b0 = e := hs1 b0 e hb0ne he
    have hb : b = t.inv ≫ σ := by
      apply (cancel_epi κ.hom).mp
      rw [← hb0map, hb0]
      simp (config := { congrConsts := false }) only [Syn, S, κ, σ, Iso.trans_hom, Category.assoc,
        Iso.hom_inv_id_assoc]

    intro θ hθ
    let Z := F0.obj S
    let u : Z ⟶ S := e0.hom
    let g : A ⟶ Z :=
      (SyntheticCategory.biShift_comp (62,64) (0,0)).inv.app S ≫ F0.map θ
    have hright :
        (SyntheticCategory.biShift_comp (62,64) (0,0)).hom.app S =
          SyntheticCategory.biShift_zero.hom.app A := by
      have hh := model.quotients.coherence.right_unit (62,64) S
      simp (config := { congrConsts := false }) only [biShiftAddIso, Iso.trans_hom, NatTrans.comp_app,
        eqToIso.hom, eqToHom_app, eqToHom_refl, Category.comp_id] at hh
      exact hh
    have hgu : g ≫ u = θ := by
      calc
        g ≫ u = (SyntheticCategory.biShift_comp (62,64) (0,0)).inv.app S ≫
            (F0.map θ ≫ SyntheticCategory.biShift_zero.hom.app S) :=
          Category.assoc _ _ _
        _ = (SyntheticCategory.biShift_comp (62,64) (0,0)).inv.app S ≫
            (SyntheticCategory.biShift_zero.hom.app A ≫ θ) :=
          congrArg (fun a : F0.obj A ⟶ S =>
            (SyntheticCategory.biShift_comp (62,64) (0,0)).inv.app S ≫ a)
            (SyntheticCategory.biShift_zero.hom.naturality θ)
        _ = (SyntheticCategory.biShift_comp (62,64) (0,0)).inv.app S ≫
            ((SyntheticCategory.biShift_comp (62,64) (0,0)).hom.app S ≫ θ) := by
          rw [hright]
        _ = θ := ((SyntheticCategory.biShift_comp (62,64) (0,0)).app S).inv_hom_id_assoc θ
    have hg2 : (2 : ℕ) • g = 0 := by
      apply (cancel_mono u).mp
      simpa only [Syn, S, Preadditive.nsmul_comp, hgu, two_nsmul, Preadditive.add_comp, zero_comp] using hθ
    have hf : f = (2 : ℕ) • j.hom := by
      dsimp only [Syn, S, f, Route.syntheticTwo, j, e0]
      simp (config := { congrConsts := false }) only
        [Functor.map_comp, Functor.map_nsmul, CategoryTheory.Functor.map_id,
          Preadditive.comp_nsmul, Category.comp_id, Functor.mapIso_hom, Iso.app_hom]
    have hfg : f ≫ g = 0 := by
      rw [hf, Preadditive.nsmul_comp, ← Preadditive.comp_nsmul, hg2, comp_zero]
    obtain ⟨gbar, hgbar⟩ := TX.yoneda_exact₂ hTX g hfg
    change g = ir ≫ gbar at hgbar
    have hgbar' : ir ≫ gbar = g := hgbar.symm
    have hbar : gbar ≫ Route.syntheticTwo = px ≫ t.inv ≫ sphereProduct e θ := by
      calc
        gbar ≫ Route.syntheticTwo = ((2 : ℕ) • 𝟙 Q) ≫ gbar ≫ u := by
          dsimp only [Syn, S, Route.syntheticTwo, u, e0]
          simp (config := { congrConsts := false }) only
            [Iso.app_hom, Category.assoc, Preadditive.comp_nsmul,
              Preadditive.nsmul_comp, Category.id_comp, Category.comp_id]
        _ = px ≫ b ≫ ir ≫ gbar ≫ u := by
          rw [hQ]
          simp (config := { congrConsts := false }) only [Syn, S, Category.assoc]
        _ = px ≫ b ≫ θ := by
          rw [← Category.assoc ir gbar u, hgbar', hgu]
        _ = px ≫ t.inv ≫ sphereProduct e θ := by
          rw [hb]
          dsimp only [Syn, S, F, σ, sphereProduct, μ]
          simp (config := { congrConsts := false }) only [Iso.app_inv, Category.assoc]
    have hv : sphereProduct e θ = lambdaMultiply 2 (sphereProduct eta θ) :=
      hproduct θ
    rw [hv] at hbar
    change Toda.Relation
      (t.inv ≫ lambdaMultiply 2 (sphereProduct eta θ)) f g Route.syntheticTwo
    refine ⟨Q, ir, px, hTX, gbar, hgbar', ?_⟩
    simpa only [Syn, S, Category.assoc] using hbar.symm

/-- Low Toda comparison used at MainPaper/main.tex:2498.
This is the original pending secondary-operation comparison. -/
public theorem toda_eta_squared :
    Route.TripleToda syntheticH0 eta syntheticH0
      (sphereProduct (m := 1) (n := 2) (k := 1) (l := 2) eta eta) := by
  sorry

/-- The symmetric comparison retains the synthetic λ² normalization from
MainPaper/main.tex:2550-2551 and applies to each actual order-two theta. -/
public theorem toda_symmetric
    (theta : BiHom 62 64 (S_0_0 : SyntheticSpectrum)) (htheta : theta + theta = 0) :
    Route.TripleToda Route.syntheticTwo theta Route.syntheticTwo
      (lambdaMultiply 2 (sphereProduct eta theta)) := by
  sorry

end
end KIP126.Literature.Standard
