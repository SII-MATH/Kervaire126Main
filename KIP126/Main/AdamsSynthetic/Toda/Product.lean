module

public import KIP126.Def.AdamsSynthetic.ComparisonStatements
import KIP126.Def.Synthetic.Context.Coherence.Proofs

@[expose] public section

/-! Compatibility of the synthetic sphere product with two powers of lambda. -/
namespace KIP126.Main.AdamsSynthetic.Toda

section SecondaryComparisonProof

open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.Synthetic.Context KIP126.AdamsSynthetic
universe u v w
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {C : Type u} [StableHomotopyCategory.{u,v} C] [HasFunctorialCofiber (C:=C)]
  {Syn : Type w} [SyntheticCategory.{w,v} Syn] [HasFunctorialCofiber (C:=Syn)]
  {H : Mod2EilenbergMacLane (C:=C)} {M' : MilnorCooperations H}
theorem secondary_star_product (D' : AdamsComparison H M' Syn)
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
      simp only [Functor.map_comp,Category.assoc]
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
  have shuffle_lambda_left_two (D' : AdamsComparison H M' Syn)
      (etaShuffle : BiHom 1 2 (S_0_0 : Syn))
      (a : BiHom 62 64 (S_0_0 : Syn)) :
      sphereAction (lambdaMultiply 2 etaShuffle) a = lambdaMultiply 2 (sphereAction etaShuffle a) := by
    let S := (S_0_0 : Syn)
    have h₁ := shift_assoc_inv D'.shiftCoherence (1,2) (62,64) (0,-2)
      (63,66) (62,62) (63,64) (by decide) (by decide) (by decide) (by decide) S
    have h₂ := shift_assoc_inv D'.shiftCoherence (1,2) (0,-2) (62,64)
      (1,0) (62,62) (63,64) (by decide) (by decide) (by decide) (by decide) S
    simp only [biShiftAddIso,Iso.trans_inv,eqToIso.inv,
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
      rw [lambda_pow_shift D'.shiftCoherence 2 (62,64) (Smn 1 2)]
      dsimp only [shiftSwap,KIP126.Synthetic.Context.lambdaDegree]
      simp only [Iso.trans_hom,Iso.trans_inv,Iso.symm_hom,Iso.app_hom,Iso.app_inv,biShiftAddIso,eqToIso.hom,eqToIso.inv,eqToHom_refl,
        Category.comp_id,Category.id_comp]
      simp only [Category.assoc]
      erw [←Category.assoc ((SyntheticCategory.biShift_comp (63,66) (0,-2)).inv.app S)]
      erw [h₁]
      simp only [Category.assoc,Smn,S,Nat.cast_ofNat,Iso.inv_hom_id_app_assoc]
      simpa only [Category.assoc,Smn,S,Nat.cast_ofNat,Nat.cast_one,Int.natCast_one] using
        (congrArg (fun z => z ≫ (SyntheticCategory.biShift (62,64)).map (lambdaPow 2 (Smn 1 2))) h₂.symm)
    unfold sphereAction lambdaMultiply
    simp only [eqToHom_refl,Category.id_comp,Functor.map_comp,Category.assoc]
    simpa only [Category.assoc,S,Smn,Int.reduceAdd,Int.reduceSub,Nat.cast_ofNat,Nat.cast_one,Int.natCast_one] using
      (congrArg (fun z => z ≫ (SyntheticCategory.biShift (62,64)).map etaShuffle ≫ a) hp).symm
  simpa only [sphereAction, sphereProduct] using shuffle_lambda_left_two D' eta theta

end
end SecondaryComparisonProof

end KIP126.Main.AdamsSynthetic.Toda
