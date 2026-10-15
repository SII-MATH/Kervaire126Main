module

public import KIP126.Main.SectionSeven.SphereClasses
public import KIP126.Main.Computation.Lambda

@[expose] public section

namespace KIP126.Main.SectionSeven
open CategoryTheory
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.SpectralSequence
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.AdamsSynthetic.SectionSeven
open KIP126.Literature.AdamsSynthetic KIP126.Main.AdamsSynthetic
noncomputable section

local notation "D" => adamsComparison
local notation "M" => standardMilnorCooperations
local notation "L" => sphereClasses
local notation "I" => computationTheorems
local notation "η" => etaClass
local notation "h₀" => literatureTheorems.toda.h0

section MultipliedIndeterminacy
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u v
variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]
  (coh : BiShiftCoherence Syn)
  (h0 : BiHom 0 1 (S_0_0 : Syn))
  (hlambda : lambdaMultiply 1 h0 = syntheticTwo)
local notation "S" => (S_0_0 : Syn)

include coh hlambda in
private theorem lambda_h0_of_two_torsion (m n : ℤ) (x : BiHom m n S)
    (hx : x + x = 0) : lambdaMultiply 2 (sphereProduct h0 x) = 0 := by
  let F := SyntheticCategory.biShift (Syn := Syn) (m,n)
  have htwo : F.map syntheticTwo ≫ x = 0 := by
    simp only [F, syntheticTwo, Functor.id_obj, Functor.map_comp, two_smul, Functor.map_add,
      Category.assoc, Preadditive.add_comp]
    rw [(SyntheticCategory.biShift (Syn := Syn) (m,n)).map_id S]
    simp only [Category.id_comp, hx, Limits.comp_zero]
  have hshift : F.map (lambdaMultiply 1 h0) ≫ x = 0 := by
    rw [hlambda]
    exact htwo
  have hpre : F.map (SyntheticCategory.lam.app (Smn 0 1)) ≫ F.map h0 ≫ x = 0 := by
    dsimp only [lambdaMultiply] at hshift
    rw [lambdaPow_one coh] at hshift
    simp only [F, eqToHom_refl, Functor.map_comp,
      Category.id_comp, Category.assoc] at hshift
    apply (cancel_epi ((SyntheticCategory.biShift (m,n)).map
      ((SyntheticCategory.biShift_comp (0,1) (0,-1)).inv.app S))).mp
    simpa [F, Smn] using hshift
  have hlam : SyntheticCategory.lam.app (F.obj (Smn 0 1)) ≫ F.map h0 ≫ x = 0 := by
    rw [coh.lambda_comm (m,n) (Smn 0 1)]
    simpa only [F, Category.assoc, Limits.comp_zero] using
      congrArg (fun z => (biShiftAddIso (m,n) (0,-1) ((m,n)+(0,-1)) rfl).hom.app
        (Smn 0 1) ≫ (biShiftAddIso (0,-1) (m,n) ((m,n)+(0,-1)) (add_comm _ _)).inv.app
        (Smn 0 1) ≫ z) hpre
  have hraw : lambdaPow 1 (Smn (0+m) (1+n)) ≫ sphereProduct h0 x = 0 := by
    rw [lambdaPow_one coh]
    dsimp only [sphereProduct]
    have hnat := SyntheticCategory.lam.naturality
      ((SyntheticCategory.biShift_comp (0,1) (m,n)).inv.app S)
    simp only [Smn, Prod.mk_add_mk, Functor.comp_obj, Functor.id_obj, Functor.id_map] at hnat ⊢
    rw [← Category.assoc, ← hnat, Category.assoc]
    simpa [F, Smn] using
      congrArg (fun z => (SyntheticCategory.biShift (0,-1)).map
        ((SyntheticCategory.biShift_comp (0,1) (m,n)).inv.app S) ≫ z) hlam
  dsimp only [lambdaMultiply]
  rw [lambdaPow_add coh 1 1 2 rfl]
  simp only [Category.assoc, hraw, Limits.comp_zero]

include coh hlambda in
private theorem multiplied_indeterminacy_of_two_torsion
    (theta : BiHom 62 64 S) (htheta : theta + theta = 0)
    (b : BiHom 62 70 S) (hb : b + b = 0) :
    ThetaBMultipliedIndeterminacy h0 theta b ∧ SymmetricTwoMultipliedIndeterminacy b := by
  constructor
  · intro a c
    apply lambda_h0_of_two_torsion coh h0 hlambda
    have hleft : sphereProduct theta a + sphereProduct theta a = 0 := by
      simpa [sphereProduct, Functor.map_add, Preadditive.comp_add, Preadditive.add_comp]
        using congrArg (fun z => sphereProduct z a) htheta
    have hright : sphereProduct c b + sphereProduct c b = 0 := by
      simpa [sphereProduct, Preadditive.comp_add] using congrArg (fun z => sphereProduct c z) hb
    rw [add_add_add_comm, hleft, hright, zero_add]
  · intro a c
    have hleft : sphereProduct syntheticTwo a = a + a := by
      have hc := coh.left_unit (63,64) S
      have hc' : (SyntheticCategory.biShift_comp (0,0) (63,64)).hom.app S =
          (SyntheticCategory.biShift (63,64)).map (SyntheticCategory.biShift_zero.hom.app S) := by
        change (biShiftAddIso (0,0) (63,64) (63,64) (by decide)).hom.app S = _ at hc
        simpa only [biShiftAddIso, Iso.trans_hom, NatTrans.comp_app,
          eqToIso.hom, eqToHom_app, eqToHom_refl, Category.comp_id] using hc
      dsimp only [sphereProduct, syntheticTwo]
      simp only [Functor.id_obj, Functor.map_comp, two_smul, Functor.map_add, Category.assoc,
        Preadditive.add_comp]
      rw [(SyntheticCategory.biShift (Syn := Syn) (63,64)).map_id S]
      simp only [Category.id_comp]
      rw [← hc']
      simp
    have hright : sphereProduct c syntheticTwo = c + c := by
      have hc := coh.right_unit (63,64) S
      have hc' : (SyntheticCategory.biShift_comp (63,64) (0,0)).hom.app S =
          SyntheticCategory.biShift_zero.hom.app (Smn 63 64) := by
        change (biShiftAddIso (63,64) (0,0) (63,64) (by decide)).hom.app S = _ at hc
        simpa only [biShiftAddIso, Iso.trans_hom, NatTrans.comp_app,
          eqToIso.hom, eqToHom_app, eqToHom_refl, Category.comp_id, Smn] using hc
      have hnat := SyntheticCategory.biShift_zero.hom.naturality c
      dsimp only [Functor.id_map] at hnat
      dsimp only [sphereProduct, syntheticTwo]
      rw [← Category.assoc (f := (SyntheticCategory.biShift (0,0)).map c), hnat]
      rw [← Category.assoc, ← hc']
      simp [two_smul, Preadditive.comp_add]
    have hz : sphereProduct ((show BiHom 63 64 S from sphereProduct syntheticTwo a) +
        (show BiHom 63 64 S from sphereProduct c syntheticTwo)) b = 0 := by
      rw [hleft, hright]
      calc
        _ = sphereProduct (a+c) (b+b) := by
          simp only [sphereProduct, Functor.map_add, Preadditive.comp_add, Preadditive.add_comp]
          abel
        _ = 0 := by rw [hb]; simp [sphereProduct]
    rw [hz]
    simp [lambdaMultiply]

end MultipliedIndeterminacy

/-- `lem:toda2ext`: lambda^2 h0=2 lambda and 2 theta=2 b=0 kill
these two images. This does not set the original high bracket's
indeterminacy to zero and does not require an extra raw computation. -/
theorem theta_b_multiplied_indeterminacy
    (theta : BiHom 62 64 (S_0_0 : KIP126.Def.standardSyntheticContext.Syn))
    (htheta : ThetaChoice M (D).toAdamsComparisonData theta)
    (b : BiHom 62 70 (S_0_0 : KIP126.Def.standardSyntheticContext.Syn)) :
    ThetaBMultipliedIndeterminacy h₀ theta b ∧
    SymmetricTwoMultipliedIndeterminacy b := by
  exact multiplied_indeterminacy_of_two_torsion (D).shiftCoherence h₀
    literatureTheorems.toda.lambda_h0 theta
    (KIP126.Computation.SphereAndCofiber.theta5_choice_order_two literatureTheorems I theta htheta) b
    (KIP126.Computation.SphereAndCofiber.two_torsion_62_70 literatureTheorems I sphereVanishing b)


end
end KIP126.Main.SectionSeven
