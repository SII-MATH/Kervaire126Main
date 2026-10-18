module

import all KIP126.Main.SectionSeven.Predicates
/-! The multiplied Toda indeterminacy calculation from
Kervaire126 bbac1fc05843, Main/Solution/Route/Section7/Indeterminacy.lean
(MIT; see the retained source LICENSE). The actual order-two hypotheses are retained; no
characteristic-two assertion is made about arbitrary homotopy groups. -/

@[expose] section
namespace KIP126.Main.SectionSeven
open CategoryTheory
open KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.AdamsSynthetic KIP126.AdamsSynthetic.Standard
open KIP126.Literature.Route
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
local instance shiftAdditive (p : ℤ × ℤ) :
    (SyntheticCategory.biShift (Syn := SyntheticSpectrum) p).Additive :=
  graded_shiftAdditive p
local notation "S" => (S_0_0 : SyntheticSpectrum)
local notation "h₀" => KIP126.Literature.Standard.syntheticH0

private theorem lambda_h0_of_two_torsion (m n : ℤ) (x : BiHom m n S)
    (hx : x + x = 0) : lambdaMultiply 2 (sphereProduct h₀ x) = 0 := by
  let F := SyntheticCategory.biShift (Syn := SyntheticSpectrum) (m,n)
  have htwo : F.map syntheticTwo ≫ x = 0 := by
    simp only [F, syntheticTwo, Functor.id_obj, Functor.map_comp, two_smul, Functor.map_add,
      Category.assoc, Preadditive.add_comp]
    rw [(SyntheticCategory.biShift (Syn := SyntheticSpectrum) (m,n)).map_id S]
    simp only [Category.id_comp, hx, Limits.comp_zero]
  have hshift : F.map (lambdaMultiply 1 h₀) ≫ x = 0 := by
    rw [KIP126.Literature.Standard.toda_lambda_h0]
    exact htwo
  have hpre : F.map (SyntheticCategory.lam.app (Smn 0 1)) ≫ F.map h₀ ≫ x = 0 := by
    dsimp only [lambdaMultiply] at hshift
    rw [lambdaPow_one graded_coherence] at hshift
    simp only [F, eqToHom_refl, Functor.map_comp,
      Category.id_comp, Category.assoc] at hshift
    apply (cancel_epi ((SyntheticCategory.biShift (m,n)).map
      ((SyntheticCategory.biShift_comp (0,1) (0,-1)).inv.app S))).mp
    simpa [F, Smn] using hshift
  have hlam : SyntheticCategory.lam.app (F.obj (Smn 0 1)) ≫ F.map h₀ ≫ x = 0 := by
    rw [graded_coherence.lambda_comm (m,n) (Smn 0 1)]
    simpa only [F, Category.assoc, Limits.comp_zero] using
      congrArg (fun z => (biShiftAddIso (m,n) (0,-1) ((m,n)+(0,-1)) rfl).hom.app
        (Smn 0 1) ≫ (biShiftAddIso (0,-1) (m,n) ((m,n)+(0,-1)) (add_comm _ _)).inv.app
        (Smn 0 1) ≫ z) hpre
  have hraw : lambdaPow 1 (Smn (0+m) (1+n)) ≫ sphereProduct h₀ x = 0 := by
    rw [lambdaPow_one graded_coherence]
    dsimp only [sphereProduct]
    have hnat := SyntheticCategory.lam.naturality
      ((SyntheticCategory.biShift_comp (0,1) (m,n)).inv.app S)
    simp only [Smn, Prod.mk_add_mk, Functor.comp_obj, Functor.id_obj, Functor.id_map] at hnat ⊢
    rw [← Category.assoc, ← hnat, Category.assoc]
    simpa [F, Smn] using
      congrArg (fun z => (SyntheticCategory.biShift (0,-1)).map
        ((SyntheticCategory.biShift_comp (0,1) (m,n)).inv.app S) ≫ z) hlam
  dsimp only [lambdaMultiply]
  rw [lambdaPow_add graded_coherence 1 1 2 rfl]
  simp only [Category.assoc, hraw, Limits.comp_zero]

private theorem multiplied_indeterminacy_of_two_torsion
    (theta : BiHom 62 64 S) (htheta : theta + theta = 0)
    (b : BiHom 62 70 S) (hb : b + b = 0) :
    ThetaBMultipliedIndeterminacy h₀ theta b ∧ SymmetricTwoMultipliedIndeterminacy b := by
  constructor
  · intro a c
    apply lambda_h0_of_two_torsion
    have hleft : sphereProduct theta a + sphereProduct theta a = 0 := by
      simpa [sphereProduct, Functor.map_add, Preadditive.comp_add, Preadditive.add_comp]
        using congrArg (fun z => sphereProduct z a) htheta
    have hright : sphereProduct c b + sphereProduct c b = 0 := by
      simpa [sphereProduct, Preadditive.comp_add] using congrArg (fun z => sphereProduct c z) hb
    rw [add_add_add_comm, hleft, hright, zero_add]
  · intro a c
    have hleft : sphereProduct syntheticTwo a = a + a := by
      have hc := graded_coherence.left_unit (63,64) S
      have hc' : (SyntheticCategory.biShift_comp (0,0) (63,64)).hom.app S =
          (SyntheticCategory.biShift (63,64)).map (SyntheticCategory.biShift_zero.hom.app S) := by
        change (biShiftAddIso (0,0) (63,64) (63,64) (by decide)).hom.app S = _ at hc
        simpa only [biShiftAddIso, Iso.trans_hom, NatTrans.comp_app,
          eqToIso.hom, eqToHom_app, eqToHom_refl, Category.comp_id] using hc
      dsimp only [sphereProduct, syntheticTwo]
      simp only [Functor.id_obj, Functor.map_comp, two_smul, Functor.map_add, Category.assoc,
        Preadditive.add_comp]
      rw [(SyntheticCategory.biShift (Syn := SyntheticSpectrum) (63,64)).map_id S]
      simp only [Category.id_comp]
      rw [← hc']
      simp
    have hright : sphereProduct c syntheticTwo = c + c := by
      have hc := graded_coherence.right_unit (63,64) S
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


end
end KIP126.Main.SectionSeven
