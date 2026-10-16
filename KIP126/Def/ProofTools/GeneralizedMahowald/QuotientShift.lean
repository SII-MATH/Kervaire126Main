module

import all KIP126.Def.ProofTools.StretchingRepresentatives
import all KIP126.Def.ProofTools.GeneralizedMahowald.NoReturn

/-! Shift a prescribed finite-quotient representative without changing its
restriction. Cofiber comparison choices agree after evaluation on spheres;
this uses the actual finite filtration window, not uniqueness of cone maps. -/

@[expose] section
namespace KIP126.ProofTools.Internal.Mahowald
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.AdamsSynthetic
open KIP126.Kervaire.Route KIP126.AdamsSynthetic.Standard
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

private theorem quotient_restriction_maps_equal_on_spheres
    (X Y : ClassicalObject) (i q : ℕ) (hi : 0 < i) (hiq : i ≤ q)
    (f g : XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q ⟶
      XModLambdaN (model.nu.functor.obj (Y.obj model.auxiliary)) i)
    (hfg : XModLambdaN.incl _ q ≫ f = XModLambdaN.incl _ q ≫ g) :
    ∀ (m w : ℤ) (c : BiHom m w
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q)),
      c ≫ f = c ≫ g := by
  apply quotient_maps_equal_on_spheres_of_no_return q f g hfg
  intro m w c z
  let V := model.nu.functor.obj (X.obj model.auxiliary)
  let ε : ((SyntheticCategory.biShift (0,-(q:ℤ))).obj V)⟦(1:ℤ)⟧ ≅
      (SyntheticCategory.biShift (0,-(q:ℤ)-1)).obj
        (model.nu.functor.obj ((ClassicalObject.shift 1 X).obj model.auxiliary)) :=
    (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).symm.app _ ≪≫
      (SyntheticCategory.biShift_comp (0,-(q:ℤ)) (1,0)).app V ≪≫
      eqToIso (congrArg (fun p => (SyntheticCategory.biShift p).obj V)
        (show (0,-(q:ℤ))+(1,0)=(1,1)+(0,-(q:ℤ)-1) by ext <;> simp)) ≪≫
      (SyntheticCategory.biShift_comp (1,1) (0,-(q:ℤ)-1)).symm.app V ≪≫
      (SyntheticCategory.biShift (0,-(q:ℤ)-1)).mapIso (model.nu.suspensionIso _).symm
  have h := nonreturn_at_window_end (.shift 1 X) Y i hi (-(q:ℤ)-1)
    (by omega) m w (c ≫ ε.hom) (ε.inv ≫ z)
  simpa only [Category.assoc,Iso.hom_inv_id_assoc] using h

private theorem shift_preserves_sphere_congruence (A B : SyntheticSpectrum)
    (δ : ℤ × ℤ) (f g : A ⟶ B)
    (hfg : ∀ (m w : ℤ) (c : BiHom m w A), c ≫ f = c ≫ g)
    (m w : ℤ) (c : BiHom m w ((SyntheticCategory.biShift δ).obj A)) :
    c ≫ (SyntheticCategory.biShift δ).map f =
      c ≫ (SyntheticCategory.biShift δ).map g := by
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) δ
  let ff := SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) δ
  let ε : F.obj (Smn (m-δ.1) (w-δ.2)) ≅ Smn m w :=
    (biShiftAddIso (m-δ.1,w-δ.2) δ (m,w) (by ext <;> simp)).app S_0_0
  let c₀ := ff.preimage (ε.hom ≫ c)
  have h := congrArg F.map (hfg (m-δ.1) (w-δ.2) c₀)
  have hc : F.map c₀ = ε.hom ≫ c := ff.map_preimage _
  rw [Functor.map_comp,Functor.map_comp,hc] at h
  apply (cancel_epi ε.hom).mp
  simpa only [Category.assoc] using h

private theorem shifted_quotient_sphere_congruence
    (X Y : ClassicalObject) (δ : ℤ × ℤ)
    (i q : ℕ) (hi : 0 < i) (hiq : i ≤ q)
    (e : XModLambdaN ((SyntheticCategory.biShift δ).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) q ≅
      (SyntheticCategory.biShift δ).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
    (he : XModLambdaN.incl _ q ≫ e.hom =
      (SyntheticCategory.biShift δ).map (XModLambdaN.incl _ q))
    (f g : XModLambdaN ((SyntheticCategory.biShift δ).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) q ⟶
      (SyntheticCategory.biShift δ).obj
        (XModLambdaN (model.nu.functor.obj (Y.obj model.auxiliary)) i))
    (hfg : XModLambdaN.incl _ q ≫ f = XModLambdaN.incl _ q ≫ g)
    (m w : ℤ) (c : BiHom m w (XModLambdaN ((SyntheticCategory.biShift δ).obj
      (model.nu.functor.obj (X.obj model.auxiliary))) q)) : c ≫ f = c ≫ g := by
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) δ
  let ff := SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) δ
  let f₀ := ff.preimage (e.inv ≫ f)
  let g₀ := ff.preimage (e.inv ≫ g)
  have hf : F.map f₀ = e.inv ≫ f := ff.map_preimage _
  have hg : F.map g₀ = e.inv ≫ g := ff.map_preimage _
  have h₀ : XModLambdaN.incl _ q ≫ f₀ = XModLambdaN.incl _ q ≫ g₀ := by
    apply ff.map_injective
    rw [Functor.map_comp,Functor.map_comp,hf,hg,←he]
    simpa only [Category.assoc,Iso.hom_inv_id_assoc] using hfg
  have hbase := quotient_restriction_maps_equal_on_spheres X Y i q hi hiq f₀ g₀ h₀
  have h := shift_preserves_sphere_congruence _ _ δ f₀ g₀ hbase m w (c ≫ e.hom)
  rw [hf,hg] at h
  simpa only [Category.assoc,Iso.hom_inv_id_assoc] using h

private theorem quotient_shift_restriction_on_spheres
    (X : ClassicalObject) (δ : ℤ × ℤ)
    (i q : ℕ) (hi : 0 < i) (hiq : i ≤ q)
    (eᵢ : XModLambdaN ((SyntheticCategory.biShift δ).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) i ≅
      (SyntheticCategory.biShift δ).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) i))
    (e_q : XModLambdaN ((SyntheticCategory.biShift δ).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) q ≅
      (SyntheticCategory.biShift δ).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
    (hᵢ : XModLambdaN.incl _ i ≫ eᵢ.hom =
      (SyntheticCategory.biShift δ).map (XModLambdaN.incl _ i))
    (h_q : XModLambdaN.incl _ q ≫ e_q.hom =
      (SyntheticCategory.biShift δ).map (XModLambdaN.incl _ q))
    (m w : ℤ) (c : BiHom m w (XModLambdaN ((SyntheticCategory.biShift δ).obj
      (model.nu.functor.obj (X.obj model.auxiliary))) q)) :
    c ≫ (model.quotients.tower _).rho i q hiq ≫ eᵢ.hom =
      c ≫ e_q.hom ≫ (SyntheticCategory.biShift δ).map
        ((model.quotients.tower _).rho i q hiq) := by
  apply shifted_quotient_sphere_congruence X X δ i q hi hiq e_q h_q
  rw [←Category.assoc,(model.quotients.tower _).rho_quotient hiq,hᵢ,
    ←Category.assoc,h_q,←Functor.map_comp,(model.quotients.tower _).rho_quotient hiq]

private def quotientShiftDesuspend (X : ClassicalObject) (δ : ℤ × ℤ) (q : ℕ)
    (e : XModLambdaN ((SyntheticCategory.biShift δ).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) q ≅
      (SyntheticCategory.biShift δ).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
    (m w : ℤ) (c : BiHom m w (XModLambdaN ((SyntheticCategory.biShift δ).obj
      (model.nu.functor.obj (X.obj model.auxiliary))) q)) :
    BiHom (m-δ.1) (w-δ.2)
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q) :=
  (SyntheticCategory.biShift_fullyFaithful δ).preimage
    ((biShiftAddIso (m-δ.1,w-δ.2) δ (m,w) (by ext <;> simp)).hom.app S_0_0 ≫
      c ≫ e.hom)

private theorem quotient_shift_desuspend_restriction
    (X : ClassicalObject) (δ : ℤ × ℤ)
    (i q : ℕ) (hi : 0 < i) (hiq : i ≤ q)
    (eᵢ : XModLambdaN ((SyntheticCategory.biShift δ).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) i ≅
      (SyntheticCategory.biShift δ).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) i))
    (e_q : XModLambdaN ((SyntheticCategory.biShift δ).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) q ≅
      (SyntheticCategory.biShift δ).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
    (hᵢ : XModLambdaN.incl _ i ≫ eᵢ.hom =
      (SyntheticCategory.biShift δ).map (XModLambdaN.incl _ i))
    (h_q : XModLambdaN.incl _ q ≫ e_q.hom =
      (SyntheticCategory.biShift δ).map (XModLambdaN.incl _ q))
    (m w : ℤ)
    (a : BiHom m w (XModLambdaN ((SyntheticCategory.biShift δ).obj
      (model.nu.functor.obj (X.obj model.auxiliary))) i))
    (c : BiHom m w (XModLambdaN ((SyntheticCategory.biShift δ).obj
      (model.nu.functor.obj (X.obj model.auxiliary))) q))
    (hc : c ≫ (model.quotients.tower _).rho i q hiq = a) :
    quotientShiftDesuspend X δ q e_q m w c ≫ (model.quotients.tower _).rho i q hiq =
      quotientShiftDesuspend X δ i eᵢ m w a := by
  apply (SyntheticCategory.biShift_fullyFaithful δ).map_injective
  rw [Functor.map_comp]
  simp only [quotientShiftDesuspend,Functor.FullyFaithful.map_preimage,Category.assoc]
  have h := quotient_shift_restriction_on_spheres X δ i q hi hiq eᵢ e_q hᵢ h_q m w c
  rw [←Category.assoc,hc] at h
  rw [←h]

end
end KIP126.ProofTools.Internal.Mahowald
