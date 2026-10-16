module
import all KIP126.Def.ProofTools.GeneralizedMahowald.FSourceActual

@[expose] section
namespace KIP126.ProofTools.Internal.Mahowald
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard KIP126.Literature
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
set_option Elab.async false

private theorem quotient_shift_desuspend_as_native_unshift
    (X : ClassicalObject) (δ p : ℤ×ℤ) (q : ℕ) (m w : ℤ)
    (hm : m-δ.1=p.1) (hw : w-δ.2=p.2)
    (ε : XModLambdaN ((SyntheticCategory.biShift δ).obj
      (model.nu.functor.obj (X.obj model.auxiliary))) q ≅
      (SyntheticCategory.biShift δ).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
    (a : BiHom m w (XModLambdaN ((SyntheticCategory.biShift δ).obj
      (model.nu.functor.obj (X.obj model.auxiliary))) q)) :
    homotopyRegrade hm hw (quotientShiftDesuspend X δ q ε m w a) =
      quotientUnshift X δ p q ε
        (homotopyRegrade (by dsimp; omega : m=(p+δ).1)
          (by dsimp; omega : w=(p+δ).2) a) := by
  rcases p with ⟨pm,pw⟩
  dsimp only [Prod.fst,Prod.snd] at hm hw
  subst pm; subst pw
  simp only [quotientShiftDesuspend,quotientUnshift,
    biShiftAddIso,Iso.trans_hom,eqToIso.hom,eqToHom_app,
    NatTrans.comp_app,regrade_precomp,Category.assoc,eqToHom_refl,Category.id_comp]

private theorem normalized_f_raw_source_unshift_detects
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g + normalizedExponent model.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible model T he)
    (r k : ℕ) (hkr : k<r) (sf tf m w : ℤ) (x : Ambient model T.X (sf,tf))
    (hm : m-1=tf-sf)
    (hw : w-((normalizedExponent model.classicalTower T.f : ℤ)+
      normalizedExponent model.classicalTower T.g)=tf-k)
    (εmain : XModLambdaN ((SyntheticCategory.biShift
      (1,(normalizedExponent model.classicalTower T.f : ℤ)+normalizedExponent model.classicalTower T.g)).obj
        (model.nu.functor.obj (T.X.obj model.auxiliary))) r ≅
      (SyntheticCategory.biShift
        (1,(normalizedExponent model.classicalTower T.f : ℤ)+normalizedExponent model.classicalTower T.g)).obj
          (XModLambdaN (model.nu.functor.obj (T.X.obj model.auxiliary)) r))
    (hεmain : XModLambdaN.incl _ r≫εmain.hom =
      (SyntheticCategory.biShift
        (1,(normalizedExponent model.classicalTower T.f : ℤ)+normalizedExponent model.classicalTower T.g)).map
          (XModLambdaN.incl _ r))
    (cGeometry : BiHom m w
      (XModLambdaN (HasFunctorialCofiber.cofib (model.normalizedMap T.Y T.Z T.g).map) r))
    (hc : Detects (model.convergence (.quotient r (.nu T.X))) (sf,tf,tf-k)
      (finiteTargetLabel model T.X r sf tf k x)
      (homotopyRegrade hm hw
        (quotientShiftDesuspend T.X
          (1,(normalizedExponent model.classicalTower T.f : ℤ)+normalizedExponent model.classicalTower T.g)
          r εmain m w
          (cGeometry≫XModLambdaN.map (normalized_g_cofiber_iso T he hT).hom r)))) :
    let cNative := homotopyRegrade
      (show m=((tf-sf,tf-k)+(1,(normalizedExponent model.classicalTower T.f : ℤ)+
        normalizedExponent model.classicalTower T.g)).1 by dsimp; omega)
      (show w=((tf-sf,tf-k)+(1,(normalizedExponent model.classicalTower T.f : ℤ)+
        normalizedExponent model.classicalTower T.g)).2 by dsimp; omega) cGeometry
    let ef : ℤ := normalizedExponent model.classicalTower T.f
    let eg : ℤ := normalizedExponent model.classicalTower T.g
    let p : ℤ×ℤ := (tf-sf,tf-k)
    let Cg := HasFunctorialCofiber.cofib (model.normalizedMap T.Y T.Z T.g).map
    ∃ (εRaw : XModLambdaN ((SyntheticCategory.biShift (0,-eg)).obj Cg) r ≅
        (SyntheticCategory.biShift (0,-eg)).obj (XModLambdaN Cg r))
      (εe : XModLambdaN ((SyntheticCategory.biShift (0,ef)).obj
          (model.nu.functor.obj (T.X.obj model.auxiliary))) r ≅
        (SyntheticCategory.biShift (0,ef)).obj
          (XModLambdaN (model.nu.functor.obj (T.X.obj model.auxiliary)) r))
      (εs : XModLambdaN ((SyntheticCategory.biShift (1,0)).obj
          ((SyntheticCategory.biShift (0,ef)).obj
            (model.nu.functor.obj (T.X.obj model.auxiliary)))) r ≅
        (SyntheticCategory.biShift (1,0)).obj
          (XModLambdaN ((SyntheticCategory.biShift (0,ef)).obj
            (model.nu.functor.obj (T.X.obj model.auxiliary))) r)),
      XModLambdaN.incl _ r≫εRaw.hom=(SyntheticCategory.biShift (0,-eg)).map (XModLambdaN.incl _ r) ∧
      XModLambdaN.incl _ r≫εe.hom=(SyntheticCategory.biShift (0,ef)).map (XModLambdaN.incl _ r) ∧
      XModLambdaN.incl _ r≫εs.hom=(SyntheticCategory.biShift (1,0)).map (XModLambdaN.incl _ r) ∧
      let aRaw := homotopyRegrade
        (show (((p+(1,ef+eg))+(0,-eg)).1)=(((p+(0,ef))+(1,0)).1) by dsimp; omega)
        (show (((p+(1,ef+eg))+(0,-eg)).2)=(((p+(0,ef))+(1,0)).2) by dsimp; omega)
        (shiftHomotopyClass (0,-eg) (p+(1,ef+eg)) cNative≫εRaw.inv)
      let α := quotientClassUnshift _ (1,0) (p+(0,ef)) r εs
        (aRaw≫XModLambdaN.map (-(normalized_f_suspended_source_iso T he hT).hom) r)
      Detects (model.convergence (.quotient r (.nu T.X))) (sf,tf,tf-k)
        (finiteTargetLabel model T.X r sf tf k x)
        (quotientUnshift T.X (0,ef) p r εe α) := by
  dsimp only
  let δ : ℤ×ℤ := (1,(normalizedExponent model.classicalTower T.f : ℤ)+
    normalizedExponent model.classicalTower T.g)
  let p : ℤ×ℤ := (tf-sf,tf-k)
  let cNative := homotopyRegrade
    (show m=(p+δ).1 by dsimp [p,δ]; omega)
    (show w=(p+δ).2 by dsimp [p,δ]; omega) cGeometry
  have hnative : Detects (model.convergence (.quotient r (.nu T.X))) (sf,tf,tf-k)
      (finiteTargetLabel model T.X r sf tf k x)
      (quotientUnshift T.X δ p r εmain
        (cNative≫XModLambdaN.map (normalized_g_cofiber_iso T he hT).hom r)) := by
    dsimp only [cNative]
    rw [←regrade_comp]
    rw [←quotient_shift_desuspend_as_native_unshift T.X δ p r m w hm hw εmain]
    exact hc
  exact normalized_f_actual_source_unshift_detects T he hT r k hkr sf tf x εmain hεmain cNative hnative

end
end KIP126.ProofTools.Internal.Mahowald
