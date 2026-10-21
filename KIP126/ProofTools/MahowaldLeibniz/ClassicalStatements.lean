module

import all KIP126.ProofTools.MahowaldLeibniz.PositiveBranches
import all KIP126.ProofTools.MahowaldLeibniz.TerminalSquare
import all KIP126.ProofTools.GeneralizedMahowald.RotatedNuTriangle
import KIP126.ProofTools.MahowaldLeibniz

/-! Internal classical statements for all three normalized exponent positions.
Every operation is constructed from the selected normalized map. These
definitions contain no theorem or extra input supplying a desired output. -/

@[expose] section
namespace KIP126.ProofTools.Internal.MahowaldLeibniz
open CategoryTheory
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard KIP126.Literature
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
open KIP126.ProofTools.Internal.Leibniz
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2000000

private def classicalLabelRegrade {X : ClassicalObject} {p q : ℤ×ℤ}
    (h : p=q) (x : Ambient model X p) : Ambient model X q := h ▸ x

private theorem classical_first_quotient_regrade
    (X : ClassicalObject) (k s t s' t' : ℤ) (hs : s=s') (ht : t=t')
    (a : BiHom (t-s) (t+k) (XModLambdaN
      ((SyntheticCategory.biShift (0,k)).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) 1)) :
    classicalLabelRegrade (q := (s',t')) (Prod.ext hs ht)
      (model.firstQuotient X k s t a) =
    model.firstQuotient X k s' t'
      (homotopyRegrade (by omega) (by omega) a) := by
  subst s'
  subst t'
  rfl

/-- The actual normalized first-quotient operation, retaining its exponent. -/
private def normalizedClassicalOperation (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (s t : ℤ) (x : Ambient model X (s,t)) :
    Ambient model Y (s+normalizedExponent model.classicalTower f,
      t+normalizedExponent model.classicalTower f) :=
  model.firstQuotient Y 0
    (s+normalizedExponent model.classicalTower f)
    (t+normalizedExponent model.classicalTower f)
    (homotopyRegrade (by omega) (by omega)
      ((model.firstQuotient X (normalizedExponent model.classicalTower f) s t).symm x ≫
        XModLambdaN.map (model.normalizedMap X Y f).map 1 ≫
        XModLambdaN.map (SyntheticCategory.biShift_zero.inv.app _) 1))

private theorem normalized_classical_operation_native_label
    (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (s t : ℤ) (x : Ambient model X (s,t)) :
    nativeFirstLabel Y (s+normalizedExponent model.classicalTower f)
      (t+normalizedExponent model.classicalTower f)
      (normalizedClassicalOperation X Y f s t x) =
    homotopyRegrade (by omega) (by omega)
      ((model.firstQuotient X (normalizedExponent model.classicalTower f) s t).symm x ≫
        XModLambdaN.map (model.normalizedMap X Y f).map 1) := by
  rw [nativeFirstLabel_eq_regrade]
  simp only [normalizedClassicalOperation,LinearEquiv.symm_apply_apply,
    regrade_precomp,Category.assoc,←model.quotients.functoriality.map_comp,
    Iso.inv_hom_id_app]
  simp only [←Category.assoc,eqToHom_trans]
  erw [Category.comp_id]

/-- The actual selected normalized arrow, transported to exponent one. -/
private def normalizedClassicalPositiveMap (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (hf : normalizedExponent model.classicalTower f = 1) :
    (SyntheticCategory.biShift (0,1)).obj
      (model.nu.functor.obj (X.obj model.auxiliary)) ⟶
        model.nu.functor.obj (Y.obj model.auxiliary) := by
  simpa only [hf,Nat.cast_one] using (model.normalizedMap X Y f).map

/-- Exponent one is the positive first-quotient operation of the same map. -/
private theorem normalized_classical_operation_one
    (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (hf : normalizedExponent model.classicalTower f = 1)
    (s t : ℤ) (x : Ambient model X (s,t)) :
    classicalLabelRegrade (q := (s+1,t+1))
      (by simp only [hf,Nat.cast_one]) (normalizedClassicalOperation X Y f s t x) =
    positiveFirstQuotientOperation X Y (normalizedClassicalPositiveMap X Y f hf) s t x := by
  have transport (k : ℕ) (hk : k=1)
      (F : (SyntheticCategory.biShift (0,(k:ℤ))).obj
        (model.nu.functor.obj (X.obj model.auxiliary)) ⟶
          model.nu.functor.obj (Y.obj model.auxiliary)) :
      classicalLabelRegrade (q := (s+1,t+1)) (by simp only [hk,Nat.cast_one])
        (model.firstQuotient Y 0 (s+k) (t+k)
          (homotopyRegrade (by omega) (by omega)
            ((model.firstQuotient X k s t).symm x ≫ XModLambdaN.map F 1 ≫
              XModLambdaN.map (SyntheticCategory.biShift_zero.inv.app _) 1))) =
      positiveFirstQuotientOperation X Y
        (by simpa only [hk,Nat.cast_one] using F) s t x := by
    subst k
    rfl
  exact transport _ hf _

/-- In the f-position the calibrated positive operation is the existing
cofiber first-quotient operation, with no additional comparison premise. -/
private theorem normalized_classical_operation_f_one
    (T : TriangleData model.auxiliary)
    (hf : normalizedExponent model.classicalTower T.f = 1)
    (s t : ℤ) (x : Ambient model T.X (s,t)) :
    classicalLabelRegrade (q := (s+1,t+1))
      (by simp only [hf,Nat.cast_one])
      (normalizedClassicalOperation T.X T.Y T.f s t x) =
    KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t x := by
  rw [normalized_classical_operation_one _ _ _ hf]
  rfl

private theorem native_first_label_injective (X : ClassicalObject) (s t : ℤ) :
    Function.Injective (nativeFirstLabel X s t) := by
  intro x y h
  rw [nativeFirstLabel_eq_regrade,nativeFirstLabel_eq_regrade] at h
  have h' := congrArg (fun a => a ≫
    XModLambdaN.map (SyntheticCategory.biShift_zero.inv.app _) 1) h
  simp only [Category.assoc,←model.quotients.functoriality.map_comp,
    Iso.hom_inv_id_app,model.quotients.functoriality.map_id,Category.comp_id] at h'
  apply (model.firstQuotient X 0 s t).symm.injective
  have injective_regrade {A : SyntheticSpectrum} {m m' w w' : ℤ}
      (hm : m=m') (hw : w=w') :
      Function.Injective (homotopyRegrade (X := A) hm hw) := by
    subst m'
    subst w'
    exact fun _ _ h => h
  exact injective_regrade rfl (Int.add_zero t) h'

/-- Exponent zero agrees with the ordinary classical page map. The proof
uses the actual normalized factorization and first-quotient naturality. -/
private theorem normalized_classical_operation_zero
    (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (hf : normalizedExponent model.classicalTower f = 0)
    (s t : ℤ) (x : Ambient model X (s,t)) :
    classicalLabelRegrade (q := (s,t))
      (by simp only [hf,Nat.cast_zero,add_zero])
      (normalizedClassicalOperation X Y f s t x) =
    (model.classical.map f).pageMap 2 (s,t) x := by
  have transport (k : ℕ) (hk : k=0)
      (F : (SyntheticCategory.biShift (0,(k:ℤ))).obj
        (model.nu.functor.obj (X.obj model.auxiliary)) ⟶
          model.nu.functor.obj (Y.obj model.auxiliary))
      (hF : F = eqToHom (congrArg (fun j : ℕ =>
        (SyntheticCategory.biShift (0,(j:ℤ))).obj
          (model.nu.functor.obj (X.obj model.auxiliary))) hk) ≫
        SyntheticCategory.biShift_zero.hom.app _ ≫ model.nu.functor.map f) :
      classicalLabelRegrade (q := (s,t)) (by simp only [hk,Nat.cast_zero,add_zero])
        (model.firstQuotient Y 0 (s+k) (t+k)
          (homotopyRegrade (by omega) (by omega)
            ((model.firstQuotient X k s t).symm x ≫ XModLambdaN.map F 1 ≫
              XModLambdaN.map (SyntheticCategory.biShift_zero.inv.app _) 1))) =
      (model.classical.map f).pageMap 2 (s,t) x := by
    subst k
    simp only [eqToHom_refl,Category.id_comp] at hF
    subst F
    rw [classical_first_quotient_regrade _ _ _ _ _ _ (by omega) (by omega)]
    apply native_first_label_injective Y s t
    rw [←native_first_label_natural X Y f]
    rw [nativeFirstLabel_eq_regrade,nativeFirstLabel_eq_regrade]
    simp only [LinearEquiv.symm_apply_apply,regrade_precomp,
      model.quotients.functoriality.map_comp,Category.assoc]
    simp only [←model.quotients.functoriality.map_comp,Iso.inv_hom_id_app,
      model.quotients.functoriality.map_id]
    simp only [←Category.assoc,eqToHom_trans]
    erw [Category.comp_id]
    rw [model.quotients.functoriality.map_comp,Category.assoc]
    rfl
  exact transport _ hf _ (normalized_zero_map X Y f hf)

/-- The PDF's NC1/NC2 classical composition proposition for the original
triangle, including all three positions of the positive exponent. -/
private def ClassicalNCCompositionStatement
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g +
      normalizedExponent model.classicalTower T.h = 1) : Prop :=
  let ef := normalizedExponent model.classicalTower T.f
  let eg := normalizedExponent model.classicalTower T.g
  let eh := normalizedExponent model.classicalTower T.h
  ∀ (_hT : NormalizedTriangleCompatible model T he)
    (R K : ℕ), 2 ≤ R → 2 ≤ K → ∀ (s t : ℤ)
    (x : Ambient model T.X (s,t))
    (z : Ambient model T.Z (s+R-eh,t+R-eh))
    (v : Ambient model T.Y (s+R+ef+K-1,t+R+ef+K-2)),
    IsCycle model T.X ((R:ℤ)-1) (s,t) x →
    IsCycle model T.Z ((K:ℤ)-1) (s+R-eh,t+R-eh) z →
    (∃ u : Ambient model T.X (s+R,t+R-1),
      (model.classicalSuspension T.X).DesuspendsClass (s+R) (t+R)
        (classicalLabelRegrade (X := .shift 1 T.X) (q := (s+R,t+R))
          (by dsimp only [eh]; ext <;> dsimp only [Prod.fst,Prod.snd] <;> omega)
          (normalizedClassicalOperation T.Z (.shift 1 T.X) T.h
            (s+R-eh) (t+R-eh) z)) u ∧
      DifferentialAt model T.X R (s,t) (s+R,t+R-1) x u) →
    DifferentialAt model T.Z K (s+R-eh,t+R-eh)
      (s+R-eh+K,t+R-eh+K-1) z
      (classicalLabelRegrade (X := T.Z) (q := (s+R-eh+K,t+R-eh+K-1)) (by
          dsimp only [ef,eg,eh]
          ext <;> dsimp only [Prod.fst,Prod.snd] <;> omega)
        (normalizedClassicalOperation T.Y T.Z T.g
          (s+R+ef+K-1) (t+R+ef+K-2) v)) →
    (∀ j : ℕ, 1 ≤ j → j < K-1 →
      cycles model T.X ((K:ℤ)-j) (s+R+j,t+R+j-1) ≤
        boundaries model T.X ((R:ℤ)+j-1) (s+R+j,t+R+j-1)) →
    (∀ a : Ambient model T.X (s+R+K-1,t+R+K-2),
      normalizedClassicalOperation T.X T.Y T.f
        (s+R+K-1) (t+R+K-2) a ∈
      boundaries model T.Y ((R:ℤ)+K-2)
        ((s+R+K-1)+ef,(t+R+K-2)+ef)) →
    let y := normalizedClassicalOperation T.X T.Y T.f s t x
    IsCycle model T.Y ((R:ℤ)+K-2) (s+ef,t+ef) y ∧
      DifferentialAt model T.Y ((R:ℤ)+K-1) (s+ef,t+ef)
        (s+R+ef+K-1,t+R+ef+K-2) y v

end
end KIP126.ProofTools.Internal.MahowaldLeibniz
