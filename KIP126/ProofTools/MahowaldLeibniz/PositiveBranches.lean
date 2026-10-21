module

import all KIP126.ProofTools.MahowaldLeibniz.FixedModel
import all KIP126.ProofTools.GeneralizedLeibniz.LevelSource
import all KIP126.ProofTools.GeneralizedMahowald.KernelTriangles
import all KIP126.ProofTools.GeneralizedMahowald.HMapCoherence
import all KIP126.ProofTools.MahowaldLeibniz.TerminalSquare

/-! Actual first-quotient operations and finite boundary comparisons for
the positive second and third normalization exponents. The negative weight
labels are transported through the actual quotient shift, rather than
identified with an independently chosen shifted comparison. -/

@[expose] section
namespace KIP126.ProofTools.Internal.MahowaldLeibniz
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard KIP126.Literature
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
open KIP126.ProofTools.Internal.Leibniz
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2000000

/-- The first-quotient operation of an actual positive normalized arrow.
The degree shift is (1,1), regardless of the filtration of the unnormalized
classical arrow. -/
private def positiveFirstQuotientOperation (X Y : ClassicalObject)
    (F : (SyntheticCategory.biShift (0,1)).obj
      (model.nu.functor.obj (X.obj model.auxiliary)) ⟶
        model.nu.functor.obj (Y.obj model.auxiliary))
    (s t : ℤ) (x : Ambient model X (s,t)) : Ambient model Y (s+1,t+1) :=
  model.firstQuotient Y 0 (s+1) (t+1)
    (homotopyRegrade (by omega) (by omega)
      ((model.firstQuotient X 1 s t).symm x ≫ XModLambdaN.map F 1 ≫
        XModLambdaN.map (SyntheticCategory.biShift_zero.inv.app _) 1))

private theorem positive_first_quotient_native_label (X Y : ClassicalObject)
    (F : (SyntheticCategory.biShift (0,1)).obj
      (model.nu.functor.obj (X.obj model.auxiliary)) ⟶
        model.nu.functor.obj (Y.obj model.auxiliary))
    (s t : ℤ) (x : Ambient model X (s,t)) :
    nativeFirstLabel Y (s+1) (t+1) (positiveFirstQuotientOperation X Y F s t x) =
      homotopyRegrade (by omega) (by omega)
        ((model.firstQuotient X 1 s t).symm x ≫ XModLambdaN.map F 1) := by
  have cast {m m' w w' : ℤ} (hm : m=m') (hw : w=w') {A : SyntheticSpectrum}
      (h : BiHom m w A = BiHom m' w' A) (a : BiHom m w A) :
      h.mp a = homotopyRegrade hm hw a := by
    subst m'
    subst w'
    rfl
  have hf (Y : ClassicalObject) (s t : ℤ) (x : Ambient model Y (s,t)) :
      firstLabel model Y s t x =
        homotopyRegrade rfl (show t+0=t by omega) ((model.firstQuotient Y 0 s t).symm x) := by
    unfold firstLabel
    exact cast rfl (by omega) _ _
  simp only [positiveFirstQuotientOperation,nativeFirstLabel,hf,
    LinearEquiv.symm_apply_apply,regrade_precomp,←Category.assoc,eqToHom_trans]
  simp only [Category.assoc,←model.quotients.functoriality.map_comp,
    Iso.inv_hom_id_app]
  erw [Category.comp_id]

/-- Self maps of a shifted finite quotient which agree on the actual
quotient inclusion also agree on every sphere class. -/
private theorem shifted_quotient_self_maps_equal_on_spheres
    (X : ClassicalObject) (e : ℤ) (q : ℕ) (hq : 0<q)
    (f g : XModLambdaN ((SyntheticCategory.biShift (0,e)).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) q ⟶
      XModLambdaN ((SyntheticCategory.biShift (0,e)).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) q)
    (hfg : XModLambdaN.incl _ q ≫ f = XModLambdaN.incl _ q ≫ g)
    (m w : ℤ) (a : BiHom m w (XModLambdaN ((SyntheticCategory.biShift (0,e)).obj
      (model.nu.functor.obj (X.obj model.auxiliary))) q)) : a≫f=a≫g := by
  let E := levelQuotientShiftIso X e q
  apply (cancel_mono E.hom).mp
  simpa only [Category.assoc] using shifted_quotient_sphere_congruence X X (0,e) q q hq le_rfl E
    (level_quotient_shift_incl X e q) (f≫E.hom) (g≫E.hom)
    (by simpa only [←Category.assoc] using congrArg (fun k => k≫E.hom) hfg) m w a

/-- The selected finite delta on a negatively shifted third vertex is
the actual projected cofiber boundary on sphere classes, with no extra
choice of a delta comparison as input. -/
private theorem shifted_selected_delta_evaluation_eq_cofiber
    (X : ClassicalObject) (e : ℤ) (i j : ℕ)
    (T : LambdaRhoDeltaTriangle ((SyntheticCategory.biShift (0,e)).obj
      (model.nu.functor.obj (X.obj model.auxiliary))) i j)
    (m w : ℤ) (a : BiHom m w
      (XModLambdaN ((SyntheticCategory.biShift (0,e)).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) i)) :
    a ≫ T.delta = a ≫ XModLambdaN.proj _ i ≫
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map
        ((SyntheticCategory.biShift (0,-(i:ℤ))).map
          (XModLambdaN.incl _ (j-i))) := by
  let A := (SyntheticCategory.biShift (0,e)).obj
    (model.nu.functor.obj (X.obj model.auxiliary))
  let base := XModLambdaN.cofiberTriangle A i
  obtain ⟨c,hc,hδ⟩ := complete_distinguished_triangle_morphism
    base (Triangle.mk T.lambdaMap T.rho T.delta)
    (XModLambdaN.cofiberTriangle_distinguished A i) T.distinguished
    ((SyntheticCategory.biShift (0,-(i:ℤ))).map (XModLambdaN.incl A (j-i)))
    (XModLambdaN.incl A j) T.lambda_quotient.symm
  change XModLambdaN A i ⟶ XModLambdaN A i at c
  change XModLambdaN.incl A i ≫ c = XModLambdaN.incl A j ≫ T.rho at hc
  have hc' : XModLambdaN.incl A i ≫ c = XModLambdaN.incl A i ≫ 𝟙 _ := by
    rw [hc,T.rho_quotient,Category.comp_id]
  have hac : a≫c=a := by
    simpa only [Category.comp_id] using
      shifted_quotient_self_maps_equal_on_spheres X e i T.i_pos c (𝟙 _) hc' m w a
  change XModLambdaN.proj A i ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map
      ((SyntheticCategory.biShift (0,-(i:ℤ))).map (XModLambdaN.incl A (j-i))) =
    c ≫ T.delta at hδ
  calc
    a ≫ T.delta = (a≫c)≫T.delta := by rw [hac]
    _ = a ≫ XModLambdaN.proj A i ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map
        ((SyntheticCategory.biShift (0,-(i:ℤ))).map (XModLambdaN.incl A (j-i))) := by
      rw [Category.assoc,←hδ]

/-- The actual quotient shift retains the cofiber projection, including
the exact functor's suspension comparison. -/
private theorem level_quotient_shift_projection (X : ClassicalObject)
    (e : ℤ) (q : ℕ) :
    let A := model.nu.functor.obj (X.obj model.auxiliary)
    let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,e)
    letI := model.exactness.shiftCommShift (0,e)
    (levelQuotientShiftIso X e q).hom ≫ F.map (XModLambdaN.proj A q) ≫
      (F.commShiftIso (1:ℤ)).hom.app _ ≫
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map
        ((shiftCommIso (0,e) (0,-(q:ℤ))).inv.app A) =
      XModLambdaN.proj (F.obj A) q := by
  let A := model.nu.functor.obj (X.obj model.auxiliary)
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,e)
  letI := model.exactness.shiftCommShift (0,e)
  have h := level_quotient_shift_boundary X e q
  change (levelQuotientShiftIso X e q).hom ≫ F.map (absoluteBoundary A q) ≫
    ((boundaryShiftNatIso e q).app A).hom = absoluteBoundary (F.obj A) q at h
  rw [boundaryShiftNatIso_app] at h
  simp only [absoluteBoundary,Iso.trans_hom,Iso.symm_hom,Functor.mapIso_hom,
    Functor.map_comp,Category.assoc] at h
  have h' := congrArg (fun k => k ≫ (biSuspensionIso q (F.obj A)).hom) h
  dsimp only [F,A] at h'
  simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id] at h'
  erw [Iso.map_inv_hom_id_assoc] at h'
  exact h'

private theorem shifted_adjacent_delta_projection (X : ClassicalObject)
    (e : ℤ) (q : ℕ) (hq : 0<q) (m w : ℤ)
    (a : BiHom m w (XModLambdaN ((SyntheticCategory.biShift (0,e)).obj
      (model.nu.functor.obj (X.obj model.auxiliary))) q)) :
    a ≫ adjacentDelta _ q hq = a ≫ XModLambdaN.proj _ q ≫
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map
        ((SyntheticCategory.biShift (0,-(q:ℤ))).map (XModLambdaN.incl _ 1)) := by
  have h := shifted_selected_delta_evaluation_eq_cofiber X e q (q+1)
    ((model.quotients.tower _).triangle hq (Nat.lt_succ_self q)) m w a
  let A := (SyntheticCategory.biShift (0,e)).obj
    (model.nu.functor.obj (X.obj model.auxiliary))
  have transport (n : ℕ) (hn : n=1)
      (d : XModLambdaN A q ⟶
        ((SyntheticCategory.biShift (0,-(q:ℤ))).obj (XModLambdaN A n))⟦(1:ℤ)⟧)
      (he : (XModLambdaN A q ⟶
        ((SyntheticCategory.biShift (0,-(q:ℤ))).obj (XModLambdaN A n))⟦(1:ℤ)⟧) =
        (XModLambdaN A q ⟶
        ((SyntheticCategory.biShift (0,-(q:ℤ))).obj (XModLambdaN A 1))⟦(1:ℤ)⟧))
      (h : a≫d=a≫XModLambdaN.proj A q≫(shiftFunctor SyntheticSpectrum (1:ℤ)).map
        ((SyntheticCategory.biShift (0,-(q:ℤ))).map (XModLambdaN.incl A n))) :
      a≫he.mp d=a≫XModLambdaN.proj A q≫(shiftFunctor SyntheticSpectrum (1:ℤ)).map
        ((SyntheticCategory.biShift (0,-(q:ℤ))).map (XModLambdaN.incl A 1)) := by
    subst n
    exact h
  exact transport (q+1-q) (by omega) _ (by rw [show q+1-q=1 by omega]) h

private theorem native_adjacent_delta_projection (X : ClassicalObject)
    (q : ℕ) (hq : 0<q) (m w : ℤ)
    (a : BiHom m w (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q)) :
    a ≫ adjacentDelta _ q hq = a ≫ XModLambdaN.proj _ q ≫
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map
        ((SyntheticCategory.biShift (0,-(q:ℤ))).map (XModLambdaN.incl _ 1)) := by
  have h := selected_delta_evaluation_eq_cofiber X q (q+1)
    ((model.quotients.tower _).triangle hq (Nat.lt_succ_self q)) m w a
  let A := model.nu.functor.obj (X.obj model.auxiliary)
  have transport (n : ℕ) (hn : n=1)
      (d : XModLambdaN A q ⟶
        ((SyntheticCategory.biShift (0,-(q:ℤ))).obj (XModLambdaN A n))⟦(1:ℤ)⟧)
      (he : (XModLambdaN A q ⟶
        ((SyntheticCategory.biShift (0,-(q:ℤ))).obj (XModLambdaN A n))⟦(1:ℤ)⟧) =
        (XModLambdaN A q ⟶
        ((SyntheticCategory.biShift (0,-(q:ℤ))).obj (XModLambdaN A 1))⟦(1:ℤ)⟧))
      (h : a≫d=a≫XModLambdaN.proj A q≫(shiftFunctor SyntheticSpectrum (1:ℤ)).map
        ((SyntheticCategory.biShift (0,-(q:ℤ))).map (XModLambdaN.incl A n))) :
      a≫he.mp d=a≫XModLambdaN.proj A q≫(shiftFunctor SyntheticSpectrum (1:ℤ)).map
        ((SyntheticCategory.biShift (0,-(q:ℤ))).map (XModLambdaN.incl A 1)) := by
    subst n
    exact h
  exact transport (q+1-q) (by omega) _ (by rw [show q+1-q=1 by omega]) h

/-- The boundary target comparison induced by the same exact shift and
the selected Q₁ comparison. -/
private def adjacentShiftComparison (X : ClassicalObject) (e : ℤ) (q : ℕ) :
    let A := model.nu.functor.obj (X.obj model.auxiliary)
    let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,e)
    F.obj (((SyntheticCategory.biShift (0,-(q:ℤ))).obj (XModLambdaN A 1))⟦(1:ℤ)⟧) ⟶
      ((SyntheticCategory.biShift (0,-(q:ℤ))).obj (XModLambdaN (F.obj A) 1))⟦(1:ℤ)⟧ :=
  let A := model.nu.functor.obj (X.obj model.auxiliary)
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,e)
  let L := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(q:ℤ))
  let S := shiftFunctor SyntheticSpectrum (1:ℤ)
  letI := model.exactness.shiftCommShift (0,e)
  (F.commShiftIso (1:ℤ)).hom.app (L.obj (XModLambdaN A 1)) ≫
    S.map ((shiftCommIso (0,e) (0,-(q:ℤ))).inv.app (XModLambdaN A 1)) ≫
    S.map (L.map (levelQuotientShiftIso X e 1).inv)

/-- Naturality of the selected adjacent finite Bockstein under an actual
weight shift, evaluated on the specified sphere representative. -/
private theorem adjacent_delta_weight_shift (X : ClassicalObject)
    (e : ℤ) (q : ℕ) (hq : 0<q) (m w : ℤ)
    (a : BiHom m w (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q)) :
    (shiftHomotopyClass (0,e) (m,w) a ≫ (levelQuotientShiftIso X e q).inv) ≫
      adjacentDelta _ q hq =
    shiftHomotopyClass (0,e) (m,w) (a ≫ adjacentDelta _ q hq) ≫
      adjacentShiftComparison X e q := by
  let A := model.nu.functor.obj (X.obj model.auxiliary)
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,e)
  let L := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(q:ℤ))
  let S := shiftFunctor SyntheticSpectrum (1:ℤ)
  letI := model.exactness.shiftCommShift (0,e)
  rw [shifted_adjacent_delta_projection X e q hq,
    native_adjacent_delta_projection X q hq]
  rw [←level_quotient_shift_projection X e q]
  simp only [adjacentShiftComparison,shift_hom_comp,Functor.map_comp,Category.assoc,
    Iso.inv_hom_id_assoc]
  erw [(F.commShiftIso (1:ℤ)).hom.naturality_assoc]
  dsimp only [Functor.comp_map]
  erw [←Functor.map_comp_assoc]
  have hn := (shiftCommIso (0,e) (0,-(q:ℤ))).inv.naturality (XModLambdaN.incl A 1)
  dsimp only [Functor.comp_map] at hn
  erw [hn]
  rw [Functor.map_comp,Category.assoc]
  have hinc : F.map (XModLambdaN.incl A 1) ≫ (levelQuotientShiftIso X e 1).inv =
      XModLambdaN.incl (F.obj A) 1 := by
    rw [←level_quotient_shift_incl X e 1,Category.assoc,Iso.hom_inv_id,Category.comp_id]
  have hfun : S.map (L.map (F.map (XModLambdaN.incl A 1))) ≫
      S.map (L.map (levelQuotientShiftIso X e 1).inv) =
      S.map (L.map (XModLambdaN.incl (F.obj A) 1)) := by
    rw [←S.map_comp,←L.map_comp,hinc]
  erw [hfun]

/-- A specified classical differential gives a specified finite Bockstein
lift in every actual weight shift. In particular e=-1 is the lift needed
when the second normalization exponent is positive. -/
private theorem shifted_classical_differential_lift (X : ClassicalObject)
    (e : ℤ) (q : ℕ) (hq : 0<q) (s t : ℤ)
    (z : Ambient model X (s,t)) (y : Ambient model X (s+q+1,t+q))
    (hd : HasDifferential (model.classical.obj (X.obj model.auxiliary))
      (q+1) (s,t) (s+q+1,t+q) z y) :
    let A := model.nu.functor.obj (X.obj model.auxiliary)
    let b := (biSuspensionHomEquiv (t-s) t (q:ℤ) (XModLambdaN A 1)).symm
      (homotopyRegrade (show (t+q)-(s+q+1)=(t-s)-1 by omega) rfl
        (nativeFirstLabel X (s+q+1) (t+q) y))
    ∃ a : BiHom ((t-s,t)+(0,e)).1 ((t-s,t)+(0,e)).2
        (XModLambdaN ((SyntheticCategory.biShift (0,e)).obj A) q),
      a ≫ (model.quotients.tower _).rho 1 q hq =
        shiftHomotopyClass (0,e) (t-s,t) (nativeFirstLabel X s t z) ≫
          (levelQuotientShiftIso X e 1).inv ∧
      a ≫ adjacentDelta _ q hq =
        shiftHomotopyClass (0,e) (t-s,t) b ≫ adjacentShiftComparison X e q := by
  dsimp only
  let A := model.nu.functor.obj (X.obj model.auxiliary)
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,e)
  let b := (biSuspensionHomEquiv (t-s) t (q:ℤ) (XModLambdaN A 1)).symm
    (homotopyRegrade (show (t+q)-(s+q+1)=(t-s)-1 by omega) rfl
      (nativeFirstLabel X (s+q+1) (t+q) y))
  obtain ⟨a₀,ha₀,hδ₀⟩ := (differential_iff_specified_finite_lift X q hq s t z y).mp hd
  have hδ : a₀ ≫ adjacentDelta A q hq = b := by
    apply (biSuspensionHomEquiv (t-s) t (q:ℤ) (XModLambdaN A 1)).injective
    rw [AddEquiv.apply_symm_apply]
    apply homotopy_regrade_injective
      (show (t-s)-1=(t+q)-(s+q+1) by omega) rfl
    rw [homotopy_regrade_inverse]
    exact hδ₀
  let a := shiftHomotopyClass (0,e) (t-s,t) a₀ ≫ (levelQuotientShiftIso X e q).inv
  refine ⟨a,?_,?_⟩
  · apply (cancel_mono (levelQuotientShiftIso X e 1).hom).mp
    rw [Category.assoc,quotient_shift_restriction_on_spheres X (0,e) 1 q
      (by decide) hq (levelQuotientShiftIso X e 1) (levelQuotientShiftIso X e q)
      (level_quotient_shift_incl X e 1) (level_quotient_shift_incl X e q)]
    dsimp only [a]
    simp only [Category.assoc,Iso.inv_hom_id_assoc,Iso.inv_hom_id,Category.comp_id]
    rw [←shift_hom_comp,ha₀]
  · dsimp only [a]
    rw [adjacent_delta_weight_shift,hδ]

private def shiftNegativePositiveUnit :
    SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-1) ⋙
      SyntheticCategory.biShift (0,1) ≅ 𝟭 SyntheticSpectrum :=
  biShiftAddIso (0,-1) (0,1) 0 (by ext <;> norm_num) ≪≫
    SyntheticCategory.biShift_zero

private theorem positive_shift_negative_lift_quotient (X Y : ClassicalObject)
    (F : (SyntheticCategory.biShift (0,1)).obj
      (model.nu.functor.obj (X.obj model.auxiliary)) ⟶
        model.nu.functor.obj (Y.obj model.auxiliary))
    (q : ℕ) (hq : 0<q) (m w : ℤ)
    (a : BiHom m w (XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
      (model.nu.functor.obj (X.obj model.auxiliary))) q)) :
    a ≫ XModLambdaN.map F q =
      a ≫ (levelQuotientShiftIso X 1 q).hom ≫
        (SyntheticCategory.biShift (0,1)).map
          (XModLambdaN.map (negativeLift 1 F) q ≫ (levelQuotientShiftIso Y (-1) q).hom) ≫
        shiftNegativePositiveUnit.hom.app
          (XModLambdaN (model.nu.functor.obj (Y.obj model.auxiliary)) q) := by
  let A := model.nu.functor.obj (X.obj model.auxiliary)
  let B := model.nu.functor.obj (Y.obj model.auxiliary)
  let P := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,1)
  let N := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-1)
  let E := levelQuotientShiftIso X 1 q
  let D := levelQuotientShiftIso Y (-1) q
  let c := E.hom ≫ P.map (XModLambdaN.map (negativeLift 1 F) q ≫ D.hom) ≫
    shiftNegativePositiveUnit.hom.app (XModLambdaN B q)
  have hbase : XModLambdaN.incl (P.obj A) q ≫ XModLambdaN.map F q =
      XModLambdaN.incl (P.obj A) q ≫ c := by
    rw [←XModLambdaN.incl_naturality]
    dsimp only [c]
    rw [←Category.assoc,level_quotient_shift_incl X 1 q]
    erw [←P.map_comp_assoc]
    rw [←Category.assoc (XModLambdaN.incl A q),←XModLambdaN.incl_naturality]
    dsimp only [D]
    simp only [Category.assoc]
    erw [level_quotient_shift_incl Y (-1) q]
    simp only [Functor.map_comp, Category.assoc]
    erw [shiftNegativePositiveUnit.hom.naturality]
    change F ≫ XModLambdaN.incl B q =
      P.map (negativeLift 1 F) ≫ shiftNegativePositiveUnit.hom.app B ≫ XModLambdaN.incl B q
    have h := shift_negativeLift_cancel 1 F
    change P.map (negativeLift 1 F) ≫ shiftNegativePositiveUnit.hom.app B = F at h
    simpa only [Category.assoc] using congrArg (fun k => k≫XModLambdaN.incl B q) h.symm
  exact normalized_quotient_maps_equal_on_spheres X Y 1 le_rfl q hq
    (XModLambdaN.map F q) c hbase m w a

private theorem shift_negative_positive_class {A : SyntheticSpectrum}
    (m w : ℤ) (a : BiHom m w A) :
    homotopyRegrade (by simp) (by dsimp; omega)
      (shiftHomotopyClass (0,1) ((m,w)+(0,-1))
        (shiftHomotopyClass (0,-1) (m,w) a)) ≫
      shiftNegativePositiveUnit.hom.app A = a := by
  have h := shift_hom_associativity model.quotients.coherence (m,w) (0,-1) (0,1)
    ((m,w)+(0,-1)) 0 (m,w) rfl (by ext <;> norm_num)
    (by ext <;> dsimp <;> omega) (by simp) a
  have hh := congrArg (fun k => k≫shiftNegativePositiveUnit.hom.app A) h
  simp only [shiftNegativePositiveUnit,Iso.trans_hom,NatTrans.comp_app,
    Category.assoc,Iso.inv_hom_id_app_assoc] at hh
  have hu := model.quotients.coherence.right_unit (m,w) S_0_0
  have hnat := SyntheticCategory.biShift_zero.hom.naturality a
  dsimp only [Functor.id_map] at hnat
  have hout : (biShiftAddIso (m,w) 0 (m,w) (by simp)).inv.app S_0_0 ≫
      (SyntheticCategory.biShift (0,0)).map a ≫
        SyntheticCategory.biShift_zero.hom.app A = a := by
    erw [hnat]
    erw [←hu,Iso.inv_hom_id_app_assoc]
  erw [hout] at hh
  simpa only [shiftHomotopyClass,regrade_precomp,Functor.map_comp,Category.assoc,
    biShiftAddIso,Iso.app_inv,Iso.trans_inv,NatTrans.comp_app,eqToIso.inv,eqToHom_app,
    shiftNegativePositiveUnit,Iso.trans_hom,eqToHom_refl,Functor.map_id,Category.id_comp] using hh.symm

/-- Coherent natural comparison choices agree on every mod-two first
quotient class. The possible sphere automorphism acts trivially there. -/
private theorem first_quotient_natural_iso_unique
    (F G : SyntheticSpectrum ⥤ SyntheticSpectrum) (ff : F.FullyFaithful)
    (α β : F ≅ G) (X : ClassicalObject) (m w : ℤ)
    (a : BiHom m w (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) 1)) :
    F.map a ≫ α.hom.app _ = F.map a ≫ β.hom.app _ := by
  obtain ⟨u,hu⟩ := natural_iso_comparison_sphere F G ff α β m w _ a
  simpa only [sphere_automorphism_first_finite] using hu


private theorem shift_class_input_regrade (δ : ℤ×ℤ)
    {m m' w w' : ℤ} (hm : m=m') (hw : w=w') {A : SyntheticSpectrum}
    (a : BiHom m w A) :
    shiftHomotopyClass δ (m',w') (homotopyRegrade hm hw a) =
      homotopyRegrade (by dsimp; omega) (by dsimp; omega)
        (shiftHomotopyClass δ (m,w) a) := by
  subst m'; subst w'; rfl

private theorem regrade_transitive {m m' m'' w w' w'' : ℤ} {A : SyntheticSpectrum}
    (hm : m=m') (hm' : m'=m'') (hw : w=w') (hw' : w'=w'')
    (a : BiHom m w A) :
    homotopyRegrade hm' hw' (homotopyRegrade hm hw a) =
      homotopyRegrade (hm.trans hm') (hw.trans hw') a := by
  subst m'; subst m''; subst w'; subst w''; rfl

/-- The native first label under the actual negative lift is exactly the
negative transport of the positive normalized operation. -/
private theorem positive_operation_negative_lift_label (X Y : ClassicalObject)
    (F : (SyntheticCategory.biShift (0,1)).obj
      (model.nu.functor.obj (X.obj model.auxiliary)) ⟶
        model.nu.functor.obj (Y.obj model.auxiliary))
    (s t : ℤ) (x : Ambient model X (s,t)) :
    nativeFirstLabel X s t x ≫ XModLambdaN.map (negativeLift 1 F) 1 =
      homotopyRegrade (by dsimp; omega) (by dsimp; omega)
        (shiftHomotopyClass (0,-1) (t+1-(s+1),t+1)
          (nativeFirstLabel Y (s+1) (t+1)
            (positiveFirstQuotientOperation X Y F s t x))) ≫
        (levelQuotientShiftIso Y (-1) 1).inv := by
  let y := positiveFirstQuotientOperation X Y F s t x
  let D := levelQuotientShiftIso Y (-1) 1
  let E := levelQuotientShiftIso X 1 1
  let a := (model.firstQuotient X 1 s t).symm x
  have ha : homotopyRegrade (by simp) (by simp)
      (shiftHomotopyClass (0,1) (t-s,t) (nativeFirstLabel X s t x)) ≫ E.inv = a := by
    have hh := firstQuotient_positive_shift X s t x E
      (level_quotient_shift_incl X 1 1)
    simpa only [nativeFirstLabel_eq_regrade] using hh
  have hpos := positive_shift_negative_lift_quotient X Y F 1 (by omega)
    (t-s) (t+1) a
  have hy := positive_first_quotient_native_label X Y F s t x
  apply (cancel_mono D.hom).mp
  dsimp only [D]
  simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id]
  apply shift_class_injective (.shift (0,-1) (.quotient 1 (.nu Y))) (0,1) (t-s,t)
  apply (cancel_mono (shiftNegativePositiveUnit.hom.app
    (XModLambdaN (model.nu.functor.obj (Y.obj model.auxiliary)) 1))).mp
  simp only [shift_hom_comp,Category.assoc]
  have hright := shift_negative_positive_class (t+1-(s+1)) (t+1)
    (nativeFirstLabel Y (s+1) (t+1) y)
  rw [shift_class_input_regrade]
  apply homotopy_regrade_injective (m' := t+1-(s+1)) (w' := t+1)
    (by dsimp; omega) (by rfl)
  simp only [regrade_comp,regrade_transitive]
  rw [hright]
  have ha' : a ≫ E.hom = homotopyRegrade (by simp) (by simp)
      (shiftHomotopyClass (0,1) (t-s,t) (nativeFirstLabel X s t x)) := by
    rw [←ha]
    simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id]
  have hp := congrArg (fun k => homotopyRegrade
      (show t-s=t+1-(s+1) by omega) rfl k) hpos
  rw [←Category.assoc a,ha'] at hp
  simp only [regrade_comp,regrade_transitive] at hp
  exact hp.symm.trans (by simpa only [regrade_comp,a,y] using hy.symm)




/-- On a first finite quotient every natural interchange of shifts gives
exactly the canonical interchange on actual sphere classes. -/
private theorem first_quotient_double_shift_commute
    (δ ε : ℤ×ℤ)
    (N : SyntheticCategory.biShift (Syn:=SyntheticSpectrum) δ ⋙ SyntheticCategory.biShift ε ≅
      SyntheticCategory.biShift ε ⋙ SyntheticCategory.biShift δ)
    (X : ClassicalObject) (p : ℤ×ℤ)
    (a : BiHom p.1 p.2 (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) 1)) :
    shiftHomotopyClass ε (p+δ) (shiftHomotopyClass δ p a) ≫ N.hom.app _ =
      homotopyRegrade (by dsimp; omega) (by dsimp; omega)
        (shiftHomotopyClass δ (p+ε) (shiftHomotopyClass ε p a)) := by
  have hn := first_quotient_natural_iso_unique
    (SyntheticCategory.biShift δ ⋙ SyntheticCategory.biShift ε)
    (SyntheticCategory.biShift ε ⋙ SyntheticCategory.biShift δ)
    ((SyntheticCategory.biShift_fullyFaithful δ).comp (SyntheticCategory.biShift_fullyFaithful ε))
    N (shiftCommIso δ ε) X p.1 p.2 a
  have hh := congrArg (fun v => (SyntheticCategory.biShift_comp (p+δ) ε).inv.app S_0_0 ≫
    (SyntheticCategory.biShift ε).map ((SyntheticCategory.biShift_comp p δ).inv.app S_0_0) ≫ v) hn
  have hN : shiftHomotopyClass ε (p+δ) (shiftHomotopyClass δ p a) ≫ N.hom.app _ =
      shiftHomotopyClass ε (p+δ) (shiftHomotopyClass δ p a) ≫
        (shiftCommIso δ ε).hom.app _ := by
    simpa only [shiftHomotopyClass,Functor.map_comp,Functor.comp_map,Category.assoc] using hh
  rw [hN]
  rcases δ with ⟨d₁,d₂⟩
  rw [shift_regrade]
  have hs := shift_hom_swap p (d₁,d₂) ε (p+(d₁,d₂)) (p+ε) ((p+(d₁,d₂))+ε)
    rfl rfl rfl (by ext <;> dsimp <;> omega) a
  simpa only [shiftHomotopyClass,biShiftAddIso,eqToIso_refl,Iso.trans_refl,Prod.eta,
    Category.assoc] using hs

private theorem first_quotient_bisuspension_weight_shift
    (X : ClassicalObject) (e : ℤ) (q : ℕ) (m w : ℤ)
    (a : BiHom (m-1) (w+q) (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) 1)) :
    homotopyRegrade (by simp) (by rfl)
        (shiftHomotopyClass (0,e) (m,w)
          ((biSuspensionHomEquiv m w (q:ℤ) _).symm a)) ≫
        adjacentShiftComparison X e q =
      (biSuspensionHomEquiv m (w+e) (q:ℤ) _).symm
        (homotopyRegrade (by dsimp; omega) (by dsimp; omega)
          (shiftHomotopyClass (0,e) (m-1,w+q) a) ≫
          (levelQuotientShiftIso X e 1).inv) := by
  let A := XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) 1
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,e)
  let L := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(q:ℤ))
  let S := shiftFunctor SyntheticSpectrum (1:ℤ)
  letI := model.exactness.shiftCommShift (0,e)
  have hb := first_quotient_double_shift_commute (1,-(q:ℤ)) (0,e)
    (boundaryShiftNatIso e q) X (m-1,w+q) a
  rw [bi_susp_symm_eq,bi_susp_symm_eq]
  have hs (n u k l : ℤ) (B : SyntheticSpectrum) (b : BiHom n u B) :
      susp_invariance n u k l B b = shiftHomotopyClass (k,l) (n,u) b := by
    simp only [susp_invariance,Equiv.trans_apply,Iso.homCongr_apply,Iso.refl_hom,
      Category.comp_id,shiftHomotopyClass]
    rfl
  simp only [hs]
  rw [shift_hom_comp,shift_class_input_regrade,regrade_comp,regrade_transitive]
  have hmap : F.map (biSuspensionIso (q:ℤ) A).hom ≫ adjacentShiftComparison X e q =
      (boundaryShiftNatIso e q).hom.app A ≫ (biSuspensionIso (q:ℤ) (F.obj A)).hom ≫
        S.map (L.map (levelQuotientShiftIso X e 1).inv) := by
    have hh := congrArg Iso.hom (boundaryShiftNatIso_app e q A)
    change (boundaryShiftNatIso e q).hom.app A = _ at hh
    rw [hh]
    simp only [adjacentShiftComparison,Iso.trans_hom,Functor.mapIso_hom,Iso.symm_hom,
      Category.assoc]
    dsimp only [F]
    erw [Iso.inv_hom_id_assoc]
    rfl
  rw [Category.assoc,hmap]
  rw [shift_hom_comp,shift_class_input_regrade,regrade_comp,regrade_transitive]
  have hn := (boundarySuspensionNatIso q).hom.naturality (levelQuotientShiftIso X e 1).inv
  change (SyntheticCategory.biShift (1,-(q:ℤ))).map (levelQuotientShiftIso X e 1).inv ≫
      (biSuspensionIso (q:ℤ) _).hom = (biSuspensionIso (q:ℤ) _).hom ≫
        S.map (L.map (levelQuotientShiftIso X e 1).inv) at hn
  simp only [Category.assoc]
  erw [hn]
  have hh := congrArg (fun k => homotopyRegrade (show (((m-1,w+q)+(1,-(q:ℤ)))+(0,e)).1=m by dsimp;omega)
      (show (((m-1,w+q)+(1,-(q:ℤ)))+(0,e)).2=w+e by dsimp;omega) k) hb
  simp only [regrade_comp,regrade_transitive] at hh
  simpa only [Category.assoc,A,F,S,L,Prod.mk.eta,Prod.fst_add,Prod.snd_add,Prod.mk_add_mk] using congrArg (fun k => k ≫ (biSuspensionIso (q:ℤ) (F.obj A)).hom ≫
    S.map (L.map (levelQuotientShiftIso X e 1).inv)) hh



private def positiveClassicalRegrade {X : ClassicalObject} {p q : ℤ×ℤ}
    (h : p=q) (x : Ambient model X p) : Ambient model X q := h ▸ x

private theorem native_first_label_transport (X : ClassicalObject)
    {s s' t t' : ℤ} (hs : s=s') (ht : t=t') (x : Ambient model X (s,t)) :
    nativeFirstLabel X s' t' (positiveClassicalRegrade (X:=X) (Prod.ext hs ht) x) =
      homotopyRegrade (by omega) ht (nativeFirstLabel X s t x) := by
  subst s'; subst t'; rfl

/-- The classical differential with the actual positive g-operation gives
the required delta--negativeLift square in the actual shifted quotient. -/
private theorem positive_classical_differential_finite_square
    (Y Z : ClassicalObject)
    (F : (SyntheticCategory.biShift (0,1)).obj
      (model.nu.functor.obj (Y.obj model.auxiliary)) ⟶
        model.nu.functor.obj (Z.obj model.auxiliary))
    (q : ℕ) (hq : 0<q) (s t : ℤ)
    (z : Ambient model Z (s,t)) (v : Ambient model Y (s+q,t+q-1))
    (hd : HasDifferential (model.classical.obj (Z.obj model.auxiliary))
      (q+1) (s,t) (s+q+1,t+q) z
      (positiveClassicalRegrade (X:=Z) (by ext <;> dsimp <;> omega)
        (positiveFirstQuotientOperation Y Z F (s+q) (t+q-1) v))) :
    let A := (SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-1)).obj
      (model.nu.functor.obj (Z.obj model.auxiliary))
    let b := (biSuspensionHomEquiv (t-s) (t-1) (q:ℤ)
      (XModLambdaN (model.nu.functor.obj (Y.obj model.auxiliary)) 1)).symm
        (homotopyRegrade (show (t+q-1)-(s+q)=(t-s)-1 by omega) (by omega)
          (nativeFirstLabel Y (s+q) (t+q-1) v))
    ∃ a : BiHom (t-s) (t-1) (XModLambdaN A q),
      a ≫ (model.quotients.tower _).rho 1 q hq =
        homotopyRegrade (by dsimp; omega) (by dsimp; omega)
          (shiftHomotopyClass (0,-1) (t-s,t) (nativeFirstLabel Z s t z)) ≫
            (levelQuotientShiftIso Z (-1) 1).inv ∧
      a ≫ adjacentDelta A q hq =
        b ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map
          ((SyntheticCategory.biShift (0,-(q:ℤ))).map
            (XModLambdaN.map (negativeLift 1 F) 1)) := by
  dsimp only
  let y : Ambient model Z (s+q+1,t+q) := positiveClassicalRegrade (X:=Z) (by ext <;> dsimp <;> omega)
    (positiveFirstQuotientOperation Y Z F (s+q) (t+q-1) v)
  let B := XModLambdaN (model.nu.functor.obj (Z.obj model.auxiliary)) 1
  let y₁ : BiHom ((t-s)-1) (t+q) B :=
    homotopyRegrade (by omega) rfl (nativeFirstLabel Z (s+q+1) (t+q) y)
  obtain ⟨a₀,ha₀,hδ₀⟩ := shifted_classical_differential_lift Z (-1) q hq s t z y hd
  let a := homotopyRegrade (show ((t-s,t)+(0,-1)).1=t-s by simp)
    (show ((t-s,t)+(0,-1)).2=t-1 by dsimp;omega) a₀
  refine ⟨a,?_,?_⟩
  · dsimp only [a]
    rw [←regrade_comp,ha₀,regrade_comp]
  · have hδ := congrArg (fun k => homotopyRegrade
        (show ((t-s,t)+(0,-1)).1=t-s by simp)
        (show ((t-s,t)+(0,-1)).2=t-1 by dsimp;omega) k) hδ₀
    have hb := first_quotient_bisuspension_weight_shift Z (-1) q (t-s) t y₁
    have hbs : homotopyRegrade rfl (show t+(-1)=t-1 by omega)
        (homotopyRegrade (by simp) rfl
          (shiftHomotopyClass (0,-1) (t-s,t)
            ((biSuspensionHomEquiv (t-s) t (q:ℤ) B).symm y₁)) ≫
            adjacentShiftComparison Z (-1) q) =
        (biSuspensionHomEquiv (t-s) (t-1) (q:ℤ) _).symm
          (homotopyRegrade (by dsimp;omega) (by dsimp;omega)
            (shiftHomotopyClass (0,-1) ((t-s)-1,t+q) y₁) ≫
            (levelQuotientShiftIso Z (-1) 1).inv) := by
      rw [hb]
      congr 1
    have hat : a ≫ adjacentDelta _ q hq =
        (biSuspensionHomEquiv (t-s) (t-1) (q:ℤ) _).symm
          (homotopyRegrade (by dsimp;omega) (by dsimp;omega)
            (shiftHomotopyClass (0,-1) ((t-s)-1,t+q) y₁) ≫
            (levelQuotientShiftIso Z (-1) 1).inv) := by
      simp only [regrade_comp,regrade_transitive] at hbs hδ
      simpa only [a,y₁,B,regrade_comp,regrade_transitive] using hδ.trans hbs
    rw [hat]
    apply (biSuspensionHomEquiv (t-s) (t-1) (q:ℤ) _).injective
    rw [AddEquiv.apply_symm_apply,bi_susp_natural model.quotients.coherence,
      AddEquiv.apply_symm_apply]
    have hm := positive_operation_negative_lift_label Y Z F (s+q) (t+q-1) v
    have hy : nativeFirstLabel Z (s+q+1) (t+q) y =
        homotopyRegrade (by omega) (by omega)
          (nativeFirstLabel Z ((s+q)+1) ((t+q-1)+1)
            (positiveFirstQuotientOperation Y Z F (s+q) (t+q-1) v)) := by
      exact native_first_label_transport Z rfl (by omega) _
    dsimp only [y₁]
    rw [hy]
    simp only [shift_class_input_regrade,regrade_transitive]
    have hh := congrArg (fun k => homotopyRegrade
      (show (t+q-1)-(s+q)=(t-s)-1 by omega)
      (show t+q-1=(t-1)+q by omega) k) hm
    simpa only [regrade_comp,regrade_transitive] using hh.symm


private def normalizedSecondPositiveMap
    (T : TriangleData model.auxiliary)
    (hg : normalizedExponent model.classicalTower T.g = 1) :
    (SyntheticCategory.biShift (0,1)).obj
      (model.nu.functor.obj (T.Y.obj model.auxiliary)) ⟶
        model.nu.functor.obj (T.Z.obj model.auxiliary) :=
  eqToHom (congrArg (fun k : ℕ => (SyntheticCategory.biShift (0,(k:ℤ))).obj
    (model.nu.functor.obj (T.Y.obj model.auxiliary))) hg.symm) ≫
    (model.normalizedMap T.Y T.Z T.g).map

private def normalizedThirdNegativeIso
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g +
      normalizedExponent model.classicalTower T.h = 1)
    (hg : normalizedExponent model.classicalTower T.g = 1) :
    (normalizedTriangle model T he).obj₃ ≅
      (SyntheticCategory.biShift (0,-1)).obj
        (model.nu.functor.obj (T.Z.obj model.auxiliary)) :=
  eqToIso (congrArg (fun k : ℕ => (SyntheticCategory.biShift (0,-(k:ℤ))).obj
    (model.nu.functor.obj (T.Z.obj model.auxiliary))) hg)

private theorem normalized_second_arrow_positive
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g +
      normalizedExponent model.classicalTower T.h = 1)
    (hg : normalizedExponent model.classicalTower T.g = 1) :
    (normalizedTriangle model T he).mor₂ ≫ (normalizedThirdNegativeIso T he hg).hom =
      negativeLift 1 (normalizedSecondPositiveMap T hg) := by
  have raw {A B : SyntheticSpectrum} (k : ℕ) (hk : k=1)
      (M : (SyntheticCategory.biShift (0,(k:ℤ))).obj A ⟶ B) :
      negativeLift k M ≫ eqToHom (congrArg (fun j : ℕ =>
        (SyntheticCategory.biShift (0,-(j:ℤ))).obj B) hk) =
      negativeLift 1 (eqToHom (congrArg (fun j : ℕ =>
        (SyntheticCategory.biShift (0,(j:ℤ))).obj A) hk.symm) ≫ M) := by
    subst k
    simp only [eqToHom_refl,Category.id_comp,Category.comp_id]
  exact raw _ hg (model.normalizedMap T.Y T.Z T.g).map

/-- Positive second exponent: the classical input constructs the exact
normalized finite May class and its specified signed target. -/
private theorem positive_second_differential_may
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g +
      normalizedExponent model.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible model T he)
    (hg : normalizedExponent model.classicalTower T.g = 1)
    (q : ℕ) (hq : 0<q) (s t : ℤ)
    (z : Ambient model T.Z (s,t)) (v : Ambient model T.Y (s+q,t+q-1))
    (hd : HasDifferential (model.classical.obj (T.Z.obj model.auxiliary))
      (q+1) (s,t) (s+q+1,t+q) z
      (positiveClassicalRegrade (X:=T.Z) (by ext <;> dsimp <;> omega)
        (positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg)
          (s+q) (t+q-1) v)))
    (ey : XModLambdaN ((normalizedTriangle model T he).obj₂⟦(1:ℤ)⟧) (q+1) ≅
      (XModLambdaN (normalizedTriangle model T he).obj₂ (q+1))⟦(1:ℤ)⟧)
    (hey : XModLambdaN.incl _ (q+1) ≫ ey.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ (q+1))) :
    let V := normalizedTriangle model T he
    let b := (biSuspensionHomEquiv (t-s) (t-1) (q:ℤ)
      (XModLambdaN (model.nu.functor.obj (T.Y.obj model.auxiliary)) 1)).symm
        (homotopyRegrade (show (t+q-1)-(s+q)=(t-s)-1 by omega) (by omega)
          (nativeFirstLabel T.Y (s+q) (t+q-1) v))
    let ly : (SyntheticCategory.biShift (0,-(q:ℤ))).obj (XModLambdaN V.obj₂ 1) ⟶
        XModLambdaN V.obj₂ (q+1) := by
      simpa only [show q.succ-q=1 by omega] using
        ((model.quotients.tower V.obj₂).triangle hq (Nat.lt_succ_self q)).lambdaMap
    ∃ (a : BiHom (t-s) (t-1) (XModLambdaN V.obj₃ q))
      (c : BiHom (t-s) (t-1) (XModLambdaN (V.obj₁⟦(1:ℤ)⟧) (q+1))),
      a ≫ (model.quotients.tower _).rho 1 q hq =
        homotopyRegrade (by dsimp;omega) (by dsimp;omega)
          (shiftHomotopyClass (0,-1) (t-s,t) (nativeFirstLabel T.Z s t z)) ≫
            (levelQuotientShiftIso T.Z (-1) 1).inv ≫
              XModLambdaN.map (normalizedThirdNegativeIso T he hg).inv 1 ∧
      a ≫ adjacentDelta V.obj₃ q hq =
        b ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map
          ((SyntheticCategory.biShift (0,-(q:ℤ))).map (XModLambdaN.map V.mor₂ 1)) ∧
      c ≫ (model.quotients.tower _).rho q (q+1) (by omega) =
        a ≫ XModLambdaN.map V.mor₃ q ∧
      c ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map V.mor₁) (q+1) ≫
        ey.hom = -(b ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map ly) := by
  dsimp only
  let V := normalizedTriangle model T he
  let E := normalizedThirdNegativeIso T he hg
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(q:ℤ))
  let S := shiftFunctor SyntheticSpectrum (1:ℤ)
  let b := (biSuspensionHomEquiv (t-s) (t-1) (q:ℤ)
    (XModLambdaN (model.nu.functor.obj (T.Y.obj model.auxiliary)) 1)).symm
      (homotopyRegrade (show (t+q-1)-(s+q)=(t-s)-1 by omega) (by omega)
        (nativeFirstLabel T.Y (s+q) (t+q-1) v))
  obtain ⟨a₀,ha₀,hab₀⟩ := positive_classical_differential_finite_square T.Y T.Z
    (normalizedSecondPositiveMap T hg) q hq s t z v hd
  let a := a₀ ≫ XModLambdaN.map E.inv q
  have hag : negativeLift 1 (normalizedSecondPositiveMap T hg) ≫ E.inv = V.mor₂ := by
    apply (cancel_mono E.hom).mp
    simpa only [Category.assoc,Iso.inv_hom_id,Category.comp_id] using
      (normalized_second_arrow_positive T he hg).symm
  have hab : a ≫ adjacentDelta V.obj₃ q hq =
      b ≫ S.map (F.map (XModLambdaN.map V.mor₂ 1)) := by
    dsimp only [a]
    rw [Category.assoc,adjacent_delta_natural E.inv q hq,←Category.assoc,hab₀]
    simp only [Category.assoc]
    rw [←Functor.map_comp,←Functor.map_comp,
      ←model.quotients.functoriality.map_comp,hag]
  obtain ⟨c,hcr,hcf⟩ := finite_may_at_normalized_triangle_explicit_lengths T he hT q 1 hq
    (by omega) (t-s) (t-1) ey hey a b hab
  refine ⟨a,c,?_,hab,hcr,hcf⟩
  dsimp only [a]
  rw [Category.assoc,←(model.quotients.natural E.inv).rho_naturality hq,
    ←Category.assoc,ha₀,Category.assoc]

end
end KIP126.ProofTools.Internal.MahowaldLeibniz
