module
import all KIP126.Def.ProofTools.GeneralizedLeibniz.CrossingDelta
import all KIP126.Def.ProofTools.GeneralizedLeibniz.SphereAutomorphisms

/-! The actual absolute boundaries before and after finite lambda division
have equal first-quotient labels, as used in AimPaper Remark `rmk:qvoewfj`.
The chosen exact shift and canonical bigraded suspension may differ. Their
comparison is natural on representable homotopy groups, hence is induced by
a sphere automorphism. Such automorphisms act trivially after Q1. -/

@[expose] section
namespace KIP126.ProofTools.Internal.Leibniz
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Standard
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2400000

private def homPostcompAddEquiv {A B C : SyntheticSpectrum} (e : B ≅ C) :
    (A ⟶ B) ≃+ (A ⟶ C) where
  toFun a := a ≫ e.hom
  invFun a := a ≫ e.inv
  left_inv a := by simp
  right_inv a := by simp
  map_add' a b := by simp only [Preadditive.add_comp]

private def boundaryDivisionSuspIso (d q : ℕ) (hdq : d ≤ q) (A : SyntheticSpectrum) :
    (SyntheticCategory.biShift (0,-(d:ℤ))).obj
      (((SyntheticCategory.biShift (0,-((q-d:ℕ):ℤ))).obj A)⟦(1:ℤ)⟧) ≅
    ((SyntheticCategory.biShift (0,-(q:ℤ))).obj A)⟦(1:ℤ)⟧ := by
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(d:ℤ))
  letI := model.exactness.shiftCommShift (0,-(d:ℤ))
  exact (F.commShiftIso (1:ℤ)).app _ ≪≫
    (shiftFunctor SyntheticSpectrum (1:ℤ)).mapIso
      ((lambdaShiftAddIso (q-d) d q (Nat.sub_add_cancel hdq)).app A)

private theorem boundaryDivisionSuspIso_natural (d q : ℕ) (hdq : d ≤ q)
    {A B : SyntheticSpectrum} (f : A ⟶ B) :
    (SyntheticCategory.biShift (0,-(d:ℤ))).map
        ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
          ((SyntheticCategory.biShift (0,-((q-d:ℕ):ℤ))).map f)) ≫
      (boundaryDivisionSuspIso d q hdq B).hom =
    (boundaryDivisionSuspIso d q hdq A).hom ≫
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map
        ((SyntheticCategory.biShift (0,-(q:ℤ))).map f) := by
  letI := model.exactness.shiftCommShift (0,-(d:ℤ))
  simp only [boundaryDivisionSuspIso,Iso.trans_hom,Functor.mapIso_hom,Iso.app_hom]
  rw [←Category.assoc,Functor.commShiftIso_hom_naturality]
  simp only [Category.assoc,←Functor.map_comp]
  congr 1
  exact congrArg ((shiftFunctor SyntheticSpectrum (1:ℤ)).map)
    ((lambdaShiftAddIso (q-d) d q (Nat.sub_add_cancel hdq)).hom.naturality f)

private def boundaryDivisionReindex (d q : ℕ) (hdq : d ≤ q) (m t : ℤ)
    (A : SyntheticSpectrum) :
    BiHom (m-1) (t+(q-d:ℕ)) A ≃+ BiHom (m-1) (t+(q-d:ℕ)) A :=
  (biSuspensionHomEquiv m t ((q-d:ℕ):ℤ) A).symm |>.trans
    (regradeAddEquiv rfl (by omega)) |>.trans
    (verticalShiftEquiv _ d m (t-d)) |>.trans
    (homPostcompAddEquiv (boundaryDivisionSuspIso d q hdq A)) |>.trans
    (biSuspensionHomEquiv m (t-d) q A) |>.trans
    (regradeAddEquiv rfl (by omega))

private theorem homotopyRegrade_comp {A B : SyntheticSpectrum}
    {m m' w w' : ℤ} (hm : m=m') (hw : w=w') (a : BiHom m w A) (f : A ⟶ B) :
    homotopyRegrade hm hw (a≫f) = homotopyRegrade hm hw a ≫ f := by
  subst m'; subst w'; rfl

private theorem bi_susp_symm_natural (m w i : ℤ) {A B : SyntheticSpectrum}
    (f : A ⟶ B) (a : BiHom (m-1) (w+i) A) :
    (biSuspensionHomEquiv m w i B).symm (a≫f) =
      (biSuspensionHomEquiv m w i A).symm a ≫
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map
          ((SyntheticCategory.biShift (0,-i)).map f) := by
  apply (biSuspensionHomEquiv m w i B).injective
  rw [AddEquiv.apply_symm_apply,bi_susp_natural model.quotients.coherence,
    AddEquiv.apply_symm_apply]

private theorem boundaryDivisionReindex_natural (d q : ℕ) (hdq : d ≤ q) (m t : ℤ)
    {A B : SyntheticSpectrum} (f : A ⟶ B)
    (a : BiHom (m-1) (t+(q-d:ℕ)) A) :
    boundaryDivisionReindex d q hdq m t B (a≫f) =
      boundaryDivisionReindex d q hdq m t A a ≫ f := by
  dsimp only [boundaryDivisionReindex,AddEquiv.trans_apply,regradeAddEquiv,
    homPostcompAddEquiv,AddEquiv.coe_mk,Equiv.coe_fn_mk]
  rw [bi_susp_symm_natural,homotopyRegrade_comp,←vertical_shift_comp,Category.assoc,
    boundaryDivisionSuspIso_natural,←Category.assoc,
    bi_susp_natural model.quotients.coherence,homotopyRegrade_comp]

private def boundaryDivisionSourceIso (d q : ℕ) (hdq : d ≤ q) (m t : ℤ) :
    Smn (m-1) (t+(q-d:ℕ)) ≅ (Smn (m-1) (t+(q-d:ℕ)) : SyntheticSpectrum) where
  hom := boundaryDivisionReindex d q hdq m t _ (𝟙 _)
  inv := (boundaryDivisionReindex d q hdq m t _).symm (𝟙 _)
  hom_inv_id := by
    rw [←boundaryDivisionReindex_natural,Category.id_comp,AddEquiv.apply_symm_apply]
  inv_hom_id := by
    apply (boundaryDivisionReindex d q hdq m t _).injective
    rw [boundaryDivisionReindex_natural,AddEquiv.apply_symm_apply,Category.id_comp]

private theorem boundaryDivisionReindex_eq_precomp (d q : ℕ) (hdq : d ≤ q) (m t : ℤ)
    (A : SyntheticSpectrum) (a : BiHom (m-1) (t+(q-d:ℕ)) A) :
    boundaryDivisionReindex d q hdq m t A a =
      (boundaryDivisionSourceIso d q hdq m t).hom ≫ a := by
  simpa only [Category.id_comp,boundaryDivisionSourceIso] using
    boundaryDivisionReindex_natural d q hdq m t a (𝟙 _)

private theorem divided_boundary_eq_reindex (X : ClassicalObject)
    (d q : ℕ) (hd : 0 < d) (hdq : d < q) (m t : ℤ)
    (b0 : BiHom m t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (q-d))) :
    let A := model.nu.functor.obj (X.obj model.auxiliary)
    let b0' : BiHom m ((t-d)+d) (XModLambdaN A (q-d)) :=
      homotopyRegrade rfl (by omega) b0
    let a := verticalShiftEquiv (XModLambdaN A (q-d)) d m (t-d) b0' ≫
      ((model.quotients.tower A).triangle hd hdq).lambdaMap
    homotopyRegrade rfl (by omega)
      (biSuspensionHomEquiv m (t-d) q A (a ≫ XModLambdaN.proj A q)) =
    boundaryDivisionReindex d q hdq.le m t A
      (biSuspensionHomEquiv m t ((q-d:ℕ):ℤ) A (b0 ≫ XModLambdaN.proj A (q-d))) := by
  dsimp only
  letI := model.exactness.shiftCommShift (0,-(d:ℤ))
  dsimp only [boundaryDivisionReindex,AddEquiv.trans_apply,regradeAddEquiv,
    homPostcompAddEquiv,AddEquiv.coe_mk,Equiv.coe_fn_mk]
  rw [AddEquiv.symm_apply_apply,homotopyRegrade_comp,←vertical_shift_comp,
    Category.assoc,Category.assoc,lambda_proj_evaluation X d q hd hdq]
  rfl

private theorem divided_boundary_first_quotient (X : ClassicalObject)
    (d q : ℕ) (hd : 0 < d) (hdq : d < q) (m t : ℤ)
    (b0 : BiHom m t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (q-d))) :
    let A := model.nu.functor.obj (X.obj model.auxiliary)
    let b0' : BiHom m ((t-d)+d) (XModLambdaN A (q-d)) :=
      homotopyRegrade rfl (by omega) b0
    let a := verticalShiftEquiv (XModLambdaN A (q-d)) d m (t-d) b0' ≫
      ((model.quotients.tower A).triangle hd hdq).lambdaMap
    homotopyRegrade rfl (by omega)
      (biSuspensionHomEquiv m (t-d) q A (a ≫ XModLambdaN.proj A q)) ≫
        XModLambdaN.incl A 1 =
    biSuspensionHomEquiv m t ((q-d:ℕ):ℤ) A
      (b0 ≫ XModLambdaN.proj A (q-d)) ≫ XModLambdaN.incl A 1 := by
  dsimp only
  rw [divided_boundary_eq_reindex X d q hd hdq m t b0,
    boundaryDivisionReindex_eq_precomp,Category.assoc]
  exact sphere_automorphism_quotient_projection _ _ _ _ _

end
end KIP126.ProofTools.Internal.Leibniz
