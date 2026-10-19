module

import KIP126.Literature.Standard

/-! Constructed finite quotient suspension comparisons for the fixed model.
The shift-comparison proof uses the actual lambda powers and chosen cofibers.
Adapted from the existing proved shift construction in
ProofTools/StretchingRepresentatives.lean; no reverse module import occurs.
The signed normalized quotient row is not asserted by this file.
-/

@[expose] section
namespace KIP126.Literature.Standard
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open CategoryTheory.Pretriangulated KIP126.StableHomotopy
open KIP126.Synthetic.Context KIP126.AdamsSynthetic KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1800000

set_option maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
private theorem finite_quotient_shift_comparison (coh : BiShiftCoherence SyntheticSpectrum)
    (a : ℤ × ℤ) (q : ℕ) (X : SyntheticSpectrum)
    [cs : (SyntheticCategory.biShift (Syn := SyntheticSpectrum) a).CommShift ℤ]
    [(SyntheticCategory.biShift (Syn := SyntheticSpectrum) a).IsTriangulated] :
    ∃ e : XModLambdaN ((SyntheticCategory.biShift a).obj X) q ≅
      (SyntheticCategory.biShift a).obj (XModLambdaN X q),
      XModLambdaN.incl ((SyntheticCategory.biShift a).obj X) q ≫ e.hom =
        (SyntheticCategory.biShift a).map (XModLambdaN.incl X q) := by
  let oneComm (a : ℤ × ℤ) :
      SyntheticCategory.biShift (Syn := SyntheticSpectrum) a ⋙ SyntheticCategory.biShift (lambdaDegree 1) ≅
        SyntheticCategory.biShift (lambdaDegree 1) ⋙ SyntheticCategory.biShift a :=
    biShiftAddIso a (0,-1) (a+(0,-1)) rfl ≪≫
      (biShiftAddIso (0,-1) a (a+(0,-1)) (add_comm _ _)).symm

  let powerComm (a : ℤ × ℤ) : (q : ℕ) →
      SyntheticCategory.biShift (Syn := SyntheticSpectrum) a ⋙ SyntheticCategory.biShift (lambdaDegree q) ≅
        SyntheticCategory.biShift (lambdaDegree q) ⋙ SyntheticCategory.biShift a := fun q =>
    Nat.rec (motive := fun q =>
      SyntheticCategory.biShift (Syn := SyntheticSpectrum) a ⋙ SyntheticCategory.biShift (lambdaDegree q) ≅
        SyntheticCategory.biShift (lambdaDegree q) ⋙ SyntheticCategory.biShift a)
      (isoWhiskerLeft _ SyntheticCategory.biShift_zero ≪≫
        Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm ≪≫
        (isoWhiskerRight SyntheticCategory.biShift_zero _).symm)
      (fun q ih =>
        isoWhiskerLeft _ (lambdaShiftAddIso 1 q (q+1) (by omega)).symm ≪≫
        (Functor.associator _ _ _).symm ≪≫
        isoWhiskerRight (oneComm a) _ ≪≫ Functor.associator _ _ _ ≪≫
        isoWhiskerLeft _ ih ≪≫
        (Functor.associator _ _ _).symm ≪≫
        isoWhiskerRight (lambdaShiftAddIso 1 q (q+1) (by omega)) _) q

  have powerComm_square (coh : BiShiftCoherence SyntheticSpectrum) (a : ℤ × ℤ)
      (q : ℕ) (X : SyntheticSpectrum) :
      lambdaPow q ((SyntheticCategory.biShift a).obj X) =
        (powerComm a q).hom.app X ≫ (SyntheticCategory.biShift a).map (lambdaPow q X) := by
    induction q generalizing X with
    | zero =>
      simp [powerComm, lambdaPow, ← Functor.map_comp]
    | succ q ih =>
      have h1 : (oneComm a).hom.app X ≫
          (SyntheticCategory.biShift a).map (SyntheticCategory.lam.app X) =
          SyntheticCategory.lam.app ((SyntheticCategory.biShift a).obj X) := by
        simpa [oneComm, Category.assoc] using (coh.lambda_comm a X).symm
      apply (cancel_epi ((lambdaShiftAddIso 1 q (q+1) (by omega)).hom.app
        ((SyntheticCategory.biShift a).obj X))).mp
      rw [lambdaPow_succ_comparison]
      simp only [powerComm, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
        isoWhiskerLeft_hom, isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app,
        Functor.associator_inv_app, Functor.associator_hom_app, Category.id_comp, Category.assoc]
      rw [Iso.hom_inv_id_app_assoc]
      rw [← Functor.map_comp, lambdaPow_succ_comparison, Functor.map_comp]
      have hn := (powerComm a q).hom.naturality (SyntheticCategory.lam.app X)
      have hn' := congrArg (fun h => h ≫ (SyntheticCategory.biShift a).map (lambdaPow q X)) hn
      simp only [Functor.comp_map, Category.assoc] at hn'
      dsimp only [KIP126.Synthetic.Context.lambdaDegree, Functor.id_obj] at hn' ⊢
      erw [← hn']
      rw [← Category.assoc, ← Functor.map_comp, h1, ih]

  let F := SyntheticCategory.biShift (Syn := SyntheticSpectrum) a
  let T := Triangle.mk (lambdaPow q X) (XModLambdaN.incl X q) (XModLambdaN.proj X q)
  let T' := Triangle.mk (lambdaPow q (F.obj X))
    (XModLambdaN.incl (F.obj X) q) (XModLambdaN.proj (F.obj X) q)
  have hT : T ∈ distTriang SyntheticSpectrum := HasFunctorialCofiber.cofib_distinguished _
  have hT' : T' ∈ distTriang SyntheticSpectrum := HasFunctorialCofiber.cofib_distinguished _
  let e := isoTriangleOfIso₁₂ T' (F.mapTriangle.obj T) hT'
    (F.map_distinguished T hT) ((powerComm a q).app X) (Iso.refl _) (by
      change lambdaPow q (F.obj X) ≫ 𝟙 _ =
        (powerComm a q).hom.app X ≫ F.map (lambdaPow q X)
      simpa only [Category.comp_id] using powerComm_square coh a q X)
  refine ⟨Triangle.π₃.mapIso e, ?_⟩
  have h := e.hom.comm₂
  change XModLambdaN.incl (F.obj X) q ≫ e.hom.hom₃ =
    e.hom.hom₂ ≫ F.map (XModLambdaN.incl X q) at h
  change XModLambdaN.incl (F.obj X) q ≫ e.hom.hom₃ =
    F.map (XModLambdaN.incl X q)
  simpa only [e, isoTriangleOfIso₁₂_hom_hom₂, Iso.refl_hom, Category.id_comp] using h

/-- An actual finite quotient comparison with ordinary suspension, preserving
the selected quotient inclusion. This construction alone does not assert
that the quotient of a normalized triangle is distinguished. -/
private theorem finite_quotient_suspension_comparison
    (q : ℕ) (X : SyntheticSpectrum) :
    ∃ esusp : XModLambdaN (X⟦(1:ℤ)⟧) q ≅ (XModLambdaN X q)⟦(1:ℤ)⟧,
      XModLambdaN.incl (X⟦(1:ℤ)⟧) q ≫ esusp.hom =
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl X q) := by
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (1,0)
  let η := SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1
  letI := model.exactness.shiftCommShift (1,0)
  letI := model.exactness.shiftExact (1,0)
  obtain ⟨e,he⟩ := finite_quotient_shift_comparison model.quotients.coherence (1,0) q X
  let eQ := (model.quotients.functoriality.functor q).mapIso (η.symm.app X)
  refine ⟨eQ ≪≫ e ≪≫ η.app (XModLambdaN X q), ?_⟩
  change XModLambdaN.incl (X⟦(1:ℤ)⟧) q ≫ XModLambdaN.map (η.inv.app X) q ≫
      e.hom ≫ η.hom.app (XModLambdaN X q) = _
  calc
    _ = (XModLambdaN.incl (X⟦(1:ℤ)⟧) q ≫ XModLambdaN.map (η.inv.app X) q) ≫
        e.hom ≫ η.hom.app (XModLambdaN X q) := by simp only [Category.assoc]
    _ = (η.inv.app X ≫ XModLambdaN.incl (F.obj X) q) ≫
        e.hom ≫ η.hom.app (XModLambdaN X q) := by
      rw [←XModLambdaN.incl_naturality]
    _ = η.inv.app X ≫ F.map (XModLambdaN.incl X q) ≫
        η.hom.app (XModLambdaN X q) := by
      simpa only [Category.assoc] using congrArg
        (fun z => η.inv.app X ≫ z ≫ η.hom.app (XModLambdaN X q)) he
    _ = η.inv.app X ≫ η.hom.app X ≫
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl X q) := by
      rw [η.hom.naturality]
    _ = _ := by rw [←Category.assoc,η.inv_hom_id_app,Category.id_comp]

end
end KIP126.Literature.Standard
