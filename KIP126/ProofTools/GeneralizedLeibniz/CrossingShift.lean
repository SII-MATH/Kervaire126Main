module
import all KIP126.ProofTools.GeneralizedLeibniz.CrossingDelta
import all KIP126.ProofTools.StretchingRepresentatives

/-! Transport the absolute-boundary crossing comparison to the vertically
shifted source of a normalized map. The quotient and boundary comparisons
come from the same triangle isomorphism. -/

@[expose] section
namespace KIP126.ProofTools.Internal.Leibniz
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Standard
open KIP126.ProofTools.Internal.Mahowald
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2400000

private def verticalTranslate (A : SyntheticSpectrum) (e m w : ℤ) :
    BiHom m w A ≃+ BiHom m (w+e) ((SyntheticCategory.biShift (0,e)).obj A) :=
  (suspInvarianceAddEquiv m w 0 e A).trans
    (regradeAddEquiv (add_zero m) rfl)

private theorem vertical_translate_filtration_iff (A : SyntheticObject)
    (e m w v : ℤ) (a : BiHom m w (A.obj model.nu model.auxiliary)) :
    FiltrationAtLeast model.syntheticTower v (verticalTranslate _ e m w a) ↔
      FiltrationAtLeast model.syntheticTower v a := by
  change FiltrationAtLeast model.syntheticTower v
    (homotopyRegrade (add_zero m) rfl (susp_invariance m w 0 e _ a)) ↔ _
  rw [regrade_filtration_iff]
  have he : susp_invariance m w 0 e _ a = shiftHomotopyClass (0,e) (m,w) a := by
    simp [susp_invariance,shiftHomotopyClass,Iso.homCongr]
  rw [he]
  exact shift_filtration_iff A (0,e) (m,w) v a

private theorem vertical_translate_comp (A B : SyntheticSpectrum) (f : A ⟶ B)
    (e m w : ℤ) (a : BiHom m w A) :
    verticalTranslate A e m w a ≫ (SyntheticCategory.biShift (0,e)).map f =
      verticalTranslate B e m w (a ≫ f) := by
  simp [verticalTranslate,AddEquiv.trans_apply,regradeAddEquiv,
    suspInvarianceAddEquiv,susp_invariance,Iso.homCongr,regrade_precomp,Functor.map_comp]

private theorem quotient_boundary_shift_exists (A : SyntheticSpectrum) (e : ℤ) (q : ℕ) :
    ∃ (eQ : XModLambdaN ((SyntheticCategory.biShift (0,e)).obj A) q ≅
        (SyntheticCategory.biShift (0,e)).obj (XModLambdaN A q))
      (eD : (SyntheticCategory.biShift (0,e)).obj
          ((SyntheticCategory.biShift (1,-(q:ℤ))).obj A) ≅
        (SyntheticCategory.biShift (1,-(q:ℤ))).obj
          ((SyntheticCategory.biShift (0,e)).obj A)),
      eQ.hom ≫ (SyntheticCategory.biShift (0,e)).map (absoluteBoundary A q) ≫ eD.hom =
        absoluteBoundary ((SyntheticCategory.biShift (0,e)).obj A) q := by
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,e)
  letI := model.exactness.shiftCommShift (0,e)
  letI := model.exactness.shiftExact (0,e)
  obtain ⟨eQ,_,e₁,_,hδ⟩ := quotient_shift_exists model.quotients.coherence (0,e) q A
  let eD := F.mapIso (biSuspensionIso q A) ≪≫
    (F.commShiftIso (1:ℤ)).app _ ≪≫
    (shiftFunctor SyntheticSpectrum (1:ℤ)).mapIso e₁.symm ≪≫
    (biSuspensionIso q (F.obj A)).symm
  refine ⟨eQ,eD,?_⟩
  have h := congrArg (fun z => z ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map e₁.inv ≫
    (biSuspensionIso q (F.obj A)).inv) hδ
  simpa only [absoluteBoundary,eD,F,Iso.trans_hom,Iso.symm_hom,Functor.mapIso_hom,
    Functor.map_comp,Category.assoc,Iso.map_inv_hom_id_assoc,Iso.map_hom_inv_id_assoc,
    Iso.app_hom] using h

private theorem shifted_boundary_crossing_correction (X : ClassicalObject)
    (q : ℕ) (e r s t u v : ℤ) (hnc : NoCrossingOn model X r (q+1) (s,t))
    (hu : s < u) (hv : v ≤ s+r)
    (a : BiHom (t-s) (t+e) (XModLambdaN ((SyntheticCategory.biShift (0,e)).obj
      (model.nu.functor.obj (X.obj model.auxiliary))) q))
    (ha : FiltrationAtLeast model.syntheticTower u a)
    (hδ : FiltrationAtLeast model.syntheticTower v
      (a ≫ absoluteBoundary ((SyntheticCategory.biShift (0,e)).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) q)) :
    ∃ a0 : BiHom (t-s) (t+e) (XModLambdaN ((SyntheticCategory.biShift (0,e)).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) q),
      FiltrationAtLeast model.syntheticTower u a0 ∧
      FiltrationAtLeast model.syntheticTower (u+1) (a-a0) ∧
      FiltrationAtLeast model.syntheticTower (v+1)
        (a0 ≫ absoluteBoundary ((SyntheticCategory.biShift (0,e)).obj
          (model.nu.functor.obj (X.obj model.auxiliary))) q) := by
  let A := model.nu.functor.obj (X.obj model.auxiliary)
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,e)
  obtain ⟨eQ,eD,hsquare⟩ := quotient_boundary_shift_exists A e q
  let E := verticalTranslate (XModLambdaN A q) e (t-s) t
  let ED := verticalTranslate ((SyntheticCategory.biShift (1,-(q:ℤ))).obj A) e (t-s) t
  let b := E.symm (a ≫ eQ.hom)
  have hb : E b = a ≫ eQ.hom := E.apply_symm_apply _
  have hfil : ∀ (k : ℤ) (z : BiHom (t-s) t (XModLambdaN A q)),
      FiltrationAtLeast model.syntheticTower k (E z ≫ eQ.inv) ↔
        FiltrationAtLeast model.syntheticTower k z := by
    intro k z
    exact (iso_filtration_iff (.shift (0,e) (.quotient q (.nu X)))
      (.quotient q (.shift (0,e) (.nu X))) eQ.symm (t-s) (t+e) k (E z)).trans
        (vertical_translate_filtration_iff (.quotient q (.nu X)) e (t-s) t k z)
  have hboundary : ∀ z : BiHom (t-s) t (XModLambdaN A q),
      (E z ≫ eQ.inv) ≫ absoluteBoundary (F.obj A) q =
        ED (z ≫ absoluteBoundary A q) ≫ eD.hom := by
    intro z
    rw [←hsquare]
    simp only [Category.assoc,Iso.inv_hom_id_assoc]
    rw [←Category.assoc,vertical_translate_comp]
  have hboundary_fil : ∀ (k : ℤ) (z : BiHom (t-s) t (XModLambdaN A q)),
      FiltrationAtLeast model.syntheticTower k
          ((E z ≫ eQ.inv) ≫ absoluteBoundary (F.obj A) q) ↔
        FiltrationAtLeast model.syntheticTower k (z ≫ absoluteBoundary A q) := by
    intro k z
    rw [hboundary]
    exact (iso_filtration_iff (.shift (0,e) (.shift (1,-(q:ℤ)) (.nu X)))
      (.shift (1,-(q:ℤ)) (.shift (0,e) (.nu X))) eD (t-s) (t+e) k _).trans
        (vertical_translate_filtration_iff (.shift (1,-(q:ℤ)) (.nu X)) e (t-s) t k _)
  have hba : E b ≫ eQ.inv = a := by rw [hb]; simp
  obtain ⟨b0,hb0,hdiff,hδ0⟩ := boundary_crossing_correction X q r s t u v hnc hu hv b
    ((hfil u b).mp (by rwa [hba])) ((hboundary_fil v b).mp (by rwa [hba]))
  refine ⟨E b0 ≫ eQ.inv,(hfil u b0).mpr hb0,?_,(hboundary_fil (v+1) b0).mpr hδ0⟩
  have h := (hfil (u+1) (b-b0)).mpr hdiff
  simpa only [map_sub,Preadditive.sub_comp,hba] using h

private theorem classical_noCrossing_shifted_absolute_boundary (X : ClassicalObject)
    (page : ℕ) (e r s t : ℤ) (hnc : NoCrossingOn model X r page (s,t)) :
    TowerNoCrossing (model.convergentMap
      (.quotient (page-1) (.shift (0,e) (.nu X)))
      (.shift (1,-((page-1:ℕ):ℤ)) (.shift (0,e) (.nu X)))
      (absoluteBoundary ((SyntheticCategory.biShift (0,e)).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) (page-1)))
      (t-s,t+e) s r := by
  apply tower_no_crossing_of_correction
  intro u v hu _ hv a ha hδ
  have hnc' : NoCrossingOn model X r ((page-1:ℕ)+1) (s,t) := by
    convert hnc using 1
    have h := hnc.1
    omega
  exact shifted_boundary_crossing_correction X (page-1) e r s t u v hnc' hu hv a ha hδ

end
end KIP126.ProofTools.Internal.Leibniz
