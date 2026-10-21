module

import all KIP126.ProofTools.MahowaldLeibniz.PositiveHBranch
import all KIP126.ProofTools.MahowaldLeibniz.OrdinaryLastLayer
import all KIP126.ProofTools.GeneralizedMahowald.QuotientShift
import all KIP126.ProofTools.GeneralizedMahowald.SuspensionDetection

/-! The actual image square for an exponent-zero first arrow. The same
comparison applies to either positive position of the other two arrows. -/

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
set_option maxHeartbeats 3000000

private theorem ordinary_regrade_zero_iff {A : SyntheticSpectrum} {m m' w w' : ℤ}
    (hm : m=m') (hw : w=w') (a : BiHom m w A) :
    homotopyRegrade hm hw a=0 ↔ a=0 := by
  subst m'
  subst w'
  rfl

private theorem normalized_first_suspension_zero
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ)+
      normalizedExponent model.classicalTower T.g+normalizedExponent model.classicalTower T.h=1)
    (hf : normalizedExponent model.classicalTower T.f=0) :
    (shiftFunctor SyntheticSpectrum (1:ℤ)).map (normalizedTriangle model T he).mor₁ =
      (normalizedSuspensionZeroIso T he hf).hom ≫
        (SyntheticCategory.biShift (1,0)).map (model.nu.functor.map T.f) ≫
          (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).hom.app _ := by
  have hn : (normalizedTriangle model T he).mor₁ =
      (zero_positive_iso (model.nu.functor.obj (T.X.obj model.auxiliary)) _ hf).hom ≫
        model.nu.functor.map T.f := by
    simpa only [normalizedTriangle,Triangle.mk_mor₁,zero_positive_iso,
      Iso.trans_hom,eqToIso.hom,Iso.app_hom,Category.assoc] using
      normalized_zero_map T.X T.Y T.f hf
  rw [hn,Functor.map_comp]
  dsimp only [normalizedSuspensionZeroIso,Iso.trans_hom,Functor.mapIso_hom,
    Iso.symm_hom,Iso.app_inv]
  rw [(SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).hom.naturality]
  simp only [Iso.app_hom,Iso.symm_hom,Category.assoc,Iso.inv_hom_id_app_assoc]

private theorem shifted_ordinary_quotient_map_on_spheres
    (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (N : ℕ) (hN : 0<N) (δ : ℤ×ℤ)
    (εX : XModLambdaN ((SyntheticCategory.biShift δ).obj
      (model.nu.functor.obj (X.obj model.auxiliary))) N ≅
      (SyntheticCategory.biShift δ).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) N))
    (εY : XModLambdaN ((SyntheticCategory.biShift δ).obj
      (model.nu.functor.obj (Y.obj model.auxiliary))) N ≅
      (SyntheticCategory.biShift δ).obj
        (XModLambdaN (model.nu.functor.obj (Y.obj model.auxiliary)) N))
    (hεX : XModLambdaN.incl _ N ≫ εX.hom =
      (SyntheticCategory.biShift δ).map (XModLambdaN.incl _ N))
    (hεY : XModLambdaN.incl _ N ≫ εY.hom =
      (SyntheticCategory.biShift δ).map (XModLambdaN.incl _ N))
    (m w : ℤ) (a : BiHom m w (XModLambdaN ((SyntheticCategory.biShift δ).obj
      (model.nu.functor.obj (X.obj model.auxiliary))) N)) :
    a ≫ XModLambdaN.map ((SyntheticCategory.biShift δ).map (model.nu.functor.map f)) N ≫
      εY.hom = a ≫ εX.hom ≫
        (SyntheticCategory.biShift δ).map (XModLambdaN.map (model.nu.functor.map f) N) := by
  apply shifted_quotient_sphere_congruence X Y δ N N hN le_rfl εX hεX
  rw [←Category.assoc,←XModLambdaN.incl_naturality,Category.assoc,hεY,
    ←Category.assoc _ εX.hom,hεX,←Functor.map_comp,←Functor.map_comp,
    XModLambdaN.incl_naturality]

/-- An ordinary native image equal to zero has zero image under the actual
raw ordinarily suspended normalized arrow. -/
private theorem native_ordinary_image_zero_implies_raw_zero
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ)+
      normalizedExponent model.classicalTower T.g+normalizedExponent model.classicalTower T.h=1)
    (hf : normalizedExponent model.classicalTower T.f=0)
    (N c : ℕ) (hN : 0<N) (s t : ℤ)
    (ε : XModLambdaN ((SyntheticCategory.biShift (1,0)).obj
      (model.nu.functor.obj (T.X.obj model.auxiliary))) N ≅
      (SyntheticCategory.biShift (1,0)).obj
        (XModLambdaN (model.nu.functor.obj (T.X.obj model.auxiliary)) N))
    (hε : XModLambdaN.incl _ N ≫ ε.hom =
      (SyntheticCategory.biShift (1,0)).map (XModLambdaN.incl _ N))
    (a : BiHom (t-s) (t-c)
      (XModLambdaN ((normalizedTriangle model T he).obj₁⟦(1:ℤ)⟧) N))
    (hz : positiveHSourceDesuspend T he hf N c s t ε a ≫
      XModLambdaN.map (model.nu.functor.map T.f) N=0) :
    a ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
      (normalizedTriangle model T he).mor₁) N=0 := by
  letI := model.exactness.shiftCommShift (1,0)
  letI := model.exactness.shiftExact (1,0)
  obtain ⟨εY,hεY,_⟩ := quotient_shift_exists model.quotients.coherence (1,0) N
    (model.nu.functor.obj (T.Y.obj model.auxiliary))
  let a₀ := positiveHSourceDesuspend T he hf N c s t ε a
  let a' := homotopyRegrade (m':=((t-(s+1),t-c)+(1,0)).1)
    (w':=((t-(s+1),t-c)+(1,0)).2) (by dsimp; omega) (by dsimp; omega)
      (a ≫ XModLambdaN.map (normalizedSuspensionZeroIso T he hf).hom N)
  have hrestore : shiftHomotopyClass (1,0) (t-(s+1),t-c) a₀ = a' ≫ ε.hom := by
    have h := congrArg (fun u => u ≫ ε.hom)
      (shift_quotient_unshift T.X (1,0) (t-(s+1),t-c) N ε a')
    simpa only [a₀,positiveHSourceDesuspend,a',Category.assoc,Iso.inv_hom_id,
      Category.comp_id] using h
  have hshift : shiftHomotopyClass (1,0) (t-(s+1),t-c) a₀ ≫
      (SyntheticCategory.biShift (1,0)).map (XModLambdaN.map (model.nu.functor.map T.f) N)=0 := by
    dsimp only [shiftHomotopyClass]
    rw [Category.assoc,←Functor.map_comp,hz,Functor.map_zero,comp_zero]
  have hs := shifted_ordinary_quotient_map_on_spheres T.X T.Y T.f N hN (1,0)
    ε εY hε hεY _ _ a'
  have hz' : a' ≫ XModLambdaN.map
      ((SyntheticCategory.biShift (1,0)).map (model.nu.functor.map T.f)) N=0 := by
    apply (cancel_mono εY.hom).mp
    rw [zero_comp,Category.assoc,hs,←Category.assoc,hrestore.symm]
    exact hshift
  have hz'' : a ≫ XModLambdaN.map (normalizedSuspensionZeroIso T he hf).hom N ≫
      XModLambdaN.map ((SyntheticCategory.biShift (1,0)).map (model.nu.functor.map T.f)) N=0 := by
    exact (ordinary_regrade_zero_iff
      (m':=((t-(s+1),t-c)+(1,0)).1) (w':=((t-(s+1),t-c)+(1,0)).2)
      (by dsimp; omega) (by dsimp; omega) _).mp
      (by simpa only [a',regrade_comp,Category.assoc] using hz')
  rw [normalized_first_suspension_zero T he hf,
    model.quotients.functoriality.map_comp,model.quotients.functoriality.map_comp]
  have hz''' := congrArg (fun u => u ≫ XModLambdaN.map
    ((SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).hom.app
      (model.nu.functor.obj (T.Y.obj model.auxiliary))) N) hz''
  simpa only [Category.assoc,zero_comp] using hz'''

private theorem positive_h_source_desuspend_sub
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ)+
      normalizedExponent model.classicalTower T.g+normalizedExponent model.classicalTower T.h=1)
    (hf : normalizedExponent model.classicalTower T.f=0)
    (N c : ℕ) (s t : ℤ)
    (ε : XModLambdaN ((SyntheticCategory.biShift (1,0)).obj
      (model.nu.functor.obj (T.X.obj model.auxiliary))) N ≅
      (SyntheticCategory.biShift (1,0)).obj
        (XModLambdaN (model.nu.functor.obj (T.X.obj model.auxiliary)) N))
    (a b : BiHom (t-s) (t-c)
      (XModLambdaN ((normalizedTriangle model T he).obj₁⟦(1:ℤ)⟧) N)) :
    positiveHSourceDesuspend T he hf N c s t ε (a-b) =
      positiveHSourceDesuspend T he hf N c s t ε a -
        positiveHSourceDesuspend T he hf N c s t ε b := by
  simp only [positiveHSourceDesuspend,Preadditive.sub_comp,homotopy_regrade_sub,quotient_unshift_sub]

/-- The common core's actual native ambiguity condition implies equality
of the two specified raw images; there is no premise naming that equality. -/
private theorem ordinary_same_x_label_raw_image
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ)+
      normalizedExponent model.classicalTower T.g+normalizedExponent model.classicalTower T.h=1)
    (hf : normalizedExponent model.classicalTower T.f=0)
    (N c : ℕ) (hN : 0<N) (s t : ℤ)
    (ε : XModLambdaN ((SyntheticCategory.biShift (1,0)).obj
      (model.nu.functor.obj (T.X.obj model.auxiliary))) N ≅
      (SyntheticCategory.biShift (1,0)).obj
        (XModLambdaN (model.nu.functor.obj (T.X.obj model.auxiliary)) N))
    (hε : XModLambdaN.incl _ N ≫ ε.hom =
      (SyntheticCategory.biShift (1,0)).map (XModLambdaN.incl _ N))
    (hkill : ∀ d : BiHom (t-(s+1)) (t-c)
      (XModLambdaN (model.nu.functor.obj (T.X.obj model.auxiliary)) N),
      FiltrationAtLeast model.syntheticTower (s+1+1) d →
        d ≫ XModLambdaN.map (model.nu.functor.map T.f) N=0)
    (x : Ambient model T.X (s+1,t))
    (a b : BiHom (t-s) (t-c)
      (XModLambdaN ((normalizedTriangle model T he).obj₁⟦(1:ℤ)⟧) N))
    (ha : Detects (model.convergence (.quotient N (.nu T.X)))
      (s+1,t,t-c) (finiteTargetLabel model T.X N (s+1) t c x)
      (positiveHSourceDesuspend T he hf N c s t ε a))
    (hb : Detects (model.convergence (.quotient N (.nu T.X)))
      (s+1,t,t-c) (finiteTargetLabel model T.X N (s+1) t c x)
      (positiveHSourceDesuspend T he hf N c s t ε b)) :
    a ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
      (normalizedTriangle model T he).mor₁) N =
    b ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
      (normalizedTriangle model T he).mor₁) N := by
  have hdiff := detects_sub_filtration (model.convergence (.quotient N (.nu T.X)))
    (s+1,t,t-c) ha hb
  rw [←positive_h_source_desuspend_sub] at hdiff
  have hz := native_ordinary_image_zero_implies_raw_zero T he hf N c hN s t ε hε
    (a-b) (hkill _ hdiff)
  exact sub_eq_zero.mp (by simpa only [Preadditive.sub_comp] using hz)

private theorem pdf_conditions_same_x_label_raw_image_zero
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ)+
      normalizedExponent model.classicalTower T.g+normalizedExponent model.classicalTower T.h=1)
    (hf : normalizedExponent model.classicalTower T.f=0)
    (c K : ℕ) (hK : 2≤K) (s t : ℤ)
    (ε : XModLambdaN ((SyntheticCategory.biShift (1,0)).obj
      (model.nu.functor.obj (T.X.obj model.auxiliary))) (c+K) ≅
      (SyntheticCategory.biShift (1,0)).obj
        (XModLambdaN (model.nu.functor.obj (T.X.obj model.auxiliary)) (c+K)))
    (hε : XModLambdaN.incl _ (c+K) ≫ ε.hom =
      (SyntheticCategory.biShift (1,0)).map (XModLambdaN.incl _ (c+K)))
    (hNC1 : ∀ j : ℕ, 1≤j → j<K-1 →
      cycles model T.X ((K:ℤ)-j) (s+1+j,t+j) ≤
        boundaries model T.X ((c:ℤ)+j+1) (s+1+j,t+j))
    (hNC2 : ∀ x : Ambient model T.X (s+1+K-1,t+K-1),
      (model.classical.map T.f).pageMap 2 (s+1+K-1,t+K-1) x ∈
        boundaries model T.Y (c+K) (s+1+K-1,t+K-1))
    (x : Ambient model T.X (s+1,t))
    (a b : BiHom (t-s) (t-c)
      (XModLambdaN ((normalizedTriangle model T he).obj₁⟦(1:ℤ)⟧) (c+K)))
    (ha : Detects (model.convergence (.quotient (c+K) (.nu T.X)))
      (s+1,t,t-c) (finiteTargetLabel model T.X (c+K) (s+1) t c x)
      (positiveHSourceDesuspend T he hf (c+K) c s t ε a))
    (hb : Detects (model.convergence (.quotient (c+K) (.nu T.X)))
      (s+1,t,t-c) (finiteTargetLabel model T.X (c+K) (s+1) t c x)
      (positiveHSourceDesuspend T he hf (c+K) c s t ε b)) :
    a ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
      (normalizedTriangle model T he).mor₁) (c+K) =
    b ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
      (normalizedTriangle model T he).mor₁) (c+K) := by
  exact ordinary_same_x_label_raw_image T he hf (c+K) c (by omega) s t ε hε
    (ordinary_map_pdf_annihilation T.X T.Y T.f c K hK (s+1) t hNC1 hNC2) x a b ha hb

end
end KIP126.ProofTools.Internal.MahowaldLeibniz
