module

import all KIP126.ProofTools.MahowaldLeibniz.CoreAtLevel
import all KIP126.ProofTools.MahowaldLeibniz.LastLayerNative
import all KIP126.ProofTools.GeneralizedMahowald.FiniteComparison
import all KIP126.ProofTools.GeneralizedMahowald.CommonEdgeLabels

/-! Actual comparison of native positive normalized images and the ordinary
suspension images occurring in the finite May square. -/

@[expose] section
namespace KIP126.ProofTools.Internal.MahowaldLeibniz
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Standard
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
open KIP126.ProofTools.Internal.Leibniz
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 4000000

private def positiveOrdinaryIso :
    SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,1) ⋙
      shiftFunctor SyntheticSpectrum (1:ℤ) ≅
      SyntheticCategory.biShift (1,1) :=
  Functor.isoWhiskerLeft (SyntheticCategory.biShift (0,1))
      (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).symm ≪≫
    biShiftAddIso (0,1) (1,0) (1,1) (by ext <;> simp)

private def positiveOrdinaryQuotientIso (X : ClassicalObject) (q : ℕ)
    (ε : XModLambdaN ((SyntheticCategory.biShift (1,1)).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) q ≅
      (SyntheticCategory.biShift (1,1)).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
    (εp : XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) q ≅
      (SyntheticCategory.biShift (0,1)).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q)) :
    XModLambdaN (((SyntheticCategory.biShift (0,1)).obj
      (model.nu.functor.obj (X.obj model.auxiliary)))⟦(1:ℤ)⟧) q ≅
      (XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) q)⟦(1:ℤ)⟧ :=
  (model.quotients.functoriality.functor q).mapIso
      (positiveOrdinaryIso.app (model.nu.functor.obj (X.obj model.auxiliary))) ≪≫
    ε ≪≫ (positiveOrdinaryIso.app _).symm ≪≫
      (shiftFunctor SyntheticSpectrum (1:ℤ)).mapIso εp.symm

private theorem positiveOrdinaryQuotientIso_incl (X : ClassicalObject) (q : ℕ)
    (ε : XModLambdaN ((SyntheticCategory.biShift (1,1)).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) q ≅
      (SyntheticCategory.biShift (1,1)).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
    (εp : XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) q ≅
      (SyntheticCategory.biShift (0,1)).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
    (hε : XModLambdaN.incl _ q ≫ ε.hom =
      (SyntheticCategory.biShift (1,1)).map (XModLambdaN.incl _ q))
    (hεp : XModLambdaN.incl _ q ≫ εp.hom =
      (SyntheticCategory.biShift (0,1)).map (XModLambdaN.incl _ q)) :
    XModLambdaN.incl _ q ≫ (positiveOrdinaryQuotientIso X q ε εp).hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ q) := by
  let A := model.nu.functor.obj (X.obj model.auxiliary)
  change XModLambdaN.incl _ q ≫ XModLambdaN.map (positiveOrdinaryIso.hom.app A) q ≫
    ε.hom ≫ positiveOrdinaryIso.inv.app (XModLambdaN A q) ≫
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map εp.inv = _
  rw [←Category.assoc,←XModLambdaN.incl_naturality,Category.assoc,
    ←Category.assoc _ ε.hom,hε,
    positiveOrdinaryIso.inv.naturality_assoc]
  dsimp only [Functor.comp_map]
  rw [Iso.hom_inv_id_app_assoc,←Functor.map_comp,←hεp,
    Category.assoc,Iso.hom_inv_id,Category.comp_id]

/-- Positive finite image zero implies zero under the actual quotient of
the ordinarily suspended map, for arbitrary inclusion-compatible quotient
comparisons at both shifts. -/
private theorem positive_image_zero_implies_suspended_image_zero
    (X Y : ClassicalObject) (q : ℕ) (hq : 0<q)
    (f : (SyntheticCategory.biShift (0,1)).obj
      (model.nu.functor.obj (X.obj model.auxiliary)) ⟶
        model.nu.functor.obj (Y.obj model.auxiliary))
    (ε : XModLambdaN ((SyntheticCategory.biShift (1,1)).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) q ≅
      (SyntheticCategory.biShift (1,1)).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
    (εp : XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) q ≅
      (SyntheticCategory.biShift (0,1)).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
    (hε : XModLambdaN.incl _ q ≫ ε.hom =
      (SyntheticCategory.biShift (1,1)).map (XModLambdaN.incl _ q))
    (hεp : XModLambdaN.incl _ q ≫ εp.hom =
      (SyntheticCategory.biShift (0,1)).map (XModLambdaN.incl _ q))
    (m w : ℤ)
    (a : BiHom (m+1) (w+1) (XModLambdaN
      (((SyntheticCategory.biShift (0,1)).obj
        (model.nu.functor.obj (X.obj model.auxiliary)))⟦(1:ℤ)⟧) q))
    (a₀ : BiHom m w (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
    (ha : shiftHomotopyClass (1,1) (m,w) a₀ =
      a ≫ XModLambdaN.map (positiveOrdinaryIso.hom.app _) q ≫ ε.hom)
    (hz : homotopyRegrade (m':=m) (w':=w+1) (by dsimp; omega) rfl
      (shiftHomotopyClass (0,1) (m,w) a₀) ≫ εp.inv ≫ XModLambdaN.map f q=0) :
    a ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map f) q=0 := by
  let A := model.nu.functor.obj (X.obj model.auxiliary)
  let ex := positiveOrdinaryQuotientIso X q ε εp
  obtain ⟨ey,hey⟩ := quotient_suspension_inclusion_exists
    (model.nu.functor.obj (Y.obj model.auxiliary)) q
  apply (cancel_mono ey.hom).mp
  rw [zero_comp,Category.assoc,finite_suspension_normalized_map_on_spheres X Y 1 (by decide) q hq f
    ex ey (positiveOrdinaryQuotientIso_incl X q ε εp hε hεp) hey]
  have hz' : (SyntheticCategory.biShift (0,1)).map a₀ ≫ εp.inv ≫ XModLambdaN.map f q=0 := by
    have hz₀ : shiftHomotopyClass (0,1) (m,w) a₀ ≫ εp.inv ≫ XModLambdaN.map f q=0 :=
      (last_layer_regrade_zero_iff (show ((m,w)+(0,1)).1=m by dsimp; omega) rfl _).mp
        (by simpa only [regrade_comp] using hz)
    exact (cancel_epi ((SyntheticCategory.biShift_comp (m,w) (0,1)).inv.app S_0_0)).mp
      (by simpa only [shiftHomotopyClass,Category.assoc,comp_zero] using hz₀)
  dsimp only [ex,positiveOrdinaryQuotientIso,Iso.trans_hom,Functor.mapIso_hom,
    Iso.symm_hom,Iso.app_hom,Iso.app_inv]
  simp only [Category.assoc]
  change a ≫ XModLambdaN.map (positiveOrdinaryIso.hom.app A) q ≫ ε.hom ≫
    positiveOrdinaryIso.inv.app (XModLambdaN A q) ≫
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map εp.inv ≫
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.map f q)=0
  have ht := congrArg (fun z => z ≫ positiveOrdinaryIso.inv.app (XModLambdaN A q) ≫
    (shiftFunctor SyntheticSpectrum (1:ℤ)).map εp.inv ≫
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.map f q)) ha
  rw [show a ≫ XModLambdaN.map (positiveOrdinaryIso.hom.app A) q ≫ ε.hom ≫
      positiveOrdinaryIso.inv.app (XModLambdaN A q) ≫
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map εp.inv ≫
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.map f q) =
    shiftHomotopyClass (1,1) (m,w) a₀ ≫ positiveOrdinaryIso.inv.app (XModLambdaN A q) ≫
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map εp.inv ≫
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.map f q) from by
        simpa only [Category.assoc] using ht.symm]
  unfold shiftHomotopyClass
  rw [Category.assoc,positiveOrdinaryIso.inv.naturality_assoc]
  dsimp only [Functor.comp_map]
  rw [←Functor.map_comp,←Functor.map_comp,hz',Functor.map_zero,comp_zero,comp_zero]

private def normalizedPositiveSourceIso (T : TriangleData model.auxiliary)
    (hf : normalizedExponent model.classicalTower T.f=1) :
    (SyntheticCategory.biShift (0,(normalizedExponent model.classicalTower T.f:ℤ))).obj
      (model.nu.functor.obj (T.X.obj model.auxiliary)) ≅
    (SyntheticCategory.biShift (0,1)).obj
      (model.nu.functor.obj (T.X.obj model.auxiliary)) :=
  eqToIso (congrArg (fun k : ℕ => (SyntheticCategory.biShift (0,(k:ℤ))).obj
    (model.nu.functor.obj (T.X.obj model.auxiliary))) hf)

private theorem normalizedPositiveSourceIso_map (T : TriangleData model.auxiliary)
    (hf : normalizedExponent model.classicalTower T.f=1) :
    (normalizedPositiveSourceIso T hf).hom ≫ lastLayerNormalizedMap T hf =
      (model.normalizedMap T.X T.Y T.f).map := by
  have transport (k : ℕ) (hk : k=1)
      (f : (SyntheticCategory.biShift (0,(k:ℤ))).obj
        (model.nu.functor.obj (T.X.obj model.auxiliary)) ⟶
        model.nu.functor.obj (T.Y.obj model.auxiliary)) :
      eqToHom (congrArg (fun j : ℕ => (SyntheticCategory.biShift (0,(j:ℤ))).obj
        (model.nu.functor.obj (T.X.obj model.auxiliary))) hk) ≫
          (show (SyntheticCategory.biShift (0,1)).obj
            (model.nu.functor.obj (T.X.obj model.auxiliary)) ⟶
              model.nu.functor.obj (T.Y.obj model.auxiliary) from
                by simpa only [hk,Nat.cast_one] using f) = f := by
    subst k
    simp only [eqToHom_refl,Category.id_comp]
    rfl
  exact transport _ hf _

private theorem normalizedPositiveSourceIso_suspension
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g +
      normalizedExponent model.classicalTower T.h=1)
    (hf : normalizedExponent model.classicalTower T.f=1) :
    (shiftFunctor SyntheticSpectrum (1:ℤ)).map (normalizedPositiveSourceIso T hf).hom ≫
      positiveOrdinaryIso.hom.app (model.nu.functor.obj (T.X.obj model.auxiliary)) =
    (normalizedSuspensionNativeIso T he hf).hom ≫
      (model.nu.suspensionIso (T.X.obj model.auxiliary)).hom := by
  let A := model.nu.functor.obj (T.X.obj model.auxiliary)
  have transport (k : ℕ) (hk : k=1) :
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map
        (eqToHom (congrArg (fun j : ℕ => (SyntheticCategory.biShift (0,(j:ℤ))).obj A) hk)) ≫
          positiveOrdinaryIso.hom.app A =
      (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).inv.app
          ((SyntheticCategory.biShift (0,(k:ℤ))).obj A) ≫
        (SyntheticCategory.biShift_comp (0,(k:ℤ)) (1,0)).hom.app A ≫
          eqToHom (congrArg (fun p : ℤ×ℤ => (SyntheticCategory.biShift p).obj A)
            (show (0,(k:ℤ))+(1,0)=(1,1) by ext <;> simp [hk])) := by
    subst k
    simp [positiveOrdinaryIso,biShiftAddIso]
  simpa only [normalizedPositiveSourceIso,eqToIso.hom,normalizedSuspensionNativeIso,normalizedTriangle,Triangle.mk_obj₁,
    Iso.trans_hom,Iso.symm_hom,Iso.app_hom,Iso.app_inv,Category.assoc,
    Iso.inv_hom_id,Category.comp_id] using transport _ hf

/-- The native positive-image zero statement is exactly sufficient for the
raw QΣf image in the May square. Both quotient comparisons remain arbitrary
and are related by a constructed inclusion-compatible ordinary comparison. -/
private theorem native_positive_image_zero_implies_raw_zero
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g +
      normalizedExponent model.classicalTower T.h=1)
    (hf : normalizedExponent model.classicalTower T.f=1)
    (N c : ℕ) (hN : 0<N) (S V : ℤ)
    (ε : XModLambdaN ((SyntheticCategory.biShift (1,1)).obj
        (model.nu.functor.obj (T.X.obj model.auxiliary))) N ≅
      (SyntheticCategory.biShift (1,1)).obj
        (XModLambdaN (model.nu.functor.obj (T.X.obj model.auxiliary)) N))
    (εp : XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
        (model.nu.functor.obj (T.X.obj model.auxiliary))) N ≅
      (SyntheticCategory.biShift (0,1)).obj
        (XModLambdaN (model.nu.functor.obj (T.X.obj model.auxiliary)) N))
    (hε : XModLambdaN.incl _ N ≫ ε.hom =
      (SyntheticCategory.biShift (1,1)).map (XModLambdaN.incl _ N))
    (hεp : XModLambdaN.incl _ N ≫ εp.hom =
      (SyntheticCategory.biShift (0,1)).map (XModLambdaN.incl _ N))
    (a : BiHom (V-S+1) (V-c+1)
      (XModLambdaN ((normalizedTriangle model T he).obj₁⟦(1:ℤ)⟧) N))
    (hz : positiveFiniteImage T hf N εp (V-S) (V-c)
      (rawMaySourceDesuspend T he hf N c S V ε a)=0) :
    a ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
      (normalizedTriangle model T he).mor₁) N=0 := by
  let a' := a ≫ XModLambdaN.map
    ((shiftFunctor SyntheticSpectrum (1:ℤ)).map (normalizedPositiveSourceIso T hf).hom) N
  let a₀ := rawMaySourceDesuspend T he hf N c S V ε a
  have hrestore := shift_quotient_unshift T.X (1,1) (V-S,V-c) N ε
    (homotopyRegrade rfl rfl
      (a ≫ XModLambdaN.map (normalizedSuspensionNativeIso T he hf).hom N ≫
        XModLambdaN.map (model.nu.suspensionIso (T.X.obj model.auxiliary)).hom N))
  have hrestore' := congrArg (fun b => b ≫ ε.hom) hrestore
  simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id] at hrestore'
  have hsource : shiftHomotopyClass (1,1) (V-S,V-c) a₀ =
      a' ≫ XModLambdaN.map (positiveOrdinaryIso.hom.app _) N ≫ ε.hom := by
    have hc : XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
        (normalizedPositiveSourceIso T hf).hom) N ≫
        XModLambdaN.map (positiveOrdinaryIso.hom.app _) N =
      XModLambdaN.map (normalizedSuspensionNativeIso T he hf).hom N ≫
        XModLambdaN.map (model.nu.suspensionIso (T.X.obj model.auxiliary)).hom N := by
      rw [←model.quotients.functoriality.map_comp,
        normalizedPositiveSourceIso_suspension T he hf,
        model.quotients.functoriality.map_comp]
    have hc' := congrArg (fun z => a ≫ z ≫ ε.hom) hc
    calc
      _ = a ≫ XModLambdaN.map (normalizedSuspensionNativeIso T he hf).hom N ≫
          XModLambdaN.map (model.nu.suspensionIso (T.X.obj model.auxiliary)).hom N ≫ ε.hom := by
            simpa only [a₀,rawMaySourceDesuspend,homotopyRegrade,Category.assoc] using hrestore'
      _ = _ := by simpa only [a',Category.assoc] using hc'.symm
  have hz' := positive_image_zero_implies_suspended_image_zero T.X T.Y N hN
    (lastLayerNormalizedMap T hf) ε εp hε hεp (V-S) (V-c) a' a₀ hsource
    (by simpa only [positiveFiniteImage,Category.assoc] using hz)
  dsimp only [a'] at hz'
  rw [Category.assoc,←model.quotients.functoriality.map_comp,←Functor.map_comp,
    normalizedPositiveSourceIso_map T hf] at hz'
  exact hz'

/-- Under the PDF conditions, the two specified raw May sources with the
same native X label have exactly equal actual QΣf-images. -/
private theorem pdf_conditions_same_x_label_raw_image
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g +
      normalizedExponent model.classicalTower T.h=1)
    (hf : normalizedExponent model.classicalTower T.f=1)
    (c K : ℕ) (hK : 2≤K) (S V : ℤ)
    (ε : XModLambdaN ((SyntheticCategory.biShift (1,1)).obj
        (model.nu.functor.obj (T.X.obj model.auxiliary))) (c+K) ≅
      (SyntheticCategory.biShift (1,1)).obj
        (XModLambdaN (model.nu.functor.obj (T.X.obj model.auxiliary)) (c+K)))
    (hε : XModLambdaN.incl _ (c+K) ≫ ε.hom =
      (SyntheticCategory.biShift (1,1)).map (XModLambdaN.incl _ (c+K)))
    (hNC1 : ∀ j : ℕ, 1≤j → j<K-1 →
      cycles model T.X ((K:ℤ)-j) (S+j,V+j) ≤
        boundaries model T.X ((c:ℤ)+j+1) (S+j,V+j))
    (hNC2 : ∀ x : Ambient model T.X (S+K-1,V+K-1),
      KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf (S+K-1) (V+K-1) x ∈
        boundaries model T.Y (c+K) (S+K-1+1,V+K-1+1))
    (x : Ambient model T.X (S,V))
    (a b : BiHom (V-S+1) (V-c+1)
      (XModLambdaN ((normalizedTriangle model T he).obj₁⟦(1:ℤ)⟧) (c+K)))
    (ha : Detects (model.convergence (.quotient (c+K) (.nu T.X)))
      (S,V,V-c) (finiteTargetLabel model T.X (c+K) S V c x)
      (rawMaySourceDesuspend T he hf (c+K) c S V ε a))
    (hb : Detects (model.convergence (.quotient (c+K) (.nu T.X)))
      (S,V,V-c) (finiteTargetLabel model T.X (c+K) S V c x)
      (rawMaySourceDesuspend T he hf (c+K) c S V ε b)) :
    a ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
      (normalizedTriangle model T he).mor₁) (c+K) =
    b ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
      (normalizedTriangle model T he).mor₁) (c+K) := by
  letI := model.exactness.shiftCommShift (0,1)
  letI := model.exactness.shiftExact (0,1)
  obtain ⟨εp,hεp,_⟩ := quotient_shift_exists model.quotients.coherence (0,1) (c+K)
    (model.nu.functor.obj (T.X.obj model.auxiliary))
  have hdiff := detects_sub_filtration
    (model.convergence (.quotient (c+K) (.nu T.X))) (S,V,V-c) ha hb
  rw [←raw_may_source_desuspend_sub] at hdiff
  have hz := pdf_conditions_native_annihilation T hf c K hK S V εp hεp hNC1 hNC2
    (rawMaySourceDesuspend T he hf (c+K) c S V ε (a-b)) hdiff
  have hraw := native_positive_image_zero_implies_raw_zero T he hf (c+K) c (by omega)
    S V ε εp hε hεp (a-b) hz
  exact sub_eq_zero.mp (by simpa only [Preadditive.sub_comp] using hraw)

/-- The actual May witness produced by the second classical differential
now gives the specified raw source the same signed target under NC1/NC2. -/
private theorem pdf_conditions_classical_second_image
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g +
      normalizedExponent model.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible model T he)
    (hf : normalizedExponent model.classicalTower T.f = 1)
    (hg : normalizedExponent model.classicalTower T.g = 0)
    (hh : normalizedExponent model.classicalTower T.h = 0)
    (c q : ℕ) (hq : 0<q) (S V : ℤ)
    (hNC1 : ∀ j : ℕ, 1≤j → j<(q+1)-1 →
      cycles model T.X (((q+1:ℕ):ℤ)-j) (S+j,V+j) ≤
        boundaries model T.X ((c:ℤ)+j+1) (S+j,V+j))
    (hNC2 : ∀ x : Ambient model T.X (S+(q+1:ℕ)-1,V+(q+1:ℕ)-1),
      KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf
        (S+(q+1:ℕ)-1) (V+(q+1:ℕ)-1) x ∈
        boundaries model T.Y (c+(q+1))
          (S+(q+1:ℕ)-1+1,V+(q+1:ℕ)-1+1))
    (u : Ambient model T.X (S,V)) (z : Ambient model T.Z (S,V+1))
    (v : Ambient model T.Y (S+q+1,(V+1)+q))
    (hu : (model.classicalSuspension T.X).DesuspendsClass S (V+1)
      ((model.classical.map T.h).pageMap 2 (S,V+1) z) (by simpa using u))
    (hdz : HasDifferential (model.classical.obj (T.Z.obj model.auxiliary))
      (q+1) (S,V+1) (S+q+1,(V+1)+q) z
      ((model.classical.map T.g).pageMap 2 (S+q+1,(V+1)+q) v))
    (ey : XModLambdaN ((normalizedTriangle model T he).obj₂⟦(1:ℤ)⟧) (q+1) ≅
      (XModLambdaN (normalizedTriangle model T he).obj₂ (q+1))⟦(1:ℤ)⟧)
    (hey : XModLambdaN.incl _ (q+1) ≫ ey.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ (q+1)))
    (ε : XModLambdaN ((SyntheticCategory.biShift (1,1)).obj
      (model.nu.functor.obj (T.X.obj model.auxiliary))) (c+(q+1)) ≅
      (SyntheticCategory.biShift (1,1)).obj
        (XModLambdaN (model.nu.functor.obj (T.X.obj model.auxiliary)) (c+(q+1))))
    (hε : XModLambdaN.incl _ (c+(q+1)) ≫ ε.hom =
      (SyntheticCategory.biShift (1,1)).map (XModLambdaN.incl _ (c+(q+1))))
    (d : BiHom (V-S+1) (V-c+1)
      (XModLambdaN ((normalizedTriangle model T he).obj₁⟦(1:ℤ)⟧) (c+(q+1))))
    (hd : Detects (model.convergence (.quotient (c+(q+1)) (.nu T.X)))
      (S,V,V-c) (finiteTargetLabel model T.X (c+(q+1)) S V c u)
      (rawMaySourceDesuspend T he hf (c+(q+1)) c S V ε d)) :
    let N := normalizedTriangle model T he
    let b := (biSuspensionHomEquiv ((V+1)-S) (V+1) (q:ℤ)
      (XModLambdaN (model.nu.functor.obj (T.Y.obj model.auxiliary)) 1)).symm
        (homotopyRegrade (show ((V+1)+q)-(S+q+1)=((V+1)-S)-1 by omega) rfl
          (nativeFirstLabel T.Y (S+q+1) ((V+1)+q) v))
    let ly : (SyntheticCategory.biShift (0,-(q:ℤ))).obj (XModLambdaN N.obj₂ 1) ⟶
        XModLambdaN N.obj₂ (q+1) := by
      simpa only [show q.succ-q=1 by omega] using
        ((model.quotients.tower N.obj₂).triangle hq (Nat.lt_succ_self q)).lambdaMap
    d ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map N.mor₁) (c+(q+1)) =
      homotopyRegrade (show (V+1)-S=V-S+1 by omega) (show (V+1)-c=V-c+1 by omega)
        (finiteCoefficientInsert (N.obj₂⟦(1:ℤ)⟧) c (q+1) (by omega) ((V+1)-S) (V+1)
          ((-(b ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map ly)) ≫ ey.inv)) := by
  dsimp only
  obtain ⟨a₀,ha₀,himage⟩ := classical_second_differential_may_at_level
    T he hT hf hg hh c q hq S (V+1) z v hdz ey hey
  let a := homotopyRegrade (show (V+1)-S=V-S+1 by omega)
    (show (V+1)-c=V-c+1 by omega) a₀
  have haSigma : Detects (model.convergence (.quotient (c+(q+1)) (.nu (.shift 1 T.X))))
      (S,V+1,V+1-c) (finiteTargetLabel model (.shift 1 T.X) (c+(q+1)) S (V+1) c
        ((model.classical.map T.h).pageMap 2 (S,V+1) z))
      (homotopyRegrade (by dsimp; omega) (by dsimp; omega)
        (a ≫ XModLambdaN.map (normalizedSuspensionNativeIso T he hf).hom (c+(q+1)))) := by
    simpa only [a,regrade_precomp,←Category.assoc,eqToHom_trans,eqToHom_refl,Category.id_comp] using ha₀
  have haX := raw_may_source_desuspend_detects T he hf (c+(q+1)) c (by omega)
    S V ε hε u _ hu a haSigma
  have hsame := pdf_conditions_same_x_label_raw_image T he hf c (q+1) (by omega)
    S V ε hε hNC1 hNC2 u d a hd haX
  refine hsame.trans ?_
  have hi := congrArg (homotopyRegrade (show (V+1)-S=V-S+1 by omega)
    (show (V+1)-c=V-c+1 by omega)) himage
  simpa only [a,regrade_comp] using hi

end
end KIP126.ProofTools.Internal.MahowaldLeibniz
