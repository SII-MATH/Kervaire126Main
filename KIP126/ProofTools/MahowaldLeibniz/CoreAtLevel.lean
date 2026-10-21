module

import all KIP126.ProofTools.MahowaldLeibniz.FixedModel
import all KIP126.ProofTools.MahowaldLeibniz.CoefficientShift

/-! Fixed-model finite-level Mahowald--Leibniz comparison.  The source
comparison here is expressed on Q_N νΣX, so its classical h₂ label is the
one produced by the actual finite May construction. -/

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

/-- The complete finite-layer surjectivity premise kills the actual source
ambiguity, expressed in the native νΣX coordinates. -/
private theorem finite_layer_surj_native_annihilation
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g +
      normalizedExponent model.classicalTower T.h = 1)
    (hf : normalizedExponent model.classicalTower T.f = 1)
    (hg : normalizedExponent model.classicalTower T.g = 0)
    (hh : normalizedExponent model.classicalTower T.h = 0)
    (hT : NormalizedTriangleCompatible model T he)
    (c K : ℕ) (hK : 2≤K) (S V : ℤ)
    (hsurj : KIP126.ProofTools.Standard.MahowaldLeibnizFiniteLayerSurjectivity
      T (c+2) K (S-(c+2:ℕ)) (V-(c+2:ℕ)+1))
    (a : BiHom (V-S+1) (V-c+1)
      (XModLambdaN ((normalizedTriangle model T he).obj₁⟦(1:ℤ)⟧) (c+K)))
    (ha : FiltrationAtLeast model.syntheticTower (S+1)
      (a ≫ XModLambdaN.map (normalizedSuspensionNativeIso T he hf).hom (c+K))) :
    a ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
      (normalizedTriangle model T he).mor₁) (c+K) = 0 := by
  let N := normalizedTriangle model T he
  let E := normalizedSuspensionNativeIso T he hf
  let EZ := normalizedThirdZeroIso T he hg
  obtain ⟨b,_,hb⟩ := finite_layer_surj_ordinary_h_filtered T c K hK S V hsurj
    (a ≫ XModLambdaN.map E.hom (c+K)) ha
  have hcomm : XModLambdaN.map N.mor₃ (c+K) ≫ XModLambdaN.map E.hom (c+K) =
      XModLambdaN.map EZ.hom (c+K) ≫
        XModLambdaN.map (model.nu.functor.map T.h) (c+K) := by
    rw [←model.quotients.functoriality.map_comp,←model.quotients.functoriality.map_comp]
    exact congrArg (fun f => XModLambdaN.map f (c+K))
      (normalized_third_arrow_zero T he hf hg hh)
  have haq : (b ≫ XModLambdaN.map EZ.inv (c+K)) ≫
      XModLambdaN.map N.mor₃ (c+K) = a := by
    let eQ := (model.quotients.functoriality.functor (c+K)).mapIso E
    apply (cancel_mono eQ.hom).mp
    change _ ≫ XModLambdaN.map E.hom (c+K) = _
    rw [Category.assoc,Category.assoc,hcomm]
    rw [←Category.assoc (XModLambdaN.map EZ.inv (c+K)),
      ←model.quotients.functoriality.map_comp,Iso.inv_hom_id,
      model.quotients.functoriality.map_id,Category.id_comp]
    exact hb
  obtain ⟨ey,_,hrow⟩ := KIP126.Literature.Standard.normalized_finite_quotient_horizontal_row
    T he hT (c+K) (by omega)
  have hzero := comp_distTriang_mor_zero₂₃ _ hrow
  change XModLambdaN.map N.mor₃ (c+K) ≫
    (-(XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map N.mor₁) (c+K) ≫
      ey.hom))=0 at hzero
  rw [Preadditive.comp_neg,neg_eq_zero] at hzero
  have hzero' : XModLambdaN.map N.mor₃ (c+K) ≫
      XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map N.mor₁) (c+K)=0 := by
    apply (cancel_mono ey.hom).mp
    simpa only [Category.assoc,zero_comp] using hzero
  rw [←haq,Category.assoc,hzero',comp_zero]

/-- Two specified actual representatives of the same finite level label
have exactly equal normalized f-images under the original full finite-layer
condition, including its final visible layer. -/
private theorem finite_layer_surj_same_source_image
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g +
      normalizedExponent model.classicalTower T.h = 1)
    (hf : normalizedExponent model.classicalTower T.f = 1)
    (hg : normalizedExponent model.classicalTower T.g = 0)
    (hh : normalizedExponent model.classicalTower T.h = 0)
    (hT : NormalizedTriangleCompatible model T he)
    (c K : ℕ) (hK : 2≤K) (S V : ℤ)
    (hsurj : KIP126.ProofTools.Standard.MahowaldLeibnizFiniteLayerSurjectivity
      T (c+2) K (S-(c+2:ℕ)) (V-(c+2:ℕ)+1))
    (u : Ambient model (.shift 1 T.X) (S,V+1))
    (a b : BiHom (V-S+1) (V-c+1)
      (XModLambdaN ((normalizedTriangle model T he).obj₁⟦(1:ℤ)⟧) (c+K)))
    (ha : Detects (model.convergence (.quotient (c+K) (.nu (.shift 1 T.X))))
      (S,V+1,V+1-c) (finiteTargetLabel model (.shift 1 T.X) (c+K) S (V+1) c u)
      (homotopyRegrade (by dsimp; omega) (by dsimp; omega)
        (a ≫ XModLambdaN.map (normalizedSuspensionNativeIso T he hf).hom (c+K))))
    (hb : Detects (model.convergence (.quotient (c+K) (.nu (.shift 1 T.X))))
      (S,V+1,V+1-c) (finiteTargetLabel model (.shift 1 T.X) (c+K) S (V+1) c u)
      (homotopyRegrade (by dsimp; omega) (by dsimp; omega)
        (b ≫ XModLambdaN.map (normalizedSuspensionNativeIso T he hf).hom (c+K)))) :
    a ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
      (normalizedTriangle model T he).mor₁) (c+K) =
    b ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
      (normalizedTriangle model T he).mor₁) (c+K) := by
  have hdiff := detects_sub_filtration
    (model.convergence (.quotient (c+K) (.nu (.shift 1 T.X)))) (S,V+1,V+1-c) ha hb
  have hfil : FiltrationAtLeast model.syntheticTower (S+1)
      ((a-b) ≫ XModLambdaN.map (normalizedSuspensionNativeIso T he hf).hom (c+K)) := by
    apply (regrade_filtration_iff (show V-S+1=(V+1)-S by omega)
      (show V-c+1=V+1-c by omega) (S+1) _).mp
    simpa only [Preadditive.sub_comp,regrade_precomp,Preadditive.comp_sub] using hdiff
  have hz := finite_layer_surj_native_annihilation T he hf hg hh hT c K hK S V hsurj
    (a-b) hfil
  exact sub_eq_zero.mp (by simpa only [Preadditive.sub_comp] using hz)

private def finiteCoefficientInsert (A : SyntheticSpectrum)
    (c K : ℕ) (hK : 0<K) (m w : ℤ)
    (a : BiHom m w (XModLambdaN A K)) :
    BiHom m (w-c) (XModLambdaN A (c+K)) :=
  finiteCoefficientShiftClass A (c+K) c (by omega) m w
    (by simpa only [Nat.add_sub_cancel_left,SyntheticObject.obj] using a)

private theorem finite_coefficient_insert_natural {A B : SyntheticSpectrum}
    (f : A ⟶ B) (c K : ℕ) (hK : 0<K) (m w : ℤ)
    (a : BiHom m w (XModLambdaN A K)) :
    finiteCoefficientInsert A c K hK m w a ≫ XModLambdaN.map f (c+K) =
      finiteCoefficientInsert B c K hK m w (a ≫ XModLambdaN.map f K) := by
  unfold finiteCoefficientInsert
  rw [finite_coefficient_shift_natural]
  congr 1
  have transport (n : ℕ) (hn : n=K)
      (hnA : BiHom m w (XModLambdaN A K)=BiHom m w (XModLambdaN A n))
      (hnB : BiHom m w (XModLambdaN B K)=BiHom m w (XModLambdaN B n)) :
      hnA.mp a ≫ XModLambdaN.map f n = hnB.mp (a ≫ XModLambdaN.map f K) := by
    subst n
    rfl
  exact transport (c+K-c) (by omega) _ _

private theorem finite_coefficient_insert_detects
    (X : ClassicalObject) (c K : ℕ) (hK : 0<K) (s t : ℤ)
    (x : Ambient model X (s,t))
    (a : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) K))
    (ha : Detects (model.convergence (.quotient K (.nu X))) (s,t,t)
      (regradeE2 (by simp) (finiteTargetLabel model X K s t 0 x)) a) :
    Detects (model.convergence (.quotient (c+K) (.nu X))) (s,t,t-c)
      (finiteTargetLabel model X (c+K) s t c x)
      (finiteCoefficientInsert _ c K hK (t-s) t a) := by
  have ha' : Detects (model.convergence (.quotient (c+K-c) (.nu X))) (s,t,t)
      ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) (c+K-c)).pageMap
        2 (s,t,t) (nuWeightLabel model X s t t (by omega) x))
      (by simpa only [Nat.add_sub_cancel_left,SyntheticObject.obj] using a) := by
    have transport (n : ℕ) (hn : n=K)
        (ht : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) K) =
          BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) n)) :
        Detects (model.convergence (.quotient n (.nu X))) (s,t,t)
          ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) n).pageMap
            2 (s,t,t) (nuWeightLabel model X s t t (by omega) x)) (ht.mp a) := by
      subst n
      rw [zero_weight_label]
      exact ha
    exact transport (c+K-c) (by omega) _
  have h := finite_coefficient_shift_detects X (c+K) c (by omega) s t t (by omega) x _ ha'
  rw [finite_coefficient_weight_label] at h
  exact h


/-- Classical second-input producer at every finite level.  The exact
same coefficient insertion is applied to the May class and its signed
image, and the specified h₂z label is retained. -/
private theorem classical_second_differential_may_at_level
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g +
      normalizedExponent model.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible model T he)
    (hf : normalizedExponent model.classicalTower T.f = 1)
    (hg : normalizedExponent model.classicalTower T.g = 0)
    (hh : normalizedExponent model.classicalTower T.h = 0)
    (c q : ℕ) (hq : 0<q) (s t : ℤ)
    (z : Ambient model T.Z (s,t)) (v : Ambient model T.Y (s+q+1,t+q))
    (hd : HasDifferential (model.classical.obj (T.Z.obj model.auxiliary))
      (q+1) (s,t) (s+q+1,t+q) z
      ((model.classical.map T.g).pageMap 2 (s+q+1,t+q) v))
    (ey : XModLambdaN ((normalizedTriangle model T he).obj₂⟦(1:ℤ)⟧) (q+1) ≅
      (XModLambdaN (normalizedTriangle model T he).obj₂ (q+1))⟦(1:ℤ)⟧)
    (hey : XModLambdaN.incl _ (q+1) ≫ ey.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ (q+1))) :
    let V := normalizedTriangle model T he
    let b := (biSuspensionHomEquiv (t-s) t (q:ℤ)
      (XModLambdaN (model.nu.functor.obj (T.Y.obj model.auxiliary)) 1)).symm
        (homotopyRegrade (show (t+q)-(s+q+1)=(t-s)-1 by omega) rfl
          (nativeFirstLabel T.Y (s+q+1) (t+q) v))
    let ly : (SyntheticCategory.biShift (0,-(q:ℤ))).obj (XModLambdaN V.obj₂ 1) ⟶
        XModLambdaN V.obj₂ (q+1) := by
      simpa only [show q.succ-q=1 by omega] using
        ((model.quotients.tower V.obj₂).triangle hq (Nat.lt_succ_self q)).lambdaMap
    ∃ a : BiHom (t-s) (t-c) (XModLambdaN (V.obj₁⟦(1:ℤ)⟧) (c+(q+1))),
      Detects (model.convergence (.quotient (c+(q+1)) (.nu (.shift 1 T.X))))
        (s,t,t-c) (finiteTargetLabel model (.shift 1 T.X) (c+(q+1)) s t c
          ((model.classical.map T.h).pageMap 2 (s,t) z))
        (a ≫ XModLambdaN.map (normalizedSuspensionNativeIso T he hf).hom (c+(q+1))) ∧
      a ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map V.mor₁) (c+(q+1)) =
        finiteCoefficientInsert (V.obj₂⟦(1:ℤ)⟧) c (q+1) (by omega) (t-s) t
          ((-(b ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map ly)) ≫ ey.inv) := by
  dsimp only
  let V := normalizedTriangle model T he
  obtain ⟨a₀,m₀,ha₀,_,hm₀,hf₀⟩ := classical_second_differential_may T he hT hg q hq s t z v hd ey hey
  have hs := (finite_may_source_detects T he hf hg hh q (q+1) hq (by omega) s t z a₀ m₀ ha₀ hm₀).1
  let m := finiteCoefficientInsert (V.obj₁⟦(1:ℤ)⟧) c (q+1) (by omega) (t-s) t m₀
  refine ⟨m,?_,?_⟩
  · dsimp only [m]
    rw [finite_coefficient_insert_natural]
    exact finite_coefficient_insert_detects (.shift 1 T.X) c (q+1) (by omega) s t
      ((model.classical.map T.h).pageMap 2 (s,t) z)
      (m₀ ≫ XModLambdaN.map (normalizedSuspensionNativeIso T he hf).hom (q+1)) hs
  · dsimp only [m]
    rw [finite_coefficient_insert_natural]
    congr 1
    apply (cancel_mono ey.hom).mp
    simpa only [Category.assoc,Iso.inv_hom_id,Category.comp_id] using hf₀

private theorem shift_class_preserves_filtration
    (X : SyntheticObject) (δ p : ℤ×ℤ) (s : ℤ)
    (a : BiHom p.1 p.2 (X.obj model.nu model.auxiliary))
    (ha : FiltrationAtLeast model.syntheticTower s a) :
    FiltrationAtLeast model.syntheticTower s (shiftHomotopyClass δ p a) := by
  let E := (essShift δ).filtered X p
  obtain ⟨b,hb⟩ := filtration_representative_exists model.syntheticTower _ p s a ha
  have hc := ConcreteCategory.congr_hom (E.level_arrow s) b
  change ((model.syntheticTower.filtration _).F s (p+δ)).arrow ((E.level s).hom b) =
    E.ambient.hom (((model.syntheticTower.filtration _).F s p).arrow b) at hc
  erw [hb,(essShift δ).ambient_eq] at hc
  have hm : shiftHomotopyClass δ p a ∈ ModuleCat.subobjectModule _
      ((model.syntheticTower.filtration _).F s (p+δ)) := ⟨(E.level s).hom b,hc⟩
  simpa only [SyntheticTowerPresentation.filtration,OrderIso.apply_symm_apply,
    FiltrationAtLeast] using hm

private theorem quotient_unshift_reflects_filtration
    (X : ClassicalObject) (δ p : ℤ×ℤ) (N : ℕ)
    (ε : XModLambdaN ((SyntheticCategory.biShift δ).obj
      (model.nu.functor.obj (X.obj model.auxiliary))) N ≅
      (SyntheticCategory.biShift δ).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) N))
    (s : ℤ)
    (a : BiHom (p+δ).1 (p+δ).2
      (XModLambdaN ((SyntheticCategory.biShift δ).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) N))
    (ha : FiltrationAtLeast model.syntheticTower s (quotientUnshift X δ p N ε a)) :
    FiltrationAtLeast model.syntheticTower s a := by
  have hs := shift_class_preserves_filtration (.quotient N (.nu X)) δ p s _ ha
  have hm := map_preserves_filtration
    (model.convergentMap (.shift δ (.quotient N (.nu X)))
      (.quotient N (.shift δ (.nu X))) ε.inv) (p+δ) s _ hs
  rw [shift_quotient_unshift] at hm
  exact hm

private def rawMaySourceDesuspend
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g +
      normalizedExponent model.classicalTower T.h = 1)
    (hf : normalizedExponent model.classicalTower T.f = 1)
    (N c : ℕ) (S V : ℤ)
    (ε : XModLambdaN ((SyntheticCategory.biShift (1,1)).obj
      (model.nu.functor.obj (T.X.obj model.auxiliary))) N ≅
      (SyntheticCategory.biShift (1,1)).obj
        (XModLambdaN (model.nu.functor.obj (T.X.obj model.auxiliary)) N))
    (a : BiHom (V-S+1) (V-c+1)
      (XModLambdaN ((normalizedTriangle model T he).obj₁⟦(1:ℤ)⟧) N)) :
    BiHom (V-S) (V-c) (XModLambdaN (model.nu.functor.obj (T.X.obj model.auxiliary)) N) :=
  quotientUnshift T.X (1,1) (V-S,V-c) N ε
    (homotopyRegrade rfl rfl
      (a ≫ XModLambdaN.map (normalizedSuspensionNativeIso T he hf).hom N ≫
        XModLambdaN.map (model.nu.suspensionIso (T.X.obj model.auxiliary)).hom N))

private theorem raw_may_source_desuspend_sub
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g +
      normalizedExponent model.classicalTower T.h = 1)
    (hf : normalizedExponent model.classicalTower T.f = 1)
    (N c : ℕ) (S V : ℤ)
    (ε : XModLambdaN ((SyntheticCategory.biShift (1,1)).obj
      (model.nu.functor.obj (T.X.obj model.auxiliary))) N ≅
      (SyntheticCategory.biShift (1,1)).obj
        (XModLambdaN (model.nu.functor.obj (T.X.obj model.auxiliary)) N))
    (a b : BiHom (V-S+1) (V-c+1)
      (XModLambdaN ((normalizedTriangle model T he).obj₁⟦(1:ℤ)⟧) N)) :
    rawMaySourceDesuspend T he hf N c S V ε (a-b) =
      rawMaySourceDesuspend T he hf N c S V ε a -
        rawMaySourceDesuspend T he hf N c S V ε b := by
  simp only [rawMaySourceDesuspend,Preadditive.sub_comp,homotopy_regrade_sub,quotient_unshift_sub]

private theorem raw_may_source_desuspend_reflects_filtration
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g +
      normalizedExponent model.classicalTower T.h = 1)
    (hf : normalizedExponent model.classicalTower T.f = 1)
    (N c : ℕ) (S V j : ℤ)
    (ε : XModLambdaN ((SyntheticCategory.biShift (1,1)).obj
      (model.nu.functor.obj (T.X.obj model.auxiliary))) N ≅
      (SyntheticCategory.biShift (1,1)).obj
        (XModLambdaN (model.nu.functor.obj (T.X.obj model.auxiliary)) N))
    (a : BiHom (V-S+1) (V-c+1)
      (XModLambdaN ((normalizedTriangle model T he).obj₁⟦(1:ℤ)⟧) N))
    (ha : FiltrationAtLeast model.syntheticTower j
      (rawMaySourceDesuspend T he hf N c S V ε a)) :
    FiltrationAtLeast model.syntheticTower j
      (a ≫ XModLambdaN.map (normalizedSuspensionNativeIso T he hf).hom N) := by
  have h := quotient_unshift_reflects_filtration T.X (1,1) (V-S,V-c) N ε j _ ha
  have h' : FiltrationAtLeast model.syntheticTower j
      (a ≫ XModLambdaN.map (normalizedSuspensionNativeIso T he hf).hom N ≫
        XModLambdaN.map (model.nu.suspensionIso (T.X.obj model.auxiliary)).hom N) := by
    exact (regrade_filtration_iff rfl rfl j _).mp h
  have hm := map_preserves_filtration
    (model.convergentMap (.quotient N (.shift (1,1) (.nu T.X)))
      (.quotient N (.nu (.shift 1 T.X)))
      (XModLambdaN.map (model.nu.suspensionIso (T.X.obj model.auxiliary)).inv N))
    (V-S+1,V-c+1) j _ h'
  simpa only [Category.assoc,←model.quotients.functoriality.map_comp,Iso.hom_inv_id,
    model.quotients.functoriality.map_id,Category.comp_id,SyntheticObject.obj,FiltrationAtLeast] using hm


/-- The two fixed raw representatives can be compared in the classical X
coordinates used by the first Bockstein boundary. -/
private theorem finite_layer_surj_same_x_label_image
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g +
      normalizedExponent model.classicalTower T.h = 1)
    (hf : normalizedExponent model.classicalTower T.f = 1)
    (hg : normalizedExponent model.classicalTower T.g = 0)
    (hh : normalizedExponent model.classicalTower T.h = 0)
    (hT : NormalizedTriangleCompatible model T he)
    (c K : ℕ) (hK : 2≤K) (S V : ℤ)
    (hsurj : KIP126.ProofTools.Standard.MahowaldLeibnizFiniteLayerSurjectivity
      T (c+2) K (S-(c+2:ℕ)) (V-(c+2:ℕ)+1))
    (ε : XModLambdaN ((SyntheticCategory.biShift (1,1)).obj
      (model.nu.functor.obj (T.X.obj model.auxiliary))) (c+K) ≅
      (SyntheticCategory.biShift (1,1)).obj
        (XModLambdaN (model.nu.functor.obj (T.X.obj model.auxiliary)) (c+K)))
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
  have hdiff := detects_sub_filtration
    (model.convergence (.quotient (c+K) (.nu T.X))) (S,V,V-c) ha hb
  rw [←raw_may_source_desuspend_sub] at hdiff
  have hfil := raw_may_source_desuspend_reflects_filtration T he hf (c+K) c S V (S+1) ε (a-b) hdiff
  have hz := finite_layer_surj_native_annihilation T he hf hg hh hT c K hK S V hsurj (a-b) hfil
  exact sub_eq_zero.mp (by simpa only [Preadditive.sub_comp] using hz)

/-- The May producer's actual νΣX label descends to the same X label as
used by the first differential, for the chosen quotient comparison. -/
private theorem raw_may_source_desuspend_detects
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g +
      normalizedExponent model.classicalTower T.h = 1)
    (hf : normalizedExponent model.classicalTower T.f = 1)
    (N c : ℕ) (hcN : c<N) (S V : ℤ)
    (ε : XModLambdaN ((SyntheticCategory.biShift (1,1)).obj
      (model.nu.functor.obj (T.X.obj model.auxiliary))) N ≅
      (SyntheticCategory.biShift (1,1)).obj
        (XModLambdaN (model.nu.functor.obj (T.X.obj model.auxiliary)) N))
    (hε : XModLambdaN.incl _ N ≫ ε.hom =
      (SyntheticCategory.biShift (1,1)).map (XModLambdaN.incl _ N))
    (x : Ambient model T.X (S,V)) (sx : Ambient model (.shift 1 T.X) (S,V+1))
    (hsx : (model.classicalSuspension T.X).DesuspendsClass S (V+1) sx (by simpa using x))
    (a : BiHom (V-S+1) (V-c+1)
      (XModLambdaN ((normalizedTriangle model T he).obj₁⟦(1:ℤ)⟧) N))
    (ha : Detects (model.convergence (.quotient N (.nu (.shift 1 T.X))))
      (S,V+1,V+1-c) (finiteTargetLabel model (.shift 1 T.X) N S (V+1) c sx)
      (homotopyRegrade (by dsimp; omega) (by dsimp; omega)
        (a ≫ XModLambdaN.map (normalizedSuspensionNativeIso T he hf).hom N))) :
    Detects (model.convergence (.quotient N (.nu T.X)))
      (S,V,V-c) (finiteTargetLabel model T.X N S V c x)
      (rawMaySourceDesuspend T he hf N c S V ε a) := by
  have h := suspension_finite_detects T.X N c hcN S V x sx ε hε hsx _ ha
  simpa only [rawMaySourceDesuspend,regrade_comp,regrade_precomp,
    ←Category.assoc,eqToHom_trans] using h

/-- The classical second input and the complete surjectivity condition
force the prescribed first-input representative to have the exact signed
finite May image.  All source labels are compared in the same X coordinates. -/
private theorem finite_layer_surj_classical_second_image
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g +
      normalizedExponent model.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible model T he)
    (hf : normalizedExponent model.classicalTower T.f = 1)
    (hg : normalizedExponent model.classicalTower T.g = 0)
    (hh : normalizedExponent model.classicalTower T.h = 0)
    (c q : ℕ) (hq : 0<q) (S V : ℤ)
    (hsurj : KIP126.ProofTools.Standard.MahowaldLeibnizFiniteLayerSurjectivity
      T (c+2) (q+1) (S-(c+2:ℕ)) (V-(c+2:ℕ)+1))
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
  have hsame := finite_layer_surj_same_x_label_image T he hf hg hh hT c (q+1) (by omega)
    S V hsurj ε u d a hd haX
  refine hsame.trans ?_
  have hi := congrArg (homotopyRegrade (show (V+1)-S=V-S+1 by omega)
    (show (V+1)-c=V-c+1 by omega)) himage
  simpa only [a,regrade_comp] using hi


end
end KIP126.ProofTools.Internal.MahowaldLeibniz
