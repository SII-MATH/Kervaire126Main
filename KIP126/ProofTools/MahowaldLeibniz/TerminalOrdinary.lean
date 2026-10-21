module
import all KIP126.ProofTools.MahowaldLeibniz.TerminalSource
import all KIP126.ProofTools.MahowaldLeibniz.PositiveHBranch

/-! The actual ordinary-map terminal branch of finite Mahowald--Leibniz. -/
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

private def zeroNormalizedSourceIso (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ)+
      normalizedExponent model.classicalTower T.g+normalizedExponent model.classicalTower T.h=1)
    (hf : normalizedExponent model.classicalTower T.f=0) :
    (normalizedTriangle model T he).obj₁ ≅ model.nu.functor.obj (T.X.obj model.auxiliary) :=
  zero_positive_iso _ _ hf

private theorem zero_normalized_source_inv_arrow (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ)+
      normalizedExponent model.classicalTower T.g+normalizedExponent model.classicalTower T.h=1)
    (hf : normalizedExponent model.classicalTower T.f=0) :
    (zeroNormalizedSourceIso T he hf).inv ≫ (normalizedTriangle model T he).mor₁ =
      model.nu.functor.map T.f := by
  have h := normalized_zero_map T.X T.Y T.f hf
  change (zeroNormalizedSourceIso T he hf).inv ≫ (model.normalizedMap T.X T.Y T.f).map = _
  have h' : (model.normalizedMap T.X T.Y T.f).map =
      (zeroNormalizedSourceIso T he hf).hom ≫ model.nu.functor.map T.f := by
    simpa [zeroNormalizedSourceIso,zero_positive_iso,Category.assoc] using h
  rw [h',←Category.assoc,Iso.inv_hom_id,Category.id_comp]

private theorem zero_normalized_source_suspension (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ)+
      normalizedExponent model.classicalTower T.g+normalizedExponent model.classicalTower T.h=1)
    (hf : normalizedExponent model.classicalTower T.f=0) :
    (shiftFunctor SyntheticSpectrum (1:ℤ)).map (zeroNormalizedSourceIso T he hf).inv ≫
      (normalizedSuspensionZeroIso T he hf).hom =
      (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).inv.app
        (model.nu.functor.obj (T.X.obj model.auxiliary)) := by
  simp only [normalizedSuspensionZeroIso,Iso.trans_hom,Functor.mapIso_hom,zeroNormalizedSourceIso]
  rw [←Category.assoc,←Functor.map_comp,Iso.inv_hom_id]
  simp

private theorem native_suspended_first_boundary_full_projection
    (X : ClassicalObject) (N : ℕ) (hN : 0<N) (s t : ℤ)
    (ex : XModLambdaN ((model.nu.functor.obj (X.obj model.auxiliary))⟦(1:ℤ)⟧) N ≅
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) N)⟦(1:ℤ)⟧)
    (hex : XModLambdaN.incl _ N ≫ ex.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ N))
    (a : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) 1)) :
    suspendedFirstFiniteBoundary _ N hN (t-s) t ex a =
      ordinarySuspendedRepresentative _ (t-s) (t+(1:ℕ))
        (biSuspensionHomEquiv (t-s) t (1:ℕ)
          (model.nu.functor.obj (X.obj model.auxiliary))
          (a ≫ XModLambdaN.proj _ 1)) ≫ XModLambdaN.incl _ N := by
  dsimp only [suspendedFirstFiniteBoundary]
  change ordinarySuspendedRepresentative _ (t-s) (t+(1:ℕ))
    (finiteTowerBoundary X 1 N (by decide) hN s t a) ≫ ex.inv = _
  rw [finiteTowerBoundary_eq,ordinarySuspendedRepresentative_natural,←hex]
  simp only [Category.assoc,Iso.hom_inv_id,Category.comp_id]

private theorem ordinary_suspended_quotient_unshift
    (X : ClassicalObject) (N : ℕ) (m w : ℤ)
    (ε : XModLambdaN ((SyntheticCategory.biShift (1,0)).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) N ≅
      (SyntheticCategory.biShift (1,0)).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) N))
    (hε : XModLambdaN.incl _ N ≫ ε.hom =
      (SyntheticCategory.biShift (1,0)).map (XModLambdaN.incl _ N))
    (a : BiHom (m-1) w (model.nu.functor.obj (X.obj model.auxiliary))) :
    quotientUnshift X (1,0) (m-1,w) N ε
      (homotopyRegrade (by dsimp; omega) (by simp)
        (ordinarySuspendedRepresentative _ m w a ≫ XModLambdaN.incl _ N ≫
          XModLambdaN.map ((SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).inv.app _) N)) =
      a ≫ XModLambdaN.incl _ N := by
  rw [←XModLambdaN.incl_naturality
    ((SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).inv.app _) N]
  simp only [ordinarySuspendedRepresentative,Category.assoc,Iso.hom_inv_id_app_assoc,
    homotopyRegrade_comp,normalized_homotopy_regrade_trans]
  exact quotient_unshift_projected_shift X (1,0) (m-1,w) N ε hε a

private def ordinaryNormalizedFirstFiniteBoundary (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ)+
      normalizedExponent model.classicalTower T.g+normalizedExponent model.classicalTower T.h=1)
    (hf : normalizedExponent model.classicalTower T.f=0)
    (N : ℕ) (hN : 0<N) (s t : ℤ)
    (ex : XModLambdaN ((model.nu.functor.obj (T.X.obj model.auxiliary))⟦(1:ℤ)⟧) N ≅
      (XModLambdaN (model.nu.functor.obj (T.X.obj model.auxiliary)) N)⟦(1:ℤ)⟧)
    (x : Ambient model T.X (s,t)) :
    BiHom (t-s) (t+(1:ℕ))
      (XModLambdaN ((normalizedTriangle model T he).obj₁⟦(1:ℤ)⟧) N) :=
  suspendedFirstFiniteBoundary _ N hN (t-s) t ex (nativeFirstLabel T.X s t x) ≫
    XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
      (zeroNormalizedSourceIso T he hf).inv) N

private theorem ordinary_normalized_boundary_desuspend_eq
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ)+
      normalizedExponent model.classicalTower T.g+normalizedExponent model.classicalTower T.h=1)
    (hf : normalizedExponent model.classicalTower T.f=0)
    (N : ℕ) (hN : 0<N) (s t : ℤ)
    (ex : XModLambdaN ((model.nu.functor.obj (T.X.obj model.auxiliary))⟦(1:ℤ)⟧) N ≅
      (XModLambdaN (model.nu.functor.obj (T.X.obj model.auxiliary)) N)⟦(1:ℤ)⟧)
    (hex : XModLambdaN.incl _ N ≫ ex.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ N))
    (ε : XModLambdaN ((SyntheticCategory.biShift (1,0)).obj
        (model.nu.functor.obj (T.X.obj model.auxiliary))) N ≅
      (SyntheticCategory.biShift (1,0)).obj
        (XModLambdaN (model.nu.functor.obj (T.X.obj model.auxiliary)) N))
    (hε : XModLambdaN.incl _ N ≫ ε.hom =
      (SyntheticCategory.biShift (1,0)).map (XModLambdaN.incl _ N))
    (x : Ambient model T.X (s,t)) :
    quotientUnshift T.X (1,0) (t-s-1,t+(1:ℕ)) N ε
      (homotopyRegrade (by dsimp; omega) (by simp)
        (ordinaryNormalizedFirstFiniteBoundary T he hf N hN s t ex x ≫
          XModLambdaN.map (normalizedSuspensionZeroIso T he hf).hom N)) =
      finiteTowerBoundary T.X 1 N (by decide) hN s t (nativeFirstLabel T.X s t x) := by
  dsimp only [ordinaryNormalizedFirstFiniteBoundary]
  rw [Category.assoc,←model.quotients.functoriality.map_comp,
    zero_normalized_source_suspension,native_suspended_first_boundary_full_projection T.X N hN s t ex hex]
  rw [finiteTowerBoundary_eq]
  simpa only [Category.assoc] using ordinary_suspended_quotient_unshift T.X N (t-s) (t+(1:ℕ)) ε hε
    (biSuspensionHomEquiv (t-s) t (1:ℕ) (model.nu.functor.obj (T.X.obj model.auxiliary))
      (nativeFirstLabel T.X s t x ≫ XModLambdaN.proj _ 1))


private theorem ordinary_first_finite_boundary_source_detects
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ)+
      normalizedExponent model.classicalTower T.g+normalizedExponent model.classicalTower T.h=1)
    (hf : normalizedExponent model.classicalTower T.f=0)
    (k N c : ℕ) (hk : 0<k) (hN : 0<N) (hc : (c:ℤ)=k-1) (s t : ℤ)
    (x : Ambient model T.X (s,t)) (u : Ambient model T.X (s+k+1,t+k))
    (hdx : HasDifferential (model.classical.obj (T.X.obj model.auxiliary))
      (k+1) (s,t) (s+k+1,t+k) x u)
    (ex : XModLambdaN ((model.nu.functor.obj (T.X.obj model.auxiliary))⟦(1:ℤ)⟧) N ≅
      (XModLambdaN (model.nu.functor.obj (T.X.obj model.auxiliary)) N)⟦(1:ℤ)⟧)
    (hex : XModLambdaN.incl _ N ≫ ex.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ N))
    (ε : XModLambdaN ((SyntheticCategory.biShift (1,0)).obj
        (model.nu.functor.obj (T.X.obj model.auxiliary))) N ≅
      (SyntheticCategory.biShift (1,0)).obj
        (XModLambdaN (model.nu.functor.obj (T.X.obj model.auxiliary)) N))
    (hε : XModLambdaN.incl _ N ≫ ε.hom =
      (SyntheticCategory.biShift (1,0)).map (XModLambdaN.incl _ N)) :
    Detects (model.convergence (.quotient N (.nu T.X))) (s+k+1,t+k,t+k-c)
      (finiteTargetLabel model T.X N (s+k+1) (t+k) c u)
      (positiveHSourceDesuspend T he hf N c (s+k) (t+k) ε
        (homotopyRegrade (by omega) (by omega)
          (ordinaryNormalizedFirstFiniteBoundary T he hf N hN s t ex x))) := by
  have h := differential_detects_first_finite_boundary T.X k N hk hN s t x u hdx
  have ht := finite_projected_weight_label_detects T.X N c (s+k+1) (t+k) (t+(1:ℕ))
    (by omega) (by omega) u _ h
  have heq := ordinary_normalized_boundary_desuspend_eq T he hf N hN s t ex hex ε hε x
  rw [←heq] at ht
  have hr := quotient_unshift_regrade T.X (1,0) (t-s-1,t+(1:ℕ))
    ((t+k)-((s+k)+1),t+k-c) N ε (by dsimp; omega) (by dsimp; omega)
    (homotopyRegrade (by dsimp; omega) (by simp)
      (ordinaryNormalizedFirstFiniteBoundary T he hf N hN s t ex x ≫
        XModLambdaN.map (normalizedSuspensionZeroIso T he hf).hom N))
  dsimp only [positiveHSourceDesuspend]
  simp only [homotopyRegrade_comp,normalized_homotopy_regrade_trans] at hr ht ⊢
  rw [hr]
  exact ht


private theorem native_suspended_first_boundary_natural
    (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (N : ℕ) (hN : 0<N) (s t : ℤ)
    (ex : XModLambdaN ((model.nu.functor.obj (X.obj model.auxiliary))⟦(1:ℤ)⟧) N ≅
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) N)⟦(1:ℤ)⟧)
    (ey : XModLambdaN ((model.nu.functor.obj (Y.obj model.auxiliary))⟦(1:ℤ)⟧) N ≅
      (XModLambdaN (model.nu.functor.obj (Y.obj model.auxiliary)) N)⟦(1:ℤ)⟧)
    (hex : XModLambdaN.incl _ N ≫ ex.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ N))
    (hey : XModLambdaN.incl _ N ≫ ey.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ N))
    (a : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) 1)) :
    suspendedFirstFiniteBoundary _ N hN (t-s) t ex a ≫
      XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map (model.nu.functor.map f)) N ≫
        ey.hom =
      ordinarySuspendedRepresentative _ (t-s) (t+(1:ℕ))
        (firstFiniteBoundaryRepresentative _ N hN (t-s) t
          (a ≫ XModLambdaN.map (model.nu.functor.map f) 1)) := by
  rw [native_suspended_first_boundary_full_projection X N hN s t ex hex,
    firstFiniteBoundaryRepresentative_natural]
  change _ = ordinarySuspendedRepresentative _ (t-s) (t+(1:ℕ))
    (finiteTowerBoundary X 1 N (by decide) hN s t a ≫
      XModLambdaN.map (model.nu.functor.map f) N)
  rw [finiteTowerBoundary_eq,ordinarySuspendedRepresentative_natural,
    ordinarySuspendedRepresentative_natural]
  simp only [Category.assoc]
  rw [←Category.assoc (XModLambdaN.incl _ N)
    (XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map (model.nu.functor.map f)) N) ey.hom,
    ←XModLambdaN.incl_naturality
      ((shiftFunctor SyntheticSpectrum (1:ℤ)).map (model.nu.functor.map f)) N]
  simp only [Category.assoc]
  rw [hey]
  have hn := congrArg ((shiftFunctor SyntheticSpectrum (1:ℤ)).map)
    (XModLambdaN.incl_naturality (model.nu.functor.map f) N)
  simp only [Functor.map_comp] at hn
  rw [hn]

private theorem ordinary_normalized_boundary_image_square
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ)+
      normalizedExponent model.classicalTower T.g+normalizedExponent model.classicalTower T.h=1)
    (hf : normalizedExponent model.classicalTower T.f=0)
    (N : ℕ) (hN : 0<N) (s t : ℤ)
    (ex : XModLambdaN ((model.nu.functor.obj (T.X.obj model.auxiliary))⟦(1:ℤ)⟧) N ≅
      (XModLambdaN (model.nu.functor.obj (T.X.obj model.auxiliary)) N)⟦(1:ℤ)⟧)
    (ey : XModLambdaN ((model.nu.functor.obj (T.Y.obj model.auxiliary))⟦(1:ℤ)⟧) N ≅
      (XModLambdaN (model.nu.functor.obj (T.Y.obj model.auxiliary)) N)⟦(1:ℤ)⟧)
    (hex : XModLambdaN.incl _ N ≫ ex.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ N))
    (hey : XModLambdaN.incl _ N ≫ ey.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ N))
    (x : Ambient model T.X (s,t)) :
    ordinaryNormalizedFirstFiniteBoundary T he hf N hN s t ex x ≫
      XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
        (normalizedTriangle model T he).mor₁) N ≫ ey.hom =
      ordinarySuspendedRepresentative _ (t-s) (t+(1:ℕ))
        (finiteTowerBoundary T.Y 1 N (by decide) hN s t
          (nativeFirstLabel T.Y s t ((model.classical.map T.f).pageMap 2 (s,t) x))) := by
  have hm := congrArg (fun z => XModLambdaN.map
      ((shiftFunctor SyntheticSpectrum (1:ℤ)).map z) N)
    (zero_normalized_source_inv_arrow T he hf)
  simp only [Functor.map_comp,model.quotients.functoriality.map_comp] at hm
  dsimp only [ordinaryNormalizedFirstFiniteBoundary]
  dsimp only [normalizedTriangle,Triangle.mk] at hm ⊢
  simp only [Category.assoc]
  rw [←Category.assoc (XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
      (zeroNormalizedSourceIso T he hf).inv) N)
      (XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
      (model.normalizedMap T.X T.Y T.f).map) N) ey.hom,hm]

  have h := native_suspended_first_boundary_natural T.X T.Y T.f N hN s t
    ex ey hex hey (nativeFirstLabel T.X s t x)
  rw [native_first_label_natural] at h
  exact h

private theorem ordinary_suspended_representative_injective_terminal
    (A : SyntheticSpectrum) (m w : ℤ) :
    Function.Injective (ordinarySuspendedRepresentative A m w) := by
  intro a b h
  have h₀ := (cancel_mono
    ((SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).hom.app A)).mp h
  have h₁ := homotopy_regrade_injective
    (show ((m-1,w)+(1,0)).1=m by dsimp; omega)
    (show ((m-1,w)+(1,0)).2=w by simp) h₀
  apply (SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) (1,0)).map_injective
  exact (cancel_epi ((SyntheticCategory.biShift_comp (m-1,w) (1,0)).inv.app S_0_0)).mp h₁

private theorem ordinary_normalized_boundary_image_decode
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ)+
      normalizedExponent model.classicalTower T.g+normalizedExponent model.classicalTower T.h=1)
    (hf : normalizedExponent model.classicalTower T.f=0)
    (p : ℕ) (hp : 0<p) (s t : ℤ)
    (x : Ambient model T.X (s,t)) (v : Ambient model T.Y (s+p+1,t+p))
    (ex : XModLambdaN ((model.nu.functor.obj (T.X.obj model.auxiliary))⟦(1:ℤ)⟧) p ≅
      (XModLambdaN (model.nu.functor.obj (T.X.obj model.auxiliary)) p)⟦(1:ℤ)⟧)
    (ey : XModLambdaN ((model.nu.functor.obj (T.Y.obj model.auxiliary))⟦(1:ℤ)⟧) p ≅
      (XModLambdaN (model.nu.functor.obj (T.Y.obj model.auxiliary)) p)⟦(1:ℤ)⟧)
    (hex : XModLambdaN.incl _ p ≫ ex.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ p))
    (hey : XModLambdaN.incl _ p ≫ ey.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ p))
    (b : BiHom (t-s-1) (t+(1:ℕ))
      (XModLambdaN (model.nu.functor.obj (T.Y.obj model.auxiliary)) p))
    (hb : Detects (model.convergence (.quotient p (.nu T.Y))) (s+p+1,t+p,t+(1:ℕ))
      ((model.family.quotientProjection (model.nu.functor.obj (T.Y.obj model.auxiliary)) p).pageMap
        2 (s+p+1,t+p,t+(1:ℕ))
        (nuWeightLabel model T.Y (s+p+1) (t+p) (t+(1:ℕ)) (by omega) v))
      (homotopyRegrade (by dsimp; omega) rfl b))
    (himage : ordinaryNormalizedFirstFiniteBoundary T he hf p hp s t ex x ≫
      XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
        (normalizedTriangle model T he).mor₁) p ≫ ey.hom =
      ordinarySuspendedRepresentative _ (t-s) (t+(1:ℕ)) b) :
    let y := (model.classical.map T.f).pageMap 2 (s,t) x
    IsCycle model T.Y p (s,t) y ∧ DifferentialAt model T.Y (p+1)
      (s,t) (s+p+1,t+p) y v := by
  have hs := ordinary_normalized_boundary_image_square T he hf p hp s t ex ey hex hey x
  have heq := ordinary_suspended_representative_injective_terminal _ (t-s) (t+(1:ℕ))
    (hs.symm.trans himage)
  have hb' := hb
  rw [←heq] at hb'
  obtain ⟨hy,hd⟩ := finite_bockstein_terminal_decode T.Y p hp s t
    ((model.classical.map T.f).pageMap 2 (s,t) x) v _ hb' rfl
  exact ⟨hy,by exact ⟨by omega,hd⟩⟩

end
end KIP126.ProofTools.Internal.MahowaldLeibniz
