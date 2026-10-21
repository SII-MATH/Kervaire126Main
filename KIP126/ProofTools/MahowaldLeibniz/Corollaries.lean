module

import all KIP126.ProofTools.MahowaldLeibniz.FixedModel
import all KIP126.ProofTools.MahowaldLeibniz.PositiveFirstCore
import all KIP126.ProofTools.MahowaldLeibniz.CoreAtLevel
import all KIP126.ProofTools.MahowaldLeibniz.MayTarget
import all KIP126.ProofTools.MahowaldLeibniz.TerminalSource
import all KIP126.ProofTools.MahowaldLeibniz.NativeImageSquare
import all KIP126.ProofTools.GeneralizedMahowald.CommonEdgeLabels
import all KIP126.ProofTools.MahowaldLeibniz.TerminalSquare
import all KIP126.ProofTools.GeneralizedMahowald.Signs

/-! Assembly of the classical Mahowald--Leibniz consequences. All
intermediate declarations retain the chosen finite boundary and the chosen
classical label. No new public interface or background assumption is added.
-/

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
set_option maxHeartbeats 2000000

/-- Only the chosen first-quotient representative has exponent two here;
there is no exponent-two assertion about the full finite homotopy group. -/
private theorem native_first_label_neg_eq
    (X : ClassicalObject) (s t : ℤ) (x : Ambient model X (s,t)) :
    -(nativeFirstLabel X s t x) = nativeFirstLabel X s t x := by
  have hx : -x=x := neg_eq_of_add_eq_zero_left
    (classical_page_two (X.obj model.auxiliary) 2 (s,t) x)
  have regrade_neg {A : SyntheticSpectrum} (m w w' : ℤ) (hw : w=w')
      (a : BiHom m w A) :
      homotopyRegrade rfl hw (-a) = -(homotopyRegrade rfl hw a) := by
    subst w'
    rfl
  have hn : nativeFirstLabel X s t (-x) = -(nativeFirstLabel X s t x) := by
    simp only [nativeFirstLabel, first_label_inline, map_neg, regrade_neg, Preadditive.neg_comp]
  exact hn.symm.trans (congrArg (nativeFirstLabel X s t) hx)

/-- A detection of the actual finite boundary immediately gives the
specified classical output and its survival; the latter is not a premise. -/
private theorem terminal_decode_of_detected_boundary
    (X : ClassicalObject) (p : ℕ) (hp : 0<p) (s t : ℤ)
    (x : Ambient model X (s,t)) (y : Ambient model X (s+p+1,t+p))
    (hb : Detects (model.convergence (.quotient p (.nu X)))
      (s+p+1,t+p,t+(1:ℕ))
      ((model.family.quotientProjection
        (model.nu.functor.obj (X.obj model.auxiliary)) p).pageMap
          2 (s+p+1,t+p,t+(1:ℕ))
          (nuWeightLabel model X (s+p+1) (t+p) (t+(1:ℕ)) (by omega) y))
      (homotopyRegrade (by dsimp; omega) rfl
        (finiteTowerBoundary X 1 p (by decide) hp s t (nativeFirstLabel X s t x)))) :
    IsCycle model X p (s,t) x ∧
      DifferentialAt model X (p+1) (s,t) (s+p+1,t+p) x y := by
  obtain ⟨hx,hd⟩ := finite_bockstein_terminal_decode X p hp s t x y _ hb rfl
  exact ⟨hx,by exact ⟨by omega,hd⟩⟩


/-- The terminal decoder in the original R,K notation. Both the output
survival and differential refer to the supplied y, including y=0. -/
private theorem composition_terminal_decode
    (X : ClassicalObject) (R K : ℕ) (hR : 2≤R) (hK : 2≤K) (s t : ℤ)
    (y : Ambient model X (s+1,t+1))
    (v : Ambient model X (s+R+K,t+R+K-1))
    (hb : Detects (model.convergence (.quotient (R+K-2) (.nu X)))
      (s+R+K,t+R+K-1,t+2)
      ((model.family.quotientProjection
        (model.nu.functor.obj (X.obj model.auxiliary)) (R+K-2)).pageMap
          2 (s+R+K,t+R+K-1,t+2)
          (nuWeightLabel model X (s+R+K) (t+R+K-1) (t+2) (by omega) v))
      (homotopyRegrade (by dsimp; omega) (by dsimp; omega)
        (finiteTowerBoundary X 1 (R+K-2) (by decide) (by omega)
          (s+1) (t+1) (nativeFirstLabel X (s+1) (t+1) y)))) :
    IsCycle model X ((R:ℤ)+K-2) (s+1,t+1) y ∧
      DifferentialAt model X ((R:ℤ)+K-1)
        (s+1,t+1) (s+R+K,t+R+K-1) y v := by
  have general (N : ℕ) (hN : 0<N) (s₀ t₀ S T W : ℤ)
      (hS : S=s₀+N+1) (hT : T=t₀+N) (hW : W=t₀+1)
      (a : Ambient model X (s₀,t₀)) (b : Ambient model X (S,T))
      (hdet : Detects (model.convergence (.quotient N (.nu X))) (S,T,W)
        ((model.family.quotientProjection
          (model.nu.functor.obj (X.obj model.auxiliary)) N).pageMap
            2 (S,T,W) (nuWeightLabel model X S T W (by omega) b))
        (homotopyRegrade (by dsimp; omega) (by dsimp; omega)
          (finiteTowerBoundary X 1 N (by decide) hN s₀ t₀
            (nativeFirstLabel X s₀ t₀ a)))) :
      IsCycle model X N (s₀,t₀) a ∧
        DifferentialAt model X (N+1) (s₀,t₀) (S,T) a b := by
    subst S
    subst T
    subst W
    exact terminal_decode_of_detected_boundary X N hN s₀ t₀ a b hdet
  have hd := general (R+K-2) (by omega) (s+1) (t+1)
    (s+R+K) (t+R+K-1) (t+2) (by omega) (by omega) (by omega) y v hb
  have hp : ((R+K-2:ℕ):ℤ) = (R:ℤ)+K-2 := by omega
  have hp' : ((R+K-2:ℕ):ℤ)+1 = (R:ℤ)+K-1 := by omega
  rw [hp',hp] at hd
  exact hd


/-- Ordinary suspension is cancelled on actual representatives, before
reading the finite boundary as a classical differential. -/
private theorem ordinary_suspended_representative_injective
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

/-- The raw finite boundary used by the normalized square is literally
that of the Bockstein decoder on a native ν-object. -/
private theorem first_finite_boundary_eq_tower_boundary
    (X : ClassicalObject) (N : ℕ) (hN : 0<N) (s t : ℤ)
    (a : BiHom (t-s) t
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) 1)) :
    firstFiniteBoundaryRepresentative
      (model.nu.functor.obj (X.obj model.auxiliary)) N hN (t-s) t a =
    finiteTowerBoundary X 1 N (by decide) hN s t a := by
  rfl

/-- The actual finite-boundary operation commutes with arithmetic
regrading; it never changes the chosen first-quotient representative. -/
private theorem first_finite_boundary_regrade
    (A : SyntheticSpectrum) (N : ℕ) (hN : 0<N)
    {m m' w w' : ℤ} (hm : m=m') (hw : w=w')
    (a : BiHom m w (XModLambdaN A 1)) :
    firstFiniteBoundaryRepresentative A N hN m' w' (homotopyRegrade hm hw a) =
      homotopyRegrade (by omega) (by omega)
        (firstFiniteBoundaryRepresentative A N hN m w a) := by
  subst m'
  subst w'
  rfl


/-- The strict normalized boundary square and a detected native target
produce the classical output. This is the common final step of both
finite-layer criteria, and it keeps the same first-quotient operation. -/
private theorem normalized_boundary_image_decode
    (T : TriangleData model.auxiliary)
    (hf : normalizedExponent model.classicalTower T.f = 1)
    (p : ℕ) (hp : 0<p) (s t : ℤ)
    (x : Ambient model T.X (s,t))
    (v : Ambient model T.Y (s+1+p+1,t+1+p))
    (ex : XModLambdaN (((SyntheticCategory.biShift (0,1)).obj
      (model.nu.functor.obj (T.X.obj model.auxiliary)))⟦(1:ℤ)⟧) p ≅
      (XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
        (model.nu.functor.obj (T.X.obj model.auxiliary))) p)⟦(1:ℤ)⟧)
    (ey : XModLambdaN ((model.nu.functor.obj (T.Y.obj model.auxiliary))⟦(1:ℤ)⟧) p ≅
      (XModLambdaN (model.nu.functor.obj (T.Y.obj model.auxiliary)) p)⟦(1:ℤ)⟧)
    (hex : XModLambdaN.incl _ p ≫ ex.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ p))
    (hey : XModLambdaN.incl _ p ≫ ey.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ p))
    (b : BiHom ((t-s)-1) ((t+1)+(1:ℕ))
      (XModLambdaN (model.nu.functor.obj (T.Y.obj model.auxiliary)) p))
    (hb : Detects (model.convergence (.quotient p (.nu T.Y)))
      (s+1+p+1,t+1+p,(t+1)+(1:ℕ))
      ((model.family.quotientProjection
        (model.nu.functor.obj (T.Y.obj model.auxiliary)) p).pageMap
          2 (s+1+p+1,t+1+p,(t+1)+(1:ℕ))
          (nuWeightLabel model T.Y (s+1+p+1) (t+1+p) ((t+1)+(1:ℕ)) (by omega) v))
      (homotopyRegrade (by dsimp; omega) rfl b))
    (himage : suspendedFirstFiniteBoundary
        ((SyntheticCategory.biShift (0,1)).obj
          (model.nu.functor.obj (T.X.obj model.auxiliary))) p hp (t-s) (t+1)
          ex ((model.firstQuotient T.X 1 s t).symm x) ≫
        XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
          (normalizedFirstMap T hf)) p ≫ ey.hom =
      ordinarySuspendedRepresentative _ (t-s) ((t+1)+(1:ℕ)) b) :
    let y := KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t x
    IsCycle model T.Y p (s+1,t+1) y ∧
      DifferentialAt model T.Y (p+1) (s+1,t+1) (s+1+p+1,t+1+p) y v := by
  let y := KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t x
  have hsq := suspendedFirstFiniteBoundary_normalized_natural
    T.X T.Y 1 (by decide) p hp (normalizedFirstMap T hf)
    ex ey hex hey (t-s) (t+1) ((model.firstQuotient T.X 1 s t).symm x)
  have heq := ordinary_suspended_representative_injective _ (t-s) ((t+1)+(1:ℕ))
    (hsq.symm.trans himage)
  apply terminal_decode_of_detected_boundary T.Y p hp (s+1) (t+1) y v
  have hd : homotopyRegrade (show ((t+1)-(s+1))-1=(t+1+p)-(s+1+p+1) by omega) rfl
      (finiteTowerBoundary T.Y 1 p (by decide) hp (s+1) (t+1)
        (nativeFirstLabel T.Y (s+1) (t+1) y)) =
      homotopyRegrade (show (t-s)-1=(t+1+p)-(s+1+p+1) by omega) rfl b := by
    rw [←first_finite_boundary_eq_tower_boundary]
    dsimp only [y]
    rw [cofiberFirstQuotientBoundary_native_label,first_finite_boundary_regrade,heq]
    simp only [regrade_precomp,←Category.assoc,eqToHom_trans]
  simpa only [hd] using hb

private theorem normalized_boundary_image_decode_general
    (T : TriangleData model.auxiliary)
    (hf : normalizedExponent model.classicalTower T.f = 1)
    (p : ℕ) (hp : 0<p) (s t S V m w : ℤ)
    (hS : S=s+1+p+1) (hV : V=t+1+p) (hm : m=t-s) (hw : w=(t+1)+(1:ℕ))
    (x : Ambient model T.X (s,t)) (v : Ambient model T.Y (S,V))
    (ex : XModLambdaN (((SyntheticCategory.biShift (0,1)).obj
      (model.nu.functor.obj (T.X.obj model.auxiliary)))⟦(1:ℤ)⟧) p ≅
      (XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
        (model.nu.functor.obj (T.X.obj model.auxiliary))) p)⟦(1:ℤ)⟧)
    (ey : XModLambdaN ((model.nu.functor.obj (T.Y.obj model.auxiliary))⟦(1:ℤ)⟧) p ≅
      (XModLambdaN (model.nu.functor.obj (T.Y.obj model.auxiliary)) p)⟦(1:ℤ)⟧)
    (hex : XModLambdaN.incl _ p ≫ ex.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ p))
    (hey : XModLambdaN.incl _ p ≫ ey.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ p))
    (b : BiHom (m-1) w (XModLambdaN (model.nu.functor.obj (T.Y.obj model.auxiliary)) p))
    (hb : Detects (model.convergence (.quotient p (.nu T.Y))) (S,V,w)
      ((model.family.quotientProjection
        (model.nu.functor.obj (T.Y.obj model.auxiliary)) p).pageMap
          2 (S,V,w) (nuWeightLabel model T.Y S V w (by omega) v))
      (homotopyRegrade (by dsimp; omega) rfl b))
    (himage : suspendedFirstFiniteBoundary
        ((SyntheticCategory.biShift (0,1)).obj
          (model.nu.functor.obj (T.X.obj model.auxiliary))) p hp (t-s) (t+1)
          ex ((model.firstQuotient T.X 1 s t).symm x) ≫
        XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
          (normalizedFirstMap T hf)) p ≫ ey.hom =
      homotopyRegrade hm hw (ordinarySuspendedRepresentative _ m w b)) :
    let y := KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t x
    IsCycle model T.Y p (s+1,t+1) y ∧
      DifferentialAt model T.Y (p+1) (s+1,t+1) (S,V) y v := by
  subst S V m w
  exact normalized_boundary_image_decode T hf p hp s t x v ex ey hex hey b hb himage

private theorem finite_layer_surj_classical_second_image_from_core
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
  apply (positive_first_finite_core T he hT hf hg hh
    c q hq S V u z v hu hdz ey hey ε hε).2 ?_ d hd
  intro a ha
  have hfil := raw_may_source_desuspend_reflects_filtration
    T he hf (c+(q+1)) c S V (S+1) ε a ha
  exact finite_layer_surj_native_annihilation T he hf hg hh hT c (q+1)
    (by omega) S V hsurj a hfil

private theorem pdf_conditions_classical_second_image_from_core
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
  apply (positive_first_finite_core T he hT hf hg hh
    c q hq S V u z v hu hdz ey hey ε hε).2 ?_ d hd
  intro a ha
  letI := model.exactness.shiftCommShift (0,1)
  letI := model.exactness.shiftExact (0,1)
  obtain ⟨εp,hεp,_⟩ := quotient_shift_exists model.quotients.coherence (0,1) (c+(q+1))
    (model.nu.functor.obj (T.X.obj model.auxiliary))
  have hz := pdf_conditions_native_annihilation T hf c (q+1) (by omega) S V
    εp hεp hNC1 hNC2 (rawMaySourceDesuspend T he hf (c+(q+1)) c S V ε a) ha
  exact native_positive_image_zero_implies_raw_zero T he hf (c+(q+1)) c (by omega)
    S V ε εp hε hεp a hz


private theorem finite_layer_surj_classical_corollary
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g +
      normalizedExponent model.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible model T he)
    (hf : normalizedExponent model.classicalTower T.f = 1)
    (hg : normalizedExponent model.classicalTower T.g = 0)
    (hh : normalizedExponent model.classicalTower T.h = 0)
    (c q : ℕ) (hq : 0<q) (s t : ℤ)
    (x : Ambient model T.X (s,t))
    (u : Ambient model T.X (s+(c+1)+1,t+(c+1)))
    (z : Ambient model T.Z (s+(c+1)+1,(t+(c+1))+1))
    (v : Ambient model T.Y ((s+(c+1)+1)+q+1,((t+(c+1))+1)+q))
    (hu : (model.classicalSuspension T.X).DesuspendsClass (s+(c+1)+1) ((t+(c+1))+1)
      ((model.classical.map T.h).pageMap 2 (s+(c+1)+1,(t+(c+1))+1) z) (by simpa using u))
    (hdx : HasDifferential (model.classical.obj (T.X.obj model.auxiliary))
      ((c+1)+1) (s,t) (s+(c+1)+1,t+(c+1)) x u)
    (hdz : HasDifferential (model.classical.obj (T.Z.obj model.auxiliary))
      (q+1) (s+(c+1)+1,(t+(c+1))+1) ((s+(c+1)+1)+q+1,((t+(c+1))+1)+q) z
      ((model.classical.map T.g).pageMap 2 ((s+(c+1)+1)+q+1,((t+(c+1))+1)+q) v))
    (hsurj : KIP126.ProofTools.Standard.MahowaldLeibnizFiniteLayerSurjectivity
      T (c+2) (q+1) ((s+(c+1)+1)-(c+2:ℕ)) ((t+(c+1))-(c+2:ℕ)+1)) :
    let y := KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t x
    IsCycle model T.Y (c+(q+1)) (s+1,t+1) y ∧
      DifferentialAt model T.Y (c+(q+1)+1) (s+1,t+1)
        ((s+(c+1)+1)+q+1,((t+(c+1))+1)+q) y v := by
  let N := c+(q+1)
  have hN : 0<N := by dsimp [N]; omega
  let S := s+(c+1)+1
  let V := t+(c+1)
  obtain ⟨ex,hex⟩ := quotient_suspension_inclusion_exists
    ((SyntheticCategory.biShift (0,1)).obj (model.nu.functor.obj (T.X.obj model.auxiliary))) N
  obtain ⟨ey,hey⟩ := quotient_suspension_inclusion_exists
    (model.nu.functor.obj (T.Y.obj model.auxiliary)) (q+1)
  obtain ⟨eY,heY⟩ := quotient_suspension_inclusion_exists
    (model.nu.functor.obj (T.Y.obj model.auxiliary)) N
  letI := model.exactness.shiftCommShift (1,1)
  letI := model.exactness.shiftExact (1,1)
  obtain ⟨ε,hε,_⟩ := quotient_shift_exists model.quotients.coherence (1,1) N
    (model.nu.functor.obj (T.X.obj model.auxiliary))
  let d := homotopyRegrade (show t-s=V-S+1 by dsimp [S,V]; omega)
    (show (t+1)+(1:ℕ)=V-c+1 by dsimp [V]; omega)
    (actualNormalizedFirstFiniteBoundary T he hf N hN s t ex x)
  have hd := actual_first_finite_boundary_source_detects T he hf (c+1) N c
    (by omega) hN (by omega) s t x u hdx ex hex ε hε
  have himage := finite_layer_surj_classical_second_image_from_core T he hT hf hg hh c q hq S V
    hsurj u z v hu hdz ey hey ε hε d hd
  obtain ⟨b,hb,hbimage⟩ := finite_may_signed_target_at_level T.Y c q hq S (V+1)
    v ey eY hey heY
  apply normalized_boundary_image_decode_general T hf N hN s t (S+q+1) ((V+1)+q)
    ((V+1)-S) ((V+1)-c) (by dsimp [S,N]; omega) (by dsimp [V,N]; omega)
    (by dsimp [S,V]; omega) (by dsimp [V]; omega) x v ex eY hex heY b hb
  apply homotopy_regrade_injective (show t-s=V-S+1 by dsimp [S,V]; omega)
    (show (t+1)+(1:ℕ)=V-c+1 by dsimp [V]; omega)
  have hi := congrArg (fun a => a ≫ eY.hom) himage
  simp only [←homotopyRegrade_comp] at hi
  dsimp only [normalizedTriangle,Triangle.mk] at hi
  rw [hbimage] at hi
  simp only [d,actualNormalizedFirstFiniteBoundary,←homotopyRegrade_comp,Category.assoc] at hi
  have hnorm := positive_normalized_source_inv_arrow T he hf
  dsimp only [normalizedTriangle,Triangle.mk] at hnorm
  rw [←Category.assoc _ (XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
      (model.normalizedMap T.X T.Y T.f).map) N),
    ←model.quotients.functoriality.map_comp,←Functor.map_comp,
    hnorm] at hi
  simpa only [homotopyRegrade_comp,normalized_homotopy_regrade_trans,Category.assoc] using hi

private theorem pdf_conditions_classical_corollary
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g +
      normalizedExponent model.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible model T he)
    (hf : normalizedExponent model.classicalTower T.f = 1)
    (hg : normalizedExponent model.classicalTower T.g = 0)
    (hh : normalizedExponent model.classicalTower T.h = 0)
    (c q : ℕ) (hq : 0<q) (s t : ℤ)
    (x : Ambient model T.X (s,t))
    (u : Ambient model T.X (s+(c+1)+1,t+(c+1)))
    (z : Ambient model T.Z (s+(c+1)+1,(t+(c+1))+1))
    (v : Ambient model T.Y ((s+(c+1)+1)+q+1,((t+(c+1))+1)+q))
    (hu : (model.classicalSuspension T.X).DesuspendsClass (s+(c+1)+1) ((t+(c+1))+1)
      ((model.classical.map T.h).pageMap 2 (s+(c+1)+1,(t+(c+1))+1) z) (by simpa using u))
    (hdx : HasDifferential (model.classical.obj (T.X.obj model.auxiliary))
      ((c+1)+1) (s,t) (s+(c+1)+1,t+(c+1)) x u)
    (hdz : HasDifferential (model.classical.obj (T.Z.obj model.auxiliary))
      (q+1) (s+(c+1)+1,(t+(c+1))+1) ((s+(c+1)+1)+q+1,((t+(c+1))+1)+q) z
      ((model.classical.map T.g).pageMap 2 ((s+(c+1)+1)+q+1,((t+(c+1))+1)+q) v))
    (hNC1 : ∀ j : ℕ, 1≤j → j<(q+1)-1 →
      cycles model T.X (((q+1:ℕ):ℤ)-j)
        ((s+(c+1)+1)+j,(t+(c+1))+j) ≤
      boundaries model T.X ((c:ℤ)+j+1)
        ((s+(c+1)+1)+j,(t+(c+1))+j))
    (hNC2 : ∀ a : Ambient model T.X
        ((s+(c+1)+1)+(q+1:ℕ)-1,(t+(c+1))+(q+1:ℕ)-1),
      KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf
        ((s+(c+1)+1)+(q+1:ℕ)-1) ((t+(c+1))+(q+1:ℕ)-1) a ∈
      boundaries model T.Y (c+(q+1))
        ((s+(c+1)+1)+(q+1:ℕ)-1+1,(t+(c+1))+(q+1:ℕ)-1+1)) :
    let y := KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t x
    IsCycle model T.Y (c+(q+1)) (s+1,t+1) y ∧
      DifferentialAt model T.Y (c+(q+1)+1) (s+1,t+1)
        ((s+(c+1)+1)+q+1,((t+(c+1))+1)+q) y v := by
  let N := c+(q+1)
  have hN : 0<N := by dsimp [N]; omega
  let S := s+(c+1)+1
  let V := t+(c+1)
  obtain ⟨ex,hex⟩ := quotient_suspension_inclusion_exists
    ((SyntheticCategory.biShift (0,1)).obj (model.nu.functor.obj (T.X.obj model.auxiliary))) N
  obtain ⟨ey,hey⟩ := quotient_suspension_inclusion_exists
    (model.nu.functor.obj (T.Y.obj model.auxiliary)) (q+1)
  obtain ⟨eY,heY⟩ := quotient_suspension_inclusion_exists
    (model.nu.functor.obj (T.Y.obj model.auxiliary)) N
  letI := model.exactness.shiftCommShift (1,1)
  letI := model.exactness.shiftExact (1,1)
  obtain ⟨ε,hε,_⟩ := quotient_shift_exists model.quotients.coherence (1,1) N
    (model.nu.functor.obj (T.X.obj model.auxiliary))
  let d := homotopyRegrade (show t-s=V-S+1 by dsimp [S,V]; omega)
    (show (t+1)+(1:ℕ)=V-c+1 by dsimp [V]; omega)
    (actualNormalizedFirstFiniteBoundary T he hf N hN s t ex x)
  have hd := actual_first_finite_boundary_source_detects T he hf (c+1) N c
    (by omega) hN (by omega) s t x u hdx ex hex ε hε
  have himage := pdf_conditions_classical_second_image_from_core T he hT hf hg hh c q hq S V
    hNC1 hNC2 u z v hu hdz ey hey ε hε d hd
  obtain ⟨b,hb,hbimage⟩ := finite_may_signed_target_at_level T.Y c q hq S (V+1)
    v ey eY hey heY
  apply normalized_boundary_image_decode_general T hf N hN s t (S+q+1) ((V+1)+q)
    ((V+1)-S) ((V+1)-c) (by dsimp [S,N]; omega) (by dsimp [V,N]; omega)
    (by dsimp [S,V]; omega) (by dsimp [V]; omega) x v ex eY hex heY b hb
  apply homotopy_regrade_injective (show t-s=V-S+1 by dsimp [S,V]; omega)
    (show (t+1)+(1:ℕ)=V-c+1 by dsimp [V]; omega)
  have hi := congrArg (fun a => a ≫ eY.hom) himage
  simp only [←homotopyRegrade_comp] at hi
  dsimp only [normalizedTriangle,Triangle.mk] at hi
  rw [hbimage] at hi
  simp only [d,actualNormalizedFirstFiniteBoundary,←homotopyRegrade_comp,Category.assoc] at hi
  have hnorm := positive_normalized_source_inv_arrow T he hf
  dsimp only [normalizedTriangle,Triangle.mk] at hnorm
  rw [←Category.assoc _ (XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
      (model.normalizedMap T.X T.Y T.f).map) N),
    ←model.quotients.functoriality.map_comp,←Functor.map_comp,
    hnorm] at hi
  simpa only [homotopyRegrade_comp,normalized_homotopy_regrade_trans,Category.assoc] using hi

private theorem finite_layer_surj_classical_corollary_heq
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g +
      normalizedExponent model.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible model T he)
    (hf : normalizedExponent model.classicalTower T.f = 1)
    (hg : normalizedExponent model.classicalTower T.g = 0)
    (hh : normalizedExponent model.classicalTower T.h = 0)
    (c q : ℕ) (hq : 0<q) (s t : ℤ)
    (x : Ambient model T.X (s,t))
    (u : Ambient model T.X (s+(c+1)+1,t+(c+1)))
    (z : Ambient model T.Z (s+(c+1)+1,(t+(c+1))+1))
    (v : Ambient model T.Y ((s+(c+1)+1)+q+1,((t+(c+1))+1)+q))
    (hu : ∃ u' : Ambient model T.X (s+(c+1)+1,((t+(c+1))+1)-1),
      (model.classicalSuspension T.X).DesuspendsClass (s+(c+1)+1) ((t+(c+1))+1)
        ((model.classical.map T.h).pageMap 2 (s+(c+1)+1,(t+(c+1))+1) z) u' ∧ HEq u' u)
    (hdx : HasDifferential (model.classical.obj (T.X.obj model.auxiliary))
      ((c+1)+1) (s,t) (s+(c+1)+1,t+(c+1)) x u)
    (hdz : HasDifferential (model.classical.obj (T.Z.obj model.auxiliary))
      (q+1) (s+(c+1)+1,(t+(c+1))+1) ((s+(c+1)+1)+q+1,((t+(c+1))+1)+q) z
      ((model.classical.map T.g).pageMap 2 ((s+(c+1)+1)+q+1,((t+(c+1))+1)+q) v))
    (hsurj : KIP126.ProofTools.Standard.MahowaldLeibnizFiniteLayerSurjectivity
      T (c+2) (q+1) ((s+(c+1)+1)-(c+2:ℕ)) ((t+(c+1))-(c+2:ℕ)+1)) :
    let y := KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t x
    IsCycle model T.Y (c+(q+1)) (s+1,t+1) y ∧
      DifferentialAt model T.Y (c+(q+1)+1) (s+1,t+1)
        ((s+(c+1)+1)+q+1,((t+(c+1))+1)+q) y v := by
  obtain ⟨u',hu',hU⟩ := hu
  apply finite_layer_surj_classical_corollary T he hT hf hg hh c q hq s t x u z v ?_ hdx hdz hsurj
  let uc : Ambient model T.X (s+(c+1)+1,((t+(c+1))+1)-1) := by simpa using u
  have hc : HEq uc u := cast_heq _ _
  have heq : u'=uc := eq_of_heq (hU.trans hc.symm)
  change (model.classicalSuspension T.X).DesuspendsClass (s+(c+1)+1) ((t+(c+1))+1)
    ((model.classical.map T.h).pageMap 2 (s+(c+1)+1,(t+(c+1))+1) z) uc
  rw [←heq]
  exact hu'

private theorem finite_layer_surj_statement
    (T : TriangleData model.auxiliary)
    (hf : normalizedExponent model.classicalTower T.f = 1)
    (hg : normalizedExponent model.classicalTower T.g = 0)
    (hh : normalizedExponent model.classicalTower T.h = 0) :
    KIP126.ProofTools.Standard.FiniteLayerSurjectivityMahowaldLeibnizStatement T hf hg hh := by
  intro hT R K hR hK
  obtain ⟨c,rfl⟩ : ∃c,R=c+2 := ⟨R-2,by omega⟩
  obtain ⟨q,rfl⟩ : ∃q,K=q+1 := ⟨K-1,by omega⟩
  intro s t x z v hx hz hu hdz hsurj
  obtain ⟨u,hu,hdx⟩ := hu
  have Hst := finite_layer_surj_classical_corollary_heq T (by simp [hf,hg,hh]) hT hf hg hh c q (by omega) s t
  rw [show (s+((c:ℤ)+1)+1)+q+1=s+(c+2:ℕ)+(q+1:ℕ) by omega,
    show ((t+((c:ℤ)+1))+1)+q=t+(c+2:ℕ)+(q+1:ℕ)-1 by omega,
    show (s+((c:ℤ)+1)+1)-(c+2:ℕ)=s by omega,
    show (t+((c:ℤ)+1))-(c+2:ℕ)+1=t by omega,
    show (t+((c:ℤ)+1))+1=t+(c+2:ℕ) by omega,
    show s+((c:ℤ)+1)+1=s+(c+2:ℕ) by omega,
    show t+((c:ℤ)+1)=t+(c+2:ℕ)-1 by omega] at Hst
  have hhpage : (((c:ℤ)+1)+1:ℤ)=(c+2:ℕ) := by omega
  have hnpage : ((c:ℤ)+((q:ℤ)+1))=(c+2:ℕ)+(q+1:ℕ)-2 := by omega
  have hnpage' : ((c:ℤ)+((q:ℤ)+1)+1)=(c+2:ℕ)+(q+1:ℕ)-1 := by omega
  rw [hhpage,hnpage',hnpage] at Hst
  exact Hst x u z v ⟨u,hu,HEq.rfl⟩ hdx.2 hdz.2 hsurj

end
end KIP126.ProofTools.Internal.MahowaldLeibniz
