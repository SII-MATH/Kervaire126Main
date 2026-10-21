module

import all KIP126.ProofTools.MahowaldLeibniz.LastLayer
import all KIP126.ProofTools.MahowaldLeibniz.Filtration

/-! The complete PDF middle-layer and last-layer conditions annihilate
actual finite source ambiguity in native νX coordinates. -/

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
set_option maxHeartbeats 3000000

private theorem last_layer_regrade_trans {A : SyntheticSpectrum}
    {m₁ m₂ m₃ w₁ w₂ w₃ : ℤ}
    (hm₁ : m₁=m₂) (hm₂ : m₂=m₃) (hw₁ : w₁=w₂) (hw₂ : w₂=w₃)
    (a : BiHom m₁ w₁ A) :
    homotopyRegrade hm₂ hw₂ (homotopyRegrade hm₁ hw₁ a) =
      homotopyRegrade (hm₁.trans hm₂) (hw₁.trans hw₂) a := by
  subst m₂; subst m₃; subst w₂; subst w₃; rfl

private theorem last_layer_regrade_zero {A : SyntheticSpectrum}
    {m m' w w' : ℤ} (hm : m=m') (hw : w=w') :
    homotopyRegrade hm hw (0 : BiHom m w A)=0 := by
  subst m'; subst w'; rfl

private theorem last_layer_regrade_zero_iff {A : SyntheticSpectrum}
    {m m' w w' : ℤ} (hm : m=m') (hw : w=w') (a : BiHom m w A) :
    homotopyRegrade hm hw a=0 ↔ a=0 := by
  subst m'; subst w'; rfl

/-- The actual normalized finite image in its native homotopy degree. -/
private def positiveFiniteImage (T : TriangleData model.auxiliary)
    (hf : normalizedExponent model.classicalTower T.f=1) (q : ℕ)
    (εq : XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
        (model.nu.functor.obj (T.X.obj model.auxiliary))) q ≅
      (SyntheticCategory.biShift (0,1)).obj
        (XModLambdaN (model.nu.functor.obj (T.X.obj model.auxiliary)) q))
    (m w : ℤ)
    (a : BiHom m w (XModLambdaN (model.nu.functor.obj (T.X.obj model.auxiliary)) q)) :
    BiHom m (w+1) (XModLambdaN (model.nu.functor.obj (T.Y.obj model.auxiliary)) q) :=
  (homotopyRegrade (by dsimp; omega) rfl
    (shiftHomotopyClass (0,1) (m,w) a) ≫ εq.inv) ≫
      XModLambdaN.map (lastLayerNormalizedMap T hf) q

private theorem positiveFiniteImage_regrade (T : TriangleData model.auxiliary)
    (hf : normalizedExponent model.classicalTower T.f=1) (q : ℕ)
    (εq : XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
        (model.nu.functor.obj (T.X.obj model.auxiliary))) q ≅
      (SyntheticCategory.biShift (0,1)).obj
        (XModLambdaN (model.nu.functor.obj (T.X.obj model.auxiliary)) q))
    {m m' w w' : ℤ} (hm : m=m') (hw : w=w')
    (a : BiHom m w (XModLambdaN (model.nu.functor.obj (T.X.obj model.auxiliary)) q)) :
    homotopyRegrade hm (show w+1=w'+1 by omega) (positiveFiniteImage T hf q εq m w a) =
      positiveFiniteImage T hf q εq m' w' (homotopyRegrade hm hw a) := by
  subst m'; subst w'; rfl

private theorem last_layer_positive_image_zero (T : TriangleData model.auxiliary)
    (hf : normalizedExponent model.classicalTower T.f=1)
    (d : ℕ) (hd : 0<d) (s t : ℤ)
    (εq : XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
        (model.nu.functor.obj (T.X.obj model.auxiliary))) (d+1) ≅
      (SyntheticCategory.biShift (0,1)).obj
        (XModLambdaN (model.nu.functor.obj (T.X.obj model.auxiliary)) (d+1)))
    (hεq : XModLambdaN.incl _ (d+1) ≫ εq.hom =
      (SyntheticCategory.biShift (0,1)).map (XModLambdaN.incl _ (d+1)))
    (hNC2 : ∀ x : Ambient model T.X (s,t),
      KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t x ∈
        boundaries model T.Y (d+1) (s+1,t+1))
    (a : BiHom (t-s) (t-d)
      (XModLambdaN (model.nu.functor.obj (T.X.obj model.auxiliary)) (d+1)))
    (ha : FiltrationAtLeast model.syntheticTower s a) :
    positiveFiniteImage T hf (d+1) εq (t-s) (t-d) a=0 := by
  have h := normalizedFirstMap_last_layer_zero T hf d hd s t εq hεq hNC2 a ha
  have hh := congrArg (homotopyRegrade (show t-s+0=t-s by omega)
    (show t+1-d=(t-d)+1 by omega)) h
  simpa only [positiveFiniteImage,regrade_comp,last_layer_regrade_trans,
    last_layer_regrade_zero,Category.assoc] using hh

private theorem last_layer_positive_image_zero_q (T : TriangleData model.auxiliary)
    (hf : normalizedExponent model.classicalTower T.f=1)
    (q : ℕ) (hq : 2≤q) (s t : ℤ)
    (εq : XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
        (model.nu.functor.obj (T.X.obj model.auxiliary))) q ≅
      (SyntheticCategory.biShift (0,1)).obj
        (XModLambdaN (model.nu.functor.obj (T.X.obj model.auxiliary)) q))
    (hεq : XModLambdaN.incl _ q ≫ εq.hom =
      (SyntheticCategory.biShift (0,1)).map (XModLambdaN.incl _ q))
    (hNC2 : ∀ x : Ambient model T.X (s,t),
      KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t x ∈
        boundaries model T.Y q (s+1,t+1))
    (a : BiHom (t-s) (t-(q-1:ℕ))
      (XModLambdaN (model.nu.functor.obj (T.X.obj model.auxiliary)) q))
    (ha : FiltrationAtLeast model.syntheticTower s a) :
    positiveFiniteImage T hf q εq (t-s) (t-(q-1:ℕ)) a=0 := by
  cases q with
  | zero => omega
  | succ d =>
    apply last_layer_positive_image_zero T hf d (by omega) s t εq hεq
    · simpa only [Nat.cast_succ] using hNC2
    · exact ha

/-- NC1 followed by NC2 kills the whole actual source ambiguity. NC1 has
all middle finite-cycle quotients, while NC2 retains the last B_(c+K)
denominator and the fixed normalized first-quotient map. -/
private theorem pdf_conditions_native_annihilation
    (T : TriangleData model.auxiliary)
    (hf : normalizedExponent model.classicalTower T.f=1)
    (c K : ℕ) (hK : 2≤K) (S V : ℤ)
    (εq : XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
        (model.nu.functor.obj (T.X.obj model.auxiliary))) (c+K) ≅
      (SyntheticCategory.biShift (0,1)).obj
        (XModLambdaN (model.nu.functor.obj (T.X.obj model.auxiliary)) (c+K)))
    (hεq : XModLambdaN.incl _ (c+K) ≫ εq.hom =
      (SyntheticCategory.biShift (0,1)).map (XModLambdaN.incl _ (c+K)))
    (hNC1 : ∀ j : ℕ, 1≤j → j<K-1 →
      cycles model T.X ((K:ℤ)-j) (S+j,V+j) ≤
        boundaries model T.X ((c:ℤ)+j+1) (S+j,V+j))
    (hNC2 : ∀ x : Ambient model T.X (S+K-1,V+K-1),
      KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf (S+K-1) (V+K-1) x ∈
        boundaries model T.Y (c+K) (S+K-1+1,V+K-1+1))
    (a : BiHom (V-S) (V-c)
      (XModLambdaN (model.nu.functor.obj (T.X.obj model.auxiliary)) (c+K)))
    (ha : FiltrationAtLeast model.syntheticTower (S+1) a) :
    positiveFiniteImage T hf (c+K) εq (V-S) (V-c) a=0 := by
  have htop := (finite_filtration_collapse_of_middle_conditions T.X c K hK S V hNC1 a).mp ha
  let a' := homotopyRegrade (show V-S=(V+K-1)-(S+K-1) by omega)
    (show V-c=(V+K-1)-(c+K-1:ℕ) by omega) a
  have ha' : FiltrationAtLeast model.syntheticTower (S+K-1) a' :=
    (regrade_filtration_iff _ _ (S+K-1) a).mpr htop
  have hz := last_layer_positive_image_zero_q T hf (c+K) (by omega)
    (S+K-1) (V+K-1) εq hεq hNC2 a' ha'
  rw [←positiveFiniteImage_regrade] at hz
  exact (last_layer_regrade_zero_iff _ _ _).mp hz

private theorem positiveFiniteImage_sub (T : TriangleData model.auxiliary)
    (hf : normalizedExponent model.classicalTower T.f=1) (q : ℕ)
    (εq : XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
        (model.nu.functor.obj (T.X.obj model.auxiliary))) q ≅
      (SyntheticCategory.biShift (0,1)).obj
        (XModLambdaN (model.nu.functor.obj (T.X.obj model.auxiliary)) q))
    (m w : ℤ)
    (a b : BiHom m w (XModLambdaN (model.nu.functor.obj (T.X.obj model.auxiliary)) q)) :
    positiveFiniteImage T hf q εq m w (a-b) =
      positiveFiniteImage T hf q εq m w a-positiveFiniteImage T hf q εq m w b := by
  simp only [positiveFiniteImage,shiftHomotopyClass,Functor.map_sub,
    Preadditive.comp_sub,regrade_precomp,Preadditive.sub_comp]

/-- The full PDF conditions identify the actual normalized images of any
two specified representatives of the same finite-level native label. -/
private theorem pdf_conditions_same_native_source_image
    (T : TriangleData model.auxiliary)
    (hf : normalizedExponent model.classicalTower T.f=1)
    (c K : ℕ) (hK : 2≤K) (S V : ℤ)
    (εq : XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
        (model.nu.functor.obj (T.X.obj model.auxiliary))) (c+K) ≅
      (SyntheticCategory.biShift (0,1)).obj
        (XModLambdaN (model.nu.functor.obj (T.X.obj model.auxiliary)) (c+K)))
    (hεq : XModLambdaN.incl _ (c+K) ≫ εq.hom =
      (SyntheticCategory.biShift (0,1)).map (XModLambdaN.incl _ (c+K)))
    (hNC1 : ∀ j : ℕ, 1≤j → j<K-1 →
      cycles model T.X ((K:ℤ)-j) (S+j,V+j) ≤
        boundaries model T.X ((c:ℤ)+j+1) (S+j,V+j))
    (hNC2 : ∀ x : Ambient model T.X (S+K-1,V+K-1),
      KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf (S+K-1) (V+K-1) x ∈
        boundaries model T.Y (c+K) (S+K-1+1,V+K-1+1))
    (u : Ambient model T.X (S,V))
    (a b : BiHom (V-S) (V-c)
      (XModLambdaN (model.nu.functor.obj (T.X.obj model.auxiliary)) (c+K)))
    (ha : Detects (model.convergence (.quotient (c+K) (.nu T.X))) (S,V,V-c)
      (finiteTargetLabel model T.X (c+K) S V c u) a)
    (hb : Detects (model.convergence (.quotient (c+K) (.nu T.X))) (S,V,V-c)
      (finiteTargetLabel model T.X (c+K) S V c u) b) :
    positiveFiniteImage T hf (c+K) εq (V-S) (V-c) a =
      positiveFiniteImage T hf (c+K) εq (V-S) (V-c) b := by
  have hdiff := detects_sub_filtration
    (model.convergence (.quotient (c+K) (.nu T.X))) (S,V,V-c) ha hb
  have hz := pdf_conditions_native_annihilation T hf c K hK S V εq hεq hNC1 hNC2 (a-b) hdiff
  rw [positiveFiniteImage_sub] at hz
  exact sub_eq_zero.mp hz

end
end KIP126.ProofTools.Internal.MahowaldLeibniz
