module

import all KIP126.ProofTools.LevelLanguage
import all KIP126.ProofTools.GeneralizedLeibniz.RightEdge

/-! Label transport for the strong finite-quotient Mahowald theorem.

The representative always remains in the stated actual quotient.  Restriction
through rho reflects its specified finite label within the visible window;
normalization then uses the same fixed quotient-shift comparison as the
level-indexed Leibniz language.  No Mahowald or Leibniz law is used here.
-/

@[expose] section
namespace KIP126.ProofTools.Internal.Mahowald
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Standard
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Leibniz
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
set_option Elab.async false

/-- A common representative whose rho image has the visible label lambda^K x
has that same label in the strong quotient, and the original x is a later
classical cycle.  The zero-label case is included. -/
private theorem finite_rho_lift_label_and_cycles (X : ClassicalObject)
    (A N K : ℕ) (hAN : A ≤ N) (hKA : K < A) (s t : ℤ)
    (x : Ambient model X (s,t))
    (a : BiHom (t-s) (t-K)
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) A))
    (ha : Detects (model.convergence (.quotient A (.nu X))) (s,t,t-K)
      (finiteTargetLabel model X A s t K x) a)
    (c : BiHom (t-s) (t-K)
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) N))
    (hc : c ≫ (model.quotients.tower _).rho A N hAN = a) :
    Detects (model.convergence (.quotient N (.nu X))) (s,t,t-K)
      (finiteTargetLabel model X N s t K x) c ∧
      x ∈ cycles model X ((N:ℤ)-K) (s,t) := by
  have hlabel (q : ℕ) :
      ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) q).pageMap
        2 (s,t,t-K) (nuWeightLabel model X s t (t-K) (by omega) x)) =
        finiteTargetLabel model X q s t K x := by
    have hk : (t-(t-K)).toNat = K := by omega
    have hn : nuWeightLabel model X s t (t-K) (by omega) x =
        targetNuLabel model X s t K x := by
      unfold nuWeightLabel
      have transport (k k' : ℕ) (h : k=k') (hp : (s,t,t-k)=(s,t,t-k')) :
          regradeE2 hp (targetNuLabel model X s t k x) =
            targetNuLabel model X s t k' x := by
        subst k'
        rfl
      exact transport _ K hk _
    rw [hn]
    rfl
  have ha' := ha
  rw [←hlabel A] at ha'
  have hdet := rho_lift_detects X A N (by omega) hAN s t (t-K)
    (by constructor <;> omega) x a ha' c hc
  have hcyc := rho_lift_detected_cycles X A N (by omega) hAN s t (t-K)
    (by constructor <;> omega) x a ha' c hc
  rw [hlabel N] at hdet
  refine ⟨hdet,?_⟩
  convert hcyc using 1
  congr 1
  omega

/-- The normalized representative in the actual quotient of the shifted
source, using the fixed comparison that defines the intrinsic source label. -/
private def finiteLevelNormalizedRepresentative (X : ClassicalObject)
    (e : ℤ) (N K : ℕ) (s t : ℤ)
    (c : BiHom (t-s) (t-K)
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) N)) :
    BiHom (t-s) (t+e-K)
      ((SyntheticObject.quotient N (.shift (0,e) (.nu X))).obj
        model.nu model.auxiliary) :=
  homotopyRegrade (by simp) (by dsimp; omega)
    (shiftHomotopyClass (0,e) (t-s,t-K) c) ≫ (levelQuotientShiftIso X e N).inv

/-- Normalization preserves the actual detection of the intrinsic finite
source label at every level. -/
private theorem finite_level_normalized_representative_detects
    (X : ClassicalObject) (e : ℤ) (N K : ℕ) (s t : ℤ)
    (x : Ambient model X (s,t))
    (c : BiHom (t-s) (t-K)
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) N))
    (hc : Detects (model.convergence (.quotient N (.nu X))) (s,t,t-K)
      (finiteTargetLabel model X N s t K x) c) :
    Detects (model.convergence (.quotient N (.shift (0,e) (.nu X))))
      (s,(t-s)+s,t+e-K)
      (KIP126.ProofTools.Standard.levelFiniteSourceLabel X N e s t K x)
      (homotopyRegrade (by dsimp; omega) rfl
        (finiteLevelNormalizedRepresentative X e N K s t c)) := by
  let A : SyntheticObject := .quotient N (.nu X)
  let p : ℤ×ℤ := (t-s,t-K)
  let δ : ℤ×ℤ := (0,e)
  have h0 : (s,t,t-K)=(s,p.1+s,p.2) := by simp [p]
  have hN : (s,(p+δ).1+s,(p+δ).2)=(s,(t-s)+s,t+e-K) := by
    ext <;> dsimp [p,δ] <;> omega
  have hc0 := detects_transport h0 _ _ hc
  have hc0' : Detects (model.convergence A) (s,p.1+s,p.2)
      (regradeE2 h0 (finiteTargetLabel model X N s t K x))
      (homotopyRegrade (by dsimp [p]; omega) rfl c) := by
    convert hc0 using 1
  have hs := detects_shift A δ p s _ c hc0'
  have ht := detects_transport hN _ _ hs
  have hm := detects_map (.shift δ A) (.quotient N (.shift (0,e) (.nu X)))
    (levelQuotientShiftIso X e N).inv (s,(t-s)+s,t+e-K) _ _ ht
  convert hm using 1
  · rfl
  · simp only [finiteLevelNormalizedRepresentative,regrade_precomp,←Category.assoc,
      eqToHom_trans]
    rfl

/-- The target level is forced by the same actual source weight; this
comparison preserves the specified y. -/
private theorem finite_level_target_label (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (N K J : ℕ) (n s t : ℤ)
    (hn : (normalizedExponent model.classicalTower f : ℤ) ≤ n)
    (hJ : (J:ℤ) = K+n-normalizedExponent model.classicalTower f)
    (y : Ambient model Y (s+n,t+n)) :
    regradeE2 (by ext <;> dsimp <;> omega)
      (finiteTargetLabel model Y N (s+n) (t+n) J y) =
      levelFiniteTargetLabel X Y f N K n s t hn y := by
  have hpow : ((t+n)-(t+normalizedExponent model.classicalTower f-K)).toNat=J := by
    omega
  unfold levelFiniteTargetLabel finiteTargetLabel nuWeightLabel
  change regradeE2 _ (familyPageMap model.family (XModLambdaN.incl _ N) 2 _ _) =
    regradeE2 _ (familyPageMap model.family (XModLambdaN.incl _ N) 2 _ (regradeE2 _ _))
  simp only [page_regrade,normalized_regrade_trans]
  have labels (k k' : ℕ) (hk : k=k') (p : Tridegree)
      (h₁ : (s+n,t+n,t+n-k)=p) (h₂ : (s+n,t+n,t+n-k')=p) :
      regradeE2 h₁ (targetNuLabel model Y (s+n) (t+n) k y) =
        regradeE2 h₂ (targetNuLabel model Y (s+n) (t+n) k' y) := by
    subst k'
    rfl
  exact congrArg (familyPageMap model.family (XModLambdaN.incl _ N) 2
    (s+n,(t-s)+(s+n),t+normalizedExponent model.classicalTower f-K))
      (labels _ _ hpow.symm _ _ _)

/-- Actual detected representatives for the same normalized finite map give
the complete level-extension witness, with arbitrary target object Y. -/
private theorem finite_level_extension_of_detected_pair
    (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (page K J : ℕ) (n s t : ℤ) (hpage : 2 ≤ page)
    (hn : (normalizedExponent model.classicalTower f : ℤ) ≤ n)
    (hnUpper : n ≤ (page:ℤ)-2+normalizedExponent model.classicalTower f)
    (hJ : (J:ℤ) = K+n-normalizedExponent model.classicalTower f)
    (x : Ambient model X (s,t)) (y : Ambient model Y (s+n,t+n))
    (a : BiHom (t-s) (t+normalizedExponent model.classicalTower f-K)
      ((SyntheticObject.quotient (page+K-1) (extensionSourceObject model X Y f)).obj
        model.nu model.auxiliary))
    (ha : Detects (model.convergence
      (.quotient (page+K-1) (extensionSourceObject model X Y f)))
      (s,(t-s)+s,t+normalizedExponent model.classicalTower f-K)
      (KIP126.ProofTools.Standard.levelFiniteSourceLabel X (page+K-1)
        (normalizedExponent model.classicalTower f) s t K x)
      (homotopyRegrade (by dsimp; omega) rfl a))
    (hb : Detects (model.convergence (.quotient (page+K-1) (.nu Y)))
      (s+n,t+n,t+n-J)
      (finiteTargetLabel model Y (page+K-1) (s+n) (t+n) J y)
      (homotopyRegrade (by dsimp; omega) (by dsimp; omega)
        (a ≫ finiteExtensionMap model X Y f (page+K-1)))) :
    KIP126.ProofTools.Standard.LevelFiniteExtension X Y f page K n s t x y := by
  have hp : (s+n,t+n,t+n-J)=
      (s+n,(t-s)+(s+n),t+normalizedExponent model.classicalTower f-K) := by
    ext <;> dsimp <;> omega
  have hb' := detects_transport hp _ _ hb
  rw [finite_level_target_label X Y f (page+K-1) K J n s t hn hJ y] at hb'
  obtain ⟨source,target,hs,ht,heq⟩ := extension_equation_of_detected_pair
    (model.convergentMap
      (.quotient (page+K-1) (extensionSourceObject model X Y f))
      (.quotient (page+K-1) (.nu Y)) (finiteExtensionMap model X Y f (page+K-1)))
    (t-s,t+normalizedExponent model.classicalTower f-K) s n
    (by have := normalizedExponent_le_one model.classicalTower f; omega)
    _ _ a (a ≫ finiteExtensionMap model X Y f (page+K-1)) ha
    (by simpa only [regrade_precomp,←Category.assoc,eqToHom_trans] using hb') rfl
  exact ⟨hpage,hn,hnUpper,source,target,hs,ht,heq⟩

/-- A native common representative and its actual normalized f image give
the level extension in the full quotient N.  The effective classical page
is N-K+1, and J<N is exactly its target visibility bound. -/
private theorem finite_level_extension_of_native_representative
    (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (N K J : ℕ) (hKN : K < N) (hJN : J < N) (n s t : ℤ)
    (hn : (normalizedExponent model.classicalTower f : ℤ) ≤ n)
    (hJ : (J:ℤ) = K+n-normalizedExponent model.classicalTower f)
    (x : Ambient model X (s,t)) (y : Ambient model Y (s+n,t+n))
    (c : BiHom (t-s) (t-K)
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) N))
    (hc : Detects (model.convergence (.quotient N (.nu X))) (s,t,t-K)
      (finiteTargetLabel model X N s t K x) c)
    (hf : Detects (model.convergence (.quotient N (.nu Y)))
      (s+n,t+n,t+n-J) (finiteTargetLabel model Y N (s+n) (t+n) J y)
      (homotopyRegrade (by dsimp; omega) (by dsimp; omega)
        (finiteLevelNormalizedRepresentative X (normalizedExponent model.classicalTower f)
          N K s t c ≫ finiteExtensionMap model X Y f N))) :
    KIP126.ProofTools.Standard.LevelFiniteExtension X Y f (N-K+1) K n s t x y := by
  have hq : (N-K+1)+K-1=N := by omega
  have ha := finite_level_normalized_representative_detects X
    (normalizedExponent model.classicalTower f) N K s t x c hc
  have result := finite_level_extension_of_detected_pair X Y f (N-K+1) K J n s t
    (by omega) hn (by omega) hJ x y
  rw [hq] at result
  exact result (finiteLevelNormalizedRepresentative X
    (normalizedExponent model.classicalTower f) N K s t c) ha hf

/-- The complete common-representative label assembly: rho fixes the source
label and its higher-cycle qualification, while the actual f image fixes
the target label in the same strong quotient. -/
private theorem finite_level_extension_of_common_representative
    (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (A N K J : ℕ) (hAN : A ≤ N) (hKA : K < A) (hJN : J < N)
    (n s t : ℤ)
    (hn : (normalizedExponent model.classicalTower f : ℤ) ≤ n)
    (hJ : (J:ℤ) = K+n-normalizedExponent model.classicalTower f)
    (x : Ambient model X (s,t)) (y : Ambient model Y (s+n,t+n))
    (a : BiHom (t-s) (t-K)
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) A))
    (ha : Detects (model.convergence (.quotient A (.nu X))) (s,t,t-K)
      (finiteTargetLabel model X A s t K x) a)
    (c : BiHom (t-s) (t-K)
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) N))
    (hρ : c ≫ (model.quotients.tower _).rho A N hAN = a)
    (hf : Detects (model.convergence (.quotient N (.nu Y)))
      (s+n,t+n,t+n-J) (finiteTargetLabel model Y N (s+n) (t+n) J y)
      (homotopyRegrade (by dsimp; omega) (by dsimp; omega)
        (finiteLevelNormalizedRepresentative X (normalizedExponent model.classicalTower f)
          N K s t c ≫ finiteExtensionMap model X Y f N))) :
    x ∈ cycles model X ((N:ℤ)-K) (s,t) ∧
      KIP126.ProofTools.Standard.LevelFiniteExtension X Y f (N-K+1) K n s t x y := by
  obtain ⟨hc,hx⟩ := finite_rho_lift_label_and_cycles X A N K hAN hKA s t x a ha c hρ
  exact ⟨hx,finite_level_extension_of_native_representative X Y f N K J (by omega)
    hJN n s t hn hJ x y c hc hf⟩

end
end KIP126.ProofTools.Internal.Mahowald
