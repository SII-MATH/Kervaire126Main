module

public import KIP126.ProofTools.MahowaldLeibniz
public import KIP126.ProofTools.GeneralizedMahowald.Coherence
public import KIP126.ProofTools.GeneralizedMahowald.Filtration
import all KIP126.ProofTools.MahowaldLeibniz.CommonCore
import all KIP126.ProofTools.MahowaldLeibniz.ClassicalComposition
import all KIP126.ProofTools.MahowaldLeibniz.TopTarget

import all KIP126.ProofTools.MahowaldLeibniz.FiniteCore
import all KIP126.ProofTools.MahowaldLeibniz.CoreAtLevel
import all KIP126.ProofTools.MahowaldLeibniz.PositiveBranches
import all KIP126.ProofTools.MahowaldLeibniz.PositiveHBranch
import all KIP126.ProofTools.MahowaldLeibniz.ClassicalStatements
import all KIP126.ProofTools.GeneralizedMahowald.Coherence

/-!
# Public finite-quotient and classical composition theorems

The finite core retains the three exhaustive normalization coordinates of
one selected triangle, the actual quotient representatives and their exact
images. The auxiliary coordinate maps are defined by the fixed model,
not supplied as extra hypotheses or freely chosen page operations.
-/

@[expose] section
namespace KIP126.ProofTools.Standard
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard KIP126.Literature
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
open KIP126.ProofTools.Internal.Leibniz
open KIP126.ProofTools.Internal.MahowaldLeibniz
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 4000000

/-- The exact additive criterion for lifting a member of the specified
correction family. The originally chosen representative need not lift. -/
public theorem representativeFamilyLift_iff
    {D A C : Type*} [AddCommGroup D] [AddCommGroup A] [AddCommGroup C]
    (q : D →+ A) (δ : A →+ C)
    (hexact : ∀ a : A, δ a = 0 ↔ ∃ d : D, q d = a)
    (V : AddSubgroup A) (a₀ : A) :
    (∃ v : A, v ∈ V ∧ ∃ d : D, q d = a₀ + v) ↔ δ a₀ ∈ V.map δ :=
  representative_family_has_lift_iff_boundary_mem q δ hexact V a₀

/-- Surjectivity of the actual graded h-maps through every higher layer
annihilates the entire ambiguity subgroup. The H filtration records the
actual normalized h shift. -/
public theorem finiteSurjectiveAmbiguityZero
    {A H B : Type*} [AddCommGroup A] [AddCommGroup H] [AddCommGroup B]
    (h : H →+ A) (f : A →+ B)
    (E : ℤ → AddSubgroup A) (L : ℤ → AddSubgroup H)
    (hL : Antitone L) (hfh : ∀ b : H, f (h b) = 0)
    (S eₕ : ℤ) (K : ℕ) (hK : 2 ≤ K)
    (hsurj : ∀ j : ℤ, 1 ≤ j → j < K → ∀ a : A, a ∈ E (S+j) →
      ∃ b : H, b ∈ L (S+j-eₕ) ∧ a-h b ∈ E (S+j+1))
    (hend : E (S+K) = ⊥) :
    ∀ a : A, a ∈ E (S+1) → f a = 0 := by
  intro a ha
  have hi := finite_level_surjectivity_image_eq h f E (fun k => L (k-eₕ))
    (fun i j hij => hL (by omega)) hfh S K hK hsurj hend a 0
    (by simpa only [sub_zero] using ha)
  simpa only [map_zero] using hi

/-- Collapse of the intermediate grades and zero action on the entire
last grade annihilate the ambiguity. The last source grade is allowed
to be nonzero and need not be an h-image. -/
public theorem finiteCollapsedAmbiguityZero
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (f : A →+ B) (E : ℤ → AddSubgroup A) (F : ℤ → AddSubgroup B)
    (S e_f : ℤ) (K : ℕ) (hK : 2 ≤ K)
    (hcollapse : ∀ j : ℤ, 1 ≤ j → j < (K:ℤ)-1 →
      E (S+j) ≤ E (S+j+1))
    (hlast : ∀ a : A, a ∈ E (S+K-1) → f a ∈ F (S+e_f+K))
    (htarget : F (S+e_f+K) = ⊥) :
    ∀ a : A, a ∈ E (S+1) → f a = 0 := by
  intro a ha
  have hi := finite_level_collapsed_image_eq (0 : ℤ →+ A) f E
    (fun _ => (⊥ : AddSubgroup ℤ)) (fun _ _ _ => le_rfl)
    (fun _ => by simp) S K hK hcollapse
    (fun b hb => by simpa only [htarget, AddSubgroup.mem_bot] using hlast b hb) a 0
    (by simpa only [sub_zero] using ha)
  simpa only [map_zero] using hi

public def FiniteQuotientFirstCoreStatement
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g +
      normalizedExponent model.classicalTower T.h = 1)
    (_hT : NormalizedTriangleCompatible model T he)
    (hf : normalizedExponent model.classicalTower T.f = 1)
    (_hg : normalizedExponent model.classicalTower T.g = 0)
    (_hh : normalizedExponent model.classicalTower T.h = 0) : Prop :=
  let biSuspensionHomEquiv (n w q : ℤ) (Q : SyntheticSpectrum) :
      BiHom n w (((SyntheticCategory.biShift (0, -q)).obj Q)⟦(1 : ℤ)⟧) ≃
        BiHom (n - 1) (w + q) Q := by
    let e : BiHom (n - 1) (w + q) Q ≃
        BiHom n w (((SyntheticCategory.biShift (0, -q)).obj Q)⟦(1 : ℤ)⟧) := by
      simpa only [sub_add_cancel, add_neg_cancel_right] using
        ((susp_invariance (n - 1) (w + q) 1 (-q) Q).trans
          (Iso.homCongr (Iso.refl _) (biSuspensionIso q Q)))
    exact e.symm
  let nativeFirstLabel (X : ClassicalObject) (s t : ℤ)
      (x : Ambient model X (s,t)) :
      BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) 1) :=
    firstLabel model X s t x ≫
      XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1
  let finiteCoefficientShiftClass (A : SyntheticSpectrum)
      (N c : ℕ) (hcN : c<N) (m w : ℤ)
      (a : BiHom m w (XModLambdaN A (N-c))) :
      BiHom m (w-c) (XModLambdaN A N) := by
    by_cases hc : c=0
    · subst c
      exact homotopyRegrade rfl (by simp) a
    · exact homotopyRegrade (by simp) (by simp [sub_eq_add_neg])
        (shiftHomotopyClass (0,-(c:ℤ)) (m,w) a) ≫
        ((model.quotients.tower A).triangle (show 0<c by omega) hcN).lambdaMap
  let finiteCoefficientInsert (A : SyntheticSpectrum)
      (c K : ℕ) (hK : 0<K) (m w : ℤ)
      (a : BiHom m w (XModLambdaN A K)) :
      BiHom m (w-c) (XModLambdaN A (c+K)) :=
    finiteCoefficientShiftClass A (c+K) c (by omega) m w
      (by simpa only [Nat.add_sub_cancel_left,SyntheticObject.obj] using a)
  let quotientUnshift (X : ClassicalObject) (δ p : ℤ × ℤ) (q : ℕ)
      (ε : XModLambdaN ((SyntheticCategory.biShift δ).obj
          (model.nu.functor.obj (X.obj model.auxiliary))) q ≅
        (SyntheticCategory.biShift δ).obj
          (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
      (a : BiHom (p+δ).1 (p+δ).2 (XModLambdaN ((SyntheticCategory.biShift δ).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) q)) :
      BiHom p.1 p.2 (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q) :=
    (SyntheticCategory.biShift_fullyFaithful δ).preimage
      ((SyntheticCategory.biShift_comp p δ).hom.app S_0_0 ≫ a ≫ ε.hom)
  let normalizedSuspensionNativeIso
      (T : TriangleData model.auxiliary)
      (he : (normalizedExponent model.classicalTower T.f : ℤ) +
        normalizedExponent model.classicalTower T.g +
        normalizedExponent model.classicalTower T.h = 1)
      (hf : normalizedExponent model.classicalTower T.f = 1) :
      ((normalizedTriangle model T he).obj₁⟦(1:ℤ)⟧) ≅
        model.nu.functor.obj ((ClassicalObject.shift 1 T.X).obj model.auxiliary) :=
    (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).symm.app _ ≪≫
      (SyntheticCategory.biShift_comp
        (0,(normalizedExponent model.classicalTower T.f:ℤ)) (1,0)).app _ ≪≫
      eqToIso (congrArg (fun p : ℤ×ℤ => (SyntheticCategory.biShift p).obj
        (model.nu.functor.obj (T.X.obj model.auxiliary)))
        (show (0,(normalizedExponent model.classicalTower T.f:ℤ))+(1,0)=(1,1)
          by ext <;> dsimp <;> omega)) ≪≫
      (model.nu.suspensionIso (T.X.obj model.auxiliary)).symm
  let rawMaySourceDesuspend
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
  ∀ (c q : ℕ) (hq : 0<q) (S V : ℤ)
    (u : Ambient model T.X (S,V)) (z : Ambient model T.Z (S,V+1))
    (v : Ambient model T.Y (S+q+1,(V+1)+q)),
    (model.classicalSuspension T.X).DesuspendsClass S (V+1)
      ((model.classical.map T.h).pageMap 2 (S,V+1) z) (by simpa using u) →
    HasDifferential (model.classical.obj (T.Z.obj model.auxiliary))
      (q+1) (S,V+1) (S+q+1,(V+1)+q) z
      ((model.classical.map T.g).pageMap 2 (S+q+1,(V+1)+q) v) →
    ∀ (ey : XModLambdaN ((normalizedTriangle model T he).obj₂⟦(1:ℤ)⟧) (q+1) ≅
      (XModLambdaN (normalizedTriangle model T he).obj₂ (q+1))⟦(1:ℤ)⟧),
    XModLambdaN.incl _ (q+1) ≫ ey.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ (q+1)) →
    ∀ (ε : XModLambdaN ((SyntheticCategory.biShift (1,1)).obj
      (model.nu.functor.obj (T.X.obj model.auxiliary))) (c+(q+1)) ≅
      (SyntheticCategory.biShift (1,1)).obj
        (XModLambdaN (model.nu.functor.obj (T.X.obj model.auxiliary)) (c+(q+1)))),
    XModLambdaN.incl _ (c+(q+1)) ≫ ε.hom =
      (SyntheticCategory.biShift (1,1)).map (XModLambdaN.incl _ (c+(q+1))) →
    let N := normalizedTriangle model T he
    let b := (biSuspensionHomEquiv ((V+1)-S) (V+1) (q:ℤ)
      (XModLambdaN (model.nu.functor.obj (T.Y.obj model.auxiliary)) 1)).symm
        (homotopyRegrade (show ((V+1)+q)-(S+q+1)=((V+1)-S)-1 by omega) rfl
          (nativeFirstLabel T.Y (S+q+1) ((V+1)+q) v))
    let ly : (SyntheticCategory.biShift (0,-(q:ℤ))).obj (XModLambdaN N.obj₂ 1) ⟶
        XModLambdaN N.obj₂ (q+1) := by
      simpa only [show q.succ-q=1 by omega] using
        ((model.quotients.tower N.obj₂).triangle hq (Nat.lt_succ_self q)).lambdaMap
    let target :=
      homotopyRegrade (show (V+1)-S=V-S+1 by omega) (show (V+1)-c=V-c+1 by omega)
        (finiteCoefficientInsert (N.obj₂⟦(1:ℤ)⟧) c (q+1) (by omega) ((V+1)-S) (V+1)
          ((-(b ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map ly)) ≫ ey.inv))
    (∃ a : BiHom (V-S+1) (V-c+1) (XModLambdaN (N.obj₁⟦(1:ℤ)⟧) (c+(q+1))),
      Detects (model.convergence (.quotient (c+(q+1)) (.nu T.X)))
        (S,V,V-c) (finiteTargetLabel model T.X (c+(q+1)) S V c u)
        (rawMaySourceDesuspend T he hf (c+(q+1)) c S V ε a) ∧
      a ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map N.mor₁)
        (c+(q+1)) = target ∧
      IsCycle model T.X (q+1) (S,V) u) ∧
    ((∀ a : BiHom (V-S+1) (V-c+1) (XModLambdaN (N.obj₁⟦(1:ℤ)⟧) (c+(q+1))),
      FiltrationAtLeast model.syntheticTower (S+1)
        (rawMaySourceDesuspend T he hf (c+(q+1)) c S V ε a) →
      a ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map N.mor₁)
        (c+(q+1)) = 0) →
      ∀ d : BiHom (V-S+1) (V-c+1) (XModLambdaN (N.obj₁⟦(1:ℤ)⟧) (c+(q+1))),
      Detects (model.convergence (.quotient (c+(q+1)) (.nu T.X)))
        (S,V,V-c) (finiteTargetLabel model T.X (c+(q+1)) S V c u)
        (rawMaySourceDesuspend T he hf (c+(q+1)) c S V ε d) →
      d ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map N.mor₁)
        (c+(q+1)) = target)

public def FiniteQuotientSecondCoreStatement
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ)+
      normalizedExponent model.classicalTower T.g+normalizedExponent model.classicalTower T.h=1)
    (_hT : NormalizedTriangleCompatible model T he)
    (hf : normalizedExponent model.classicalTower T.f=0)
    (hg : normalizedExponent model.classicalTower T.g=1)
    (_hh : normalizedExponent model.classicalTower T.h=0) : Prop :=
  let biSuspensionHomEquiv (n w q : ℤ) (Q : SyntheticSpectrum) :
      BiHom n w (((SyntheticCategory.biShift (0, -q)).obj Q)⟦(1 : ℤ)⟧) ≃
        BiHom (n - 1) (w + q) Q := by
    let e : BiHom (n - 1) (w + q) Q ≃
        BiHom n w (((SyntheticCategory.biShift (0, -q)).obj Q)⟦(1 : ℤ)⟧) := by
      simpa only [sub_add_cancel, add_neg_cancel_right] using
        ((susp_invariance (n - 1) (w + q) 1 (-q) Q).trans
          (Iso.homCongr (Iso.refl _) (biSuspensionIso q Q)))
    exact e.symm
  let nativeFirstLabel (X : ClassicalObject) (s t : ℤ)
      (x : Ambient model X (s,t)) :
      BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) 1) :=
    firstLabel model X s t x ≫
      XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1
  let finiteCoefficientShiftClass (A : SyntheticSpectrum)
      (N c : ℕ) (hcN : c<N) (m w : ℤ)
      (a : BiHom m w (XModLambdaN A (N-c))) :
      BiHom m (w-c) (XModLambdaN A N) := by
    by_cases hc : c=0
    · subst c
      exact homotopyRegrade rfl (by simp) a
    · exact homotopyRegrade (by simp) (by simp [sub_eq_add_neg])
        (shiftHomotopyClass (0,-(c:ℤ)) (m,w) a) ≫
        ((model.quotients.tower A).triangle (show 0<c by omega) hcN).lambdaMap
  let finiteCoefficientInsert (A : SyntheticSpectrum)
      (c K : ℕ) (hK : 0<K) (m w : ℤ)
      (a : BiHom m w (XModLambdaN A K)) :
      BiHom m (w-c) (XModLambdaN A (c+K)) :=
    finiteCoefficientShiftClass A (c+K) c (by omega) m w
      (by simpa only [Nat.add_sub_cancel_left,SyntheticObject.obj] using a)
  let positiveFirstQuotientOperation (X Y : ClassicalObject)
      (F : (SyntheticCategory.biShift (0,1)).obj
        (model.nu.functor.obj (X.obj model.auxiliary)) ⟶
          model.nu.functor.obj (Y.obj model.auxiliary))
      (s t : ℤ) (x : Ambient model X (s,t)) : Ambient model Y (s+1,t+1) :=
    model.firstQuotient Y 0 (s+1) (t+1)
      (homotopyRegrade (by omega) (by omega)
        ((model.firstQuotient X 1 s t).symm x ≫ XModLambdaN.map F 1 ≫
          XModLambdaN.map (SyntheticCategory.biShift_zero.inv.app _) 1))
  let zero_positive_iso (A : SyntheticSpectrum) (k : ℕ) (hk : k=0) :
      (SyntheticCategory.biShift (0,(k:ℤ))).obj A ≅ A :=
    eqToIso (congrArg (fun j : ℕ => (SyntheticCategory.biShift (0,(j:ℤ))).obj A) hk) ≪≫
      SyntheticCategory.biShift_zero.app A
  let normalizedSuspensionZeroIso (T : TriangleData model.auxiliary)
      (he : (normalizedExponent model.classicalTower T.f : ℤ)+
        normalizedExponent model.classicalTower T.g+normalizedExponent model.classicalTower T.h=1)
      (hf : normalizedExponent model.classicalTower T.f=0) :
      ((normalizedTriangle model T he).obj₁⟦(1:ℤ)⟧) ≅
        (SyntheticCategory.biShift (1,0)).obj (model.nu.functor.obj (T.X.obj model.auxiliary)) :=
    (shiftFunctor SyntheticSpectrum (1:ℤ)).mapIso
      (zero_positive_iso (model.nu.functor.obj (T.X.obj model.auxiliary)) _ hf) ≪≫
        (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).symm.app _
  let quotientUnshift (X : ClassicalObject) (δ p : ℤ × ℤ) (q : ℕ)
      (ε : XModLambdaN ((SyntheticCategory.biShift δ).obj
          (model.nu.functor.obj (X.obj model.auxiliary))) q ≅
        (SyntheticCategory.biShift δ).obj
          (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
      (a : BiHom (p+δ).1 (p+δ).2 (XModLambdaN ((SyntheticCategory.biShift δ).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) q)) :
      BiHom p.1 p.2 (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q) :=
    (SyntheticCategory.biShift_fullyFaithful δ).preimage
      ((SyntheticCategory.biShift_comp p δ).hom.app S_0_0 ≫ a ≫ ε.hom)
  let positiveHSourceDesuspend
      (T : TriangleData model.auxiliary)
      (he : (normalizedExponent model.classicalTower T.f : ℤ)+
        normalizedExponent model.classicalTower T.g+normalizedExponent model.classicalTower T.h=1)
      (hf : normalizedExponent model.classicalTower T.f=0)
      (N c : ℕ) (s t : ℤ)
      (ε : XModLambdaN ((SyntheticCategory.biShift (1,0)).obj
        (model.nu.functor.obj (T.X.obj model.auxiliary))) N ≅
        (SyntheticCategory.biShift (1,0)).obj
          (XModLambdaN (model.nu.functor.obj (T.X.obj model.auxiliary)) N))
      (a : BiHom (t-s) (t-c)
        (XModLambdaN ((normalizedTriangle model T he).obj₁⟦(1:ℤ)⟧) N)) :
      BiHom (t-(s+1)) (t-c) (XModLambdaN (model.nu.functor.obj (T.X.obj model.auxiliary)) N) :=
    quotientUnshift T.X (1,0) (t-(s+1),t-c) N ε
      (homotopyRegrade (by dsimp; omega) (by dsimp; omega)
        (a ≫ XModLambdaN.map (normalizedSuspensionZeroIso T he hf).hom N))
  let normalizedSecondPositiveMap
      (T : TriangleData model.auxiliary)
      (hg : normalizedExponent model.classicalTower T.g = 1) :
      (SyntheticCategory.biShift (0,1)).obj
        (model.nu.functor.obj (T.Y.obj model.auxiliary)) ⟶
          model.nu.functor.obj (T.Z.obj model.auxiliary) :=
    eqToHom (congrArg (fun k : ℕ => (SyntheticCategory.biShift (0,(k:ℤ))).obj
      (model.nu.functor.obj (T.Y.obj model.auxiliary))) hg.symm) ≫
      (model.normalizedMap T.Y T.Z T.g).map
  ∀ (c q : ℕ) (_hq : 0<q) (s t : ℤ)
    (z : Ambient model T.Z (s+1,t+1)) (u : Ambient model T.X (s+1,t))
    (v : Ambient model T.Y (s+q+1,t+q)),
    (model.classicalSuspension T.X).DesuspendsClass (s+1) (t+1)
      ((model.classical.map T.h).pageMap 2 (s+1,t+1) z) (by simpa using u) →
    HasDifferential (model.classical.obj (T.Z.obj model.auxiliary))
      (q+1) (s+1,t+1) ((s+q+1)+1,(t+q)+1) z
      (positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg)
        (s+q+1) (t+q) v) →
    ∀ (ey : XModLambdaN ((normalizedTriangle model T he).obj₂⟦(1:ℤ)⟧) (q+1) ≅
      (XModLambdaN (normalizedTriangle model T he).obj₂ (q+1))⟦(1:ℤ)⟧),
    XModLambdaN.incl _ (q+1) ≫ ey.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ (q+1)) →
    ∀ (ε : XModLambdaN ((SyntheticCategory.biShift (1,0)).obj
      (model.nu.functor.obj (T.X.obj model.auxiliary))) (c+(q+1)) ≅
      (SyntheticCategory.biShift (1,0)).obj
        (XModLambdaN (model.nu.functor.obj (T.X.obj model.auxiliary)) (c+(q+1)))),
    XModLambdaN.incl _ (c+(q+1)) ≫ ε.hom =
      (SyntheticCategory.biShift (1,0)).map (XModLambdaN.incl _ (c+(q+1))) →
    let V := normalizedTriangle model T he
    let b := (biSuspensionHomEquiv (t-s) t (q:ℤ)
      (XModLambdaN (model.nu.functor.obj (T.Y.obj model.auxiliary)) 1)).symm
        (homotopyRegrade (show (t+q)-(s+q+1)=(t-s)-1 by omega) rfl
          (nativeFirstLabel T.Y (s+q+1) (t+q) v))
    let ly : (SyntheticCategory.biShift (0,-(q:ℤ))).obj (XModLambdaN V.obj₂ 1) ⟶
        XModLambdaN V.obj₂ (q+1) := by
      simpa only [show q.succ-q=1 by omega] using
        ((model.quotients.tower V.obj₂).triangle _hq (Nat.lt_succ_self q)).lambdaMap
    let target := finiteCoefficientInsert (V.obj₂⟦(1:ℤ)⟧) c (q+1) (by omega) (t-s) t
      ((-(b ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map ly)) ≫ ey.inv)
    IsCycle model T.X (q+1) (s+1,t) u ∧
    ∃ a : BiHom (t-s) (t-c) (XModLambdaN (V.obj₁⟦(1:ℤ)⟧) (c+(q+1))),
      Detects (model.convergence (.quotient (c+(q+1)) (.nu T.X)))
        (s+1,t,t-c) (finiteTargetLabel model T.X (c+(q+1)) (s+1) t c u)
        (positiveHSourceDesuspend T he hf (c+(q+1)) c s t ε a) ∧
      a ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map V.mor₁)
        (c+(q+1)) = target ∧
      ((∀ d : BiHom (t-(s+1)) (t-c)
          (XModLambdaN (model.nu.functor.obj (T.X.obj model.auxiliary)) (c+(q+1))),
        FiltrationAtLeast model.syntheticTower (s+2) d →
          d ≫ XModLambdaN.map (model.nu.functor.map T.f) (c+(q+1)) = 0) →
        ∀ d : BiHom (t-s) (t-c) (XModLambdaN (V.obj₁⟦(1:ℤ)⟧) (c+(q+1))),
        Detects (model.convergence (.quotient (c+(q+1)) (.nu T.X)))
          (s+1,t,t-c) (finiteTargetLabel model T.X (c+(q+1)) (s+1) t c u)
          (positiveHSourceDesuspend T he hf (c+(q+1)) c s t ε d) →
        d ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map V.mor₁)
          (c+(q+1)) = target)

public def FiniteQuotientThirdCoreStatement
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g +
      normalizedExponent model.classicalTower T.h = 1)
    (_hT : NormalizedTriangleCompatible model T he)
    (hf : normalizedExponent model.classicalTower T.f = 0)
    (_hg : normalizedExponent model.classicalTower T.g = 0)
    (hh : normalizedExponent model.classicalTower T.h = 1)
 : Prop :=
  let biSuspensionHomEquiv (n w q : ℤ) (Q : SyntheticSpectrum) :
      BiHom n w (((SyntheticCategory.biShift (0, -q)).obj Q)⟦(1 : ℤ)⟧) ≃
        BiHom (n - 1) (w + q) Q := by
    let e : BiHom (n - 1) (w + q) Q ≃
        BiHom n w (((SyntheticCategory.biShift (0, -q)).obj Q)⟦(1 : ℤ)⟧) := by
      simpa only [sub_add_cancel, add_neg_cancel_right] using
        ((susp_invariance (n - 1) (w + q) 1 (-q) Q).trans
          (Iso.homCongr (Iso.refl _) (biSuspensionIso q Q)))
    exact e.symm
  let nativeFirstLabel (X : ClassicalObject) (s t : ℤ)
      (x : Ambient model X (s,t)) :
      BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) 1) :=
    firstLabel model X s t x ≫
      XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1
  let finiteCoefficientShiftClass (A : SyntheticSpectrum)
      (N c : ℕ) (hcN : c<N) (m w : ℤ)
      (a : BiHom m w (XModLambdaN A (N-c))) :
      BiHom m (w-c) (XModLambdaN A N) := by
    by_cases hc : c=0
    · subst c
      exact homotopyRegrade rfl (by simp) a
    · exact homotopyRegrade (by simp) (by simp [sub_eq_add_neg])
        (shiftHomotopyClass (0,-(c:ℤ)) (m,w) a) ≫
        ((model.quotients.tower A).triangle (show 0<c by omega) hcN).lambdaMap
  let finiteCoefficientInsert (A : SyntheticSpectrum)
      (c K : ℕ) (hK : 0<K) (m w : ℤ)
      (a : BiHom m w (XModLambdaN A K)) :
      BiHom m (w-c) (XModLambdaN A (c+K)) :=
    finiteCoefficientShiftClass A (c+K) c (by omega) m w
      (by simpa only [Nat.add_sub_cancel_left,SyntheticObject.obj] using a)
  let positiveFirstQuotientOperation (X Y : ClassicalObject)
      (F : (SyntheticCategory.biShift (0,1)).obj
        (model.nu.functor.obj (X.obj model.auxiliary)) ⟶
          model.nu.functor.obj (Y.obj model.auxiliary))
      (s t : ℤ) (x : Ambient model X (s,t)) : Ambient model Y (s+1,t+1) :=
    model.firstQuotient Y 0 (s+1) (t+1)
      (homotopyRegrade (by omega) (by omega)
        ((model.firstQuotient X 1 s t).symm x ≫ XModLambdaN.map F 1 ≫
          XModLambdaN.map (SyntheticCategory.biShift_zero.inv.app _) 1))
  let zero_positive_iso (A : SyntheticSpectrum) (k : ℕ) (hk : k=0) :
      (SyntheticCategory.biShift (0,(k:ℤ))).obj A ≅ A :=
    eqToIso (congrArg (fun j : ℕ => (SyntheticCategory.biShift (0,(j:ℤ))).obj A) hk) ≪≫
      SyntheticCategory.biShift_zero.app A
  let normalizedSuspensionZeroIso (T : TriangleData model.auxiliary)
      (he : (normalizedExponent model.classicalTower T.f : ℤ)+
        normalizedExponent model.classicalTower T.g+normalizedExponent model.classicalTower T.h=1)
      (hf : normalizedExponent model.classicalTower T.f=0) :
      ((normalizedTriangle model T he).obj₁⟦(1:ℤ)⟧) ≅
        (SyntheticCategory.biShift (1,0)).obj (model.nu.functor.obj (T.X.obj model.auxiliary)) :=
    (shiftFunctor SyntheticSpectrum (1:ℤ)).mapIso
      (zero_positive_iso (model.nu.functor.obj (T.X.obj model.auxiliary)) _ hf) ≪≫
        (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).symm.app _
  let quotientUnshift (X : ClassicalObject) (δ p : ℤ × ℤ) (q : ℕ)
      (ε : XModLambdaN ((SyntheticCategory.biShift δ).obj
          (model.nu.functor.obj (X.obj model.auxiliary))) q ≅
        (SyntheticCategory.biShift δ).obj
          (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
      (a : BiHom (p+δ).1 (p+δ).2 (XModLambdaN ((SyntheticCategory.biShift δ).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) q)) :
      BiHom p.1 p.2 (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q) :=
    (SyntheticCategory.biShift_fullyFaithful δ).preimage
      ((SyntheticCategory.biShift_comp p δ).hom.app S_0_0 ≫ a ≫ ε.hom)
  let positiveHSourceDesuspend
      (T : TriangleData model.auxiliary)
      (he : (normalizedExponent model.classicalTower T.f : ℤ)+
        normalizedExponent model.classicalTower T.g+normalizedExponent model.classicalTower T.h=1)
      (hf : normalizedExponent model.classicalTower T.f=0)
      (N c : ℕ) (s t : ℤ)
      (ε : XModLambdaN ((SyntheticCategory.biShift (1,0)).obj
        (model.nu.functor.obj (T.X.obj model.auxiliary))) N ≅
        (SyntheticCategory.biShift (1,0)).obj
          (XModLambdaN (model.nu.functor.obj (T.X.obj model.auxiliary)) N))
      (a : BiHom (t-s) (t-c)
        (XModLambdaN ((normalizedTriangle model T he).obj₁⟦(1:ℤ)⟧) N)) :
      BiHom (t-(s+1)) (t-c) (XModLambdaN (model.nu.functor.obj (T.X.obj model.auxiliary)) N) :=
    quotientUnshift T.X (1,0) (t-(s+1),t-c) N ε
      (homotopyRegrade (by dsimp; omega) (by dsimp; omega)
        (a ≫ XModLambdaN.map (normalizedSuspensionZeroIso T he hf).hom N))
  let positiveHMap (T : TriangleData model.auxiliary)
      (hh : normalizedExponent model.classicalTower T.h=1) :
      (SyntheticCategory.biShift (0,1)).obj (model.nu.functor.obj (T.Z.obj model.auxiliary)) ⟶
        model.nu.functor.obj ((ClassicalObject.shift 1 T.X).obj model.auxiliary) := by
    simpa only [hh,Nat.cast_one] using (model.normalizedMap T.Z (.shift 1 T.X) T.h).map
  ∀ (c q : ℕ) (hq : 0<q) (s t : ℤ)
    (z : Ambient model T.Z (s,t)) (u : Ambient model T.X (s+1,t))
    (v : Ambient model T.Y (s+q+1,t+q))
    (hu : (model.classicalSuspension T.X).DesuspendsClass (s+1) (t+1)
      (positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh) s t z)
      (by simpa using u))
    (hd : HasDifferential (model.classical.obj (T.Z.obj model.auxiliary))
      (q+1) (s,t) (s+q+1,t+q) z
      ((model.classical.map T.g).pageMap 2 (s+q+1,t+q) v))
    (ey : XModLambdaN ((normalizedTriangle model T he).obj₂⟦(1:ℤ)⟧) (q+1) ≅
      (XModLambdaN (normalizedTriangle model T he).obj₂ (q+1))⟦(1:ℤ)⟧)
    (hey : XModLambdaN.incl _ (q+1) ≫ ey.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ (q+1)))
    (εN : XModLambdaN ((SyntheticCategory.biShift (1,0)).obj
      (model.nu.functor.obj (T.X.obj model.auxiliary))) (c+(q+1)) ≅
      (SyntheticCategory.biShift (1,0)).obj
        (XModLambdaN (model.nu.functor.obj (T.X.obj model.auxiliary)) (c+(q+1))))
    (hεN : XModLambdaN.incl _ (c+(q+1)) ≫ εN.hom =
      (SyntheticCategory.biShift (1,0)).map (XModLambdaN.incl _ (c+(q+1)))),
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
      Detects (model.convergence (.quotient (c+(q+1)) (.nu T.X)))
        (s+1,t,t-c) (finiteTargetLabel model T.X (c+(q+1)) (s+1) t c u)
        (positiveHSourceDesuspend T he hf (c+(q+1)) c s t εN a) ∧
      a ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map V.mor₁) (c+(q+1)) =
        finiteCoefficientInsert (V.obj₂⟦(1:ℤ)⟧) c (q+1) (by omega) (t-s) t
          ((-(b ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map ly)) ≫ ey.inv) ∧
      IsCycle model T.X (q+1) (s+1,t) u ∧
      ((∀ e : BiHom (t-s) (t-c) (XModLambdaN (V.obj₁⟦(1:ℤ)⟧) (c+(q+1))),
        FiltrationAtLeast model.syntheticTower ((s+1)+1)
          (positiveHSourceDesuspend T he hf (c+(q+1)) c s t εN e) →
        e ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map V.mor₁) (c+(q+1))=0) →
        ∀ d : BiHom (t-s) (t-c) (XModLambdaN (V.obj₁⟦(1:ℤ)⟧) (c+(q+1))),
          Detects (model.convergence (.quotient (c+(q+1)) (.nu T.X)))
            (s+1,t,t-c) (finiteTargetLabel model T.X (c+(q+1)) (s+1) t c u)
            (positiveHSourceDesuspend T he hf (c+(q+1)) c s t εN d) →
          d ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map V.mor₁) (c+(q+1)) =
            a ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map V.mor₁) (c+(q+1)))

/-- The complete finite-quotient core in the three exhaustive exponent
positions, together with the exact identification of each signed
coefficient output with the selected highest-layer inclusion. All levels,
coherent shift comparisons and prescribed labels are quantified; no
representative producer, output survival or infinite lift is assumed. -/
public def FiniteQuotientMahowaldLeibnizCoreStatement
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g +
      normalizedExponent model.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible model T he) : Prop :=
  let exactTopTarget : Prop :=
    let biSuspensionHomEquiv (n w q : ℤ) (Q : SyntheticSpectrum) :
        BiHom n w (((SyntheticCategory.biShift (0, -q)).obj Q)⟦(1 : ℤ)⟧) ≃
          BiHom (n - 1) (w + q) Q := by
      let e : BiHom (n - 1) (w + q) Q ≃
          BiHom n w (((SyntheticCategory.biShift (0, -q)).obj Q)⟦(1 : ℤ)⟧) := by
        simpa only [sub_add_cancel, add_neg_cancel_right] using
          ((susp_invariance (n - 1) (w + q) 1 (-q) Q).trans
            (Iso.homCongr (Iso.refl _) (biSuspensionIso q Q)))
      exact e.symm
    let nativeFirstLabel (X : ClassicalObject) (s t : ℤ)
        (x : Ambient model X (s,t)) :
        BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) 1) :=
      firstLabel model X s t x ≫
        XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1
    let finiteCoefficientShiftClass (A : SyntheticSpectrum)
        (N c : ℕ) (hcN : c<N) (m w : ℤ)
        (a : BiHom m w (XModLambdaN A (N-c))) :
        BiHom m (w-c) (XModLambdaN A N) := by
      by_cases hc : c=0
      · subst c
        exact homotopyRegrade rfl (by simp) a
      · exact homotopyRegrade (by simp) (by simp [sub_eq_add_neg])
          (shiftHomotopyClass (0,-(c:ℤ)) (m,w) a) ≫
          ((model.quotients.tower A).triangle (show 0<c by omega) hcN).lambdaMap
    let finiteCoefficientInsert (A : SyntheticSpectrum)
        (c K : ℕ) (hK : 0<K) (m w : ℤ)
        (a : BiHom m w (XModLambdaN A K)) :
        BiHom m (w-c) (XModLambdaN A (c+K)) :=
      finiteCoefficientShiftClass A (c+K) c (by omega) m w
        (by simpa only [Nat.add_sub_cancel_left,SyntheticObject.obj] using a)
    let oneInclusionCast (A B : SyntheticSpectrum) (d n : ℕ) (hn : n=1)
        (l : (SyntheticCategory.biShift (0,-(d:ℤ))).obj (XModLambdaN A n) ⟶ B) :
        (SyntheticCategory.biShift (0,-(d:ℤ))).obj (XModLambdaN A 1) ⟶ B := hn ▸ l
    let finiteTopInclusion (A : SyntheticSpectrum) (d : ℕ) (hd : 0 < d) :
        (SyntheticCategory.biShift (0,-(d:ℤ))).obj (XModLambdaN A 1) ⟶
          XModLambdaN A (d+1) :=
      oneInclusionCast A _ d ((d+1)-d) (by omega)
        ((model.quotients.tower A).triangle hd (Nat.lt_succ_self d)).lambdaMap
    let finiteTopOfFirst (A : SyntheticSpectrum) (d : ℕ) (hd : 0 < d)
        (m w : ℤ) (a : BiHom m w (XModLambdaN A 1)) :
        BiHom m (w-d) (XModLambdaN A (d+1)) :=
      homotopyRegrade (by simp) (by simp [sub_eq_add_neg])
        (shiftHomotopyClass (0,-(d:ℤ)) (m,w) a) ≫ finiteTopInclusion A d hd
    let finiteTopLabel (X : ClassicalObject) (d : ℕ) (hd : 0 < d)
        (s t : ℤ) (x : Ambient model X (s,t)) :
        BiHom (t-s) (t-d)
          (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (d+1)) :=
      finiteTopOfFirst _ d hd (t-s) t (nativeFirstLabel X s t x)
    let finiteTopLabelAtWeight (X : ClassicalObject) (d : ℕ) (hd : 0<d)
        (N : ℕ) (hN : d+1=N) (s t w : ℤ) (hw : t-d=w)
        (x : Ambient model X (s,t)) :
        BiHom (t-s) w (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) N) :=
      hN ▸ homotopyRegrade rfl hw (finiteTopLabel X d hd s t x)
    let finiteMayTopLabel (X : ClassicalObject) (c q : ℕ) (hq : 0<q)
        (s t : ℤ) (v : Ambient model X (s+q+1,t+q)) :
        BiHom ((t-s)-1) (t-c)
          (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (c+(q+1))) :=
      homotopyRegrade (by omega) rfl
        (finiteTopLabelAtWeight X (c+q) (by omega) (c+(q+1)) (by omega)
          (s+q+1) (t+q) (t-c) (by omega) v)
    let ordinarySuspendedRepresentative (A : SyntheticSpectrum) (m w : ℤ)
        (a : BiHom (m-1) w A) : BiHom m w (A⟦(1:ℤ)⟧) :=
      homotopyRegrade (by dsimp; omega) (by simp)
        (shiftHomotopyClass (1,0) (m-1,w) a) ≫
          (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).hom.app A
    ∀ (X : ClassicalObject) (c q : ℕ) (hq : 0<q) (s t : ℤ)
      (v : Ambient model X (s+q+1,t+q))
      (en : XModLambdaN ((model.nu.functor.obj (X.obj model.auxiliary))⟦(1:ℤ)⟧) (q+1) ≅
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (q+1))⟦(1:ℤ)⟧)
      (eN : XModLambdaN ((model.nu.functor.obj (X.obj model.auxiliary))⟦(1:ℤ)⟧) (c+(q+1)) ≅
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (c+(q+1)))⟦(1:ℤ)⟧)
      (hen : XModLambdaN.incl _ (q+1)≫en.hom=
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ (q+1)))
      (heN : XModLambdaN.incl _ (c+(q+1))≫eN.hom=
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ (c+(q+1)))),
      let b := (biSuspensionHomEquiv (t-s) t (q:ℤ)
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) 1)).symm
          (homotopyRegrade (show (t+q)-(s+q+1)=(t-s)-1 by omega) rfl
            (nativeFirstLabel X (s+q+1) (t+q) v))
      let ly : (SyntheticCategory.biShift (0,-(q:ℤ))).obj
          (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) 1) ⟶
          XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (q+1) := by
        simpa only [show q.succ-q=1 by omega] using
          ((model.quotients.tower _).triangle hq (Nat.lt_succ_self q)).lambdaMap
      finiteCoefficientInsert _ c (q+1) (by omega) (t-s) t
          ((-(b≫(shiftFunctor SyntheticSpectrum (1:ℤ)).map ly))≫en.inv)≫eN.hom =
        ordinarySuspendedRepresentative _ (t-s) (t-c) (finiteMayTopLabel X c q hq s t v)
  ((∀ hf hg hh, FiniteQuotientFirstCoreStatement T he hT hf hg hh) ∧
  (∀ hf hg hh, FiniteQuotientSecondCoreStatement T he hT hf hg hh) ∧
  (∀ hf hg hh, FiniteQuotientThirdCoreStatement T he hT hf hg hh)) ∧ exactTopTarget

/-- The common finite-quotient Mahowald theorem at every lambda level.
Its hypotheses are the actual classical differential and triangle
compatibility; its conclusion includes the original source cycle and
exact image of every same-label representative under ambiguity annihilation. -/
public theorem finiteQuotientMahowaldLeibnizCore
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g +
      normalizedExponent model.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible model T he) :
    FiniteQuotientMahowaldLeibnizCoreStatement T he hT := by
  refine ⟨finite_quotient_mahowald_leibniz_core T he hT, ?_⟩
  exact finite_may_signed_target_eq_top_at_level

public def normalizedClassicalOperation (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (s t : ℤ) (x : Ambient model X (s,t)) :
    Ambient model Y (s+normalizedExponent model.classicalTower f,
      t+normalizedExponent model.classicalTower f) :=
  model.firstQuotient Y 0
    (s+normalizedExponent model.classicalTower f)
    (t+normalizedExponent model.classicalTower f)
    (homotopyRegrade (by omega) (by omega)
      ((model.firstQuotient X (normalizedExponent model.classicalTower f) s t).symm x ≫
        XModLambdaN.map (model.normalizedMap X Y f).map 1 ≫
        XModLambdaN.map (SyntheticCategory.biShift_zero.inv.app _) 1))

public def ClassicalNCCompositionStatement
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g +
      normalizedExponent model.classicalTower T.h = 1) : Prop :=
  let classicalLabelRegrade {X : ClassicalObject} {p q : ℤ×ℤ}
      (h : p=q) (x : Ambient model X p) : Ambient model X q := h ▸ x
  let ef := normalizedExponent model.classicalTower T.f
  let eg := normalizedExponent model.classicalTower T.g
  let eh := normalizedExponent model.classicalTower T.h
  ∀ (_hT : NormalizedTriangleCompatible model T he)
    (R K : ℕ), 2 ≤ R → 2 ≤ K → ∀ (s t : ℤ)
    (x : Ambient model T.X (s,t))
    (z : Ambient model T.Z (s+R-eh,t+R-eh))
    (v : Ambient model T.Y (s+R+ef+K-1,t+R+ef+K-2)),
    IsCycle model T.X ((R:ℤ)-1) (s,t) x →
    IsCycle model T.Z ((K:ℤ)-1) (s+R-eh,t+R-eh) z →
    (∃ u : Ambient model T.X (s+R,t+R-1),
      (model.classicalSuspension T.X).DesuspendsClass (s+R) (t+R)
        (classicalLabelRegrade (X := .shift 1 T.X) (q := (s+R,t+R))
          (by dsimp only [eh]; ext <;> dsimp only [Prod.fst,Prod.snd] <;> omega)
          (normalizedClassicalOperation T.Z (.shift 1 T.X) T.h
            (s+R-eh) (t+R-eh) z)) u ∧
      DifferentialAt model T.X R (s,t) (s+R,t+R-1) x u) →
    DifferentialAt model T.Z K (s+R-eh,t+R-eh)
      (s+R-eh+K,t+R-eh+K-1) z
      (classicalLabelRegrade (X := T.Z) (q := (s+R-eh+K,t+R-eh+K-1)) (by
          dsimp only [ef,eg,eh]
          ext <;> dsimp only [Prod.fst,Prod.snd] <;> omega)
        (normalizedClassicalOperation T.Y T.Z T.g
          (s+R+ef+K-1) (t+R+ef+K-2) v)) →
    (∀ j : ℕ, 1 ≤ j → j < K-1 →
      cycles model T.X ((K:ℤ)-j) (s+R+j,t+R+j-1) ≤
        boundaries model T.X ((R:ℤ)+j-1) (s+R+j,t+R+j-1)) →
    (∀ a : Ambient model T.X (s+R+K-1,t+R+K-2),
      normalizedClassicalOperation T.X T.Y T.f
        (s+R+K-1) (t+R+K-2) a ∈
      boundaries model T.Y ((R:ℤ)+K-2)
        ((s+R+K-1)+ef,(t+R+K-2)+ef)) →
    let y := normalizedClassicalOperation T.X T.Y T.f s t x
    IsCycle model T.Y ((R:ℤ)+K-2) (s+ef,t+ef) y ∧
      DifferentialAt model T.Y ((R:ℤ)+K-1) (s+ef,t+ef)
        (s+R+ef+K-1,t+R+ef+K-2) y v

/-- The PDF/NC classical composition theorem, including all three
positions of the positive normalization exponent, the complete last-layer
NC2 condition and the specified output differential. -/
public theorem classicalNCComposition
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g +
      normalizedExponent model.classicalTower T.h = 1) :
    ClassicalNCCompositionStatement T he :=
  classical_nc_composition T he

/-- Finite-layer surjectivity proves the already public fixed-model
composition proposition. The output is the selected first-quotient
boundary; no comparison to a separately specified Ext boundary is asserted. -/
public theorem finiteLayerSurjectivityMahowaldLeibniz
    (T : TriangleData model.auxiliary)
    (hf : normalizedExponent model.classicalTower T.f = 1)
    (hg : normalizedExponent model.classicalTower T.g = 0)
    (hh : normalizedExponent model.classicalTower T.h = 0) :
    FiniteLayerSurjectivityMahowaldLeibnizStatement T hf hg hh :=
  finite_layer_surj_statement T hf hg hh

end
end KIP126.ProofTools.Standard
