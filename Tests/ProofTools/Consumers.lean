module

import KIP126.ProofTools

/-! The fixed tools preserve genuine page, cycle, extension, triangle and
crossing hypotheses; their callers never supply upstream result packages. -/
namespace Tests.ProofTools
open CategoryTheory KIP126.StableHomotopy
open KIP126.Kervaire.Route KIP126.ProofTools
open KIP126.AdamsSynthetic
open KIP126.AdamsSynthetic.Standard (model)

example (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary) :
    FinitePageExtensionStretchingLaw model X Y f :=
  KIP126.ProofTools.Standard.finitePageExtensionStretching X Y f

example (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary) :
    GeneralizedLeibnizLaw model X Y f :=
  KIP126.ProofTools.Standard.generalizedLeibniz X Y f

example (T : TriangleData model.auxiliary) : GeneralizedMahowaldLaw model T :=
  KIP126.ProofTools.Standard.generalizedMahowald T

example (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (rEarlier rLater : ℕ) (n s t : ℤ)
    (x : Ambient model X (s,t)) (y : Ambient model Y (s+n,t+n))
    (hr : 2 ≤ rEarlier) (hle : rEarlier ≤ rLater)
    (hn : (normalizedExponent model.classicalTower f : ℤ) ≤ n)
    (hnUpper : n ≤ (rEarlier : ℤ)-2+normalizedExponent model.classicalTower f)
    (hx : IsCycle model X ((rLater : ℤ)-1) (s,t) x)
    (hy : IsCycle model Y ((rLater : ℤ)-1-n+normalizedExponent model.classicalTower f)
      (s+n,t+n) y)
    (hW : FiniteExtension model X Y f rEarlier n s t x y)
    (hcross : ¬ FiniteExtensionNonliftableCrossing model X Y f rEarlier rLater n s t) :
    FiniteExtension model X Y f rLater n s t x y :=
  KIP126.ProofTools.Standard.finitePageExtensionStretching X Y f
    rEarlier rLater n s t x y hr hle hn hnUpper hx hy hW hcross

/-- The complete representative criterion applies to ordinary filtered
homotopy groups, independently of any synthetic background choice. -/
example {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (f : A →+ B) (F : ℤ → AddSubgroup A) (G : ℤ → AddSubgroup B)
    (hF : Antitone F) (hG : Antitone G)
    (hf : ∀ u a, a ∈ F u → f a ∈ G u)
    (s n p : ℤ) (hp : p ≤ s+n) (a0 : A)
    (ha0 : a0 ∈ F s) (hfa0 : f a0 ∈ G (s+n)) :
    Paper.FilteredNoCrossingRange f F G s n p ↔
      ∀ a, a ∈ F s → a-a0 ∈ F (s+1) → f a ∈ G p →
        f a ∈ G (s+n) ∧ f a-f a0 ∈ G (s+n+1) :=
  Paper.filtered_extension_noCrossingRange_iff f F G hF hG hf s n p hp a0 ha0 hfa0

example (X : ClassicalObject) (page : ℕ) (r s t : ℤ)
    (hpage : 2 ≤ page) (hpr : (page : ℤ) ≤ r) :
    HasCrossingOn model X r page (s,t) ↔ Paper.DeltaHasCrossing X page r s t :=
  Paper.classical_crossing_iff_delta_crossing X page r s t hpage hpr

#check Paper.lambda_rho_extension_collapse_finite
#check Paper.lambda_rho_extension_collapse_infinite
#check Paper.syntheticDeltaExtension_prop46_above_absolute
#check Paper.syntheticDeltaExtension_prop46_below_absolute
#check Paper.syntheticDeltaExtension_prop46_above_finite
#check Paper.syntheticDeltaExtension_prop46_below_finite
#check Paper.syntheticDeltaSource_vanishes
#check Paper.syntheticDeltaFiniteTarget_vanishes

/-- A finite classical differential supplies an actual synthetic boundary
extension on the same quotient, with both prescribed E2 labels retained. -/
example (X : ClassicalObject) (n m k a : ℕ)
    (hn : 0 < n) (ha : a ≤ n) (hnm : n < m) (hnk : n ≤ a+k)
    (s t : ℤ) (x : Ambient model X (s,t))
    (y : Ambient model X (s+k+1,t+k))
    (hd : KIP126.Core.SpectralSequence.HasDifferential
      (model.classical.obj (X.obj model.auxiliary)) (k+1) (s,t) (s+k+1,t+k) x y)
    (hy : y ∈ KIP126.Literature.permanentCycles model X (s+k+1,t+k)) :
    ∃ ex ey,
      KIP126.AdamsSynthetic.HasInfinityRepresentative _ 2 (s,(t-s)+s,t-a)
        (Paper.syntheticDeltaSourceLabel X n s t a x) ex ∧
      KIP126.AdamsSynthetic.HasInfinityRepresentative _ 2
        (s+(k+1),(t-s)+(s+(k+1)),t-a)
        (Paper.syntheticDeltaFiniteLabel X n m k a s t hnk y) ey ∧
      TowerExtensionEquation (model.convergentMap (.quotient n (.nu X))
        (.shift (1,-(n:ℤ)) (.quotient (m-n) (.nu X)))
        (Paper.syntheticFiniteBoundary X n m hn hnm))
        (t-s,t-a) s (k+1) ex ey :=
  Paper.syntheticDeltaExtension_finite X n m k a hn ha hnm hnk s t x y hd hy

#check_failure KIP126.ProofTools.Standard.lambda_target_class
#check_failure KIP126.Challenge2
#check_failure KIP126.Literature.LiteratureResults
#check_failure KIP126.Main.h6_sq_permanent
end Tests.ProofTools
