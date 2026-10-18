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

/-- Proposition 6.20 descends the prescribed source and target, within the
earlier page's defining length range. -/
example (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (rEarlier rLater : ℕ) (n s t : ℤ)
    (x : Ambient model X (s,t)) (y : Ambient model Y (s+n,t+n))
    (hr : 2 ≤ rEarlier) (hle : rEarlier ≤ rLater)
    (hnUpper : n ≤ (rEarlier : ℤ)-2+normalizedExponent model.classicalTower f)
    (h : FiniteExtension model X Y f rLater n s t x y) :
    FiniteExtension model X Y f rEarlier n s t x y :=
  Paper.finiteExtension_descends X Y f rEarlier rLater n s t x y hr hle hnUpper h

/-- The revised second clause supplies an actual classical early-cycle
source, without a nonliftability premise or an unrelated target. -/
example (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (rEarlier rLater : ℕ) (n s t : ℤ)
    (x : Ambient model X (s,t)) (y : Ambient model Y (s+n,t+n))
    (Wlater : FiniteExtensionWitness model X Y f rLater n s t x y)
    (Wearly : FiniteExtensionWitness model X Y f rEarlier n s t x y)
    (hle : rEarlier ≤ rLater) (hess : Wlater.Essential)
    (hne : ¬ Wearly.Essential) :
    ∃ a : ℕ, 0 < a ∧ (a : ℤ) ≤ n-normalizedExponent model.classicalTower f ∧
      ∃ x' : Ambient model X (s+a,(t-s)+(s+a)),
        x' ∈ KIP126.Literature.cycles model X
          (((rEarlier-1 : ℕ) : ℤ)-(a : ℤ)) (s+a,(t-s)+(s+a)) := by
  obtain ⟨a,ha,han,x',hx',_⟩ :=
    (Paper.finiteExtension_inessential_iff_shorter
      X Y f rEarlier rLater n s t x y Wlater Wearly hle hess).mp hne
  exact ⟨a,ha,han,x',hx'⟩

/-- At the minimal normalized length, later essentiality cannot become
inessential earlier: the positive shorter-source interval is empty. -/
example (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (rEarlier rLater : ℕ) (n s t : ℤ)
    (x : Ambient model X (s,t)) (y : Ambient model Y (s+n,t+n))
    (Wlater : FiniteExtensionWitness model X Y f rLater n s t x y)
    (Wearly : FiniteExtensionWitness model X Y f rEarlier n s t x y)
    (hle : rEarlier ≤ rLater) (hess : Wlater.Essential)
    (hn : n = (normalizedExponent model.classicalTower f : ℤ)) :
    Wearly.Essential := by
  classical
  by_contra hne
  obtain ⟨a,ha,han,_⟩ :=
    (Paper.finiteExtension_inessential_iff_shorter
      X Y f rEarlier rLater n s t x y Wlater Wearly hle hess).mp hne
  omega

/-- The teacher's latest formulation consumes the complete existential failure
of the fixed-target difference branch, giving a crossing in the actual late ESS. -/
example (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (rEarlier rLater : ℕ) (n s t : ℤ)
    (x : Ambient model X (s,t)) (y : Ambient model Y (s+n,t+n))
    (Wlater : FiniteExtensionWitness model X Y f rLater n s t x y)
    (Wearly : FiniteExtensionWitness model X Y f rEarlier n s t x y)
    (hle : rEarlier ≤ rLater) (hess : Wlater.Essential) (hne : ¬Wearly.Essential)
    (hno : ¬ Paper.FiniteExtensionNonliftableShortTo
      X Y f rEarlier rLater n s t x y Wearly) :
    ¬ Paper.ExtensionNoCrossingRange (model.convergentMap
      (.quotient (rLater-1) (extensionSourceObject model X Y f))
      (.quotient (rLater-1) (.nu Y)) (finiteExtensionMap model X Y f (rLater-1)))
      (t-s,t+normalizedExponent model.classicalTower f) s n s :=
  (Paper.finiteExtension_nonliftableShort_or_lateCrossing
    X Y f rEarlier rLater n s t x y Wlater Wearly hle hess hne).resolve_left hno

#check_failure Paper.finiteExtension_essential_shorter_source
#check_failure Paper.correction_source_lift_of_late_cycle
#check_failure Paper.infinityTowerNatural

#check_failure Paper.correctionShiftIso
#check_failure Paper.inessential_length_strict

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

/-- The public arbitrary-level GL is consumed through the ordinary module
entry, with all its mathematical premises explicit. -/
example (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (page level : ℕ) (r m l s t : ℤ)
    (x : Ambient model X (s,t)) (y : Ambient model Y (s+m,t+m))
    (xInfinity : Ambient model X (s+r,t+r-1))
    (yInfinity : Ambient model Y (s+r+l,t+r-1+l))
    (hpage : 2 ≤ page) (hpr : (page:ℤ) ≤ r)
    (hm : (normalizedExponent model.classicalTower f:ℤ) ≤ m)
    (hmUpper : m ≤ (page:ℤ)-2+normalizedExponent model.classicalTower f)
    (hl : (normalizedExponent model.classicalTower f:ℤ) ≤ l)
    (hxInfinity : IsPermanent model X (s+r,t+r-1) xInfinity)
    (hyInfinity : IsPermanent model Y (s+r+l,t+r-1+l) yInfinity)
    (hdx : DifferentialAt model X r (s,t) (s+r,t+r-1) x xInfinity)
    (hFinite : Standard.LevelFiniteExtension X Y f page level m s t x y)
    (hInfinity : InfiniteExtension model X Y f l (s+r) (t+r-1) xInfinity yInfinity)
    (hsourceCrossing : Standard.LevelBoundaryNoCrossing X Y f page level r s t ∨
      Standard.LevelFiniteNoCrossing X Y f page level m s t)
    (hbottomCrossing : Standard.LevelBottomNoCrossing X Y f page level r l s t) :
    DifferentialAt model Y (r+l-m) (s+m,t+m) (s+r+l,t+r-1+l) y yInfinity :=
  Standard.generalizedLeibnizAtLevel X Y f page level r m l s t
    x y xInfinity yInfinity hpage hpr hm hmUpper hl hxInfinity hyInfinity
    hdx hFinite hInfinity hsourceCrossing hbottomCrossing

/-- The old finite extension can be supplied at level zero without any
additional representative or crossing premise. -/
example (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (page : ℕ) (m s t : ℤ)
    (x : Ambient model X (s,t)) (y : Ambient model Y (s+m,t+m))
    (h : FiniteExtension model X Y f page m s t x y) :
    Standard.LevelFiniteExtension X Y f page 0 m s t x y :=
  Standard.finiteExtensionAtLevelZero X Y f page m s t x y h
section PublicLevelPredicates
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Core.SpectralSequence KIP126.Classical.Adams
open KIP126.ProofTools.Standard

-- The public predicate is actually usable as a witness, not an opaque axiom.
example (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (page level : ℕ) (m s t : ℤ)
    (x : Ambient model X (s,t)) (y : Ambient model Y (s+m,t+m))
    (h : LevelFiniteExtension X Y f page level m s t x y) : 2 ≤ page := by
  unfold LevelFiniteExtension at h
  exact h.1

-- The exposed crossing predicate reduces to its actual quantified ESS condition.
example (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (page level : ℕ) (m s t : ℤ) :
    LevelFiniteNoCrossing X Y f page level m s t ↔ (
  ∀ u v : ℤ, s < u → u ≤ v → v ≤ s+m →
    ∀ source target, ¬ TowerEssentialExtension
      (model.convergentMap
        (.quotient (page+level-1) (extensionSourceObject model X Y f))
        (.quotient (page+level-1) (.nu Y)) (finiteExtensionMap model X Y f (page+level-1)))
      (t-s,t+normalizedExponent model.classicalTower f-level) u (v-u) source target ) := Iff.rfl

-- The exposed crossing predicate reduces to its actual quantified ESS condition.
example (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (page level : ℕ) (r s t : ℤ) :
    LevelBoundaryNoCrossing X Y f page level r s t ↔ (
  ∀ u v : ℤ, s < u → u ≤ v → v ≤ s+r →
    ∀ source target, ¬ TowerEssentialExtension
      (model.convergentMap
        (.quotient (page+level-1) (extensionSourceObject model X Y f))
        (.shift (1,-((page+level-1:ℕ):ℤ)) (extensionSourceObject model X Y f))
        (XModLambdaN.proj ((extensionSourceObject model X Y f).obj model.nu model.auxiliary)
          (page+level-1) ≫
          (KIP126.ProofTools.Operations.biSuspensionIso (page+level-1:ℕ)
            ((extensionSourceObject model X Y f).obj model.nu model.auxiliary)).inv))
      (t-s,t+normalizedExponent model.classicalTower f-level) u (v-u) source target ) := Iff.rfl

-- The exposed crossing predicate reduces to its actual quantified ESS condition.
example (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (page level : ℕ) (r l s t : ℤ) :
    LevelBottomNoCrossing X Y f page level r l s t ↔ (
  ∀ u v : ℤ, s+r < u → u ≤ v → v ≤ s+r+l →
    ∀ source target, ¬ TowerEssentialExtension
      (model.convergentMap
        (.shift (1,-((page+level-1:ℕ):ℤ)) (extensionSourceObject model X Y f))
        (.shift (1,-((page+level-1:ℕ):ℤ)) (.nu Y))
        ((SyntheticCategory.biShift (1,-((page+level-1:ℕ):ℤ))).map
          (model.normalizedMap X Y f).map))
      (t-s,t+normalizedExponent model.classicalTower f-level) u (v-u) source target ) := Iff.rfl

end PublicLevelPredicates
section PublicLambdaDivision
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Core.SpectralSequence KIP126.Classical.Adams
open KIP126.ProofTools.Standard

-- The complete public statement is callable with its stated hypotheses only.
example
    (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (q i : ℕ) (hi : 0 < i) (hiq : i < q) (s t N : ℤ) (hsN : s+i ≤ N)
    (hcross : FiniteLambdaKernelNoCrossing X Y f q i hi hiq s t N)
    (a : BiHom (t-s) (t+normalizedExponent model.classicalTower f)
      (XModLambdaN ((extensionSourceObject model X Y f).obj model.nu model.auxiliary) q))
    (ha : FiltrationAtLeast model.syntheticTower (s+i) a)
    (hfa : FiltrationAtLeast model.syntheticTower N (a ≫ finiteExtensionMap model X Y f q)) :
    ∃ b : BiHom (t-s) (t+normalizedExponent model.classicalTower f)
        ((SyntheticCategory.biShift (0,-(i:ℤ))).obj
          (XModLambdaN ((extensionSourceObject model X Y f).obj model.nu model.auxiliary) (q-i))),
      b ≫ ((model.quotients.tower _).triangle hi hiq).lambdaMap = a ∧
      FiltrationAtLeast model.syntheticTower (s+i) b ∧
      (b ≫ (SyntheticCategory.biShift (0,-(i:ℤ))).map
        (finiteExtensionMap model X Y f (q-i))) ≫
          ((model.quotients.tower _).triangle hi hiq).lambdaMap =
        a ≫ finiteExtensionMap model X Y f q ∧
      FiltrationAtLeast model.syntheticTower N
        (b ≫ (SyntheticCategory.biShift (0,-(i:ℤ))).map
          (finiteExtensionMap model X Y f (q-i))) :=
  finiteLambdaDivision
    X Y f q i hi hiq s t N hsN hcross a ha hfa


-- Ordinary import exposes the complete kernel crossing range and actual target lambda arrow.
example (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (q i : ℕ) (hi : 0 < i) (hiq : i < q) (s t N : ℤ) :
    FiniteLambdaKernelNoCrossing X Y f q i hi hiq s t N ↔ (
  ∀ u v : ℤ, s+i ≤ u → u ≤ v → v < N → ∀ source target,
    TowerEssentialExtension
      (model.convergentMap
        (.shift (0,-(i:ℤ)) (.quotient (q-i) (extensionSourceObject model X Y f)))
        (.shift (0,-(i:ℤ)) (.quotient (q-i) (.nu Y)))
        ((SyntheticCategory.biShift (0,-(i:ℤ))).map (finiteExtensionMap model X Y f (q-i))))
      (t-s,t+normalizedExponent model.classicalTower f) u (v-u) source target →
      (model.family.functor.map
        ((model.quotients.tower (model.nu.functor.obj (Y.obj model.auxiliary))).triangle
          hi hiq).lambdaMap).eInftyMap
        (u+(v-u),(t-s)+(u+(v-u)),t+normalizedExponent model.classicalTower f) target ≠ 0 ) := Iff.rfl

end PublicLambdaDivision
end Tests.ProofTools
