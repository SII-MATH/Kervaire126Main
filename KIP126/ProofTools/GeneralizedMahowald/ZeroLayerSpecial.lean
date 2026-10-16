module
import KIP126.ProofTools.Laws
import all KIP126.ProofTools.GeneralizedMahowald.NoReturn
import all KIP126.ProofTools.GeneralizedMahowald.Geometry
import all KIP126.ProofTools.GeneralizedMahowald.OctahedralPullback
import all KIP126.ProofTools.GeneralizedMahowald.CommonShiftEdge
import all KIP126.ProofTools.GeneralizedMahowald.CofiberIdentification
import all KIP126.ProofTools.GeneralizedMahowald.QuotientShift
import all KIP126.ProofTools.GeneralizedMahowald.Signs
import all KIP126.ProofTools.GeneralizedMahowald.Synchronization
import all KIP126.ProofTools.GeneralizedMahowald.HSourceSelection
import all KIP126.ProofTools.GeneralizedMahowald.ShortSource
import all KIP126.ProofTools.GeneralizedMahowald.HTargetDetection
import all KIP126.ProofTools.GeneralizedMahowald.TargetSurvival
import all KIP126.ProofTools.GeneralizedMahowald.FinalDivision
import all KIP126.ProofTools.GeneralizedMahowald.FSourceRegrade
import all KIP126.ProofTools.GeneralizedMahowald.Sphere
import all KIP126.ProofTools.GeneralizedMahowald.Adjacent
import all KIP126.ProofTools.GeneralizedMahowald.FinalOperations
import all KIP126.ProofTools.GeneralizedMahowald.Detection
import all KIP126.ProofTools.GeneralizedMahowald.PageCalculus
import all KIP126.ProofTools.GeneralizedMahowald.BoundaryDetection
import all KIP126.ProofTools.DetectionOperations
import all KIP126.ProofTools.GeneralizedMahowald.ZeroLayerAssembly
import all KIP126.ProofTools.GeneralizedMahowald.ZeroLayerTarget
/-! Internal zero-layer MH2: m=e(g), l=e(h), and Y the sphere.
This proves the Main instance using common May representatives and normalized
quotient geometry, without the false general MH2 law or lambda cancellation.
Registered upstream construction obligations remain upstream dependencies. -/
@[expose] section
namespace KIP126.ProofTools.Internal.Mahowald
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard KIP126.Literature
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option Elab.async false
private theorem zero_level_native_detection
    (X : ClassicalObject) (r : ℕ) (s t : ℤ) (k : ℕ) (hk : k=0)
    (x : Ambient model X (s,t))
    (c : BiHom (t-s) (t-k) (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) r))
    (hc : Detects (model.convergence (.quotient r (.nu X))) (s,t,t-k)
      (finiteTargetLabel model X r s t k x) c) :
    Detects (model.convergence (.quotient r (.nu X))) (s,t,t)
      (regradeE2 (by simp) (finiteTargetLabel model X r s t 0 x))
      (homotopyRegrade rfl (by omega : t-k=t) c) := by
  subst k
  exact detects_transport (show (s,t,t-(0:ℕ))=(s,t,t) by simp) _ _ hc

private def ZeroLayerDetectedPair
    (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (r : ℕ) (n s t b : ℤ) (hn : (normalizedExponent model.classicalTower f : ℤ)≤n)
    (x : Ambient model X (s,t)) (y : Ambient model Y (s+n,t+n)) : Prop :=
  ∃ y' : Ambient model Y (s+n,t+n), y'-y∈boundaries model Y b (s+n,t+n) ∧
    ∃ (af : BiHom (t-s) (t+normalizedExponent model.classicalTower f)
          (XModLambdaN ((extensionSourceObject model X Y f).obj model.nu model.auxiliary) r))
      (bf : BiHom (t-s) (t+normalizedExponent model.classicalTower f)
          (XModLambdaN (model.nu.functor.obj (Y.obj model.auxiliary)) r)),
      Detects (model.convergence (.quotient r (extensionSourceObject model X Y f)))
        (s,(t-s)+s,t+normalizedExponent model.classicalTower f)
        (finiteSourceForExtension model X Y f r s t x)
        (homotopyRegrade (by dsimp; omega) rfl af) ∧
      Detects (model.convergence (.quotient r (.nu Y)))
        (s+n,(t-s)+(s+n),t+normalizedExponent model.classicalTower f)
        (finiteTargetForExtension model X Y f r n s t hn y')
        (homotopyRegrade (by dsimp; omega) rfl bf) ∧
      af≫finiteExtensionMap model X Y f r=bf

private theorem generalized_mahowald_zero_layer_sphere
    (T : TriangleData model.auxiliary) (hY : T.Y = .sphere) :
  ∀ he : (normalizedExponent model.classicalTower T.f : ℤ) + normalizedExponent model.classicalTower T.g +
      normalizedExponent model.classicalTower T.h = 1,
  KIP126.Literature.NormalizedTriangleCompatible model T he →
  ∀ (n m l s t : ℤ),
  m = (normalizedExponent model.classicalTower T.g : ℤ) →
  l = (normalizedExponent model.classicalTower T.h : ℤ) →
    let r := n + m + l
    let n₁ := n - normalizedExponent model.classicalTower T.f
    let m₁ := m - normalizedExponent model.classicalTower T.g
    let l₁ := l - normalizedExponent model.classicalTower T.h
    let r' := r - m₁
    ∀ (x : Ambient model (T.X) (s + l, t + l - 1))
      (y : Ambient model (T.Y) (s + l + n, t + l - 1 + n))
      (xBar : Ambient model (T.Z) (s, t))
      (yBar : Ambient model (T.Z) (s + l + n + m, t + l - 1 + n + m))
      (suspendedX : Ambient model (.shift 1 T.X) (s + l, t + l)),
      1 ≤ n₁ → 0 ≤ m₁ → 0 ≤ l₁ →
      IsCycle model (T.X) n₁ (s + l, t + l - 1) x →
      IsCycle model (T.Y) (m₁ + 1) (s + l + n, t + l - 1 + n) y →
      IsCycle model (T.Z) (r - 1) (s, t) xBar →
      IsPermanent model (T.Z) (s + l + n + m, t + l - 1 + n + m) yBar →
      (model.classicalSuspension T.X).DesuspendsClass (s + l) (t + l) suspendedX x →
      FiniteExtension model T.Z (.shift 1 T.X) T.h r'.toNat l s t xBar suspendedX →
      DifferentialAt model (T.Z) r (s, t)
        (s + l + n + m, t + l - 1 + n + m) xBar yBar →
      (FiniteNoCrossing model T.Z (.shift 1 T.X) T.h r'.toNat l s t ∨
        NoCrossingOn model (T.Z) r r' (s, t)) →
      FiniteExtension model T.Y T.Z T.g (m₁ + 2).toNat m (s + l + n) (t + l - 1 + n) y yBar →
      IsCycle model (T.X) (n + m + normalizedExponent model.classicalTower T.h) (s + l, t + l - 1) x ∧
        ∃ y' : Ambient model (T.Y) (s + l + n, t + l - 1 + n),
          FiniteExtension model T.X T.Y T.f (n + m + 1 + normalizedExponent model.classicalTower T.h).toNat
            n (s + l) (t + l - 1) x y' ∧
          Congruent model (T.Y) r' (s + l + n, t + l - 1 + n) y' y := by
  intro he htriangle n m l s t
  dsimp only
  intro hmZero hlZero x y xBar yBar suspendedX hn hm hl
    hx hy hxBar hyBar hsusp hh hd hcross hg
  let eg : ℤ := normalizedExponent model.classicalTower T.g
  let ef : ℤ := normalizedExponent model.classicalTower T.f
  let eh : ℤ := normalizedExponent model.classicalTower T.h
  let pg : ℕ := (m-eg+2).toNat
  let q : ℕ := pg-1
  let i : ℕ := (n+l+eg-1).toNat
  let Q : ℕ := (n+m+eh).toNat
  let sf : ℤ := s+l
  let tf : ℤ := t+l-1
  have hpg : 2 ≤ pg := by dsimp [pg,eg]; omega
  have hq : 0 < q := by dsimp [q]; omega
  have hqZ : (q:ℤ)=m-eg+1 := by dsimp [q,pg]; omega
  have hi : 0 < i := by dsimp [i,eg,ef,eh] at *; omega
  have hiZ : (i:ℤ)=n+l+eg-1 := by dsimp [i,eg,ef,eh] at *; omega
  have hQ : 0 < Q := by dsimp [Q,eg,ef,eh] at *; omega
  have hQZ : (Q:ℤ)=n+m+eh := by dsimp [Q,eg,ef,eh] at *; omega
  have hn0 : 0 ≤ n := by have := Nat.zero_le (normalizedExponent model.classicalTower T.f); omega
  have hnf : ef ≤ n := by dsimp [ef]; omega
  let Wg : FiniteExtensionWitness model T.Y T.Z T.g pg m (sf+n) (tf+n) y yBar :=
    Classical.choice hg
  let Zν := model.nu.functor.obj (T.Z.obj model.auxiliary)
  let boundary (aZ : BiHom (t-s) t (XModLambdaN Zν i)) :
      BiHom ((tf+n)-(sf+n)) (tf+n+eg) (XModLambdaN Zν q) :=
    homotopyRegrade (by dsimp [tf,sf]; omega) (by dsimp [tf]; omega)
      (biSuspensionHomEquiv (t-s) t (i:ℤ) (XModLambdaN Zν q)
        (by simpa only [Nat.add_sub_cancel_left] using
          (aZ ≫ ((model.quotients.tower Zν).triangle hi (show i < i + q by omega)).delta)))
  have boundary_representative :
      ∃ aZ : BiHom (t-s) t (XModLambdaN Zν i),
        Detects (model.convergence (.quotient i (.nu T.Z))) (s,t,t)
          (regradeE2 (by simp) (finiteTargetLabel model T.Z i s t 0 xBar)) aZ ∧
        Detects (model.convergence (.quotient q (.nu T.Z)))
          (sf+n+m,((tf+n)-(sf+n))+(sf+n+m),tf+n+eg)
          (finiteTargetForExtension model T.Y T.Z T.g q m (sf+n) (tf+n) Wg.length_lower yBar)
          (homotopyRegrade (by dsimp; omega) rfl (boundary aZ)) ∧
        (NoCrossingOn model T.Z (n+m+l) (n+m+l-(m-eg)) (s,t) →
          ∀ a : BiHom (t-s) t (XModLambdaN Zν i),
            Detects (model.convergence (.quotient i (.nu T.Z))) (s,t,t)
              (regradeE2 (by simp) (finiteTargetLabel model T.Z i s t 0 xBar)) a →
            boundary a = boundary aZ) := by
    have hmi : eg ≤ m := by dsimp [eg]; omega
    have hxi : xBar ∈ cycles model T.Z (i:ℤ) (s,t) :=
      cycles_antitone model T.Z (s,t) (by omega : (i:ℤ) ≤ n+m+l-1) hxBar.2
    have hxiR : ReachesPage (model.classical.obj (T.Z.obj model.auxiliary)) (i+1) (s,t) xBar :=
      (isCycle_iff_reaches model T.Z (i+1) (by omega) (s,t) xBar).mp
        ⟨by omega, by simpa only [add_sub_cancel_right] using hxi⟩
    obtain ⟨a0Zero,ha0Zero⟩ := (KIP126.Literature.Standard.bhs_finite_lift T.Z i hi s t xBar).mp hxiR
    let a0 : BiHom (t-s) t (XModLambdaN Zν i) :=
      a0Zero ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app Zν) i
    have ha0first : a0 ≫ (model.quotients.tower Zν).rho 1 i hi =
        firstLabel model T.Z s t xBar ≫
          XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app Zν) 1 := by
      dsimp only [a0]
      have hnat : (model.quotients.tower (nuZero model T.Z)).rho 1 i hi ≫
          XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app Zν) 1 =
          XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app Zν) i ≫
            (model.quotients.tower Zν).rho 1 i hi :=
        (model.quotients.natural
          (SyntheticCategory.biShift_zero.hom.app Zν)).rho_naturality hi
      rw [Category.assoc,←hnat,←Category.assoc,ha0Zero]
    have target_correction :
        ∃ c : BiHom (t-s) t (XModLambdaN Zν i),
          c ≫ (model.quotients.tower Zν).rho 1 i hi = 0 ∧
          Detects (model.convergence (.quotient q (.nu T.Z)))
            (sf+n+m,((tf+n)-(sf+n))+(sf+n+m),tf+n+eg)
            (finiteTargetForExtension model T.Y T.Z T.g q m (sf+n) (tf+n) Wg.length_lower yBar)
            (homotopyRegrade (by dsimp; omega) rfl (boundary (a0+c))) := by
      by_cases hyB : yBar ∈ boundaries model T.Z (q:ℤ) (sf+n+m,tf+n+m)
      · have hd0 : KIP126.Core.SpectralSequence.HasDifferential
            (model.classical.obj (T.Z.obj model.auxiliary)) (i+q)
            (s,t) (s+i+q,t+i+q-1) xBar 0 := by
          have reindex (r r' : ℤ) (hr : r=r') (p p' : ℤ×ℤ) (hp : p=p')
              (h : KIP126.Core.SpectralSequence.HasDifferential
                (model.classical.obj (T.Z.obj model.auxiliary)) r
                (s,t) p xBar 0) : KIP126.Core.SpectralSequence.HasDifferential
                (model.classical.obj (T.Z.obj model.auxiliary)) r'
                (s,t) p' xBar 0 := by
            subst r'; subst p'; exact h
          have hd' := boundary_target_zero model T.Z (n+m+l) q (s,t) (sf+n+m,tf+n+m)
            hd.1 (by omega) xBar yBar hyB hd.2
          exact reindex _ _ (by omega) _ _ (by ext <;> dsimp [sf,tf] <;> omega) hd'
        have htarget : Detects (model.convergence (.quotient q (.nu T.Z)))
            (sf+n+m,((tf+n)-(sf+n))+(sf+n+m),tf+n+eg)
            (finiteTargetForExtension model T.Y T.Z T.g q m (sf+n) (tf+n) Wg.length_lower yBar) 0 := by
          have transport_zero {p p' : Tridegree} (hp : p=p')
              (z : (model.family.obj (XModLambdaN Zν q)).E₂ p)
              (hz : Detects (model.convergence (.quotient q (.nu T.Z))) p z 0) :
              Detects (model.convergence (.quotient q (.nu T.Z))) p' (regradeE2 hp z) 0 := by
            subst p'
            exact hz
          have label_transport (s0 t0 : ℤ) (z : Ambient model T.Z (s0,t0))
              (k k' : ℕ) (hk : k=k') (p : Tridegree)
              (hp : (s0,t0,t0-k)=p) (hp' : (s0,t0,t0-k')=p) :
              regradeE2 hp (finiteTargetLabel model T.Z q s0 t0 k z) =
                regradeE2 hp' (finiteTargetLabel model T.Z q s0 t0 k' z) := by
            subst k'
            rfl
          unfold finiteTargetForExtension
          convert transport_zero
            (p := (sf+n+m,tf+n+m,(tf+n+m)-(q-1:ℕ)))
            (p' := (sf+n+m,((tf+n)-(sf+n))+(sf+n+m),tf+n+eg))
            (by ext <;> dsimp <;> omega) _ (finite_top_boundary_detects_zero T.Z q hq _ _ yBar hyB) using 1
          exact label_transport _ _ yBar _ (q-1) (by dsimp [eg] at hqZ hmi; omega) _ _ _
        obtain ⟨a,hafirst,hazero⟩ := zero_target_actual_lift T.Z i q hi hq s t xBar hd0
        refine ⟨a-a0,?_,?_⟩
        · rw [Preadditive.sub_comp,hafirst,ha0first,sub_self]
        · have hsum : a0+(a-a0)=a := by abel
          rw [hsum]
          have regrade_zero {u u' v v' : ℤ} {A : SyntheticSpectrum} (hu : u=u') (hv : v=v') :
              homotopyRegrade hu hv (0 : BiHom u v A)=0 := by
            subst u'; subst v'; rfl
          have hboundary : boundary a=0 := by
            have hom_cast_zero {U V V' : SyntheticSpectrum} (h : V=V') (he : (U ⟶ V)=(U ⟶ V')) :
                he.mp (0 : U ⟶ V)=0 := by
              subst V'
              rfl
            dsimp only [boundary]
            rw [hazero]
            rw [hom_cast_zero (congrArg (fun j =>
              ((SyntheticCategory.biShift (0,-(i:ℤ))).obj (XModLambdaN Zν j))⟦(1:ℤ)⟧)
              (Nat.add_sub_cancel_left i q))]
            rw [map_zero,regrade_zero]
          rw [hboundary,regrade_zero]
          exact htarget
      ·
        by_cases hq1 : q=1
        · have hm_eq : (normalizedExponent model.classicalTower T.g : ℤ)=m := by dsimp [eg] at hqZ; omega
          have adjacent_reindexed (r u v : ℤ)
              (hr : r=(i:ℤ)+1) (hu : u=s+i+1) (hv : v=t+i)
              (y' : Ambient model T.Z (u,v))
              (hdy : KIP126.Core.SpectralSequence.HasDifferential
                (model.classical.obj (T.Z.obj model.auxiliary))
                r (s,t) (u,v) xBar y') :
              let δ : XModLambdaN Zν i ⟶
                  ((SyntheticCategory.biShift (0,-(i:ℤ))).obj (XModLambdaN Zν 1))⟦(1:ℤ)⟧ := by
                simpa only [show i.succ-i=1 by omega] using
                  ((model.quotients.tower Zν).triangle hi (Nat.lt_succ_self i)).delta
              ∃ a : BiHom (t-s) t (XModLambdaN Zν i),
                a ≫ (model.quotients.tower Zν).rho 1 i hi =
                  firstLabel model T.Z s t xBar ≫
                    XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app Zν) 1 ∧
                Detects (model.convergence (.quotient 1 (.nu T.Z))) (u,v,v)
                  (regradeE2 (by simp) (finiteTargetLabel model T.Z 1 u v 0 y'))
                  (homotopyRegrade (by dsimp; omega) (by dsimp; omega)
                    (biSuspensionHomEquiv (t-s) t (i:ℤ) (XModLambdaN Zν 1) (a≫δ))) := by
            subst r
            subst u
            subst v
            exact adjacent_mahowald_case T.Z i hi s t xBar y' hdy
          obtain ⟨a,ha,hda⟩ := adjacent_reindexed (n+m+l) (sf+n+m) (tf+n+m)
            (by dsimp [eg] at hiZ; omega) (by dsimp [sf]; dsimp [eg] at hiZ; omega)
            (by dsimp [tf]; dsimp [eg] at hiZ; omega) yBar hd.2
          have finite_target_detects_of_exponent_eq
              (Y Z : ClassicalObject) (g : Y.obj model.auxiliary ⟶ Z.obj model.auxiliary)
              (m s0 t0 : ℤ) (hm : (normalizedExponent model.classicalTower g : ℤ) ≤ m)
              (he : (normalizedExponent model.classicalTower g : ℤ) = m)
              (y : Ambient model Z ((s0+m),(t0+m)))
              (a : BiHom ((t0+m)-(s0+m)) (t0+m)
                (XModLambdaN (model.nu.functor.obj (Z.obj model.auxiliary)) 1))
              (ha : Detects (model.convergence (.quotient 1 (.nu Z))) (s0+m,t0+m,t0+m)
                (regradeE2 (by simp) (finiteTargetLabel model Z 1 (s0+m) (t0+m) 0 y)) a) :
              Detects (model.convergence (.quotient 1 (.nu Z)))
                (s0+m,(t0-s0)+(s0+m),t0+normalizedExponent model.classicalTower g)
                (finiteTargetForExtension model Y Z g 1 m s0 t0 hm y)
                (homotopyRegrade (by dsimp; omega) (by dsimp; omega) a) := by
            have transport {i j : Tridegree} (h : i=j)
                (x : (model.family.obj (XModLambdaN (model.nu.functor.obj (Z.obj model.auxiliary)) 1)).E₂ i)
                (b : BiHom (i.2.1-i.1) i.2.2
                  (XModLambdaN (model.nu.functor.obj (Z.obj model.auxiliary)) 1))
                (hb : Detects (model.convergence (.quotient 1 (.nu Z))) i x b) :
                Detects (model.convergence (.quotient 1 (.nu Z))) j (regradeE2 h x)
                  (homotopyRegrade (congrArg (fun k : Tridegree => k.2.1-k.1) h)
                    (congrArg (fun k : Tridegree => k.2.2) h) b) := by
              subst j
              exact hb
            have label_transport (s t : ℤ) (z : Ambient model Z (s,t))
                (k k' : ℕ) (hk : k=k') (i j : Tridegree)
                (h : (s,t,t-k)=j) (h0 : (s,t,t-k')=i) (h1 : i=j) :
                regradeE2 h (finiteTargetLabel model Z 1 s t k z) =
                  regradeE2 h1 (regradeE2 h0 (finiteTargetLabel model Z 1 s t k' z)) := by
              subst k'
              subst i
              subst j
              rfl
            subst m
            unfold finiteTargetForExtension
            convert transport
              (i := (s0+normalizedExponent model.classicalTower g,t0+normalizedExponent model.classicalTower g,t0+normalizedExponent model.classicalTower g))
              (j := (s0+normalizedExponent model.classicalTower g,(t0-s0)+(s0+normalizedExponent model.classicalTower g),
                t0+normalizedExponent model.classicalTower g))
              (by ext <;> dsimp; omega) _ _ ha using 1
            exact label_transport _ _ y _ 0 (by simp) _ _ _ _ _
          have htarget := finite_target_detects_of_exponent_eq T.Y T.Z T.g
            m (sf+n) (tf+n) Wg.length_lower hm_eq yBar _ hda
          refine ⟨a-a0,?_,?_⟩
          · rw [Preadditive.sub_comp,ha,ha0first,sub_self]
          · have haa : a0+(a-a0)=a := by abel
            rw [haa]
            have transport_q (j : ℕ) (hj : 0<j) (hj1 : j=1)
                (hb : Detects (model.convergence (.quotient 1 (.nu T.Z)))
                  (sf+n+m,((tf+n)-(sf+n))+(sf+n+m),tf+n+eg)
                  (finiteTargetForExtension model T.Y T.Z T.g 1 m (sf+n) (tf+n) Wg.length_lower yBar)
                  (homotopyRegrade
                    (show (tf+n+m)-(sf+n+m)=((tf+n)-(sf+n))+(sf+n+m)-(sf+n+m) by omega)
                    (show tf+n+m=tf+n+eg by dsimp [eg]; omega)
                    (homotopyRegrade
                      (show (t-s)-1=(tf+n+m)-(sf+n+m) by dsimp [sf,tf]; omega)
                      (show t+(i:ℤ)=tf+n+m by dsimp [tf]; dsimp [eg] at hiZ; omega)
                      (biSuspensionHomEquiv (t-s) t (i:ℤ) (XModLambdaN Zν 1)
                        (a ≫ (by simpa only [show i.succ-i=1 by omega] using
                          ((model.quotients.tower Zν).triangle hi (Nat.lt_succ_self i)).delta)))))) :
                Detects (model.convergence (.quotient j (.nu T.Z)))
                  (sf+n+m,((tf+n)-(sf+n))+(sf+n+m),tf+n+eg)
                  (finiteTargetForExtension model T.Y T.Z T.g j m (sf+n) (tf+n) Wg.length_lower yBar)
                  (homotopyRegrade
                    (show (tf+n)-(sf+n)=((tf+n)-(sf+n))+(sf+n+m)-(sf+n+m) by omega) rfl
                    (homotopyRegrade
                      (show (t-s)-1=(tf+n)-(sf+n) by dsimp [sf,tf]; omega)
                      (show t+(i:ℤ)=tf+n+eg by dsimp [tf]; omega)
                      (biSuspensionHomEquiv (t-s) t (i:ℤ) (XModLambdaN Zν j)
                        (by simpa only [Nat.add_sub_cancel_left] using
                          (a ≫ ((model.quotients.tower Zν).triangle hi (show i < i+j by omega)).delta))))) := by
              subst j
              convert hb using 1
              have regrade_comp {m w m' w' m'' w'' : ℤ} {B : SyntheticSpectrum}
                  (hm : m=m') (hw : w=w') (hm' : m'=m'') (hw' : w'=w'')
                  (b : BiHom m w B) :
                  homotopyRegrade hm' hw' (homotopyRegrade hm hw b) =
                    homotopyRegrade (hm.trans hm') (hw.trans hw') b := by
                subst m'; subst w'; subst m''; subst w''; rfl
              simp only [regrade_comp]
              congr 2
              have cast_comp {S U A B : SyntheticSpectrum} (h : A=B)
                  (ha : (S ⟶ A)=(S ⟶ B)) (hf : (U ⟶ A)=(U ⟶ B))
                  (a : S ⟶ U) (f : U ⟶ A) : ha.mp (a≫f)=a≫hf.mp f := by
                subst B
                rfl
              exact cast_comp (congrArg (fun k =>
                ((SyntheticCategory.biShift (0,-(i:ℤ))).obj (XModLambdaN Zν k))⟦(1:ℤ)⟧)
                (Nat.add_sub_cancel_left i 1)) _ _ _ _
            exact transport_q q hq hq1 htarget
        · have hqgt : 1<q := by omega
          have selected_reindexed (X : ClassicalObject)
              (r u v : ℤ) (hr : r=((i+q:ℕ):ℤ))
              (hu : u=s+i+q) (hv : v=t+i+q-1)
              (x' : Ambient model X (s,t))
              (y' : Ambient model X (u,v))
              (hdy : KIP126.Core.SpectralSequence.HasDifferential
                (model.classical.obj (X.obj model.auxiliary))
                r (s,t) (u,v) x' y')
              (hperm : y' ∈ permanentCycles model X (u,v)) :
              let A := model.nu.functor.obj (X.obj model.auxiliary)
              let δ : XModLambdaN A i ⟶
                  ((SyntheticCategory.biShift (0,-(i:ℤ))).obj (XModLambdaN A q))⟦(1:ℤ)⟧ := by
                simpa only [Nat.add_sub_cancel_left] using
                  ((model.quotients.tower A).triangle hi (show i < i+q by omega)).delta
              ∃ a : BiHom (t-s) t (XModLambdaN A i),
                a ≫ (model.quotients.tower A).rho 1 i hi =
                  firstLabel model X s t x' ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app A) 1 ∧
                Detects (model.convergence (.quotient q (.nu X))) (u,v,t+i)
                  (regradeE2 (by exact congrArg (fun w : ℤ => (u,v,w)) (by omega))
                    (finiteTargetLabel model X q u v (q-1) y'))
                  (homotopyRegrade (by dsimp; omega) rfl
                    (biSuspensionHomEquiv (t-s) t (i:ℤ) (XModLambdaN A q) (a≫δ))) := by
            subst r
            subst u
            subst v
            exact selected_mahowald_case X i q hi hq s t x' y' hdy hperm
          obtain ⟨a,ha,hda⟩ := selected_reindexed T.Z (n+m+l) (sf+n+m) (tf+n+m)
            (by omega) (by dsimp [sf]; omega) (by dsimp [tf]; omega) xBar yBar hd.2 hyBar
          have transport {p p' : Tridegree} (hp : p=p')
              (z : (model.family.obj (XModLambdaN Zν q)).E₂ p)
              (b : BiHom (p.2.1-p.1) p.2.2 (XModLambdaN Zν q))
              (hb : Detects (model.convergence (.quotient q (.nu T.Z))) p z b) :
              Detects (model.convergence (.quotient q (.nu T.Z))) p' (regradeE2 hp z)
                (homotopyRegrade (congrArg (fun p : Tridegree => p.2.1-p.1) hp)
                  (congrArg (fun p : Tridegree => p.2.2) hp) b) := by
            subst p'
            exact hb
          have label_transport (s0 t0 : ℤ) (z : Ambient model T.Z (s0,t0))
              (k k' : ℕ) (hk : k=k') (p p' : Tridegree)
              (hp : (s0,t0,t0-k)=p') (h0 : (s0,t0,t0-k')=p) (h1 : p=p') :
              regradeE2 hp (finiteTargetLabel model T.Z q s0 t0 k z) =
                regradeE2 h1 (regradeE2 h0 (finiteTargetLabel model T.Z q s0 t0 k' z)) := by
            subst k'
            subst p
            subst p'
            rfl
          have hdegree : (sf+n+m,tf+n+m,t+(i:ℤ)) =
              (sf+n+m,((tf+n)-(sf+n))+(sf+n+m),tf+n+eg) := by
            ext <;> dsimp only [tf] <;> omega
          have htarget := transport hdegree _ _ hda
          have hlabel : finiteTargetForExtension model T.Y T.Z T.g q m (sf+n) (tf+n) Wg.length_lower yBar =
              regradeE2 hdegree
                (regradeE2 (by exact congrArg (fun w : ℤ => (sf+n+m,tf+n+m,w)) (by omega))
                  (finiteTargetLabel model T.Z q (sf+n+m) (tf+n+m) (q-1) yBar)) := by
            unfold finiteTargetForExtension
            exact label_transport _ _ yBar _ (q-1) (by dsimp [eg] at hqZ hmi; omega) _ _ _ _ _
          rw [←hlabel] at htarget
          refine ⟨a-a0,?_,?_⟩
          · rw [Preadditive.sub_comp,ha,ha0first,sub_self]
          · have haa : a0+(a-a0)=a := by abel
            rw [haa]
            have regrade_comp {m w m' w' m'' w'' : ℤ} {B : SyntheticSpectrum}
                (hm : m=m') (hw : w=w') (hm' : m'=m'') (hw' : w'=w'')
                (b : BiHom m w B) :
                homotopyRegrade hm' hw' (homotopyRegrade hm hw b) =
                  homotopyRegrade (hm.trans hm') (hw.trans hw') b := by
              subst m'; subst w'; subst m''; subst w''; rfl
            dsimp only [boundary]
            simp (config := { congrConsts := false }) only [regrade_comp] at htarget ⊢
            convert htarget using 1
            congr 2
            have cast_comp {S U A B : SyntheticSpectrum} (h : A=B)
                (ha : (S ⟶ A)=(S ⟶ B)) (hf : (U ⟶ A)=(U ⟶ B))
                (a : S ⟶ U) (f : U ⟶ A) : ha.mp (a≫f)=a≫hf.mp f := by
              subst B
              rfl
            exact cast_comp (congrArg (fun k =>
              ((SyntheticCategory.biShift (0,-(i:ℤ))).obj (XModLambdaN Zν k))⟦(1:ℤ)⟧)
              (Nat.add_sub_cancel_left i q)) _ _ _ _
    obtain ⟨c,hc,hdelta⟩ := target_correction
    have hfirst : (a0+c) ≫ (model.quotients.tower Zν).rho 1 i hi =
        firstLabel model T.Z s t xBar ≫
          XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app Zν) 1 := by
      rw [Preadditive.add_comp,ha0first,hc,add_zero]
    have hsource := first_label_detects_unshifted T.Z i hi s t xBar (a0+c) hfirst
    refine ⟨a0+c,hsource,hdelta,?_⟩
    intro hnc a ha
    have hnc' : NoCrossingOn model T.Z (i+q) (i+1) (s,t) := by
      convert hnc using 1 <;> omega
    have heq := relative_boundary_equal_of_no_crossing T.Z i q hi hq s t hnc' a (a0+c)
      (detects_sub_filtration (model.convergence (.quotient i (.nu T.Z))) (s,t,t) ha hsource)
    dsimp only [boundary]
    rw [heq]
  obtain ⟨aZ,haZ,hdelta,hboundaryStable⟩ := boundary_representative
  have may_boundary_lift :
      ∀ ag : BiHom ((tf+n)-(sf+n)) (tf+n+eg)
          ((SyntheticObject.quotient q (extensionSourceObject model T.Y T.Z T.g)).obj model.nu model.auxiliary),
        Detects (model.convergence (.quotient q (extensionSourceObject model T.Y T.Z T.g)))
          (sf+n,((tf+n)-(sf+n))+(sf+n),tf+n+eg)
          (finiteSourceForExtension model T.Y T.Z T.g q (sf+n) (tf+n) y)
          (homotopyRegrade (by dsimp; omega) rfl ag) →
        ag ≫ finiteExtensionMap model T.Y T.Z T.g q = boundary aZ →
        (∃ c : BiHom (tf-sf) tf (XModLambdaN (nuZero model T.X) Q),
          c ≫ (model.quotients.tower (nuZero model T.X)).rho 1 Q hQ = firstLabel model T.X sf tf x) ∧
        ∃ y' : Ambient model T.Y ((sf+n),(tf+n)),
          y'-y ∈ boundaries model T.Y (n+m+l-(m-eg)) (sf+n,tf+n) ∧
          ∃ (af : BiHom (tf-sf) (tf+ef)
                ((SyntheticObject.quotient Q (extensionSourceObject model T.X T.Y T.f)).obj model.nu model.auxiliary))
            (bf : BiHom (tf-sf) (tf+ef)
                (XModLambdaN (model.nu.functor.obj (T.Y.obj model.auxiliary)) Q)),
            Detects (model.convergence (.quotient Q (extensionSourceObject model T.X T.Y T.f)))
              (sf,(tf-sf)+sf,tf+ef) (finiteSourceForExtension model T.X T.Y T.f Q sf tf x)
              (homotopyRegrade (by dsimp; omega) rfl af) ∧
            Detects (model.convergence (.quotient Q (.nu T.Y)))
              (sf+n,(tf-sf)+(sf+n),tf+ef) (finiteTargetForExtension model T.X T.Y T.f Q n sf tf hnf y')
              (homotopyRegrade (by dsimp; omega) rfl bf) ∧
            af ≫ finiteExtensionMap model T.X T.Y T.f Q = bf := by
    intro ag hag hstrict
    let Wh : FiniteExtensionWitness model T.Z (.shift 1 T.X) T.h
        (i+1) l s t xBar suspendedX := by
      convert (Classical.choice hh) using 1
      dsimp only [eg] at hiZ
      omega
    obtain ⟨aZSelected,haZSelected,hδSelected,hSelectedH⟩ :=
      select_finite_extension_source T.Z (.shift 1 T.X) T.h
        (i+1) q hq l s t xBar suspendedX Wh aZ haZ
    have hSelectedBoundary : boundary aZSelected = boundary aZ := by
      dsimp only [boundary]
      rw [hδSelected]
    have hSelectedBoundaryStable
        (hnc : NoCrossingOn model T.Z (n+m+l) (n+m+l-(m-eg)) (s,t))
        (a : BiHom (t-s) t (XModLambdaN Zν i))
        (ha : Detects (model.convergence (.quotient i (.nu T.Z))) (s,t,t)
          (regradeE2 (by simp) (finiteTargetLabel model T.Z i s t 0 xBar)) a) :
        boundary a = boundary aZSelected :=
      (hboundaryStable hnc a ha).trans hSelectedBoundary.symm
    have hstrictSelected : ag ≫ finiteExtensionMap model T.Y T.Z T.g q =
        boundary aZSelected := hstrict.trans hSelectedBoundary.symm
    let aZ := aZSelected
    have haZ := haZSelected
    have hstrict := hstrictSelected
    have hboundaryStable := hSelectedBoundaryStable
    have hSourceReady :
        (FiniteNoCrossing model T.Z (.shift 1 T.X) T.h (i+1) l s t ∧ eh+1<l) ∨
        FiniteExtensionAtSource T.Z (.shift 1 T.X) T.h (i+1) l s t
          xBar suspendedX Wh aZ := by
      rcases hcross with hhcross | hδcross
      · have hncFinite : FiniteNoCrossing model T.Z (.shift 1 T.X) T.h (i+1) l s t := by
          convert hhcross using 1
          dsimp only [eg] at hiZ
          omega
        by_cases hlShort : l≤eh+1
        · right
          exact KIP126.ProofTools.Internal.Leibniz.finite_extension_at_source_short
            T.Z (.shift 1 T.X) T.h (i+1) l s t xBar suspendedX Wh
            (by exact hlShort) hncFinite aZ haZ
        · exact Or.inl ⟨hncFinite,by omega⟩
      · right
        apply hSelectedH
        convert hδcross using 1 <;> dsimp only [eg] at hiZ hqZ <;> omega
    have hSourceShort (hlShort : l≤eh+1) :
        FiniteExtensionAtSource T.Z (.shift 1 T.X) T.h (i+1) l s t
          xBar suspendedX Wh aZ := by
      rcases hSourceReady with ⟨_,hlong⟩ | hsource
      · omega
      · exact hsource
    have hstrictSameSource
        (hnc : NoCrossingOn model T.Z (n+m+l) (n+m+l-(m-eg)) (s,t))
        (a : BiHom (t-s) t (XModLambdaN Zν i))
        (ha : Detects (model.convergence (.quotient i (.nu T.Z))) (s,t,t)
          (regradeE2 (by simp) (finiteTargetLabel model T.Z i s t 0 xBar)) a) :
        ag ≫ finiteExtensionMap model T.Y T.Z T.g q = boundary a := by
      rw [hboundaryStable hnc a ha]
      exact hstrict
    have hagNeg := finite_source_detects_neg T.Y T.Z T.g q (sf+n) (tf+n) y _ hag
    let G := (model.normalizedMap T.Y T.Z T.g).map
    obtain ⟨ug,hugIncl,hugProj,lamg,vg,wg,hlamgIncl,hlamgProj,hvgIncl,hvgProj,hwgIncl,hgTriangle⟩ :=
      quotient_octahedron_fill G q
    have hugFixed := normalized_quotient_maps_equal_on_spheres T.Y T.Z
      (normalizedExponent model.classicalTower T.g)
      (normalizedExponent_le_one model.classicalTower T.g) q hq ug (XModLambdaN.map G q)
      (hugIncl.trans (XModLambdaN.incl_naturality G q))
    have hugStrict : ag ≫ ug = boundary aZ := (hugFixed _ _ ag).trans hstrict
    let Cg := HasFunctorialCofiber.cofib G
    let jg : Zν ⟶ Cg := HasFunctorialCofiber.cofibι G
    let eCg := normalized_g_cofiber_iso T he htriangle
    let eCgShift := normalized_g_shifted_cofiber_iso T he htriangle
    have heCgIncl := normalized_g_shifted_cofiber_inclusion T he htriangle
    have heCgProj := normalized_g_shifted_cofiber_boundary T he htriangle
    have hGj : G ≫ jg = 0 :=
      comp_distTriang_mor_zero₁₂ _ (HasFunctorialCofiber.cofib_distinguished G)
    let ag' : BiHom (t-s-1) (t+i)
        (XModLambdaN ((extensionSourceObject model T.Y T.Z T.g).obj model.nu model.auxiliary) q) :=
      homotopyRegrade (by dsimp [tf,sf]; omega) (by dsimp [tf]; omega) ag
    have hstrict' : ag' ≫ XModLambdaN.map G q =
        biSuspensionHomEquiv (t-s) t i (XModLambdaN Zν q)
          (by simpa only [Nat.add_sub_cancel_left] using
            aZ ≫ ((model.quotients.tower Zν).triangle hi (show i < i+q by omega)).delta) := by
      have regrade_comp {m m' w w' : ℤ} {A B : SyntheticSpectrum}
          (hm : m=m') (hw : w=w') (a : BiHom m w A) (f : A ⟶ B) :
          homotopyRegrade hm hw (a ≫ f) = homotopyRegrade hm hw a ≫ f := by
        subst m'; subst w'; rfl
      have regrade_back {m m' w w' : ℤ} {A : SyntheticSpectrum}
          (hm : m=m') (hw : w=w') (hm' : m'=m) (hw' : w'=w)
          (a : BiHom m w A) : homotopyRegrade hm' hw' (homotopyRegrade hm hw a) = a := by
        subst m'; subst w'; rfl
      have H := congrArg (homotopyRegrade
        (show (tf+n)-(sf+n)=t-s-1 by dsimp [tf,sf]; omega)
        (show tf+n+eg=t+i by dsimp [tf]; omega)) hstrict
      dsimp only [boundary] at H
      rw [regrade_comp,regrade_back] at H
      exact H
    let hg : Cg ⟶
        ((extensionSourceObject model T.Y T.Z T.g).obj model.nu model.auxiliary)⟦(1:ℤ)⟧ :=
      HasFunctorialCofiber.cofibδ G
    have hjghg : jg ≫ hg = 0 :=
      comp_distTriang_mor_zero₂₃ _ (HasFunctorialCofiber.cofib_distinguished G)
    obtain ⟨pGeometry,vGeometry,hpGeometry,hvGeometry,hvSecond⟩ :=
      finite_quotient_octahedral_pullback_desuspended G i q hi hq (t-s) t aZ ag' hstrict'
    obtain ⟨φGeometry,KGeometry,hφGeometry,hKGeometry,hρGeometry⟩ :=
      normalized_octahedral_comparison T.X T.Y Zν Cg _ ef eg
        (by dsimp [ef]; omega) eCg G jg hg hGj hjghg i q hi hq pGeometry hpGeometry
    let cGeometry : BiHom (t-s) t (XModLambdaN Cg (i+q)) := vGeometry ≫ φGeometry
    have hcGeometry : cGeometry ≫ (model.quotients.tower Cg).rho i (i+q) (by omega) =
        aZ ≫ XModLambdaN.map jg i := by
      change (vGeometry ≫ φGeometry) ≫ _ = _
      rw [Category.assoc,hρGeometry,←Category.assoc,hvGeometry]
    let compositeGeometry :=
      (SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(i:ℤ))).map
        (XModLambdaN.map G (i+q-i)) ≫
          ((model.quotients.tower Zν).triangle hi (show i < i+q by omega)).lambdaMap
    have hsecondGeometry : cGeometry ≫ XModLambdaN.map hg (i+q) =
        (vGeometry ≫ HasFunctorialCofiber.cofibδ compositeGeometry) ≫ KGeometry := by
      dsimp only [cGeometry,compositeGeometry]
      rw [Category.assoc,←hKGeometry,←Category.assoc]
    obtain ⟨dGeometry,tGeometry,hEdgeGeometry⟩ :=
      quotient_unquotiented_boundary_defect G i q hi hq
        φGeometry KGeometry hφGeometry hKGeometry
    obtain ⟨bGeometry,hbGeometry⟩ := quotient_lift_image_division jg hg hjghg
      i (i+q) hi (by omega) aZ cGeometry hcGeometry
    let cShift : BiHom (t-s) t (XModLambdaN
        ((SyntheticCategory.biShift (1,ef+eg)).obj
          (model.nu.functor.obj (T.X.obj model.auxiliary))) (i+q)) :=
      cGeometry ≫ XModLambdaN.map eCg.hom (i+q)
    have hcShift : cShift ≫ (model.quotients.tower
        ((SyntheticCategory.biShift (1,ef+eg)).obj
          (model.nu.functor.obj (T.X.obj model.auxiliary)))).rho i (i+q) (by omega) =
        aZ ≫ XModLambdaN.map (jg ≫ eCg.hom) i := by
      dsimp only [cShift]
      rw [Category.assoc, ← (model.quotients.natural eCg.hom).rho_naturality (by omega),
        ← Category.assoc, hcGeometry, Category.assoc,
        ← model.quotients.functoriality.map_comp]
    letI := model.exactness.shiftCommShift (1,ef+eg)
    letI := model.exactness.shiftExact (1,ef+eg)
    obtain ⟨eQi,heQi,_⟩ := quotient_shift_exists model.quotients.coherence (1,ef+eg) i
      (model.nu.functor.obj (T.X.obj model.auxiliary))
    obtain ⟨eQr,heQr,_⟩ := quotient_shift_exists model.quotients.coherence (1,ef+eg) (i+q)
      (model.nu.functor.obj (T.X.obj model.auxiliary))
    let cNu : BiHom (t-s-1) (t-(ef+eg))
        (XModLambdaN (model.nu.functor.obj (T.X.obj model.auxiliary)) (i+q)) :=
      quotientShiftDesuspend T.X (1,ef+eg) (i+q) eQr (t-s) t cShift
    let aNu : BiHom (t-s-1) (t-(ef+eg))
        (XModLambdaN (model.nu.functor.obj (T.X.obj model.auxiliary)) i) :=
      quotientShiftDesuspend T.X (1,ef+eg) i eQi (t-s) t
        (aZ ≫ XModLambdaN.map (jg ≫ eCg.hom) i)
    have hcNu : cNu ≫ (model.quotients.tower
        (model.nu.functor.obj (T.X.obj model.auxiliary))).rho i (i+q) (by omega) = aNu :=
      quotient_shift_desuspend_restriction T.X (1,ef+eg) i (i+q) hi (by omega)
        eQi eQr heQi heQr (t-s) t _ cShift hcShift
    let k : ℕ := (l-eh).toNat
    have hkZ : (k:ℤ)=l-eh := by
      have := Wh.length_lower
      dsimp only [k,eh]
      exact Int.toNat_of_nonneg (by omega)
    have hki : k < i := by
      have hh := Wh.length_upper
      dsimp only [eh] at hkZ
      omega
    have hweight : t-(ef+eg)=tf-k := by
      have hsum : ef+eg+eh=1 := he
      dsimp only [tf]
      omega
    let aNuNative : BiHom (tf-sf) (tf-k)
        (XModLambdaN (model.nu.functor.obj (T.X.obj model.auxiliary)) i) :=
      homotopyRegrade (by dsimp [tf,sf]; omega) hweight aNu
    let cNuNative : BiHom (tf-sf) (tf-k)
        (XModLambdaN (model.nu.functor.obj (T.X.obj model.auxiliary)) (i+q)) :=
      homotopyRegrade (by dsimp [tf,sf]; omega) hweight cNu
    have hcNuNative : cNuNative ≫ (model.quotients.tower
        (model.nu.functor.obj (T.X.obj model.auxiliary))).rho i (i+q) (by omega) = aNuNative := by
      dsimp only [cNuNative,aNuNative]
      rw [←regrade_comp,hcNu]
    have hTargetReady :
        FiniteNoCrossing model T.Z (.shift 1 T.X) T.h (i+1) l s t ∨
        Detects (model.convergence (.quotient i (.nu T.X))) (sf,tf,tf-k)
          (finiteTargetLabel model T.X i sf tf k x) aNuNative := by
      rcases hSourceReady with ⟨hnc,_⟩ | hsource
      · exact Or.inl hnc
      · right
        exact normalized_h_target_detects_native T he htriangle i l s t xBar x suspendedX
          Wh hsusp aZ hsource eQi heQi
    have hTargetShort (hlShort : l≤eh+1) :
        Detects (model.convergence (.quotient i (.nu T.X))) (sf,tf,tf-k)
          (finiteTargetLabel model T.X i sf tf k x) aNuNative :=
      normalized_h_target_detects_native T he htriangle i l s t xBar x suspendedX
        Wh hsusp aZ (hSourceShort hlShort) eQi heQi
    have hk0 : k=0 := by dsimp [k,eh]; rw [hlZero]; simp
    have hTarget := hTargetShort (by dsimp [eh]; omega)
    have hcDetected := finite_target_rho_detects T.X i (i+q) k hki (by omega)
      sf tf x aNuNative hTarget cNuNative hcNuNative
    have hcNative : Detects (model.convergence (.quotient (i+q) (.nu T.X))) (sf,tf,tf)
        (regradeE2 (by simp) (finiteTargetLabel model T.X (i+q) sf tf 0 x))
        (homotopyRegrade rfl (by omega : tf-k=tf) cNuNative) := by
      exact zero_level_native_detection T.X (i+q) sf tf k hk0 x cNuNative hcDetected
    have hSurvival : ∃ c : BiHom (tf-sf) tf (XModLambdaN (nuZero model T.X) Q),
        c ≫ (model.quotients.tower (nuZero model T.X)).rho 1 Q hQ = firstLabel model T.X sf tf x := by
      have hIQ : i+q=Q := by dsimp [ef,eg,eh] at *; omega
      have transport (a b : ℕ) (hab : a=b) (ha : 0<a) (hb : 0<b)
          (hh : ∃ c : BiHom (tf-sf) tf (XModLambdaN (nuZero model T.X) a),
            c≫(model.quotients.tower (nuZero model T.X)).rho 1 a ha=firstLabel model T.X sf tf x) :
          ∃ c : BiHom (tf-sf) tf (XModLambdaN (nuZero model T.X) b),
            c≫(model.quotients.tower (nuZero model T.X)).rho 1 b hb=firstLabel model T.X sf tf x := by
        subst b
        exact hh
      exact transport (i+q) Q hIQ (by omega) hQ
        (native_bottom_detected_first_lift T.X (i+q) (by omega) sf tf x _ hcNative)
    let Yν := model.nu.functor.obj (T.Y.obj model.auxiliary)
    let Xν := model.nu.functor.obj (T.X.obj model.auxiliary)
    let Af := (extensionSourceObject model T.X T.Y T.f).obj model.nu model.auxiliary
    let Ag := (extensionSourceObject model T.Y T.Z T.g).obj model.nu model.auxiliary
    letI := model.exactness.shiftCommShift (0,eg)
    letI := model.exactness.shiftExact (0,eg)
    obtain ⟨eAg,heAg,_⟩ := quotient_shift_exists model.quotients.coherence (0,eg) (i+q) Yν
    obtain ⟨esusp,hesusp⟩ := quotient_suspension_inclusion_exists Ag (i+q)
    letI := model.exactness.shiftCommShift (0,ef)
    letI := model.exactness.shiftExact (0,ef)
    obtain ⟨εe,hεe,_⟩ := quotient_shift_exists model.quotients.coherence (0,ef) (i+q) Xν
    letI := model.exactness.shiftCommShift (1,eg)
    letI := model.exactness.shiftExact (1,eg)
    obtain ⟨εA,hεA,_⟩ := quotient_shift_exists model.quotients.coherence (1,eg) (i+q) Af
    have Wgq : FiniteExtensionWitness model T.Y T.Z T.g (q+1) m (sf+n) (tf+n) y yBar := by
      convert Wg using 1 <;> omega
    obtain ⟨c',hρ',hu'⟩ := sphere_source_actual_mahowald_second_image T he htriangle hY
      i q hi hq (t-s) t m (sf+n) (tf+n)
      (by dsimp [sf,tf]; omega) (by dsimp [sf,tf]; omega) hqZ y yBar Wgq
      (s,t) xBar (by convert hd.2 using 1 <;> omega) hyBar
      eQr eAg esusp hesusp φGeometry KGeometry hφGeometry hKGeometry
      vGeometry ag hag hvSecond
    rw [normalized_included_source_label] at hu'
    let Dzero : SyntheticObject := .shift (0,(i:ℤ)+eg) (.quotient (i+q) (.nu T.Y))
    let Jzero := (SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) (1,-(i:ℤ))).preimage
      ((biSuspensionIso (i:ℤ) (XModLambdaN Ag (i+q-i))).hom≫
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map
          ((model.quotients.tower Ag).triangle hi (show i < i+q by omega)).lambdaMap≫esusp.inv≫
            (commonEdgeTargetFlatIso Yν eg i q esusp eAg).hom)
    have huLength := finite_edge_detection_source_length T.Y T.Z T.g (i+q-i) q
      (by omega) (sf+n) (tf+n) y Dzero Jzero _ hu'

    have hagNative := actual_extension_source_native_detects T.Y T.Z T.g q (sf+n) (tf+n) y ag hag
    rw [normalized_included_source_label] at hagNative
    obtain ⟨agFinal,hagFinal⟩ := finite_native_bottom_detection_reindex_exists T.Y q (i+q-i)
      (by omega) eg (sf+n) (tf+n) y ag hagNative
    have hFull := minimal_corrected_total_extension T he htriangle i q hi hq sf tf n
      (n+m+l-(m-eg)) (by dsimp [ef,eg,eh] at *; omega)
      (t-s) t (by dsimp [sf,tf]; omega) (by dsimp [sf,tf,ef,eg,eh] at *; omega)
      x y eQr εe εA eAg esusp heQr hεe hεA heAg hesusp cGeometry
      (homotopyRegrade (by dsimp [sf,tf]; omega) (by dsimp [sf,tf,ef,eg,eh] at *; omega) c')
      (by
        have hr := congrArg (homotopyRegrade
          (show (tf+n)-(sf+n)=t-s-1 by dsimp [sf,tf]; omega)
          (show tf+n+eg=t+i by dsimp [sf,tf]; omega)) hρ'
        simpa only [regrade_comp,common_regrade_trans,homotopy_regrade_inverse,homotopy_regrade_self,cGeometry,
          Category.assoc] using hr)
      (by simpa only [cNuNative,cNu,cShift,regrade_comp,common_regrade_trans] using hcNative)
      agFinal hagFinal
      (by
        simpa only [regrade_comp,common_regrade_trans,homotopy_regrade_inverse,homotopy_regrade_self,
          Dzero,Jzero,Ag,Yν,eg,SyntheticObject.obj] using huLength)
    refine ⟨hSurvival,?_⟩
    have hIQ : i+q=Q := by dsimp [ef,eg,eh] at *; omega
    exact Eq.mp (congrArg (fun r => ZeroLayerDetectedPair T.X T.Y T.f r n sf tf
      (n+m+l-(m-eg)) hnf x y) hIQ) hFull
  obtain ⟨ag,hag,hagDetect⟩ := finite_top_extension_preimage
    T.Y T.Z T.g pg m (sf+n) (tf+n) y yBar Wg (by dsimp [pg,eg]; omega)
    (boundary aZ) hdelta
  obtain ⟨⟨c,hc⟩,y',hcong,af,bf,haf,hbf,hfstrict⟩ := may_boundary_lift ag hagDetect hag
  have hxLater : IsCycle model T.X (n+m+eh) (sf,tf) x := by
    refine ⟨by dsimp [ef,eg,eh] at *; omega,?_⟩
    have hcR := (KIP126.Literature.Standard.bhs_finite_lift T.X Q hQ sf tf x).mpr ⟨c,hc⟩
    have hc' := ((isCycle_iff_reaches model T.X (Q+1) (by omega) (sf,tf) x).mpr hcR).2
    simpa only [add_sub_cancel_right,hQZ] using hc'
  have hyLater : IsCycle model T.Y
      (((Q+1:ℕ):ℤ)-1-n+normalizedExponent model.classicalTower T.f) (sf+n,tf+n) y' := by
    have hlevel : ((Q+1:ℕ):ℤ)-1-n+normalizedExponent model.classicalTower T.f = m-eg+1 := by
      simp only [Nat.cast_add,Nat.cast_one,hQZ]
      dsimp [ef,eg,eh] at *
      omega
    rw [hlevel]
    refine ⟨by dsimp [eg]; omega,?_⟩
    have hby := boundaries_le_cycles model T.Y (sf+n,tf+n)
      (n+m+l-(m-eg)) (m-eg+1) hcong
    have hadd := (cycles model T.Y (m-eg+1) (sf+n,tf+n)).add_mem hby hy.2
    simpa only [sub_add_cancel] using hadd
  obtain ⟨xf,yf,hxf,hyf,heq⟩ := extension_equation_of_detected_pair
    (model.convergentMap (.quotient Q (extensionSourceObject model T.X T.Y T.f))
      (.quotient Q (.nu T.Y)) (finiteExtensionMap model T.X T.Y T.f Q))
    (tf-sf,tf+ef) sf n hn0 _ _ af bf haf hbf hfstrict
  refine ⟨hxLater,y',?_,⟨by dsimp [ef,eg,eh] at *; omega,hcong⟩⟩
  have hpage : (n+m+1+normalizedExponent model.classicalTower T.h).toNat = Q+1 := by
    dsimp [Q,eh,ef,eg] at *
    omega
  rw [hpage]
  refine ⟨{
    page_ge_two := by omega
    length_lower := hnf
    length_upper := by simp only [Nat.cast_add,Nat.cast_one,hQZ]; dsimp [ef,eg,eh] at *; omega
    source_cycle := (isCycle_iff_reaches model T.X ((Q+1:ℕ):ℤ) (by omega) (sf,tf) x).mp
      (by simpa only [Nat.cast_add,Nat.cast_one,add_sub_cancel_right,hQZ] using hxLater)
    target_cycle := (isCycle_iff_reaches model T.Y
      (((Q+1:ℕ):ℤ)-n+normalizedExponent model.classicalTower T.f)
      (by have hp := hyLater.1; omega) (sf+n,tf+n) y').mp
      (by
        rw [show ((Q+1:ℕ):ℤ)-n+normalizedExponent model.classicalTower T.f-1 =
          ((Q+1:ℕ):ℤ)-1-n+normalizedExponent model.classicalTower T.f by omega]
        exact hyLater)
    source := xf
    target := yf
    source_rep := hxf
    target_rep := hyf
    equation := heq }⟩

/-- The exact numerical MH2 instance consumed in Main's NuThree argument. -/
private theorem main_nu_mahowald_zero_layer
    (x : Ambient model (.shift 3 .sphere) (8,133))
    (y : Ambient model .sphere (11,136))
    (xBar : Ambient model .nuCofiber (8,134))
    (yBar : Ambient model .nuCofiber (11,136))
    (suspendedX : Ambient model (.shift 1 (.shift 3 .sphere)) (8,134))
    (hx : IsCycle model (.shift 3 .sphere) 2 (8,133) x)
    (hy : IsCycle model .sphere 1 (11,136) y)
    (hxBar : IsCycle model .nuCofiber 2 (8,134) xBar)
    (hyBar : IsPermanent model .nuCofiber (11,136) yBar)
    (hsusp : (model.classicalSuspension (.shift 3 .sphere)).DesuspendsClass
      8 134 suspendedX x)
    (hh : FiniteExtension model .nuCofiber (.shift 1 (.shift 3 .sphere))
      (HasFunctorialCofiber.cofibδ model.auxiliary.nuMap) 3 0 8 134 xBar suspendedX)
    (hd : DifferentialAt model .nuCofiber 3 (8,134) (11,136) xBar yBar)
    (hcross : FiniteNoCrossing model .nuCofiber (.shift 1 (.shift 3 .sphere))
        (HasFunctorialCofiber.cofibδ model.auxiliary.nuMap) 3 0 8 134 ∨
      NoCrossingOn model .nuCofiber 3 3 (8,134))
    (hg : FiniteExtension model .sphere .nuCofiber
      (HasFunctorialCofiber.cofibι model.auxiliary.nuMap) 2 0 11 136 y yBar) :
    IsCycle model (.shift 3 .sphere) 3 (8,133) x ∧
      ∃ y' : Ambient model .sphere (11,136),
        FiniteExtension model (.shift 3 .sphere) .sphere model.auxiliary.nuMap
          4 3 8 133 x y' ∧ Congruent model .sphere 3 (11,136) y' y := by
  have hmZero : (0:ℤ) = (normalizedExponent model.classicalTower
      model.auxiliary.nuRouteTriangle.g : ℤ) := by
    exact_mod_cast KIP126.Literature.Standard.nuCofiber_bottom_exponent.symm
  have hlZero : (0:ℤ) = (normalizedExponent model.classicalTower
      model.auxiliary.nuRouteTriangle.h : ℤ) := by
    exact_mod_cast KIP126.Literature.Standard.nuCofiber_top_exponent.symm
  have h := generalized_mahowald_zero_layer_sphere model.auxiliary.nuRouteTriangle rfl
    KIP126.Literature.Standard.nuCofiber_exponent_sum
    (KIP126.Literature.Standard.nuCofiber_triangle _) 3 0 0 8 134 hmZero hlZero
    x y xBar yBar suspendedX
  have hf := KIP126.Literature.Standard.nuCofiber_nu_exponent
  have hb := KIP126.Literature.Standard.nuCofiber_bottom_exponent
  have ht := KIP126.Literature.Standard.nuCofiber_top_exponent
  change normalizedExponent model.classicalTower model.auxiliary.nuRouteTriangle.f=1 at hf
  simp only [hf,hb,ht,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Int.reduceSub,
    Int.reduceToNat,add_zero,sub_zero] at h
  exact h (by decide) (by decide) (by decide) hx hy hxBar hyBar hsusp hh hd hcross hg

end
end KIP126.ProofTools.Internal.Mahowald
