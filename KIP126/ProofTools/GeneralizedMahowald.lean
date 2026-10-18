module
public import KIP126.ProofTools.Laws
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
/-! AimPaper Theorem 6.12, retaining the complete proof from bbac1fc05843 (MIT).
The finite boundary comparison (MH1) is proved for every selected object.
The original May boundary lift (MH2) remains pending; representative, quotient
and case-assembly steps use the same fixed mathematical objects. -/
@[expose] section
namespace KIP126.ProofTools.Standard
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard KIP126.Literature
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
public theorem generalizedMahowald
    (T : TriangleData model.auxiliary) :
    GeneralizedMahowaldLaw model T := by
  intro he htriangle n m l s t
  dsimp only
  intro x y xBar yBar suspendedX hn hm hl
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
    have hActualFSource
        (htarget : Detects (model.convergence (.quotient i (.nu T.X))) (sf,tf,tf-k)
          (finiteTargetLabel model T.X i sf tf k x) aNuNative) :=
      normalized_f_raw_source_unshift_detects T he htriangle (i+q) k (by omega)
        sf tf (t-s) t x (by dsimp [tf,sf]; omega) hweight eQr heQr cGeometry
        (finite_target_rho_detects T.X i (i+q) k hki (by omega)
          sf tf x aNuNative htarget cNuNative hcNuNative)
    have hActualFSourceReady := hTargetReady.imp (fun h => h) hActualFSource
    have hDividedSourceReady :
        FiniteNoCrossing model T.Z (.shift 1 T.X) T.h (i+1) l s t ∨
        ∃ b : BiHom (tf-sf) tf
            (XModLambdaN (model.nu.functor.obj (T.X.obj model.auxiliary)) (i+q-k)),
          b ≫ (model.quotients.tower _).rho 1 (i+q-k) (by omega) =
            firstLabel model T.X sf tf x ≫
              XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1 ∧
          Detects (model.convergence (.quotient (i+q-k) (.nu T.X))) (sf,tf,tf)
            (regradeE2 (by simp) (finiteTargetLabel model T.X (i+q-k) sf tf 0 x)) b ∧
          KIP126.ProofTools.Internal.Leibniz.finiteLambdaDivisionClass T.X (i+q) k
            (by omega) sf tf b = cNuNative := by
      rcases hTargetReady with hnc | htarget
      · exact Or.inl hnc
      · right
        have hcDetected := finite_target_rho_detects T.X i (i+q) k hki (by omega)
          sf tf x aNuNative htarget cNuNative hcNuNative
        exact finite_target_source_division_exact T.X (i+q) k (by omega)
          sf tf x cNuNative hcDetected
    have hSurvivalReady :
        FiniteNoCrossing model T.Z (.shift 1 T.X) T.h (i+1) l s t ∨
        (∃ c : BiHom (tf-sf) tf (XModLambdaN (nuZero model T.X) Q),
          c ≫ (model.quotients.tower (nuZero model T.X)).rho 1 Q hQ =
            firstLabel model T.X sf tf x) := by
      rcases hDividedSourceReady with hnc | hdivided
      · exact Or.inl hnc
      · right
        have hQk : i+q-k=Q := by omega
        obtain ⟨b,hb,_,_⟩ := hdivided
        let f : model.nu.functor.obj (T.X.obj model.auxiliary) ⟶ nuZero model T.X :=
          SyntheticCategory.biShift_zero.inv.app _
        have hlift : ∃ c : BiHom (tf-sf) tf (XModLambdaN (nuZero model T.X) (i+q-k)),
            c ≫ (model.quotients.tower _).rho 1 (i+q-k) (by omega) =
              firstLabel model T.X sf tf x := by
          refine ⟨b≫XModLambdaN.map f (i+q-k),?_⟩
          rw [Category.assoc,←(model.quotients.natural f).rho_naturality (by omega),
            ←Category.assoc,hb]
          simp only [f,Category.assoc,←model.quotients.functoriality.map_comp,
            Iso.hom_inv_id_app,model.quotients.functoriality.map_id,Category.comp_id]
        have transport (q₁ q₂ : ℕ) (h : q₁=q₂) (hq₁ : 0<q₁) (hq₂ : 0<q₂)
            (hh : ∃ c : BiHom (tf-sf) tf (XModLambdaN (nuZero model T.X) q₁),
              c ≫ (model.quotients.tower (nuZero model T.X)).rho 1 q₁ hq₁ =
                firstLabel model T.X sf tf x) :
            ∃ c : BiHom (tf-sf) tf (XModLambdaN (nuZero model T.X) q₂),
              c ≫ (model.quotients.tower (nuZero model T.X)).rho 1 q₂ hq₂ =
                firstLabel model T.X sf tf x := by
          subst q₂
          exact hh
        exact transport _ _ hQk (by omega) hQ hlift
    -- MH2, MainPaper lines 1875–1917: vGeometry is constructed from the
    -- prescribed pair aZ/ag'; hvGeometry and hvSecond fix both of its images.
    -- The same cGeometry=vGeometry≫φGeometry lies in the fixed λ^(i+q)
    -- quotient. Finite no-return proves its strict ρ equation hcGeometry.
    -- hsecondGeometry factors its second image through the fixed KGeometry
    -- evaluated on the prescribed ag' (via hvSecond). It remains to identify
    -- this K evaluation with the required signed λ_i image of ag'.
    -- hEdgeGeometry now records the actual unquotiented edge defect for
    -- these same φGeometry/KGeometry, retaining both dGeometry and tGeometry.
    -- Passing that defect to the prescribed finite source still requires
    -- the filtered correction; its two residual terms are not set to zero.
    -- hbGeometry independently retains membership in the actual λ_i image;
    -- its arbitrary preimage bGeometry is not identified with ag'.
    -- cShift transports that same lift to the specified shifted νX;
    -- heCgIncl/heCgProj retain the normalized h map and rotated −f map.
    -- cNu is that same lift in the unshifted νX quotient; hcNu preserves
    -- its restriction after the chosen quotient/shift comparison.
    -- ug and its complementary lamg filling are selected by three actual
    -- octahedra. hgTriangle retains the signed triangle on Cg, cone(ug)
    -- and cone(F_q G)[1], with hlamgIncl/hlamgProj and hvgIncl/hvgProj/hwgIncl
    -- recording its actual comparison maps. hugStrict identifies the
    -- action of ug on ag with the fixed quotient map, including exponent one.
    -- aZ is selected from the actual h witness in the differential
    -- no-crossing branch, with the same unshifted label and δ image.
    -- hSourceReady retains either the finite h no-crossing hypothesis or
    -- that actual h-source/target detection and its strict inverse transport.
    -- The source comparison uses the registered positive-shift compatibility.
    -- hTargetReady identifies the actual aNu with the prescribed weighted
    -- x label in the differential no-crossing or short h branch (k<=1).
    -- hTargetShort gives this detection directly under the short length
    -- bound, with the excluded branch retaining its strict k>=2 range.
    -- hSurvivalReady then
    -- supplies the required Q_Q firstLabel lift via the actual cNu restriction.
    -- hDividedSourceReady also divides that same cNuNative by lambda^k
    -- while preserving its strict lambda image and the exact original x
    -- first label, using a torsion lift of the source boundary ambiguity.
    -- The target filtration of its actual f image remains to be proved.
    -- hActualFSourceReady transports the same original cGeometry to the
    -- actual signed normalized f source, retaining the native lambda^k x
    -- detection after inverse ef transport, with internally chosen quotient
    -- comparisons and no equality between independent commShift choices.
    -- The remaining common-lift comparison must impose the second May
    -- equation, finish the finite h no-crossing branch, and
    -- retain the finite B_(n+m+l-(m-e(g))) ambiguity after λ division.
    -- The proved label sign comparison applies only after detection;
    -- no exponent-two assertion is made for synthetic homotopy groups.
    sorry
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
end
end KIP126.ProofTools.Standard
