module
public import KIP126.Def.ProofTools.Laws
import all KIP126.Def.ProofTools.GeneralizedMahowald.Sphere
import all KIP126.Def.ProofTools.GeneralizedMahowald.Adjacent
import all KIP126.Def.ProofTools.GeneralizedMahowald.FinalOperations
import all KIP126.Def.ProofTools.GeneralizedMahowald.Detection
import all KIP126.Def.ProofTools.GeneralizedMahowald.PageCalculus
import all KIP126.Def.ProofTools.GeneralizedMahowald.BoundaryDetection
import all KIP126.Def.ProofTools.DetectionOperations
/-! AimPaper Theorem 6.12, retaining the complete proof from bbac1fc05843 (MIT).
The original MH1 and MH2 geometric gaps remain in their original branches;
all formerly proved representative, quotient and case-assembly steps are retained. -/
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
          (homotopyRegrade (by dsimp; omega) rfl (boundary aZ)) := by
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
          by_cases hZ : T.Z = ClassicalObject.sphere
          · have sphere_reindexed (X : ClassicalObject) (hX : X=.sphere)
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
              subst X
              subst r
              subst u
              subst v
              exact sphere_mahowald_case i q hi hq s t x' y' hdy hperm
            obtain ⟨a,ha,hda⟩ := sphere_reindexed T.Z hZ (n+m+l) (sf+n+m) (tf+n+m)
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
          · -- MH1: the remaining nonzero comparison is for T.Z other than the sphere.
            sorry
    obtain ⟨c,hc,hdelta⟩ := target_correction
    have hfirst : (a0+c) ≫ (model.quotients.tower Zν).rho 1 i hi =
        firstLabel model T.Z s t xBar ≫
          XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app Zν) 1 := by
      rw [Preadditive.add_comp,ha0first,hc,add_zero]
    exact ⟨a0+c,first_label_detects_unshifted T.Z i hi s t xBar (a0+c) hfirst,hdelta⟩
  obtain ⟨aZ,haZ,hdelta⟩ := boundary_representative
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
    -- MH2, MainPaper lines 1875–1917: hcross synchronizes the h-extension
    -- with the delta representative aZ; htriangle and may.boundary then
    -- give the actual lift through lambda^Q and the strict f_Q square.
    -- hsusp identifies the ordinary suspension label with x. Transport
    -- through lambda powers must retain the finite B_(n+m+l-(m-e(g)))
    -- ambiguity in y', not merely equality in the infinity quotient.
    -- May supplies a signed homotopy relation; removing its sign requires
    -- the mod-2 label comparison, not an assertion of characteristic two
    -- for the homotopy groups. No FiniteExtension conclusion is assumed here.
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
