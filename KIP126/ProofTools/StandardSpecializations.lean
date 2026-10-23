module

public import KIP126.ProofTools.GeneralizedLeibnizAtLevel
public import KIP126.ProofTools.GeneralizedMahowald.FiniteLevelAssembly
public import KIP126.AdamsComputation.Standard
import all KIP126.ProofTools.SyntheticProgramRules
import all KIP126.ProofTools.Paper.NumericalExamples
import all KIP126.ProofTools.Paper.NuNumericalExtensions
import all KIP126.ProofTools.Paper.NuCofiberNumericalDifferential

/-! Fixed-model specializations of the extension-square, Leibniz and
Mahowald rules, and numerical conclusions with their specified actual labels.
The proofs retain the registered upstream model and comparison obligations.
-/

@[expose] section
namespace KIP126.ProofTools.Standard
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Standard
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
open KIP126.ProofTools.Internal.Leibniz KIP126.ProofTools.Paper
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000


public def QuotientBoundaryCutoffStatement (A B : SyntheticObject)
    (g : A.obj model.nu model.auxiliary ⟶ B.obj model.nu model.auxiliary)
    (q : ℕ) : Prop :=
  let QA : SyntheticObject := .quotient q A
  let QB : SyntheticObject := .quotient q B
  let SA : SyntheticObject := .shift (1,-(q:ℤ)) A
  let SB : SyntheticObject := .shift (1,-(q:ℤ)) B
  let top := model.convergentMap QA QB (XModLambdaN.map g q)
  let left := model.convergentMap QA SA ((XModLambdaN.proj (A.obj model.nu model.auxiliary) q ≫
    (KIP126.ProofTools.Internal.Mahowald.biSuspensionIso q (A.obj model.nu model.auxiliary)).inv))
  let bottom := model.convergentMap SA SB ((SyntheticCategory.biShift (1,-(q:ℤ))).map g)
  let right := model.convergentMap QB SB ((XModLambdaN.proj (B.obj model.nu model.auxiliary) q ≫
    (KIP126.ProofTools.Internal.Mahowald.biSuspensionIso q (B.obj model.nu model.auxiliary)).inv))
  ∀ (p : ℤ × ℤ) (s M b L κ : ℤ)
    (_hM : 0 ≤ M) (_hb : 0 ≤ b) (_hL : 0 ≤ L)
    (_hκ : 0 < κ) (_hκD : κ ≤ b+L-M)
    (ξ : ((model.family.obj (QA.obj model.nu model.auxiliary)).sequence.ssData
      (s,p.1+s,p.2)).eInfty)
    (η : ((model.family.obj (QB.obj model.nu model.auxiliary)).sequence.ssData
      (s+M,p.1+(s+M),p.2)).eInfty)
    (ζ : ((model.family.obj (SA.obj model.nu model.auxiliary)).sequence.ssData
      (s+b,p.1+(s+b),p.2)).eInfty)
    (ω : ((model.family.obj (SB.obj model.nu model.auxiliary)).sequence.ssData
      (s+b+L,p.1+(s+b+L),p.2)).eInfty),
  TowerExtensionEquation top p s M ξ η →
  TowerExtensionEquation left p s b ξ ζ →
  TowerExtensionEquation bottom p (s+b) L ζ ω →
  ((∀ u v : ℤ, s < u → u ≤ v → v ≤ s+M →
      ∀ source target, ¬ TowerEssentialExtension top p u (v-u) source target) ∨
    (∀ u v : ℤ, s < u → u ≤ v → v ≤ s+b →
      ∀ source target, ¬ TowerEssentialExtension left p u (v-u) source target)) →
  (∀ u v : ℤ, s+b < u → u ≤ v → s+M+κ ≤ v → v ≤ s+b+L →
    ∀ source target, ¬ TowerEssentialExtension bottom p u (v-u) source target) →
  TowerExtensionEquation right p (s+M) (κ-1) η 0 →
  (∀ u v : ℤ, s+M < u → u ≤ v → v ≤ s+M+(κ-1) →
    ∀ source target, ¬ TowerEssentialExtension right p u (v-u) source target) →
  TowerExtensionEquation right p (s+M) (b+L-M) η
    ((eqToHom (congrArg (fun q => ((model.family.obj
      (SB.obj model.nu model.auxiliary)).sequence.ssData q).eInfty)
      (show (s+b+L,p.1+(s+b+L),p.2) =
        (s+M+(b+L-M),p.1+(s+M+(b+L-M)),p.2) by ext <;> dsimp <;> omega))) ω)

public theorem cutoffLeibnizSquare
    (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (q : ℕ) : QuotientBoundaryCutoffStatement
      (extensionSourceObject model X Y f) (.nu Y)
      (model.normalizedMap X Y f).map q := by
  change KIP126.ProofTools.Internal.ProgramRules.QuotientBoundaryCutoffStatement
    (extensionSourceObject model X Y f) (.nu Y)
    (model.normalizedMap X Y f).map q
  exact KIP126.ProofTools.Internal.ProgramRules.cutoffLeibnizSquare X Y f q


public theorem ssCutoffSquareAtLevel
    (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (page level : ℕ) (_hpage : 2 ≤ page) : QuotientBoundaryCutoffStatement
      (extensionSourceObject model X Y f) (.nu Y)
      (model.normalizedMap X Y f).map (page+level-1) := by
  change KIP126.ProofTools.Internal.ProgramRules.QuotientBoundaryCutoffStatement
    (extensionSourceObject model X Y f) (.nu Y)
    (model.normalizedMap X Y f).map (page+level-1)
  exact KIP126.ProofTools.Internal.ProgramRules.ssCutoffSquareAtLevel X Y f page level _hpage


public theorem ssLeibnizAtLevelZero
    (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (page : ℕ) (b M L s t : ℤ)
    (x : Ambient model X (s,t)) (y : Ambient model Y (s+M,t+M))
    (u : Ambient model X (s+b,t+b-1))
    (v : Ambient model Y (s+b+L,t+b-1+L))
    (hpage : 2 ≤ page) (hpageb : (page:ℤ) ≤ b)
    (hM : (normalizedExponent model.classicalTower f:ℤ) ≤ M)
    (hMUpper : M ≤ (page:ℤ)-2+normalizedExponent model.classicalTower f)
    (hL : (normalizedExponent model.classicalTower f:ℤ) ≤ L)
    (hu : IsPermanent model X (s+b,t+b-1) u)
    (hv : IsPermanent model Y (s+b+L,t+b-1+L) v)
    (hdx : DifferentialAt model X b (s,t) (s+b,t+b-1) x u)
    (hFinite : KIP126.ProofTools.Standard.LevelFiniteExtension X Y f page 0 M s t x y)
    (hInfinity : InfiniteExtension model X Y f L (s+b) (t+b-1) u v)
    (hsource : KIP126.ProofTools.Standard.LevelBoundaryNoCrossing X Y f page 0 b s t ∨
      KIP126.ProofTools.Standard.LevelFiniteNoCrossing X Y f page 0 M s t)
    (hbottom : KIP126.ProofTools.Standard.LevelBottomNoCrossing X Y f page 0 b L s t) :
    DifferentialAt model Y (b+L-M) (s+M,t+M) (s+b+L,t+b-1+L) y v := by
  exact KIP126.ProofTools.Internal.ProgramRules.ssLeibnizAtLevelZero
    X Y f page b M L s t x y u v hpage hpageb hM hMUpper hL hu hv
    hdx hFinite hInfinity hsource hbottom


public def FiniteMahowaldZeroInputStatement
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g +
      normalizedExponent model.classicalTower T.h = 1) : Prop :=
  let shiftFinitePageLabel (V : SyntheticObject) (δ : ℤ × ℤ)
      (q : Tridegree)
      (x : (model.family.obj (V.obj model.nu model.auxiliary)).E₂ q) :
      (model.family.obj ((SyntheticObject.shift δ V).obj model.nu model.auxiliary)).E₂
        (q.1,q.2.1+δ.1,q.2.2+δ.2) :=
    regradeE2 (by
      ext <;> dsimp
      omega)
      ((KIP126.AdamsSynthetic.Standard.shift_page δ V 2 (by decide)
        (q.2.1-q.1,q.2.2) q.1).hom (regradeE2 (by ext <;> simp) x))
  ∀ (_hT : NormalizedTriangleCompatible model T he)
    (n₁ m₁ k : ℕ) (_hn₁ : 0 < n₁) (s t : ℤ),
  let i : ℕ := 0
  let j : ℕ := 0
  let hj : j < n₁ := _hn₁
  let ef : ℤ := normalizedExponent model.classicalTower T.f
  let eg : ℤ := normalizedExponent model.classicalTower T.g
  let eh : ℤ := normalizedExponent model.classicalTower T.h
  let n : ℤ := n₁+ef
  let m : ℤ := m₁+eg
  let l : ℤ := k+eh
  let r : ℤ := n+m+l
  let A : ℕ := n₁+k+i-j
  let B : ℕ := m₁+j+1
  let N : ℕ := A+B
  let K : ℕ := i+k
  let J : ℕ := A+j
  let Q : ℕ := N-K
  let V := normalizedTriangle model T he
  let VX : SyntheticObject := .shift (0,ef) (.nu T.X)
  let VY : SyntheticObject := .nu T.Y
  let VZ : SyntheticObject := .shift (0,-eg) (.nu T.Z)
  let QA : SyntheticObject := .quotient A VZ
  let HA : SyntheticObject := .shift (1,0) (.quotient A VX)
  let DB : SyntheticObject := .shift (1,0) (.shift (0,-(A:ℤ)) (.quotient B VZ))
  let GB : SyntheticObject := .shift (1,0) (.shift (0,-(A:ℤ)) (.quotient B VY))
  let CN : SyntheticObject := .shift (1,0) (.quotient N VX)
  let FN : SyntheticObject := .shift (1,0) (.quotient N VY)
  let p : ℤ × ℤ := (t-s,t-i-eg)
  let hA : 0 < A := by dsimp [A]; omega
  let hAN : A < N := by dsimp [N,B]; omega
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(A:ℤ))
  let LZ := (model.quotients.tower V.obj₃).triangle hA hAN
  let LY := (model.quotients.tower V.obj₂).triangle hA hAN
  let delta : XModLambdaN V.obj₃ A ⟶ (F.obj (XModLambdaN V.obj₃ B))⟦(1:ℤ)⟧ := by
    simpa only [N,Nat.add_sub_cancel_left] using LZ.delta
  let lambdaY : F.obj (XModLambdaN V.obj₂ B) ⟶ XModLambdaN V.obj₂ N := by
    simpa only [N,Nat.add_sub_cancel_left] using LY.lambdaMap
  ∀ (exA : XModLambdaN (V.obj₁⟦(1:ℤ)⟧) A ≅
      (XModLambdaN V.obj₁ A)⟦(1:ℤ)⟧)
    (exN : XModLambdaN (V.obj₁⟦(1:ℤ)⟧) N ≅
      (XModLambdaN V.obj₁ N)⟦(1:ℤ)⟧)
    (eyN : XModLambdaN (V.obj₂⟦(1:ℤ)⟧) N ≅
      (XModLambdaN V.obj₂ N)⟦(1:ℤ)⟧),
  XModLambdaN.incl _ A ≫ exA.hom =
    (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl V.obj₁ A) →
  XModLambdaN.incl _ N ≫ exN.hom =
    (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl V.obj₁ N) →
  XModLambdaN.incl _ N ≫ eyN.hom =
    (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl V.obj₂ N) →
  let hmap : QA.obj model.nu model.auxiliary ⟶ HA.obj model.nu model.auxiliary :=
    XModLambdaN.map V.mor₃ A ≫ exA.hom ≫
      (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).inv.app _
  let dmap : QA.obj model.nu model.auxiliary ⟶ DB.obj model.nu model.auxiliary :=
    delta ≫ (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).inv.app _
  let gmap : GB.obj model.nu model.auxiliary ⟶ DB.obj model.nu model.auxiliary :=
    (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).hom.app _ ≫
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (F.map (XModLambdaN.map V.mor₂ B)) ≫
      (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).inv.app _
  let Mh := model.convergentMap QA HA hmap
  let Md := model.convergentMap QA DB dmap
  let Mg := model.convergentMap GB DB gmap
  ∀ (xbar : Ambient model T.Z (s,t))
    (x : Ambient model T.X (s+l,t+l-1))
    (y : Ambient model T.Y (s+l+n,t+l+n-1))
    (ybar : Ambient model T.Z (s+r,t+r-1)),
  IsCycle model T.Z (r-1) (s,t) xbar →
  DifferentialAt model T.Z r (s,t) (s+r,t+r-1) xbar ybar →
  IsPermanent model T.Z (s+r,t+r-1) ybar →
  IsCycle model T.X (n₁-j) (s+l,t+l-1) x →
  IsCycle model T.Y (m₁+1) (s+l+n,t+l+n-1) y →
  let xbarA : (model.family.obj (QA.obj model.nu model.auxiliary)).E₂
      (s,p.1+s,p.2) :=
    regradeE2 (by
      ext <;> dsimp [p]
      omega)
      (KIP126.ProofTools.Standard.levelFiniteSourceLabel T.Z A (-eg) s t i xbar)
  let xA : (model.family.obj (HA.obj model.nu model.auxiliary)).E₂
      (s+l,p.1+(s+l),p.2) :=
    regradeE2 (by
      ext <;> dsimp [p,l,K,ef,eg,eh] at * <;> omega)
      (shiftFinitePageLabel (.quotient A VX) (1,0) _
        (KIP126.ProofTools.Standard.levelFiniteSourceLabel T.X A ef (s+l) (t+l-1) K x))
  let yB : (model.family.obj (GB.obj model.nu model.auxiliary)).E₂
      (s+l+n,p.1+(s+l+n),p.2) :=
    regradeE2 (by
      have hja : j ≤ n₁+k+i := by omega
      ext <;> dsimp [p,l,n,A,ef,eg,eh] at * <;>
        (try simp only [Nat.cast_sub hja,Nat.cast_add]) <;> omega)
      (shiftFinitePageLabel (.shift (0,-(A:ℤ)) (.quotient B VY)) (1,0) _
        (shiftFinitePageLabel (.quotient B VY) (0,-(A:ℤ)) _
          (finiteTargetLabel model T.Y B (s+l+n) (t+l+n-1) j y)))
  let ybarB : (model.family.obj (DB.obj model.nu model.auxiliary)).E₂
      (s+r,p.1+(s+r),p.2) :=
    regradeE2 (by
      have hja : j ≤ n₁+k+i := by omega
      ext <;> dsimp [p,r,l,n,m,A,B,ef,eg,eh] at * <;>
        (try simp only [Nat.cast_sub hja,Nat.cast_add]) <;> omega)
      (shiftFinitePageLabel (.shift (0,-(A:ℤ)) (.quotient B VZ)) (1,0) _
        (shiftFinitePageLabel (.quotient B VZ) (0,-(A:ℤ)) _
          (KIP126.ProofTools.Standard.levelFiniteSourceLabel T.Z B (-eg) (s+r) (t+r-1) (B-1) ybar)))
  let xN : (model.family.obj (CN.obj model.nu model.auxiliary)).E₂
      (s+l,p.1+(s+l),p.2) :=
    regradeE2 (by
      ext <;> dsimp [p,l,K,ef,eg,eh] at * <;> omega)
      (shiftFinitePageLabel (.quotient N VX) (1,0) _
        (KIP126.ProofTools.Standard.levelFiniteSourceLabel T.X N ef (s+l) (t+l-1) K x))
  let yN : (model.family.obj (FN.obj model.nu model.auxiliary)).E₂
      (s+l+n,p.1+(s+l+n),p.2) :=
    regradeE2 (by
      have hja : j ≤ n₁+k+i := by omega
      ext <;> dsimp [p,l,n,A,J,ef,eg,eh] at * <;>
        (try simp only [Nat.cast_sub hja,Nat.cast_add]) <;> omega)
      (shiftFinitePageLabel (.quotient N VY) (1,0) _
        (finiteTargetLabel model T.Y N (s+l+n) (t+l+n-1) J y))
  ∀ (e0 : ((model.family.obj (QA.obj model.nu model.auxiliary)).sequence.ssData
        (s,p.1+s,p.2)).eInfty)
    (ex : ((model.family.obj (HA.obj model.nu model.auxiliary)).sequence.ssData
        (s+l,p.1+(s+l),p.2)).eInfty)
    (ey : ((model.family.obj (GB.obj model.nu model.auxiliary)).sequence.ssData
        (s+l+n,p.1+(s+l+n),p.2)).eInfty)
    (ez : ((model.family.obj (DB.obj model.nu model.auxiliary)).sequence.ssData
        (s+r,p.1+(s+r),p.2)).eInfty),
  HasInfinityRepresentative _ 2 _ xbarA e0 →
  HasInfinityRepresentative _ 2 _ xA ex →
  HasInfinityRepresentative _ 2 _ yB ey →
  HasInfinityRepresentative _ 2 _ ybarB ez →
  TowerExtensionEquation Mh p s l e0 ex →
  TowerExtensionEquation Md p s r e0 ez →
  TowerExtensionEquation Mg p (s+l+n) m ey
    ((eqToHom (congrArg (fun q =>
      ((model.family.obj (DB.obj model.nu model.auxiliary)).sequence.ssData q).eInfty)
      (show (s+r,p.1+(s+r),p.2)=(s+l+n+m,p.1+(s+l+n+m),p.2) by
        ext <;> dsimp [r] <;> omega))) ez) →
  (ActualNoCrossing Mh p s l ∨ ActualNoCrossing Md p s r) →
  ∃ (a : BiHom p.1 p.2 (XModLambdaN V.obj₃ A))
    (b : BiHom p.1 p.2 ((F.obj (XModLambdaN V.obj₂ B))⟦(1:ℤ)⟧))
    (c : BiHom p.1 p.2 (XModLambdaN (V.obj₁⟦(1:ℤ)⟧) N)),
    Detects (model.convergence QA) (s,p.1+s,p.2) xbarA
      (homotopyRegrade (by dsimp [p]; omega) rfl a) ∧
    Detects (model.convergence HA) (s+l,p.1+(s+l),p.2) xA
      (homotopyRegrade (by dsimp; omega) rfl (a ≫ hmap)) ∧
    Detects (model.convergence DB) (s+r,p.1+(s+r),p.2) ybarB
      (homotopyRegrade (by dsimp; omega) rfl (a ≫ dmap)) ∧
    Detects (model.convergence GB) (s+l+n,p.1+(s+l+n),p.2) yB
      (homotopyRegrade (by dsimp; omega) rfl
        (b ≫ (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).inv.app _)) ∧
    Detects (model.convergence DB) (s+r,p.1+(s+r),p.2) ybarB
      (homotopyRegrade (by dsimp; omega) rfl
        (b ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map
          (F.map (XModLambdaN.map V.mor₂ B)) ≫
          (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).inv.app _)) ∧
    a ≫ delta = b ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map
      (F.map (XModLambdaN.map V.mor₂ B)) ∧
    c ≫ (model.quotients.tower (V.obj₁⟦(1:ℤ)⟧)).rho A N hAN.le =
      a ≫ XModLambdaN.map V.mor₃ A ∧
    c ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map V.mor₁) N ≫
      eyN.hom = -(b ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map lambdaY) ∧
    Detects (model.convergence CN) (s+l,p.1+(s+l),p.2) xN
      (homotopyRegrade (by dsimp; omega) rfl
        (c ≫ exN.hom ≫
          (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).inv.app _)) ∧
    Detects (model.convergence FN) (s+l+n,p.1+(s+l+n),p.2) yN
      (homotopyRegrade (by dsimp; omega) rfl
        (c ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map V.mor₁) N ≫
          eyN.hom ≫
          (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).inv.app _)) ∧
    IsCycle model T.X Q (s+l,t+l-1) x ∧
    KIP126.ProofTools.Standard.LevelFiniteExtension T.X T.Y T.f
      (Q+1) K n (s+l) (t+l-1) x
      ((eqToHom (congrArg (fun q => (model.classical.obj
          (T.Y.obj model.auxiliary)).Page 2 q)
        (show (s+l+n,t+l+n-1)=(s+l+n,t+l-1+n) by ext <;> omega))) y)

public theorem ssMahowaldZeroInputLevels (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g +
      normalizedExponent model.classicalTower T.h = 1) :
    FiniteMahowaldZeroInputStatement T he := by
  change KIP126.ProofTools.Internal.ProgramRules.FiniteMahowaldZeroInputStatement T he
  exact KIP126.ProofTools.Internal.ProgramRules.ssMahowaldZeroInputLevels T he


end
end KIP126.ProofTools.Standard
end



@[expose] section
namespace KIP126.ProofTools.Standard
open CategoryTheory KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.StableHomotopy KIP126.AdamsSynthetic KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard (model)
open KIP126.Computation KIP126.Computation.Standard
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000


@[no_expose] public def p : model.classical.sphere.Page 2 (4,37) :=
  KIP126.ProofTools.Paper.NumericalExamples.p


public def h0p : model.classical.sphere.Page 2 (5,38) := product h0 p


public theorem paper6_7_classical_d3 :
    HasNonzeroDifferential model.classical.sphere 3 (2,36) (5,38)
      (KIP126.Literature.Standard.hiProduct 2 5) h0p := by
  change HasNonzeroDifferential model.classical.sphere 3 (2,36) (5,38)
    (KIP126.Literature.Standard.hiProduct 2 5)
    KIP126.ProofTools.Paper.NumericalExamples.h0p
  exact KIP126.ProofTools.Paper.NumericalExamples.paper6_7_classical_d3


end
end KIP126.ProofTools.Standard
end

/-! The specified suspended sphere label and its finite and full nu extensions. -/
@[expose] section
namespace KIP126.ProofTools.Standard
open CategoryTheory KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.StableHomotopy KIP126.AdamsSynthetic KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard (model Spectrum)
open KIP126.Computation KIP126.Computation.Standard
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- The actual classical suspension of the specified sphere class h0 h4^2
on S3. Every suspension relation and the final actual shift map is retained. -/
public def IsSphereThreeH0H4Square
    (x : Ambient model (.shift 3 .sphere) (3,36)) : Prop :=
  let e :
      ((ClassicalObject.shift 1 (.shift 1 (.shift 1 .sphere))).obj model.auxiliary) ≅
        ((ClassicalObject.shift 3 .sphere).obj model.auxiliary) :=
    (shiftFunctor Spectrum (1:ℤ)).mapIso
      (((shiftFunctorAdd' Spectrum (1:ℤ) 1 2 (by decide)).app
        (SphereSpectrum (C := Spectrum))).symm) ≪≫
      ((shiftFunctorAdd' Spectrum (2:ℤ) 1 3 (by decide)).app
        (SphereSpectrum (C := Spectrum))).symm
  ∃ (x1 : Ambient model (.shift 1 .sphere) (3,34))
    (x2 : Ambient model (.shift 1 (.shift 1 .sphere)) (3,35))
    (x3 : Ambient model (.shift 1 (.shift 1 (.shift 1 .sphere))) (3,36)),
    (model.classicalSuspension .sphere).DesuspendsClass 3 34 x1
      (product h0 (model.standardClasses.standardHiSquare 4)) ∧
    (model.classicalSuspension (.shift 1 .sphere)).DesuspendsClass 3 35 x2 x1 ∧
    (model.classicalSuspension (.shift 1 (.shift 1 .sphere))).DesuspendsClass
      3 36 x3 x2 ∧
    (model.classical.map e.hom).pageMap 2 (3,36) x3 = x

/-- Exact finite E3 nu-extension conclusion, with the actual fixed S3 source
and the actual archived target. Reaching the page does not assert nonzero. -/
public theorem paper6_19_finite_nu_extension :
    ∃ x : Ambient model (.shift 3 .sphere) (3,36),
      IsSphereThreeH0H4Square x ∧
      ReachesPage (model.classical.obj ((ClassicalObject.shift 3 .sphere).obj
        model.auxiliary)) 3 (3,36) x ∧
      FiniteExtension model (.shift 3 .sphere) .sphere model.auxiliary.nuMap
        3 2 3 36 x h0p := by
  change KIP126.ProofTools.Paper.NumericalExamples.Paper6_19FiniteNuExtensionStatement
  exact KIP126.ProofTools.Paper.NuNumericalExtensions.paper6_19_finite_nu_extension

/-- Exact full nu-extension conclusion. The existing InfiniteExtension
requires the same actual full source and its prescribed actual image. -/
public theorem paper6_24_infinite_nu_extension :
    ∃ x : Ambient model (.shift 3 .sphere) (3,36),
      IsSphereThreeH0H4Square x ∧
      InfiniteExtension model (.shift 3 .sphere) .sphere model.auxiliary.nuMap
        2 3 36 x h0p := by
  change KIP126.ProofTools.Paper.NumericalExamples.Paper6_24InfiniteNuExtensionStatement
  exact KIP126.ProofTools.Paper.NuNumericalExtensions.paper6_24_infinite_nu_extension

end
end KIP126.ProofTools.Standard
end


/-! The actual nu-cofiber differential, retaining both cell-map labels. -/
@[expose] section
namespace KIP126.ProofTools.Standard
open CategoryTheory KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.StableHomotopy KIP126.AdamsSynthetic KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard (model)
open KIP126.Literature
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- There exists an actual cofiber source above the actual suspension of
h0 h4^2 on S3, with the specified actual top and bottom E2 maps, d2 value,
and permanence of the bottom value. No nonzero or uniqueness assertion is
added to the underlying DifferentialAt conclusion. -/
public theorem paper6_19_actual_cofiber_d2 :
    ∃ x : Ambient model (.shift 3 .sphere) (3,36),
      IsSphereThreeH0H4Square x ∧
      x ∈ permanentCycles model (.shift 3 .sphere) (3,36) ∧
      ∃ uTop : Ambient model (.shift 1 (.shift 3 .sphere)) (3,37),
        (model.classicalSuspension (.shift 3 .sphere)).DesuspendsClass 3 37 uTop x ∧
        ∃ xbar : Ambient model .nuCofiber (3,37),
          (model.classical.map model.auxiliary.nuRouteTriangle.h).pageMap 2 (3,37) xbar = uTop ∧
          DifferentialAt model .nuCofiber 2 (3,37) (5,38) xbar
            ((model.classical.map model.auxiliary.nuRouteTriangle.g).pageMap 2 (5,38) h0p) ∧
          IsPermanent model .nuCofiber (5,38)
            ((model.classical.map model.auxiliary.nuRouteTriangle.g).pageMap 2 (5,38) h0p) := by
  exact KIP126.ProofTools.Paper.NuCofiberNumericalDifferential.paper6_19_actual_cofiber_d2

end
end KIP126.ProofTools.Standard
end
