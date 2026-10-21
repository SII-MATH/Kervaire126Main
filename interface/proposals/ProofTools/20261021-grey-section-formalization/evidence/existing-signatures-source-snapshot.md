# KIP126/ProofTools/GeneralizedLeibnizAtLevel.lean

```lean
module

public import KIP126.ProofTools.LevelLanguage
import all KIP126.ProofTools.LevelLanguage
import all KIP126.ProofTools.GeneralizedLeibniz.LevelGL
import all KIP126.ProofTools.GeneralizedLeibniz.LevelZero

/-! The generalized Leibniz rule with an arbitrary explicit lambda level.
This public entry point reuses the proved four-edge argument at the actual
quotient and weight. The original public generalized Leibniz statement is
unchanged. The zero-level input conversion does not identify its original
crossing predicates with the actual crossing conditions used here. -/

@[expose] section
namespace KIP126.ProofTools.Standard
open CategoryTheory KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.Classical.Adams KIP126.AdamsSynthetic KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard
noncomputable section

/-- AimPaper's generalized Leibniz square at any source lambda level.
The finite extension is in quotient `page + level - 1`. Its upper or left
edge must have no crossing, and its actual propagated bottom edge must have
no crossing. There is no upper bound on `level`. The infinite input is the
original zero-level extension; its required propagation is proved internally. -/
public theorem generalizedLeibnizAtLevel
    (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
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
    (hFinite : LevelFiniteExtension X Y f page level m s t x y)
    (hInfinity : InfiniteExtension model X Y f l (s+r) (t+r-1) xInfinity yInfinity)
    (hsourceCrossing : LevelBoundaryNoCrossing X Y f page level r s t ∨
      LevelFiniteNoCrossing X Y f page level m s t)
    (hbottomCrossing : LevelBottomNoCrossing X Y f page level r l s t) :
    DifferentialAt model Y (r+l-m) (s+m,t+m) (s+r+l,t+r-1+l) y yInfinity := by
  obtain ⟨WFinite⟩ := (levelFiniteExtension_iff_internal X Y f page level m s t x y).mp hFinite
  obtain ⟨WInfinity⟩ := hInfinity
  exact KIP126.ProofTools.Internal.Leibniz.generalizedLeibniz_at_level
    X Y f page level r m l s t x y xInfinity yInfinity hpage hpr hm hmUpper hl
    hxInfinity hyInfinity hdx WFinite WInfinity
    (hsourceCrossing.imp
      (levelBoundaryNoCrossing_iff_internal X Y f page level r s t).mp
      (levelFiniteNoCrossing_iff_internal X Y f page level m s t).mp)
    ((levelBottomNoCrossing_iff_internal X Y f page level r l s t).mp hbottomCrossing)

/-- Every original finite extension supplies the corresponding zero-level
finite input. This preserves its actual map equation and compares its
representative labels; it makes no claim about crossing conditions. -/
public theorem finiteExtensionAtLevelZero
    (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (page : ℕ) (m s t : ℤ)
    (x : Ambient model X (s,t)) (y : Ambient model Y (s+m,t+m))
    (h : FiniteExtension model X Y f page m s t x y) :
    LevelFiniteExtension X Y f page 0 m s t x y := by
  obtain ⟨W⟩ := h
  apply (levelFiniteExtension_iff_internal X Y f page 0 m s t x y).mpr
  exact ⟨KIP126.ProofTools.Internal.Leibniz.level_finite_extension_of_zero
    X Y f page m s t x y W⟩

end
end KIP126.ProofTools.Standard

```

# KIP126/ProofTools/GeneralizedMahowald/FiniteLevelStatement.lean

```lean
module

public import KIP126.ProofTools.GeneralizedMahowald.ActualNoCrossing
public import KIP126.ProofTools.Language
public import KIP126.ProofTools.ConvergenceOperations
public import KIP126.ProofTools.LevelLanguage

/-!
# Complete finite-level Mahowald target

This file defines a target proposition. It does not assert that proposition.
The two actual equations in the conclusion have one and the same lift. The
no-crossing premise quantifies actual essential extensions, rather than
assuming the desired simultaneous representative.
-/

@[expose] section
namespace KIP126.ProofTools.Standard
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard KIP126.Literature
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

/-- The complete double-input-layer finite MH assertion in the selected
normalized triangle. All arithmetic, classical labels, actual extension
relations, comparisons, output representatives, and output detections occur
inside this proposition. No truth value is supplied by this definition.

The shifted finite source labels use the actual quotient-shift construction
`levelFiniteSourceLabel`; they do not assume an unproved calibration of
positive-layer `nuE2` coordinates.

The natural parameters encode exactly n₁≥1,m₁≥0,k≥0,i≥0,0≤j<n₁; n,m,l
are recovered by adding the prescribed normalization exponents. Ordinary
suspension is kept explicit in both signed image equations. Quotient-shift
comparisons preserve the actual inclusion and the rho square on every sphere
representative; no global equality of independently chosen cone maps is imposed.
-/
public def FiniteMahowaldAtLevelStatement
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
    (n₁ m₁ k i j : ℕ) (_hn₁ : 0 < n₁) (hj : j < n₁) (s t : ℤ),
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

end
end KIP126.ProofTools.Standard

```

# KIP126/Literature/Standard/AdamsTwoLine.lean

```lean
module

public import KIP126.Literature.Standard

/-! Classical inputs for AimPaper Corollary 1.5, on the fixed sphere Adams
sequence. Original sources and adaptation limits are recorded in Blueprint.
Each source-to-model statement is a separate registered upstream obligation;
the exhaustive classification itself is proved in Main. -/

@[expose] section
namespace KIP126.Literature.Standard
open CategoryTheory KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.AdamsSynthetic.Standard (model)

/-- The actual product of the two specified standard one-line classes. -/
public noncomputable def hiProduct (i j : ℕ) :
    ActualE2At model.classical (hiDegree i + hiDegree j) :=
  model.sphereAlgebra.product (hiDegree i) (hiDegree j)
    (model.standardClasses.standardHi i) (model.standardClasses.standardHi j)

/-- May's three exceptional low-dimensional mixed products. -/
public theorem may_two_line_products_permanent (i j : ℕ)
    (h : (i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 3) ∨ (i = 2 ∧ j = 4)) :
    NonzeroSurvival model.classical.sphere (hiDegree i + hiDegree j) (hiProduct i j) := by
  sorry

/-- The low Kervaire squares, including the degree-zero class h₀². -/
public theorem may_low_squares_permanent (j : ℕ) (hj : j ≤ 3) :
    NonzeroSurvival model.classical.sphere (2,((2^(j+1) : ℕ) : ℤ))
      (model.standardClasses.standardHiSquare j) := by
  sorry

/-- Mahowald--Tangora's 30-stem Kervaire class. -/
public theorem mahowald_tangora_h4_square_permanent :
    NonzeroSurvival model.classical.sphere (2,32)
      (model.standardClasses.standardHiSquare 4) := by
  sorry

/-- Mahowald, Theorem 1', restricted to the family needed by Corollary 1.5. -/
public theorem mahowald_eta_family_permanent (j : ℕ) (hj : 3 ≤ j) :
    NonzeroSurvival model.classical.sphere (hiDegree 1 + hiDegree j) (hiProduct 1 j) := by
  sorry

/-- Only the nonzero differential and its actual target degree are chosen;
no arbitrary E₂ symbol is substituted for the target. -/
public theorem mahowald_tangora_h2_h5_d3 :
    ∃ y : model.classical.sphere.Page 2 (5,38),
      HasNonzeroDifferential model.classical.sphere 3 (2,36) (5,38) (hiProduct 2 5) y := by
  sorry

public theorem mahowald_tangora_h3_h5_d4 :
    ∃ y : model.classical.sphere.Page 2 (6,43),
      HasNonzeroDifferential model.classical.sphere 4 (2,40) (6,43) (hiProduct 3 5) y := by
  sorry

public theorem iwx_h3_h6_d3 :
    ∃ y : model.classical.sphere.Page 2 (5,74),
      HasNonzeroDifferential model.classical.sphere 3 (2,72) (5,74) (hiProduct 3 6) y := by
  sorry

/-- IWX's nonzero classical d₃ on h₀h₄. This class reaches E₃ and must
therefore be retained by d₂-stage screening before this later exclusion. -/
public theorem iwx_h0_h4_d3 :
    ∃ y : model.classical.sphere.Page 2 (5,19),
      HasNonzeroDifferential model.classical.sphere 3 (2,17) (5,19) (hiProduct 0 4) y := by
  sorry

/-- HHR's nonexistence theorem transported to the specified standard squares.
It neither selects a differential length nor asserts a known target. -/
public theorem hhr_high_squares_not_permanent (j : ℕ) (hj : 7 ≤ j) :
    ¬ NonzeroSurvival model.classical.sphere (2,((2^(j+1) : ℕ) : ℤ))
      (model.standardClasses.standardHiSquare j) := by
  sorry

end KIP126.Literature.Standard

```

# KIP126/ProofTools/Paper/OriginalStatements.lean (exact extensionSquare)

```lean
public theorem extensionSquare (X Y Z W : ClassicalObject)
    (f : X.obj D.auxiliary ⟶ Y.obj D.auxiliary)
    (p : X.obj D.auxiliary ⟶ Z.obj D.auxiliary)
    (g : Z.obj D.auxiliary ⟶ W.obj D.auxiliary)
    (q : Y.obj D.auxiliary ⟶ W.obj D.auxiliary)
    (hcomm : f ≫ q = p ≫ g)
    (m n l k s d : ℤ) (hm : 0 ≤ m) (hn : 0 ≤ n) (hl : 0 ≤ l)
    (hk : 0 < k) (hkl : k ≤ m+l-n)
    (x : ClassicalGrade D X s d) (y : ClassicalGrade D Y (s+n) d)
    (z : ClassicalGrade D Z (s+m) d) (w : ClassicalGrade D W (s+m+l) d)
    (hf : ClassicalExtension D X Y f d s (s+n) x y)
    (hp : ClassicalExtension D X Z p d s (s+m) x z)
    (hnc : ClassicalNoCrossing D X Y f d s (s+n) ∨
      ClassicalNoCrossing D X Z p d s (s+m))
    (hg : ClassicalExtension D Z W g d (s+m) (s+m+l) z w)
    (hgnc : ClassicalNoCrossingRange D Z W g d (s+m) (s+m+l) (s+n+k))
    (hq : ClassicalExtension D Y W q d (s+n) (s+n+k-1) y 0)
    (hqnc : ClassicalNoCrossing D Y W q d (s+n) (s+n+k-1)) :
    ClassicalExtension D Y W q d (s+n) (s+m+l) y w := by
  have common : ∃ a : HomotopyGroup d (X.obj D.auxiliary),
      ClassicalRepresents D Y (s+n) d y (a ≫ f) ∧
      ClassicalRepresents D Z (s+m) d z (a ≫ p) := by
    rcases hnc with hfnc | hpnc
    · obtain ⟨a,hax,haz⟩ := hp
      exact ⟨a,classical_extension_universal D X Y f d s (s+n) x y hf hfnc a hax,haz⟩
    · obtain ⟨a,hax,hay⟩ := hf
      exact ⟨a,hay,classical_extension_universal D X Z p d s (s+m) x z hp hpnc a hax⟩
  obtain ⟨a,hay,haz⟩ := common
  have hqzero := classical_extension_universal D Y W q d (s+n) (s+n+k-1) y 0 hq hqnc (a ≫ f) hay
  have hhigh := (classical_represents_zero_iff D W (s+n+k-1) d _).mp hqzero
  have hhigh' : (a ≫ p) ≫ g ∈
      (D.classicalTower.tower (W.obj D.auxiliary)).filtrationSubmodule (s+n+k) d := by
    simpa only [Category.assoc, hcomm, sub_add_cancel] using hhigh
  refine ⟨a ≫ f, hay, ?_⟩
  have hw := classical_extension_range_universal D Z W g d (s+m) (s+m+l)
    (s+n+k) z w hg hgnc (by omega) (a ≫ p) haz hhigh'
  simpa only [Category.assoc, ←hcomm] using hw


```
