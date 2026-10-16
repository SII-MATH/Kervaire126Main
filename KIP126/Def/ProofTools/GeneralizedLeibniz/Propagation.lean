module

import all KIP126.Def.ProofTools.GeneralizedLeibniz.Filtration
import all KIP126.Def.ProofTools.GeneralizedMahowald.SphereLabels

/-! AimPaper 1641–1643: forward propagation of the complete bottom extension.
The infinity classes and page labels below are the actual shift/map images of
the input classes. No inverse lifting or preservation of no-crossing is used.
-/

@[expose] section
namespace KIP126.ProofTools.Internal.Leibniz
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.Synthetic.SpectralSequence KIP126.Classical.Adams KIP126.AdamsSynthetic
open KIP126.Core.SpectralSequence KIP126.Kervaire.Route KIP126.Literature
open KIP126.AdamsSynthetic.Standard
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 100000
set_option Elab.async false

private abbrev lambdaBoundaryPoint (k q : ℕ) (p : ℤ × ℤ) : ℤ × ℤ :=
  p + (0,-(k:ℤ)) + (1,-(q:ℤ))

private def lambdaBoundaryInfinity (A : SyntheticObject) (k q : ℕ)
    (p : ℤ × ℤ) (s : ℤ)
    (x : ((model.family.obj (A.obj model.nu model.auxiliary)).sequence.ssData
      (s,p.1+s,p.2)).eInfty) :
    ((model.family.obj ((SyntheticObject.shift (1,-(q:ℤ)) A).obj
      model.nu model.auxiliary)).sequence.ssData
        (s,(lambdaBoundaryPoint k q p).1+s,(lambdaBoundaryPoint k q p).2)).eInfty := by
  let p' : ℤ × ℤ := p+(0,-(k:ℤ))
  let I : ((model.family.obj (A.obj model.nu model.auxiliary)).sequence.ssData
      (s,p.1+s,p.2)).eInfty ≅
      ((model.family.obj ((SyntheticObject.shift (0,-(k:ℤ)) A).obj model.nu model.auxiliary)).sequence.ssData
      (s,p'.1+s,p'.2)).eInfty :=
    towerInfinityIso (model.convergence A) (model.convergence (.shift (0,-(k:ℤ)) A))
      ((essShift (0,-(k:ℤ))).filtered A p) s
  let z : ((model.family.obj ((SyntheticObject.shift (0,-(k:ℤ)) A).obj model.nu model.auxiliary)).sequence.ssData
      (s,p'.1+s,p'.2)).eInfty := I.hom x
  let L : ((model.family.obj ((SyntheticObject.shift (0,-(k:ℤ)) A).obj model.nu model.auxiliary)).sequence.ssData
      (s,p'.1+s,p'.2)).eInfty ⟶
      ((model.family.obj (A.obj model.nu model.auxiliary)).sequence.ssData
      (s,p'.1+s,p'.2)).eInfty :=
    (model.family.map (lambdaPow k (A.obj model.nu model.auxiliary))).eInftyMap
      (s,p'.1+s,p'.2)
  let y : ((model.family.obj (A.obj model.nu model.auxiliary)).sequence.ssData
      (s,p'.1+s,p'.2)).eInfty := L z
  let J : ((model.family.obj (A.obj model.nu model.auxiliary)).sequence.ssData
      (s,p'.1+s,p'.2)).eInfty ≅
      ((model.family.obj ((SyntheticObject.shift (1,-(q:ℤ)) A).obj model.nu model.auxiliary)).sequence.ssData
      (s,(p'+(1,-(q:ℤ))).1+s,(p'+(1,-(q:ℤ))).2)).eInfty :=
    towerInfinityIso (model.convergence A) (model.convergence (.shift (1,-(q:ℤ)) A))
      ((essShift (1,-(q:ℤ))).filtered A p') s
  exact J.hom y

private def lambdaBoundaryLabel (A : SyntheticObject) (k q : ℕ)
    (p : ℤ × ℤ) (s : ℤ)
    (x : (model.family.obj (A.obj model.nu model.auxiliary)).E₂ (s,p.1+s,p.2)) :
    (model.family.obj ((SyntheticObject.shift (1,-(q:ℤ)) A).obj
      model.nu model.auxiliary)).E₂
        (s,(lambdaBoundaryPoint k q p).1+s,(lambdaBoundaryPoint k q p).2) := by
  let p' : ℤ × ℤ := p+(0,-(k:ℤ))
  let I : (model.family.obj (A.obj model.nu model.auxiliary)).E₂ (s,p.1+s,p.2) ≅
      (model.family.obj ((SyntheticObject.shift (0,-(k:ℤ)) A).obj model.nu model.auxiliary)).E₂
        (s,p'.1+s,p'.2) := (essShift (0,-(k:ℤ))).page A 2 (by decide) p s
  let z : (model.family.obj ((SyntheticObject.shift (0,-(k:ℤ)) A).obj model.nu model.auxiliary)).E₂
      (s,p'.1+s,p'.2) := I.hom x
  let L : (model.family.obj ((SyntheticObject.shift (0,-(k:ℤ)) A).obj model.nu model.auxiliary)).E₂
      (s,p'.1+s,p'.2) ⟶
      (model.family.obj (A.obj model.nu model.auxiliary)).E₂ (s,p'.1+s,p'.2) :=
    familyPageMap model.family (lambdaPow k (A.obj model.nu model.auxiliary)) 2 (s,p'.1+s,p'.2)
  let y : (model.family.obj (A.obj model.nu model.auxiliary)).E₂ (s,p'.1+s,p'.2) := L z
  let J : (model.family.obj (A.obj model.nu model.auxiliary)).E₂ (s,p'.1+s,p'.2) ≅
      (model.family.obj ((SyntheticObject.shift (1,-(q:ℤ)) A).obj model.nu model.auxiliary)).E₂
        (s,(p'+(1,-(q:ℤ))).1+s,(p'+(1,-(q:ℤ))).2) :=
    (essShift (1,-(q:ℤ))).page A 2 (by decide) p' s
  exact J.hom y

private theorem lambdaBoundary_representative (A : SyntheticObject) (k q : ℕ)
    (p : ℤ × ℤ) (s : ℤ)
    (x : (model.family.obj (A.obj model.nu model.auxiliary)).E₂ (s,p.1+s,p.2))
    (z : ((model.family.obj (A.obj model.nu model.auxiliary)).sequence.ssData
      (s,p.1+s,p.2)).eInfty)
    (hz : HasInfinityRepresentative (model.family.obj (A.obj model.nu model.auxiliary))
      2 (s,p.1+s,p.2) x z) :
    HasInfinityRepresentative
      (model.family.obj ((SyntheticObject.shift (1,-(q:ℤ)) A).obj model.nu model.auxiliary))
      2 (s,(lambdaBoundaryPoint k q p).1+s,(lambdaBoundaryPoint k q p).2)
      (lambdaBoundaryLabel A k q p s x)
      (lambdaBoundaryInfinity A k q p s z) := by
  have hm := Internal.Mahowald.shifted_representative_map A A (0,-(k:ℤ)) p s
    (lambdaPow k (A.obj model.nu model.auxiliary)) x z hz
  have hf := ((essShift (1,-(q:ℤ))).representative_iff A 2 (by decide)
    (p+(0,-(k:ℤ))) s _ _).mp hm
  exact hf

/-- Push the entire actual extension through lambda^k and the absolute-boundary
shift. This gives precisely the third edge needed by square_frames. -/
private theorem extension_lambda_boundary_shift (A B : SyntheticObject)
    (g : A.obj model.nu model.auxiliary ⟶ B.obj model.nu model.auxiliary)
    (k q : ℕ) (p : ℤ × ℤ) (s n : ℤ)
    (x : ((model.family.obj (A.obj model.nu model.auxiliary)).sequence.ssData
      (s,p.1+s,p.2)).eInfty)
    (y : ((model.family.obj (B.obj model.nu model.auxiliary)).sequence.ssData
      (s+n,p.1+(s+n),p.2)).eInfty)
    (he : TowerExtensionEquation (model.convergentMap A B g) p s n x y) :
    TowerExtensionEquation
      (model.convergentMap (.shift (1,-(q:ℤ)) A) (.shift (1,-(q:ℤ)) B)
        ((SyntheticCategory.biShift (1,-(q:ℤ))).map g))
      (lambdaBoundaryPoint k q p) s n
      (lambdaBoundaryInfinity A k q p s x)
      (lambdaBoundaryInfinity B k q p (s+n) y) := by
  have hs := ((essShift (0,-(k:ℤ))).towerExtensionEquation_iff A B g p s n x y).mp he
  have hl := tower_extension_map
    (model.convergentMap (.shift (0,-(k:ℤ)) A) (.shift (0,-(k:ℤ)) B)
      ((SyntheticCategory.biShift (0,-(k:ℤ))).map g))
    (model.convergentMap A B g)
    (model.convergentMap (.shift (0,-(k:ℤ)) A) A
      (lambdaPow k (A.obj model.nu model.auxiliary)))
    (model.convergentMap (.shift (0,-(k:ℤ)) B) B
      (lambdaPow k (B.obj model.nu model.auxiliary)))
    (lambdaPow_naturality k g) (p+(0,-(k:ℤ))) s n _ _ hs
  exact ((essShift (1,-(q:ℤ))).towerExtensionEquation_iff A B g
    (p+(0,-(k:ℤ))) s n _ _).mp hl

/-- Witness-level interface for the GL bottom edge. Both labels are explicitly
the actual E2 shift/lambda images of W's original labels, and both infinity
classes are exactly the corresponding images of W.source and W.target. -/
private theorem infinite_extension_lambda_boundary_shift
    (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (k q : ℕ) (n s t : ℤ)
    (x : Ambient model X (s,t)) (y : Ambient model Y (s+n,t+n))
    (W : InfiniteExtensionWitness model X Y f n s t x y) :
    let A := extensionSourceObject model X Y f
    let B := SyntheticObject.nu Y
    let p : ℤ × ℤ := (t-s,t+normalizedExponent model.classicalTower f)
    TowerExtensionEquation
      (model.convergentMap (.shift (1,-(q:ℤ)) A) (.shift (1,-(q:ℤ)) B)
        ((SyntheticCategory.biShift (1,-(q:ℤ))).map (model.normalizedMap X Y f).map))
      (lambdaBoundaryPoint k q p) s n
      (lambdaBoundaryInfinity A k q p s W.source)
      (lambdaBoundaryInfinity B k q p (s+n) W.target) ∧
    HasInfinityRepresentative _ 2 _
      (lambdaBoundaryLabel A k q p s (infiniteSourceForExtension model X Y f s t x))
      (lambdaBoundaryInfinity A k q p s W.source) ∧
    HasInfinityRepresentative _ 2 _
      (lambdaBoundaryLabel B k q p (s+n)
        (infiniteTargetForExtension model X Y f n s t W.length_lower y))
      (lambdaBoundaryInfinity B k q p (s+n) W.target) := by
  refine ⟨extension_lambda_boundary_shift _ _ _ k q _ s n _ _ W.equation, ?_, ?_⟩
  · exact lambdaBoundary_representative _ k q _ s _ _ W.source_rep
  · exact lambdaBoundary_representative _ k q _ (s+n) _ _ W.target_rep

/-- The transformed bottom stem/weight is exactly the GL square's stem/weight. -/
private theorem gl_bottom_point (page : ℕ) (r s t e : ℤ)
    (hpage : 2 ≤ page) (hpr : (page:ℤ) ≤ r) :
    lambdaBoundaryPoint (r-page).toNat (page-1)
      ((t+r-1)-(s+r),(t+r-1)+e) = (t-s,t+e) := by
  have hk : ((r-page).toNat:ℤ) = r-page := Int.toNat_of_nonneg (by omega)
  have hq : ((page-1:ℕ):ℤ) = (page:ℤ)-1 := by omega
  ext <;> dsimp [lambdaBoundaryPoint] <;> omega

end
end KIP126.ProofTools.Internal.Leibniz
