module

public import KIP126.Def.Synthetic.PageExtension.Solutions.Data
public import KIP126.Def.Synthetic.PageExtension.Solutions.Permanent.Data
public import KIP126.Def.Synthetic.ExtensionSS.Square.Construction.Data

@[expose] public section
/-!
# Restriction maps and coherent page-extension solutions

These definitions specify comparison maps and their compatibility with
representatives, differentials and products on the given mathematical objects.
-/

namespace KIP126.Comparison

open CategoryTheory CategoryTheory.MonoidalCategory
open Classical.Adams SpectralSequence

universe u v w

section PageExtensionSolutions

set_option backward.isDefEq.respectTransparency false

open StableHomotopy StableHomotopy.Cohomology Synthetic.Context Synthetic.SpectralSequence
open Synthetic.PageExtension Classical.Adams.PageRepresentatives SpectralSequence

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {N : NuFunctorData C Syn}
  {F : SyntheticAdamsFamily Syn} {X Y : C} {f : X ⟶ Y}

/-- 同一有限商塔的实际 ρ 同伦映射保持指定收敛滤过。
交换方块由 P.towerMap 导出，不另假设，也不选择独立的 ESS 映射。 -/
structure PageExtensionRestrictionFiltration (P : NormalizedPageFamily H N F f) : Prop where
  source_preserves : ∀ (i j : ℕ) (hi : 0 < i) (hj : 0 < j) (hij : i ≤ j) s p,
    ∃ φ : Subobject.underlying.obj ((P.finite j hj).source.filtration.F s p) ⟶
        Subobject.underlying.obj ((P.finite i hi).source.filtration.F s p),
      φ ≫ ((P.finite i hi).source.filtration.F s p).arrow =
        ((P.finite j hj).source.filtration.F s p).arrow ≫
          syntheticHomotopyMap (P.sourceTower.rho i j hij) p
  target_preserves : ∀ (i j : ℕ) (hi : 0 < i) (hj : 0 < j) (hij : i ≤ j) s p,
    ∃ φ : Subobject.underlying.obj ((P.finite j hj).target.filtration.F s p) ⟶
        Subobject.underlying.obj ((P.finite i hi).target.filtration.F s p),
      φ ≫ ((P.finite i hi).target.filtration.F s p).arrow =
        ((P.finite j hj).target.filtration.F s p).arrow ≫
          syntheticHomotopyMap (P.targetTower.rho i j hij) p

set_option linter.defProp false in
/-- 固定 normalized map 的实际商方块；comm 来自既有塔态射。 -/
def PageExtensionRestrictionFiltration.square {P : NormalizedPageFamily H N F f}
    (I : PageExtensionRestrictionFiltration P) (i j : ℕ)
    (hi : 0 < i) (hj : 0 < j) (hij : i ≤ j) :
    SyntheticExtensionData.FilteredSquare (P.finite j hj) (P.finite i hi)
      (P.sourceTower.rho i j hij) (P.targetTower.rho i j hij) where
  comm := P.towerMap.rho_naturality hij
  source_preserves := I.source_preserves i j hi hj hij
  target_preserves := I.target_preserves i j hi hj hij

/-- 限制链映射由实际 ρ 方块构造，不由自由的页面操作指定。 -/
noncomputable def PageExtensionRestrictionFiltration.complexMap
    {P : NormalizedPageFamily H N F f} (I : PageExtensionRestrictionFiltration P)
    (i j : ℕ) (hi : 0 < i) (hj : 0 < j) (hij : i ≤ j) (p : ℤ × ℤ) :
    FilteredComplex.Morphism ((P.finite j hj).complex p) ((P.finite i hi).complex p) :=
  (I.square i j hi hj hij).complexMap p

/-- 实际 ρ 限制保留同一个经典 E₂ 标签。只列出源／靶的比较图；
解集、差群与限制函数随后由真实代表元方程构造。 -/
structure PageExtensionRestrictionLabels (P : NormalizedPageFamily H N F f)
    (I : PageExtensionRestrictionFiltration P) : Prop where
  source : ∀ (i j : ℕ) (hi : 0 < i) (hj : 0 < j) (hij : i ≤ j) (s t : ℤ)
    (xi : cycles H X i (s, t)) (xj : cycles H X j (s, t)), xi.val = xj.val →
      elementMap (P.finiteSourceMap j hj s t xj) ≫
          (I.complexMap i j hi hj hij (P.degree s t)).associatedGradedMap s 1 =
        elementMap (P.finiteSourceMap i hi s t xi)
  target : ∀ (i j : ℕ) (hi : 0 < i) (hj : 0 < j) (hij : i ≤ j) (n s t : ℤ)
    (hn : (normalizedExponent H f : ℤ) ≤ n)
    (hki : P.lambdaExponent n < i) (hkj : P.lambdaExponent n < j)
    (yi : cycles H Y (i - P.lambdaExponent n : ℕ) (s + n, t + n))
    (yj : cycles H Y (j - P.lambdaExponent n : ℕ) (s + n, t + n)), yi.val = yj.val →
      P.finiteTargetClass j hj n s t hn hkj yj ≫
          (I.complexMap i j hi hj hij (P.degree s t)).associatedGradedMap (s + n) 0 =
        P.finiteTargetClass i hi n s t hn hki yi

/-- 两个实际比较图给出经典标签固定后的解纤维限制。此定义不声称满射。 -/
noncomputable def restrictFiniteSolution {P : NormalizedPageFamily H N F f}
    (I : PageExtensionRestrictionFiltration P) (J : PageExtensionRestrictionLabels P I)
    (i j : ℕ) (hi : 0 < i) (hj : 0 < j) (hij : i ≤ j) (n s t : ℤ)
    (hn : (normalizedExponent H f : ℤ) ≤ n)
    (hki : P.lambdaExponent n < i) (hkj : P.lambdaExponent n < j)
    (xi : cycles H X i (s, t)) (xj : cycles H X j (s, t)) (hx : xi.val = xj.val)
    (yi : cycles H Y (i - P.lambdaExponent n : ℕ) (s + n, t + n))
    (yj : cycles H Y (j - P.lambdaExponent n : ℕ) (s + n, t + n)) (hy : yi.val = yj.val)
    (a : P.FiniteSolutions j hj n s t hn hkj xj yj) :
    P.FiniteSolutions i hi n s t hn hki xi yi := by
  dsimp only [NormalizedPageFamily.FiniteSolutions] at a ⊢
  have b := FilteredComplex.Solutions.restrict (I.complexMap i j hi hj hij (P.degree s t)) a
  erw [J.source i j hi hj hij s t xi xj hx] at b
  erw [J.target i j hi hj hij n s t hn hki hkj yi yj hy] at b
  exact b

set_option backward.isDefEq.respectTransparency true

/-- 在同一永久标签上特化实际限制；只使用永久 cycle 的规范包含。 -/
noncomputable def restrictPermanentFiniteSolution {P : NormalizedPageFamily H N F f}
    (I : PageExtensionRestrictionFiltration P) (J : PageExtensionRestrictionLabels P I)
    (i j : ℕ) (hij : i ≤ j) (n s t : ℤ)
    (hn : (normalizedExponent H f : ℤ) ≤ n)
    (hki : P.lambdaExponent n < i) (hkj : P.lambdaExponent n < j)
    (x : permanentCycles H X (s, t)) (y : permanentCycles H Y (s + n, t + n))
    (a : P.PermanentFiniteSolutions j n s t hn hkj x y) :
    P.PermanentFiniteSolutions i n s t hn hki x y :=
  restrictFiniteSolution (P := P) I J i j
    (lt_of_le_of_lt (Nat.zero_le _) hki) (lt_of_le_of_lt (Nat.zero_le _) hkj)
    hij n s t hn hki hkj
    (Submodule.inclusion (permanentCycles_le_cycles H X (s, t) i) x)
    (Submodule.inclusion (permanentCycles_le_cycles H X (s, t) j) x) rfl
    (Submodule.inclusion (permanentCycles_le_cycles H Y (s + n, t + n)
      (i - P.lambdaExponent n : ℕ)) y)
    (Submodule.inclusion (permanentCycles_le_cycles H Y (s + n, t + n)
      (j - P.lambdaExponent n : ℕ)) y) rfl a

/-- 固定永久标签在所有允许的有限商上的实际相容解。
每层必须提供真实方程的一个解，相邻层用同一实际 ρ 限制相容。
此类型不选择成员，也不声称各层非空就足以得到相容塔或无穷解。 -/
structure CoherentPageExtensionSolutions (P : NormalizedPageFamily H N F f)
    (I : PageExtensionRestrictionFiltration P) (J : PageExtensionRestrictionLabels P I)
    (n s t : ℤ) (hn : (normalizedExponent H f : ℤ) ≤ n)
    (x : permanentCycles H X (s, t)) (y : permanentCycles H Y (s + n, t + n)) : Type v where
  solution : ∀ (q : ℕ) (hkq : P.lambdaExponent n < q),
    P.PermanentFiniteSolutions q n s t hn hkq x y
  compatible : ∀ (q : ℕ) (hkq : P.lambdaExponent n < q),
    restrictPermanentFiniteSolution I J q (q + 1) (Nat.le_succ q)
      n s t hn hkq (lt_trans hkq (Nat.lt_succ_self q)) x y
      (solution (q + 1) (lt_trans hkq (Nat.lt_succ_self q))) = solution q hkq

end PageExtensionSolutions

end KIP126.Comparison
