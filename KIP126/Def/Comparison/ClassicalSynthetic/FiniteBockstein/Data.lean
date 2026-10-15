module

public import KIP126.Def.Comparison.ClassicalSynthetic.Data
public import KIP126.Def.Comparison.ClassicalSynthetic.FirstQuotient.Data
public import KIP126.Def.Synthetic.Bockstein.Hom.Data
public import KIP126.Def.Synthetic.QuotientFunctor.Data
public import KIP126.Def.ClassicalAdams.Convergence.Tower.Predicates
public import KIP126.Def.ClassicalAdams.Completion.Predicates
public import KIP126.Def.ClassicalAdams.PageRepresentatives.Predicates

@[expose] public section
/-!
# Classical–synthetic comparison and finite Bockstein differentials

These definitions specify comparison maps and their compatibility with
representatives, differentials and products on the given mathematical objects.
-/

namespace KIP126.Comparison

open CategoryTheory CategoryTheory.MonoidalCategory
open Classical.Adams SpectralSequence

universe u v w

/-- 经典–合成比较：classic 页面由实际 unit 塔构造，synthetic
页面是同一 family 在 νX 的取值。该类型不声称比较已经构造或为同构。 -/
abbrev NuComparison {C : Type u} [StableHomotopy.StableHomotopyCategory.{u, v} C]
    [StableHomotopy.HasFunctorialCofiber (C := C)]
    {Syn : Type w} [Synthetic.Context.SyntheticCategory.{w, v} Syn]
    {H : C} (unit : 𝟙_ C ⟶ H) (N : Synthetic.Context.NuFunctorData C Syn)
    (F : Synthetic.SpectralSequence.SyntheticAdamsFamily Syn) (X : C) :=
  Comparison.ClassicalSynthetic.ReindexedSpectralSequenceMap
    (adamsTowerInternalSpectralSequence unit X) (F.nu N X)

section SyntheticEInfty

open StableHomotopy StableHomotopy.Cohomology Synthetic.Context Synthetic.SpectralSequence
open Classical.Adams.PageRepresentatives

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  (H : Mod2EilenbergMacLane (C := C)) (N : NuFunctorData C Syn)
  (F : SyntheticAdamsFamily Syn)

/-- 指定 X 的一阶 λ 商实际同伦群与经典 E₂ 的比较。
`a = 0` 对应 MainPaper `thm:17e90ac0`(1) / BHS `lemm:ctauE2`；
任意 a 的版本还需实际 shift 与 λ 商的比较。此处使用同一个一阶商同伦比较。
不声称已构造模型见证，也不由 E∞ 的 specialFiber 字段直接推出。 -/
abbrev FirstQuotientHomotopyComparison (X : C) :=
  Comparison.ClassicalSynthetic.FirstQuotientHomotopyComparison H N X

/-- 只用同一比较的 a=0 分量及实际商函子的零移位同构，恢复 νX 本身的
一阶商比较；不选择另一份边缘同构。 -/
noncomputable def FirstQuotientHomotopyComparison.unshifted {X : C}
    (Q : FirstQuotientHomotopyComparison H N X)
    (cofib : FunctorialCofiberCoherence Syn) (s t : ℤ) :
    BiHom (t - s) t (XModLambdaN (N.functor.obj X) 1) ≃+ Ambient H X (s, t) := by
  let e := (XModLambdaN.functor cofib 1).mapIso
    (SyntheticCategory.biShift_zero.app (N.functor.obj X))
  let transport : BiHom (t - s) t (XModLambdaN (N.functor.obj X) 1) ≃+
      BiHom (t - s) t
        (XModLambdaN ((SyntheticCategory.biShift (0, 0)).obj (N.functor.obj X)) 1) :=
    { toFun := fun f => f ≫ e.inv
      invFun := fun f => f ≫ e.hom
      left_inv := by intro f; simp
      right_inv := by intro f; simp
      map_add' := by intro f g; simp only [Preadditive.add_comp] }
  exact transport.trans
    (Eq.mp (congrArg (fun weight : ℤ =>
      BiHom (t - s) weight
        (XModLambdaN ((SyntheticCategory.biShift (0, 0)).obj (N.functor.obj X)) 1) ≃+
          Ambient H X (s, t)) (Int.add_zero t)) (Q 0 s t))

/-- 把实际 β_q 的像放进同一经典 E₂ 的目标次数。β_q 降低 stem 一次、
增加 weight q，因此对应 d_(q+1) 的 (s+q+1,t+q)，不是 d_q。 -/
noncomputable def FirstQuotientHomotopyComparison.bocksteinTargetClass {X : C}
    (Q : FirstQuotientHomotopyComparison H N X)
    (cofib : FunctorialCofiberCoherence Syn) (q : ℕ) (s t : ℤ)
    (z : BiHom (t - s) t (XModLambdaN (N.functor.obj X) q)) :
    Ambient H X (s + (q : ℤ) + 1, t + (q : ℤ)) :=
  FirstQuotientHomotopyComparison.unshifted H N Q cofib
    (s + (q : ℤ) + 1) (t + (q : ℤ))
    (Eq.mp (congrArg (fun n => BiHom n (t + (q : ℤ))
      (XModLambdaN (N.functor.obj X) 1))
      (by omega : t - s - 1 = (t + (q : ℤ)) - (s + (q : ℤ) + 1)))
      (Synthetic.Bockstein.betaHom (N.functor.obj X) q (t - s) t z))

section FiniteBockstein
variable [CategoryTheory.Limits.HasProductsOfShape ℕ C]

/-- BHS A.1 的有限提升／微分部分，绑定同一一阶商比较及实际 λ 商映射。
同时保留原文的 E-nilpotent completeness 和同一实际 Adams 塔的强收敛。
q=1 对应无先行微分，q=2 对应 d₂=0；β_q 对应 d_(q+1)。
负号来自原文，消去它只需已比较 E₂ 的模二性质，不对所有 synthetic
同伦群假设 2=0。这里只断言存在合适的 lift，并按实际页上的关系比较像，
不把它加强成任意 lift 在 E₂ 上有唯一相同代表。 -/
structure FiniteLambdaBocksteinComparison (coh : BiShiftCoherence Syn)
    (cofib : FunctorialCofiberCoherence Syn) (X : C)
    (Q : FirstQuotientHomotopyComparison H N X) : Prop where
  lifting : IsENilpotentComplete H.unit X → IsAdamsTowerStronglyConvergent H.unit X →
    ∀ (q : ℕ) (hq : 1 ≤ q) (s t : ℤ) (x : Ambient H X (s, t)),
      IsCycle H X (q : ℤ) (s, t) x ↔
        ∃ z : BiHom (t - s) t (XModLambdaN (N.functor.obj X) q),
          Synthetic.Bockstein.firstRestrictionHom coh (N.functor.obj X) q hq (t - s) t z =
            (FirstQuotientHomotopyComparison.unshifted H N Q cofib s t).symm x
  differential : IsENilpotentComplete H.unit X → IsAdamsTowerStronglyConvergent H.unit X →
    ∀ (q : ℕ) (hq : 1 ≤ q) (s t : ℤ) (x : Ambient H X (s, t)),
      IsCycle H X (q : ℤ) (s, t) x →
        ∃ z : BiHom (t - s) t (XModLambdaN (N.functor.obj X) q),
          Synthetic.Bockstein.firstRestrictionHom coh (N.functor.obj X) q hq (t - s) t z =
            (FirstQuotientHomotopyComparison.unshifted H N Q cofib s t).symm x ∧
          DifferentialAt H X ((q : ℤ) + 1) (s, t) (s + (q : ℤ) + 1, t + (q : ℤ)) x
            (-(FirstQuotientHomotopyComparison.bocksteinTargetClass H N Q cofib q s t z))

end FiniteBockstein

end SyntheticEInfty

end KIP126.Comparison
