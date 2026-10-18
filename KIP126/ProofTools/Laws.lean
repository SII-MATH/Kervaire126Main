module

public import KIP126.ProofTools.Language

/-! Actual page labels and crossing predicates for the paper's reusable tools.
Adapted from PageRepresentatives/Predicates and Route/Extensions at
bbac1fc05843 (MIT; see the retained source LICENSE); all operations refer to the same given model. -/

@[expose] section
namespace KIP126.ProofTools
noncomputable section
open CategoryTheory KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.Synthetic.SpectralSequence KIP126.Classical.Adams KIP126.AdamsSynthetic
open KIP126.Core.SpectralSequence KIP126.Kervaire.Route
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w,v} Syn]
  [HasFunctorialCofiber (C := Syn)] (D : Model C Syn)

/-- 本文待证工具（原 am7）：MainPaper Theorem 6.1 (`thm:e73f481e`) 的准确交付命题。
所有页面、微分、有限／无限 extension 和 crossing 均来自同一 D。
末端次数是 (s+r+l,t+r+l-1)，l-extension 不额外减一次 t。
本定义只给出命题；证明使用同一 D 上的文献比较定理及
论文中的 δ／λ／ρ 推理。不要求微分或 extension 非零。 -/
public def GeneralizedLeibnizLaw (X Y : ClassicalObject) (f : X.obj D.auxiliary ⟶ Y.obj D.auxiliary) : Prop :=
  ∀ (page : ℕ) (r m l s t : ℤ)
    (x : Ambient D X (s, t)) (y : Ambient D Y (s + m, t + m))
    (xInfinity : Ambient D X (s + r, t + r - 1))
    (yInfinity : Ambient D Y (s + r + l, t + r - 1 + l)),
    2 ≤ page → (page : ℤ) ≤ r →
    (normalizedExponent D.classicalTower f : ℤ) ≤ m →
    m ≤ (page : ℤ) - 2 + normalizedExponent D.classicalTower f →
    (normalizedExponent D.classicalTower f : ℤ) ≤ l →
    IsCycle D X (r - 1) (s, t) x →
    IsCycle D Y (r - 1 - m + normalizedExponent D.classicalTower f) (s + m, t + m) y →
    IsPermanent D X (s + r, t + r - 1) xInfinity →
    IsPermanent D Y (s + r + l, t + r - 1 + l) yInfinity →
    DifferentialAt D X r (s, t) (s + r, t + r - 1) x xInfinity →
    FiniteExtension D X Y f page m s t x y →
    InfiniteExtension D X Y f l (s + r) (t + r - 1) xInfinity yInfinity →
    (NoCrossingOn D X r page (s, t) ∨
      FiniteNoCrossing D X Y f page m s t) →
    InfiniteNoCrossing D X Y f l (s + r) (t + r - 1) →
    DifferentialAt D Y (r + l - m) (s + m, t + m)
      (s + r + l, t + r - 1 + l) y yInfinity


/-- 本文待证工具（原 am7）：MainPaper Theorem 6.12 (`thm:158d451a`) 的实际三角版本。
第二个 no-crossing 分支属于 Z 上的 d_r，在 E_r′ 页检查；不属于 g。
h 的 target 位于 ΣX，其标签通过 D.classicalSuspension 的实际 tower/layer 图和 raw-cycle
商代表元与 x 关联。该比较的构造证明尚未交付，不能以任意 E₂ 等价代替。
结论是存在同余于 y 的真实 f-extension target，模实际 B_r′；不是自由
选取的 fTarget 操作。r′ 及结论页的正性由指数和与三个长度界保证。 -/
public def GeneralizedMahowaldLaw (T : TriangleData D.auxiliary) : Prop :=
  ∀ he : (normalizedExponent D.classicalTower T.f : ℤ) + normalizedExponent D.classicalTower T.g +
      normalizedExponent D.classicalTower T.h = 1,
  KIP126.Literature.NormalizedTriangleCompatible D T he →
  ∀ (n m l s t : ℤ),
    let r := n + m + l
    let n₁ := n - normalizedExponent D.classicalTower T.f
    let m₁ := m - normalizedExponent D.classicalTower T.g
    let l₁ := l - normalizedExponent D.classicalTower T.h
    let r' := r - m₁
    ∀ (x : Ambient D (T.X) (s + l, t + l - 1))
      (y : Ambient D (T.Y) (s + l + n, t + l - 1 + n))
      (xBar : Ambient D (T.Z) (s, t))
      (yBar : Ambient D (T.Z) (s + l + n + m, t + l - 1 + n + m))
      (suspendedX : Ambient D (.shift 1 T.X) (s + l, t + l)),
      1 ≤ n₁ → 0 ≤ m₁ → 0 ≤ l₁ →
      IsCycle D (T.X) n₁ (s + l, t + l - 1) x →
      IsCycle D (T.Y) (m₁ + 1) (s + l + n, t + l - 1 + n) y →
      IsCycle D (T.Z) (r - 1) (s, t) xBar →
      IsPermanent D (T.Z) (s + l + n + m, t + l - 1 + n + m) yBar →
      (D.classicalSuspension T.X).DesuspendsClass (s + l) (t + l) suspendedX x →
      FiniteExtension D T.Z (.shift 1 T.X) T.h r'.toNat l s t xBar suspendedX →
      DifferentialAt D (T.Z) r (s, t)
        (s + l + n + m, t + l - 1 + n + m) xBar yBar →
      (FiniteNoCrossing D T.Z (.shift 1 T.X) T.h r'.toNat l s t ∨
        NoCrossingOn D (T.Z) r r' (s, t)) →
      FiniteExtension D T.Y T.Z T.g (m₁ + 2).toNat m (s + l + n) (t + l - 1 + n) y yBar →
      IsCycle D (T.X) (n + m + normalizedExponent D.classicalTower T.h) (s + l, t + l - 1) x ∧
        ∃ y' : Ambient D (T.Y) (s + l + n, t + l - 1 + n),
          FiniteExtension D T.X T.Y T.f (n + m + 1 + normalizedExponent D.classicalTower T.h).toNat
            n (s + l) (t + l - 1) x y' ∧
          Congruent D (T.Y) r' (s + l + n, t + l - 1 + n) y' y


/-- 本文待证工具（原 am7）：保留 λ 层数的有限页 stretching 充分条件。
参考 MainPaper Proposition `prop:dec738d3` 中同一有限商内的修正过程。
源、靶须属于后页所需的 cycle 层；排除的障碍是在早页同一个有限商中，
源不属于后页 ρ 的 E∞ 像、目标非零的实际较短扩张（包括非 essential 的扩张）。
不能改为只排除较小商中的无层扩张：乘 λ 可能杀掉低滤过项。
这比只排除 essential crossings 更强，不声称等价于原跨页候选或印出的推论。
原仓库已证明有限滤过修正；当前迁移状态另行追踪，不将迁移缺口认定为新假设。
结论只给出后页 extension 的存在，不声称任意指定的早期严格解可提升，
也不蕴含相容解塔或未截断 extension 的存在。 -/
public def FinitePageExtensionStretchingLaw (X Y : ClassicalObject) (f : X.obj D.auxiliary ⟶ Y.obj D.auxiliary) : Prop :=
  ∀ (rEarlier rLater : ℕ) (n s t : ℤ)
    (x : Ambient D X (s, t)) (y : Ambient D Y (s + n, t + n)),
    2 ≤ rEarlier → rEarlier ≤ rLater →
    (normalizedExponent D.classicalTower f : ℤ) ≤ n →
    n ≤ (rEarlier : ℤ) - 2 + normalizedExponent D.classicalTower f →
    IsCycle D X ((rLater : ℤ) - 1) (s, t) x →
    IsCycle D Y ((rLater : ℤ) - 1 - n + normalizedExponent D.classicalTower f) (s + n, t + n) y →
    FiniteExtension D X Y f rEarlier n s t x y →
    ¬ FiniteExtensionNonliftableCrossing D X Y f rEarlier rLater n s t →
    FiniteExtension D X Y f rLater n s t x y


end
end KIP126.ProofTools
