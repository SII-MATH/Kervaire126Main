module

public import KIP126.Def.ClassicalAdams.PageRepresentatives.Predicates
public import KIP126.Def.AdamsSynthetic.Extensions.Crossing.Predicates

@[expose] public section

/-! 广义 Leibniz 法则的命题。
对象、代表元、微分及扩张都属于同一个 `AdamsComparison`。
本文件仅定义命题；同目录 `Proofs.lean` 中的论证仍有明确标出的待补证明。 -/
namespace KIP126.AdamsSynthetic.ExtensionLaws

open CategoryTheory CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Classical.Adams KIP126.Classical.Adams.PageRepresentatives

universe u v w
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H}
  (D : AdamsComparison H M Syn)

/-- MainPaper Theorem 6.1 (`thm:e73f481e`) 的广义 Leibniz 命题（旧来源编号 am7）。
所有页面、微分、有限／无限 extension 和 crossing 均来自同一 H、D。
末端次数是 (s+r+l,t+r+l-1)，l-extension 不额外减一次 t。
本定义不声称仅由 M 就能推出此 law；证明使用同一 D 上的文献比较输入及
论文中的 δ／λ／ρ 推理。不要求微分或 extension 非零。 -/
def GeneralizedLeibnizLaw (X Y : ClassicalObject) (f : X.obj D.hopfAndDetector ⟶ Y.obj D.hopfAndDetector) : Prop :=
  ∀ (page : ℕ) (r m l s t : ℤ)
    (x : Ambient H (X.obj D.hopfAndDetector) (s, t)) (y : Ambient H (Y.obj D.hopfAndDetector) (s + m, t + m))
    (xInfinity : Ambient H (X.obj D.hopfAndDetector) (s + r, t + r - 1))
    (yInfinity : Ambient H (Y.obj D.hopfAndDetector) (s + r + l, t + r - 1 + l)),
    2 ≤ page → (page : ℤ) ≤ r →
    (normalizedExponent H f : ℤ) ≤ m →
    m ≤ (page : ℤ) - 2 + normalizedExponent H f →
    (normalizedExponent H f : ℤ) ≤ l →
    IsCycle H (X.obj D.hopfAndDetector) (r - 1) (s, t) x →
    IsCycle H (Y.obj D.hopfAndDetector) (r - 1 - m + normalizedExponent H f) (s + m, t + m) y →
    IsPermanent H (X.obj D.hopfAndDetector) (s + r, t + r - 1) xInfinity →
    IsPermanent H (Y.obj D.hopfAndDetector) (s + r + l, t + r - 1 + l) yInfinity →
    DifferentialAt H (X.obj D.hopfAndDetector) r (s, t) (s + r, t + r - 1) x xInfinity →
    FiniteExtension D X Y f page m s t x y →
    InfiniteExtension D X Y f l (s + r) (t + r - 1) xInfinity yInfinity →
    (NoCrossingOn H (X.obj D.hopfAndDetector) r page (s, t) ∨
      FiniteExtension.NoCrossing D X Y f page m s t) →
    InfiniteExtension.NoCrossing D X Y f l (s + r) (t + r - 1) →
    DifferentialAt H (Y.obj D.hopfAndDetector) (r + l - m) (s + m, t + m)
      (s + r + l, t + r - 1 + l) y yInfinity

end KIP126.AdamsSynthetic.ExtensionLaws
