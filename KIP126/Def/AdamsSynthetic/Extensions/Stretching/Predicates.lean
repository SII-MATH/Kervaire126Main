module

public import KIP126.Def.AdamsSynthetic.Extensions.Predicates

@[expose] public section

namespace KIP126.AdamsSynthetic
open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H}
  (D : AdamsComparison H M Syn) (X Y : ClassicalObject)
  (f : X.obj D.hopfAndDetector ⟶ Y.obj D.hopfAndDetector)

/-- 有限 stretching 的障碍候选，直接在同一个早期 λ 商的实际 ESS 中定义。
源和靶的 synthetic weight 固定为原 extension 的 `t + e(f)`，而源的
filtration 提高 `a`。源必须不在后期商到早期商的实际 `ρ` 所诱导的
`E∞` 映射像中；这与某个普通 Adams 代表元不属于后页 cycle 层不同。
允许 `b = 0` 及长度 `n - a - b = 0` 的 synthetic extension，包括
`e(f) = 1` 的情形。要求同商中实际 extension equation 的靶非零，不要求
essential 性，不换成较小 λ 商的 extension，也不额外施加普通 Adams
boundary 排除条件。排除这些候选强于仅排除 essential crossings；这是
修复后的充分条件，不声称与原普通 Adams 代表元谓词等价。 -/
def FiniteExtensionNonliftableCrossing
    (rEarlier rLater : ℕ) (n s t : ℤ) : Prop :=
  ∃ hle : rEarlier ≤ rLater, ∃ a b : ℕ,
    0 < a ∧ a ≤ rEarlier - 2 ∧ (a : ℤ) + b ≤ n ∧
    ∃ (source : ((D.family.obj ((SyntheticObject.quotient (rEarlier - 1)
          (extensionSourceObject D X Y f)).obj D.nu D.hopfAndDetector)).sequence.ssData
          (s + a, (t - s) + (s + a), t + normalizedExponent H f)).eInfty)
      (target : ((D.family.obj ((SyntheticObject.quotient (rEarlier - 1)
          (.nu Y)).obj D.nu D.hopfAndDetector)).sequence.ssData
          (s + a + (n - a - b), (t - s) + (s + a + (n - a - b)),
            t + normalizedExponent H f)).eInfty),
      source ∉ Set.range (((D.family.functor.map
        ((D.quotientTower ((extensionSourceObject D X Y f).obj D.nu D.hopfAndDetector)).rho
          (rEarlier - 1) (rLater - 1) (Nat.sub_le_sub_right hle 1))).eInftyMap
            (s + a, (t - s) + (s + a), t + normalizedExponent H f)).hom) ∧
      ExtensionEquation (finiteExtensionMap D X Y f (rEarlier - 1))
        (D.convergence (.quotient (rEarlier - 1) (extensionSourceObject D X Y f)))
        (D.convergence (.quotient (rEarlier - 1) (.nu Y)))
        (t - s, t + normalizedExponent H f) (s + a) (n - a - b) source target ∧
      target ≠ 0

end KIP126.AdamsSynthetic
