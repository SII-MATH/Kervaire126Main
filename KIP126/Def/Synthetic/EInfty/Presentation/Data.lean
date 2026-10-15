module

public import KIP126.Def.ClassicalAdams.PageRepresentatives.Quotient.Window.Data
public import KIP126.Def.Synthetic.EInfty.Shift.Data

@[expose] public section

namespace KIP126.Synthetic.SpectralSequence
open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Synthetic.Context KIP126.Classical.Adams.PageRepresentatives
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]
  (H : Mod2EilenbergMacLane (C := C)) (N : NuFunctorData C Syn)
  (F : SyntheticAdamsFamily Syn)

/-- BHS A.9 的准确内部公式类型；存在性及文献输入另行处理。 -/
abbrev NuEInftyFormula := ∀ (X : C) (p : ℤ × ℤ) (w : ℤ),
  ((F.nu N X).sequence.ssData (p.1, p.2, w)).eInfty ≃ₗ[ℤ]
    nuEInftyModel H X p w

/-- BHS A.11 的准确指数范围，不包含 q=1。 -/
abbrev FiniteEInftyFormula := ∀ (X : C) (q : ℕ), 2 ≤ q → ∀ (p : ℤ × ℤ) (w : ℤ),
  ((F.nuQuotient N X q).sequence.ssData (p.1, p.2, w)).eInfty ≃ₗ[ℤ]
    finiteEInftyModel H X q p w

/-- 同一模型在所有 weight 上的 E∞ 公式。`nu` 对应 BHS Corollary A.9，
`quotient` 只在 A.11 的 q≥2 范围使用；q=1 的 special-fiber 结论单独陈述。
比较靶由实际 classical E₂ 子模定义，范围外严格为零。该数据不自动满足
λ、ρ 相容性；下面的独立谓词固定这些数学义务。 -/
structure SyntheticEInftyPresentation where
  nu : NuEInftyFormula H N F
  quotient : FiniteEInftyFormula H N F
  specialFiber : ∀ (X : C) (p : ℤ × ℤ) (w : ℤ),
    ((F.nuQuotient N X 1).sequence.ssData (p.1, p.2, w)).eInfty ≃ₗ[ℤ]
      finiteEInftyModel H X 1 p w

namespace SyntheticEInftyPresentation
variable {H N F}

/-- 仅使用已有两个指数范围的比较；不在每次使用时重新选择同构。 -/
noncomputable def finite (P : SyntheticEInftyPresentation H N F)
    (X : C) (q : ℕ) (hq : 0 < q) (p : ℤ × ℤ) (w : ℤ) :
    ((F.nuQuotient N X q).sequence.ssData (p.1, p.2, w)).eInfty ≃ₗ[ℤ]
      finiteEInftyModel H X q p w := by
  by_cases hq1 : q = 1
  · subst q
    exact P.specialFiber X p w
  · exact P.quotient X q (by omega) p w

noncomputable def nuWindow (P : SyntheticEInftyPresentation H N F)
    (X : C) (p : ℤ × ℤ) (w : ℤ) (hw : w ≤ p.2) :
    ((F.nu N X).sequence.ssData (p.1, p.2, w)).eInfty ≃ₗ[ℤ]
      PermanentQuotient H X (1 + p.2 - w) p :=
  (P.nu X p w).trans (nuEInftyWindow H X p w hw)

noncomputable def finiteWindow (P : SyntheticEInftyPresentation H N F)
    (X : C) (q : ℕ) (hq : 0 < q) (p : ℤ × ℤ) (w : ℤ)
    (hw : 0 ≤ p.2 - w ∧ p.2 - w < q) :
    ((F.nuQuotient N X q).sequence.ssData (p.1, p.2, w)).eInfty ≃ₗ[ℤ]
      CycleQuotient H X (q - p.2 + w) (1 + p.2 - w) p :=
  (P.finite X q hq p w).trans (finiteEInftyWindow H X q p w hw)

end SyntheticEInftyPresentation

end KIP126.Synthetic.SpectralSequence
