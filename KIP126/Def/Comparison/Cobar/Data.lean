module

public import KIP126.Def.ClassicalAdams.MilnorCohomology.Comparison.Data
public import KIP126.Def.ClassicalAdams.MilnorCohomology.Multiplication.Data
public import KIP126.Def.Steenrod.MilnorExt.Resolution.Data

@[expose] public section
/-!
# Cobar, derived Ext and cup-product comparison

These definitions specify comparison maps and their compatibility with
representatives, differentials and products on the given mathematical objects.
-/

namespace KIP126.Comparison

open CategoryTheory CategoryTheory.MonoidalCategory
open Classical.Adams SpectralSequence

universe u v w

/-- 规范 cobar–E₂ 比较：每个 cocycle 都必须映到同一 Adams 塔中的
实际类。该公式固定 cocycle 的像；导出 Ext 的比较单独陈述。 -/
def CobarE2Comparison {C : Type u} [StableHomotopy.StableHomotopyCategory.{u, v} C]
    [StableHomotopy.HasFunctorialCofiber (C := C)]
    (H : StableHomotopy.Cohomology.Mod2EilenbergMacLane (C := C))
    (M : MilnorCooperations H) : Prop :=
  ∀ s t : ℕ, ∃ e : MilnorCohomology.Cohomology H M s t ≃ₗ[ℤ]
      (adamsTowerInternalSpectralSequence H.unit StableHomotopy.SphereSpectrum).Page 2
        ((s : ℤ), (t : ℤ)),
    ∀ (x : Steenrod.Milnor.cochains s t) (hx : Steenrod.Milnor.differential s t x = 0),
      e (MilnorCohomology.ofCocycle H M x hx) =
        MilnorCohomology.internalClassOfCocycle H M x hx

/-- 独立的导出 Ext 比较。分解的逐项 comodule、微分和增广都由实际
Milnor 多项式公式固定；每个 cocycle 的像必须是该分解中的 `extMk` 类。
因此不能用另一份任意线性等价替代。左 Steenrod-module 约定及 Yoneda
乘法相容性仍是单独义务，本组不从加法比较自动推出它们。 -/
structure CobarDerivedExtComparison {C : Type u}
    [StableHomotopy.StableHomotopyCategory.{u, v} C]
    [StableHomotopy.HasFunctorialCofiber (C := C)]
    (H : StableHomotopy.Cohomology.Mod2EilenbergMacLane (C := C))
    (M : MilnorCooperations H) where
  cobarResolution : Steenrod.Milnor.Ext.CobarResolution
  comparison : ∀ (s t : ℕ), MilnorCohomology.Cohomology H M s t ≃ₗ[Algebra.F2]
    Steenrod.Milnor.Ext.SphereExt s (t : ℤ)
  representatives : ∀ (s t : ℕ) (x : Steenrod.Milnor.cochains s t)
      (hx : Steenrod.Milnor.differential s t x = 0),
    ∃ (f : Steenrod.Milnor.Ext.trivialAt (t : ℤ) ⟶
        cobarResolution.resolution.cocomplex.X s)
      (hf : f ≫ cobarResolution.resolution.cocomplex.d s (s + 1) = 0),
      cobarResolution.representativePolynomial f = Steenrod.Milnor.insertRight s x.val ∧
        comparison s t (MilnorCohomology.ofCocycle H M x hx) =
          cobarResolution.resolution.extMk f (s + 1) rfl hf

/-- 同一比较在内部 Adams E₂ 上的形式：只复合已固定的 cobar/E₂ 比较，
不重新选择页面坐标或另一份 Ext 等价。 -/
noncomputable def CobarDerivedExtComparison.internalEquiv {C : Type u}
    [StableHomotopy.StableHomotopyCategory.{u, v} C]
    [StableHomotopy.HasFunctorialCofiber (C := C)]
    {H : StableHomotopy.Cohomology.Mod2EilenbergMacLane (C := C)}
    {M : MilnorCooperations H} (E : CobarDerivedExtComparison H M) (s t : ℕ) :
    (adamsTowerInternalSpectralSequence H.unit StableHomotopy.SphereSpectrum).Page 2
      ((s : ℤ), (t : ℤ)) ≃ₗ[ℤ] Steenrod.Milnor.Ext.SphereExt s (t : ℤ) :=
  (MilnorCohomology.comparison H M s t).symm.trans
    ((E.comparison s t).restrictScalars ℤ)

/-- cobar 乘法比较；使用从 cochain concatenation 真正下降的 cup，
不另选乘法。与内部 Adams 高页配对的相容性是另一个义务。 -/
structure CobarCupCalculus {C : Type u}
    [StableHomotopy.StableHomotopyCategory.{u, v} C]
    [StableHomotopy.HasFunctorialCofiber (C := C)]
    (H : StableHomotopy.Cohomology.Mod2EilenbergMacLane (C := C))
    (M : MilnorCooperations H) : Prop where
  representatives : ∀ {s t s' t' : ℕ} (x : Steenrod.Milnor.cochains s t)
    (y : Steenrod.Milnor.cochains s' t')
    (hx : Steenrod.Milnor.IsCycle x) (hy : Steenrod.Milnor.IsCycle y),
    MilnorCohomology.cup H M (MilnorCohomology.ofCocycle H M x hx)
      (MilnorCohomology.ofCocycle H M y hy) =
        MilnorCohomology.ofCocycle H M (Steenrod.Milnor.cup x y)
          (Steenrod.Milnor.cup_isCycle x y hx hy)
  standard_squares : ∀ i : ℕ, MilnorCohomology.hiSquare H M i =
    MilnorCohomology.cohomologyReindex H M rfl (Steenrod.Milnor.hiSquare_internalDegree i)
      (MilnorCohomology.cup H M (MilnorCohomology.hi H M i) (MilnorCohomology.hi H M i))

end KIP126.Comparison
