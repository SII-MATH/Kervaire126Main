module

public import KIP126.Def.AdamsSynthetic.Comparison.Coherent.Data
public import KIP126.Def.StableHomotopy.Spectra.Tensor
public import KIP126.Def.StableHomotopy.Cohomology.Data
public import KIP126.Def.ClassicalAdams.MilnorCooperations.Data
public import KIP126.Def.ClassicalAdams.MapFiltration.Predicates
public import KIP126.Def.Synthetic.Context.Data
public import KIP126.Def.Synthetic.Localization.Recovery.Data
public import KIP126.Def.Synthetic.QuotientTower.Predicates
public import KIP126.Def.Synthetic.QuotientTower.Data
public import KIP126.Def.StableHomotopy.InverseSequence.Data
public import KIP126.Def.StableHomotopy.InverseSequence.Predicates
public import KIP126.Def.ClassicalAdams.Completion.Predicates
public import KIP126.Def.ClassicalAdams.TowerHomology.MilnorCoordinates.Data
public import KIP126.Def.StableHomotopy.Cohomology.Cooperations.Kunneth.Suspension.Predicates
public import KIP126.Def.StableHomotopy.Cohomology.Cooperations.Kunneth.Diagonal.Predicates
public import KIP126.Def.StableHomotopy.Cohomology.Cooperations.Kunneth.Unit.Predicates
public import KIP126.Def.StableHomotopy.Cohomology.Cooperations.MilnorBasis.Coproduct.Predicates
public import KIP126.Def.StableHomotopy.Context.Mapping.Data
public import KIP126.Def.StableHomotopy.Context.Proofs
public import KIP126.Def.StableHomotopy.Toda.Predicates
public import KIP126.Def.HigherAlgebra.Operad.Moduli.Data
public import KIP126.Def.HigherAlgebra.Operad.Model.Data
public import KIP126.Def.HigherAlgebra.Operad.Topological.Predicates
public import Mathlib.Topology.Homotopy.HomotopyGroup
public import Mathlib.AlgebraicTopology.ModelCategory.Instances
public import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant
public import Mathlib.CategoryTheory.Localization.Predicate
public import Mathlib.Algebra.Exact.Basic

@[expose] public section

/-! The classical mod-two Adams context and its synthetic comparisons.

`Mod2StableHomotopyContext` specifies a stable category and H𝔽₂.
`MilnorCoordinates` identifies the sphere's Adams first page with the Milnor
cobar complex, while `TensorTriangulatedStructure` and
`MilnorCooperationStructure` record the compatible smash product and
cooperations. `HF2AdamsContext` also identifies this category and its tensor
product with the HF₂-local prespectra of `StableHomotopy.Spectra`.

These are mathematical structures, parameterized by their stated data.
Their existence and a fixed choice are assumed separately in
`AdamsSynthetic.Standard.ClassicalContext` and `ClassicalAdams.Context.Standard`.
All subsequent synthetic, literature and computation statements concern
that same choice. -/
namespace KIP126

open StableHomotopy StableHomotopy.Cohomology Classical.Adams

namespace Foundation

open CategoryTheory MonoidalCategory

/-- 带有指定 H𝔽₂ 的稳定同伦范畴，并具有可数积与可数余积。

`stable` 给出加性、整数悬移、幺半结构、零对象及预三角结构；
`cofiber` 给出选定的余纤维三角及交换方块的相容提升。
H𝔽₂ 满足 π₀(H𝔽₂) ≅ 𝔽₂，且其他同伦群消失。
对称闭张量、三角公理及其相容性另由 `TensorTriangulatedStructure` 给出。 -/
structure Mod2StableHomotopyContext where
  Spectrum : Type 1
  stable : StableHomotopyCategory.{1, 0} Spectrum
  cofiber : letI := stable; HasFunctorialCofiber (C := Spectrum)
  countableProducts : @CategoryTheory.Limits.HasProductsOfShape ℕ Spectrum stable.toCategory
  countableCoproducts : @CategoryTheory.Limits.HasCoproductsOfShape ℕ Spectrum stable.toCategory
  HF2 : Spectrum
  pi0Equiv : @HomotopyGroup Spectrum stable 0 HF2 ≃+ ZMod 2
  homotopy_vanishes : ∀ n : ℤ, n ≠ 0 →
    Subsingleton (@HomotopyGroup Spectrum stable n HF2)

attribute [instance] Mod2StableHomotopyContext.stable Mod2StableHomotopyContext.cofiber Mod2StableHomotopyContext.countableProducts Mod2StableHomotopyContext.countableCoproducts

/-- 此稳定同伦范畴中的指定模二 Eilenberg–Mac Lane 对象。 -/
def Mod2StableHomotopyContext.hf2 (F : Mod2StableHomotopyContext) :
    @Mod2EilenbergMacLane F.Spectrum F.stable where
  HF2 := F.HF2
  pi0Equiv := F.pi0Equiv
  homotopy_vanishes := F.homotopy_vanishes

/-- 模二 Adams 构造所用的稳定同伦背景；与 `Mod2StableHomotopyContext`
为同一个类型。 -/
abbrev _root_.KIP126.Classical.Adams.StandardAdamsFoundation := Mod2StableHomotopyContext

/-- 将此稳定同伦背景视为 Adams 构造的背景，保持全部数据不变。 -/
def Mod2StableHomotopyContext.toStandard (F : Mod2StableHomotopyContext) : StandardAdamsFoundation := F

/-- 同一基础上的 Milnor 坐标与第一微分相容性。

坐标覆盖所有非负双次数，等价的标量环是 ℤ；第一页面及其微分来自
`F.hf2.unit` 的实际 Adams 塔构造。这里不另行假设乘法相容或永久存活。 -/
structure MilnorCoordinates (F : Mod2StableHomotopyContext) where
  coordinates : ∀ s t : ℕ,
    adamsPage F.hf2.unit (SphereSpectrum (C := F.Spectrum)) 1 (by decide) s t ≃ₗ[ℤ]
      Steenrod.Milnor.cochains s t
  differential_coordinates : ∀ (s t : ℕ)
      (x : adamsPage F.hf2.unit (SphereSpectrum (C := F.Spectrum)) 1 (by decide) s t),
    coordinates (s + 1) t (sphereFirstDifferential F.hf2 s t x) =
      Steenrod.Milnor.differential s t (coordinates s t x)

/-- The Milnor cooperations determined by these first-page coordinates and
their compatibility with the cobar differential. -/
def MilnorCoordinates.toMilnor {F : Mod2StableHomotopyContext} (M : MilnorCoordinates F) :
    MilnorCooperations F.hf2 where
  coordinates := M.coordinates
  differential_coordinates := M.differential_coordinates

/-- A synthetic Adams category over the specified classical mod-two context.
The Adams comparison records ν, λ-localization, towers, convergence and compatible
classical/synthetic comparisons on the objects used in Section 7.
The external theorems and computations are separate hypotheses about these
objects; existence of this structure is assumed separately. -/
structure SyntheticAdamsContext (F : Mod2StableHomotopyContext) (M : MilnorCoordinates F) where
  Syn : Type 1
  synthetic : KIP126.Synthetic.Context.SyntheticCategory.{1, 0} Syn
  cofiber : letI := synthetic.toStableHomotopyCategory; HasFunctorialCofiber (C := Syn)
  adamsComparison : @KIP126.AdamsSynthetic.AdamsComparison F.Spectrum F.stable F.cofiber
    F.hf2 M.toMilnor Syn synthetic cofiber

attribute [instance] SyntheticAdamsContext.synthetic SyntheticAdamsContext.cofiber

/-- 模二稳定同伦范畴上的对称闭张量三角结构。
左右张量与内部 Hom 的精确性、悬移比较及其伴随相容性均使用同一组结构；
Künneth 公式与余纤维边界公式采用这些指定的悬移比较。 -/
class TensorTriangulatedStructure (F : Mod2StableHomotopyContext) where
  [triangulated : IsTriangulated F.Spectrum]
  [monoidalPreadditive : MonoidalPreadditive F.Spectrum]
  [symmetric : SymmetricCategory F.Spectrum]
  [closed : MonoidalClosed F.Spectrum]
  [leftShift : ∀ X : F.Spectrum, (tensorLeft X).CommShift ℤ]
  [rightShift : ∀ X : F.Spectrum, (tensorRight X).CommShift ℤ]
  [ihomShift : ∀ X : F.Spectrum, (ihom X).CommShift ℤ]
  [leftExact : ∀ X : F.Spectrum, (tensorLeft X).IsTriangulated]
  [rightExact : ∀ X : F.Spectrum, (tensorRight X).IsTriangulated]
  [ihomExact : ∀ X : F.Spectrum, (ihom X).IsTriangulated]
  [unitShift : (mod2UnitNatTrans F.hf2).CommShift ℤ]
  leftShift_eq : ∀ X : F.Spectrum,
    leftShift X = Functor.CommShift.ofIso (BraidedCategory.tensorLeftIsoTensorRight X).symm ℤ
  ihom_unit_shift : ∀ X : F.Spectrum, NatTrans.CommShift (ihom.adjunction X).unit ℤ
  ihom_counit_shift : ∀ X : F.Spectrum, NatTrans.CommShift (ihom.adjunction X).counit ℤ

attribute [reducible] TensorTriangulatedStructure.symmetric TensorTriangulatedStructure.closed TensorTriangulatedStructure.leftShift TensorTriangulatedStructure.rightShift TensorTriangulatedStructure.ihomShift
attribute [instance] TensorTriangulatedStructure.triangulated TensorTriangulatedStructure.monoidalPreadditive TensorTriangulatedStructure.symmetric TensorTriangulatedStructure.closed TensorTriangulatedStructure.leftShift TensorTriangulatedStructure.rightShift TensorTriangulatedStructure.leftExact TensorTriangulatedStructure.rightExact TensorTriangulatedStructure.ihomShift TensorTriangulatedStructure.ihomExact TensorTriangulatedStructure.unitShift

/-- H𝔽₂ 的环结构、Künneth 同构与约化 Milnor 基。
这些数据与悬移、对角、单位和余乘法相容；`coordinates_eq` 要求它们诱导的
Adams 第一页坐标恰为指定的 `MilnorCoordinates`。 -/
structure MilnorCooperationStructure (F : Mod2StableHomotopyContext) [TensorTriangulatedStructure F] (M : MilnorCoordinates F) where
  ring : Mod2RingStructure F.hf2
  kunneth : Mod2CooperationKunneth F.hf2 ring
  basis : Mod2ReducedMilnorBasis F.hf2 ring
  suspension : Mod2KunnethSuspensionCompatible F.hf2 ring kunneth
  diagonal : Mod2KunnethDiagonalCompatible F.hf2 ring kunneth
  unit : Mod2KunnethUnitCompatible F.hf2 ring kunneth
  coproduct : Mod2MilnorCoproductCompatible F.hf2 ring kunneth basis
  coordinates_eq : ∀ (s t : ℕ)
      (x : adamsPage F.hf2.unit (SphereSpectrum (C := F.Spectrum)) 1 (by decide) s t),
    M.coordinates s t x = sphereFirstPageMilnorEquiv F.hf2 ring kunneth basis s t x

/-- Milnor cobar 微分满足 d² = 0。
此性质可由 Adams 第一页的复形结构和 Milnor 坐标相容性推出。 -/
def MilnorCobarSquareZero : Prop :=
  ∀ (s t : ℕ) (x : Steenrod.Milnor.cochains s t),
    Steenrod.Milnor.differential (s + 1) t
      (Steenrod.Milnor.differential s t x) = 0

open CategoryTheory.Limits

universe u v

universe u' v'

end Foundation

/-- The mod-two Adams context on an HF₂-local stable homotopy category.
It comprises H𝔽₂, the Milnor cobar coordinates, compatible tensor and
cooperation structures, and an equivalence with the specified HF₂-local
prespectrum category respecting suspension, cofibers, homotopy and smash.
All comparisons use the one HF₂-local reflection `Q`.
Existence is the separate assumption `AdamsSynthetic.hf2AdamsContext_exists`. -/
structure HF2AdamsContext (Q : StableHomotopy.Spectra.CompletionModel) where
  stableContext : Foundation.Mod2StableHomotopyContext
  milnorCoordinates : Foundation.MilnorCoordinates stableContext
  tensorStructure : Foundation.TensorTriangulatedStructure stableContext
  cooperationStructure : @Foundation.MilnorCooperationStructure stableContext tensorStructure milnorCoordinates
  sourceComparison : StableHomotopy.Spectra.SourceComparison Q stableContext.hf2
  sourceTensor : letI := tensorStructure
    StableHomotopy.Spectra.TensorComparison sourceComparison

namespace HF2AdamsContext

open Foundation

variable {Q : StableHomotopy.Spectra.CompletionModel}

/-- 此 HF₂ Adams 背景中的稳定同伦范畴与模二系数对象。 -/
def foundation (c : KIP126.HF2AdamsContext Q) : StandardAdamsFoundation :=
  c.stableContext.toStandard

/-- 此背景中球面 Adams 第一页的 Milnor 坐标与微分相容性。 -/
def milnor (c : KIP126.HF2AdamsContext Q) :
    @MilnorCooperations c.foundation.Spectrum c.foundation.stable
      c.foundation.cofiber c.foundation.hf2 where
  coordinates := c.milnorCoordinates.coordinates
  differential_coordinates := c.milnorCoordinates.differential_coordinates

end HF2AdamsContext



namespace Synthetic

open CategoryTheory CategoryTheory.Pretriangulated MonoidalCategory
open Context

universe u v u' v'

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type u'} [SyntheticCategory.{u', v'} Syn]

/-- 点集模型中的单位箭头在 L 下实现 synthetic 球面的一阶 λ 商映射。
单位对象、商对象及其映射通过同一个交换方块比较；L 的局部化性质、
派生张量与代数模型比较是另行陈述的条件。 -/
structure LambdaQuotientRealization {M : Type u} [Category.{v} M] [MonoidalCategory M]
    [HasFunctorialCofiber (C := Syn)] (L : M ⥤ Syn) where
  object : M
  unit : 𝟙_ M ⟶ object
  unitIso : L.obj (𝟙_ M) ≅ (S_0_0 : Syn)
  quotientIso : L.obj object ≅ XModLambdaN (S_0_0 : Syn) 1
  unit_comparison : L.map unit ≫ quotientIso.hom =
    unitIso.hom ≫ XModLambdaN.incl (S_0_0 : Syn) 1

/-- 一阶 λ 商的拓扑富集 operad 模型。
张量、E∞ operad、转移的代数模型结构与商单位都定义于同一个模型范畴；
其单位对象须为 cofibrant。与 synthetic 交换代数的高阶比较仍是独立条件，
仅有底层同伦范畴的局部化不足以给出这一比较。 -/
structure LambdaQuotientOperadPresentation {M : Type (u + 1)} [Category.{u + 1} M]
    [MonoidalCategory M] [SymmetricCategory M]
    [EnrichedOrdinaryCategory TopCat.{u + 1} M]
    [HomotopicalAlgebra.ModelCategory M] [HasFunctorialCofiber (C := Syn)]
    (L : M ⥤ Syn) where
  localization : L.IsLocalization (HomotopicalAlgebra.weakEquivalences M)
  unit_cofibrant : HomotopicalAlgebra.IsCofibrant (𝟙_ M)
  tensor : HigherAlgebra.EnrichedTensor.Presentation M
  tensor_laws : HigherAlgebra.EnrichedTensor.SymmetricTensorLaws tensor
  operad : HigherAlgebra.Operad.TopologicalOperad.{u + 1}
  eInfinity : operad.IsEInfinity
  reduced : operad.IsReduced
  nullary : operad.Op HigherAlgebra.EnrichedTensor.empty
  algebraModel : HigherAlgebra.Operad.TransferredModelStructure
    tensor tensor_laws.toTensorLaws operad
  quotient : LambdaQuotientRealization L

/-- a09 的具体模空间候选：以同一模型的实际弱等价取 nerve，实现后沿保单位
忘却函子取路径纤维；基点是所选商箭头，且它由 `unit_comparison` 固定到原来的
一阶 λ 商映射。不是自由指定的空间，也不是严格 action 集合的 Subsingleton。 -/
noncomputable def LambdaQuotientOperadPresentation.moduli
    {M : Type (u + 1)} [Category.{u + 1} M] [MonoidalCategory M] [SymmetricCategory M]
    [EnrichedOrdinaryCategory TopCat.{u + 1} M]
    [HomotopicalAlgebra.ModelCategory M] [HasFunctorialCofiber (C := Syn)]
    {L : M ⥤ Syn} (I : LambdaQuotientOperadPresentation L) : TopCat.{u + 1} :=
  HigherAlgebra.Operad.EnrichedAlgebra.unitModuli I.tensor I.tensor_laws.toTensorLaws
    I.operad I.nullary (HomotopicalAlgebra.weakEquivalences M) I.quotient.unit

/-! ## λ 反演与 classical 稳定同伦范畴

局部对象由 `lam.app` 为同构定义。反射函子、局部范畴与 classical 范畴的
等价，以及 ν 的局部化比较，均作为指定背景上的数学数据陈述。
来源：Pstrągowski 的 `prop:tau_inversion_functor_exists`、
`thm:tau_invertible_synthetic_spectra_are_just_spectra`，以及
`prop:spectral_yoneda_embedding_the_tau_inversion_of_the_synthetic_analogue`。
-/

/-! ## ν 保持余纤维的判据与 Adams 滤过提升

参数 H 与 N 分别是同一背景中的 H𝔽₂ 和 synthetic analogue ν。
以下命题显式保留模二同调的完整短正合条件，以及提升映射在 λ 下还原为
ν 的实际映射的等式。它们在固定 synthetic 背景中的成立性由文献假设给出。
-/

/-- 每个整数次数上的完整短正合条件；仅有中间 `Exact` 不够。 -/
def HomologyShortExact (H : Mod2EilenbergMacLane (C := C)) (T : Triangle C) : Prop :=
  ∀ n : ℤ,
    Function.Injective (Mod2Homology.pushforward H T.mor₁ n) ∧
    Function.Exact (Mod2Homology.pushforward H T.mor₁ n)
      (Mod2Homology.pushforward H T.mor₂ n) ∧
    Function.Surjective (Mod2Homology.pushforward H T.mor₂ n)

/-- 同一个 classical 三角的 ν 前两条箭头能否组成 synthetic distinguished triangle。
第三箭头落在 ΣνX；它与 ν(ΣX) 的关系由 a11 单独控制。 -/
def NuImageIsCofiber (N : NuFunctorData C Syn) (T : Triangle C) : Prop :=
  ∃ δ : N.functor.obj T.obj₃ ⟶ (N.functor.obj T.obj₁)⟦(1 : ℤ)⟧,
    Triangle.mk (N.functor.map T.mor₁) (N.functor.map T.mor₂) δ ∈ distTriang Syn

/-- a10：Pstrągowski Lemma 4.23 的完整双向判据。
来源：MainPaper `prop:1f7950df`；Pst 原文
`lemma:fibre_sequences_that_are_short_exaft_sequences_on_homology_preserved_by_synthetic_analogue_construction`。
不额外限制有限谱、连通性或完备性。 -/
def NuCofiberCriterion (H : Mod2EilenbergMacLane (C := C))
    (N : NuFunctorData C Syn) : Prop :=
  ∀ T : Triangle C, T ∈ distTriang C →
    (NuImageIsCofiber N T ↔ HomologyShortExact H T)

/-- a11 的 full lift：使用 BHS 图中的负移靶写法 νX → Σ^(0,-k)νY。
所选映射与 νf 的 λᵏ 分解等式是同一个见证的两个字段。 -/
structure SyntheticFullLift (N : NuFunctorData C Syn) {X Y : C}
    (f : X ⟶ Y) (k : ℕ) where
  map : N.functor.obj X ⟶
    (SyntheticCategory.biShift (0, -(k : ℤ))).obj (N.functor.obj Y)
  factorization : map ≫ lambdaPow k (N.functor.obj Y) = N.functor.map f

/-- a11：BHS Lemma 9.15；filtration 下界由实际 Adams 塔因子分解定义。
来源：BHS `SynRevBigraded.tex`, `lemm:adams-fil1`；MainPaper `prop:ef21f9bc`。
该类型不假设任意 full lift 都是提升三角的分量。 -/
def SyntheticLiftComparison (H : Mod2EilenbergMacLane (C := C))
    (N : NuFunctorData C Syn) : Prop :=
  ∀ {X Y : C} (f : X ⟶ Y) (k : ℕ),
    AdamsFiltrationAtLeast H f k → Nonempty (SyntheticFullLift N f k)

/-- a11 的三角提升：前两条箭头固定为 νf、νg，第三箭头同时满足
λ 下的分解等式和 distinguished 条件，不能用无关三角填入。 -/
structure SyntheticTriangleLift (N : NuFunctorData C Syn) (T : Triangle C) where
  connecting : N.functor.obj T.obj₃ ⟶
    (SyntheticCategory.biShift (0, -1)).obj (N.functor.obj (T.obj₁⟦(1 : ℤ)⟧))
  factorization :
    connecting ≫ SyntheticCategory.lam.app (N.functor.obj (T.obj₁⟦(1 : ℤ)⟧)) =
      N.functor.map T.mor₃
  distinguished :
    Triangle.mk (N.functor.map T.mor₁) (N.functor.map T.mor₂)
      (connecting ≫ (N.boundaryLandingIso T.obj₁).hom) ∈ distTriang Syn

/-- 实际 Hom 群中的 λ-torsion：某个源上的 λ 幂消去该映射。 -/
def LambdaTorsion {A B : Syn} (f : A ⟶ B) : Prop :=
  ∃ n : ℕ, lambdaPow n A ≫ f = 0

/-- 将 full lift 的靶乘 λ^(k-1)，仅形成一次 λ 除法的候选映射。
此构造本身不声称它就是某个 distinguished triangle 的 connecting map。 -/
noncomputable def SyntheticFullLift.normalizedMap (N : NuFunctorData C Syn)
    {X Y : C} {f : X ⟶ Y} {k : ℕ} (L : SyntheticFullLift N f k) (hk : 1 ≤ k) :
    N.functor.obj X ⟶ (SyntheticCategory.biShift (0, -1)).obj (N.functor.obj Y) :=
  L.map ≫ lowerFullLiftTarget (N.functor.obj Y) k hk

/-- MainPaper `prop:41561db2` 后的 remark：任意 full lift 与选定三角分量
仅模 λ-torsion 比较，不能将这项要求加强为两个映射严格相等。 -/
def SyntheticTriangleLift.FullLiftComparison (N : NuFunctorData C Syn)
    {T : Triangle C} (D : SyntheticTriangleLift N T) : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k) (L : SyntheticFullLift N T.mor₃ k),
    LambdaTorsion (D.connecting - SyntheticFullLift.normalizedMap N L hk)

/-- BHS Lemma 9.15 的证明及 MainPaper `prop:41561db2` 给出的三角提升性质。
将正 filtration、完整短正合、三条映射及 λ-torsion 比较同时列出；正 filtration
蕴含同调短正合的派生证明独立处理，不从最小抽象背景中擅自省去条件。 -/
def SyntheticTriangleLiftComparison (H : Mod2EilenbergMacLane (C := C))
    (N : NuFunctorData C Syn) : Prop :=
  ∀ T : Triangle C, T ∈ distTriang C →
    AdamsFiltrationAtLeast H T.mor₃ 1 → HomologyShortExact H T →
      ∃ D : SyntheticTriangleLift N T, D.FullLiftComparison N

/-- ν 的余纤维判据、Adams 滤过提升及三角提升性质。
三个命题使用同一个 H𝔽₂ 与 ν；此结构陈述这些性质，并不证明它们成立。 -/
structure NuCofiberAndLiftTheorems (H : Mod2EilenbergMacLane (C := C))
    (N : NuFunctorData C Syn) : Prop where
  nu_cofiber : NuCofiberCriterion H N
  lift : SyntheticLiftComparison H N
  triangle_lift : SyntheticTriangleLiftComparison H N

end Synthetic

end KIP126
