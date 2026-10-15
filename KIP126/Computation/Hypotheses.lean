module

public import KIP126.Def.SpectralSequence.Computation.CyclesAndBoundaries.Predicates
public import KIP126.Literature.Standard.Sphere.Sequence
public import KIP126.Literature.Standard.Sphere.Classes
public import KIP126.Computation.LinCoordinates.Model.Classes.Data
public import KIP126.Computation.LinCoordinates.Model.BasisCatalogue.Data
public import KIP126.Def.ClassicalAdams.SphereMultiplication.Data
public import KIP126.Def.ClassicalAdams.Suspension.Predicates
public import KIP126.Computation.LinCoordinates.Generated.Differentials.Table
public import KIP126.Computation.LinCoordinates.Generated.Staircase.Table
public import KIP126.Def.ComputationModel.Interpretation.Staircase.Data
public import KIP126.Def.SpectralSequence.Computation.Predicates
public import KIP126.Computation.LinCoordinates.Presentation
public import KIP126.Computation.Tmf.Standard
public import KIP126.Computation.LinCoordinates.Interpretation.SphereAndCofiber.Certification
public import KIP126.Literature.Hypotheses

@[expose] public section

namespace KIP126

namespace ExternalHypotheses

open CategoryTheory CategoryTheory.MonoidalCategory
open Classical.Adams LinE2
open SpectralSequence

universe u v w

/-- cm1：球面 E₂ 在 t ≤ 261 范围内的完整基。
坐标等价同时给出线性无关性与生成性；各单位向量经同一
`presentation` 拉回后，恰为固定 CSV 记录指定的单项式。 -/
structure SphereE2Basis (P : LinE2Presentation) where
  coordinates : ∀ (s t : ℕ), t ≤ 261 →
    sphereAdamsData.Page 2 ((s : ℤ), (t : ℤ)) ≃ₗ[ℤ]
      (BasisIndex s t →₀ Algebra.F2)
  csv_values : ∀ (s t : ℕ) (ht : t ≤ 261) (i : BasisIndex s t),
    ((P.comparison s t ht).symm
      ((coordinates s t ht).symm (Finsupp.single i 1))).val =
        basisValue (basisRowAt s t i)

/-- cm1/am4：Lin 的 cobar 坐标与实际球面 E₂ 乘法、单位的比较。
在 t+t′≤261 的范围内，实际 Adams 塔代表元的乘积仍是第二页循环，
其商类等于 `presentation.product` 给出的乘积。此陈述的范围限于
E₂ 的有界乘法比较；高页 Leibniz 公式另行证明。 -/
def SphereE2MultiplicationComparison (P : LinE2Presentation) : Prop :=
  let c := KIP126.AdamsSynthetic.Standard.classicalContext
  letI : Foundation.TensorTriangulatedStructure c.stableContext := c.tensorStructure
  (∃ x : LinE2.E2At 0 0, x.val = 1 ∧
    P.comparison 0 0 (by decide) x =
      Suspension.classOfSecondCycle c.stableContext.hf2
        StableHomotopy.SphereSpectrum 0 0
        (Sphere.Multiplication.unitSecondCycle c.stableContext.hf2)) ∧
  ∀ (s t s' t' : ℕ), t + t' ≤ 261 →
    ∀ (a : adamsCycles c.stableContext.hf2.unit StableHomotopy.SphereSpectrum
          2 (by decide) s t)
      (b : adamsCycles c.stableContext.hf2.unit StableHomotopy.SphereSpectrum
          2 (by decide) s' t'),
      ∃ z : adamsCycles c.stableContext.hf2.unit StableHomotopy.SphereSpectrum
          2 (by decide) ((s + s' : ℕ) : ℤ) ((t + t' : ℕ) : ℤ),
        z.val = Sphere.Multiplication.firstProduct c.stableContext.hf2
          c.cooperationStructure.ring s t s' t' a.val b.val ∧
        P.product s t s' t'
          (Suspension.classOfSecondCycle c.stableContext.hf2
            StableHomotopy.SphereSpectrum s t a)
          (Suspension.classOfSecondCycle c.stableContext.hf2
            StableHomotopy.SphereSpectrum s' t' b) =
          Suspension.classOfSecondCycle c.stableContext.hf2
            StableHomotopy.SphereSpectrum
            ((s + s' : ℕ) : ℤ) ((t + t' : ℕ) : ℤ) z

/-- Literal CSV coordinates, independent of any choice of comparison map. -/
def HasCoordinates {s t : Nat} (x : E2At s t) (indices : List Nat) : Prop :=
  ∃ rows : List BasisRow,
    rows.map BasisRow.index = indices ∧
    (∀ row ∈ rows, row ∈ basisRows ∧ row.s = s ∧ row.t = t) ∧
    x.val = (rows.map basisValue).sum

/-- A fixed differential-table row interpreted in the actual sphere Adams
spectral sequence, using one Lin comparison for both source and target. -/
def DifferentialStatement (presentation : Classical.Adams.LinE2Presentation)
    (row : Computation.LinCalculations.DifferentialRow) : Prop :=
  ∃ (hx : row.t ≤ 261) (hy : row.t + row.r - 1 ≤ 261),
    ∃ (x : E2At row.s row.t) (y : E2At (row.s + row.r) (row.t + row.r - 1)),
      HasCoordinates x row.x ∧ HasCoordinates y row.dx ∧
      ∃ (h : ((row.s : ℤ), (row.t : ℤ)) + Classical.Adams.sphereAdamsData.diffDeg row.r =
          (((row.s + row.r : Nat) : ℤ), ((row.t + row.r - 1 : Nat) : ℤ)))
        (xr : Classical.Adams.sphereAdamsData.Page row.r ((row.s : ℤ), (row.t : ℤ)))
        (yr : Classical.Adams.sphereAdamsData.Page row.r
          (((row.s + row.r : Nat) : ℤ), ((row.t + row.r - 1 : Nat) : ℤ))),
        RepresentsOnPage Classical.Adams.sphereAdamsData row.r _
          (presentation.comparison row.s row.t hx x) xr ∧
        RepresentsOnPage Classical.Adams.sphereAdamsData row.r _
          (presentation.comparison (row.s + row.r) (row.t + row.r - 1) hy y) yr ∧
        (Classical.Adams.sphereAdamsData.d row.r _ ≫
          eqToHom (congrArg (Classical.Adams.sphereAdamsData.Page row.r) h)) xr = yr

/-- cm5：固定 staircase 解码所得结论。全部坐标经同一实际球面 E₂
比较解释；unknown incoming 仅给累计边界，unknown outgoing 仅给提升。
9000 层仅记录到 E₁₀₀₀ 的提升，不能仅凭程序阈值追加非零 E∞ 存活。 -/
def StaircaseClaimStatement (presentation : Classical.Adams.LinE2Presentation) :
    Computation.LinCalculations.Staircase.Claim → Prop
  | .equation r s t indices target =>
      ∃ (hx : t ≤ 261) (hy : t + r - 1 ≤ 261)
        (x : E2At s t) (y : E2At (s + r) (t + r - 1)),
        HasCoordinates x indices ∧ HasCoordinates y target ∧
          HasDifferential sphereAdamsData r
            ((s : ℤ), (t : ℤ)) (((s + r : ℕ) : ℤ), ((t + r - 1 : ℕ) : ℤ))
            (presentation.comparison s t hx x)
            (presentation.comparison (s + r) (t + r - 1) hy y)
  | .reaches r s t indices =>
      ∃ (ht : t ≤ 261) (x : E2At s t), HasCoordinates x indices ∧
        ReachesPage sphereAdamsData r ((s : ℤ), (t : ℤ))
          (presentation.comparison s t ht x)
  | .boundaryBy r s t indices =>
      ∃ (ht : t ≤ 261) (x : E2At s t), HasCoordinates x indices ∧
        IsBoundaryBy sphereAdamsData r ((s : ℤ), (t : ℤ))
          (presentation.comparison s t ht x)

/-- cm5：固定球面 staircase 表中每条记录的正确性。
每条存在的记录均须成功解码，且所得微分、存活页数或累计边界陈述
经同一 `presentation` 解释后在实际球面谱序列中成立。 -/
structure SphereStaircaseSoundness (presentation : Classical.Adams.LinE2Presentation) : Prop where
  rows_sound : ∀ (shard offset : Nat) (row : Computation.LinCalculations.Raw.StaircaseRow),
    Computation.LinCalculations.StaircaseData.lookup shard offset = some row →
      ∃ claim, Computation.LinCalculations.Staircase.decode row = some claim ∧
        StaircaseClaimStatement presentation claim

/-- The actual sphere E₂ group in bidegree (2,128) consists of zero and the
nonzero class represented by `LinE2.dataH6Sq`; the specified comparison
identifies that class with `standardH6Square`. This is an E₂ statement;
permanent survival is the conclusion of the main proof. -/
structure H6SquareE2Facts (presentation : Classical.Adams.LinE2Presentation) : Prop where
  nonzero : presentation.comparison 2 128 (by decide) LinE2.dataH6Sq ≠ 0
  exhaustive : ∀ x : Classical.Adams.sphereAdamsData.Page 2 (2, 128),
    x = 0 ∨ x = presentation.comparison 2 128 (by decide) LinE2.dataH6Sq
  standard_class : presentation.comparison 2 128 (by decide) LinE2.dataH6Sq =
    Classical.Adams.standardH6Square

end ExternalHypotheses
end KIP126

/-! Interpretation of the fixed calculations on the actual Adams sequences.
The tmf comparison uses the literature source objects and classes; the
computational theorems refer to this same interpretation. -/
namespace KIP126.ExternalHypotheses
open Classical.Adams SpectralSequence

/-- A common interpretation of the Lin and tmf coordinates on the fixed
Adams sequences. The tmf classes agree with the specified BR21 source
classes under the literature comparison isomorphism. -/
structure ComputationInterpretation (literature : LiteratureHypotheses) where
  presentation : LinE2Presentation
  sphereAndCofiberCoordinates : Computation.SphereAndCofiber.E2Interpretation standardAdamsComparison
  tmfCoordinates : Tmf.E2Presentation standardFoundation.hf2 Def.standardTmfTarget
  tmfMultiplicative : StandardTmfMultiplicationComparison
    { target := Def.standardTmfTarget, coordinates := tmfCoordinates }
  tmf_v2Sixteen : tmfCoordinates.v2Sixteen =
    adamsInternalE2Induced standardFoundation.hf2.unit
      literature.sources.sourceComparisons.tmfComparison.detectorIso.inv (16, 112)
      literature.sources.br21Classes.v2Sixteen
  tmf_betaGFour : tmfCoordinates.betaGFour =
    adamsInternalE2Induced standardFoundation.hf2.unit
      literature.sources.sourceComparisons.tmfComparison.detectorIso.inv (19, 114)
      literature.sources.br21Classes.betaGFour

/-- The four distinguished sphere E₂ classes defined by their fixed Lin
coordinates. Their multiplicative and differential properties occur in
`ComputationTheorems`. -/
noncomputable def ComputationInterpretation.sphereClasses {literature : LiteratureHypotheses}
    (interpretation : ComputationInterpretation literature) :
    AdamsSynthetic.SphereAdamsClasses standardFoundation.hf2 where
  x_126_8_4 := interpretation.sphereAndCofiberCoordinates.sphere 8 134 (Computation.Near126.atom .x_126_8_4)
  x_126_8 := interpretation.sphereAndCofiberCoordinates.sphere 8 134 (Computation.Near126.atom .x_126_8)
  x_124_8 := interpretation.sphereAndCofiberCoordinates.sphere 8 132 (Computation.Near126.atom .x_124_8)
  x_109_12 := interpretation.sphereAndCofiberCoordinates.sphere 12 121 (Computation.Near126.atom .x_109_12)

/-- Basis, product, differential and staircase theorems for this interpretation
on the actual Adams sequences, with agreement between the sphere comparisons. -/
structure ComputationTheorems (literature : LiteratureHypotheses)
    (interpretation : ComputationInterpretation literature) where
  sphereBasis : SphereE2Basis interpretation.presentation
  sphereMultiplicative : SphereE2MultiplicationComparison interpretation.presentation
  sphereStaircase : SphereStaircaseSoundness interpretation.presentation
  sphereSquare : H6SquareE2Facts interpretation.presentation
  sphereTable_sound : ∀ (shard offset : Nat) (row : Computation.LinCalculations.DifferentialRow),
    Computation.LinCalculations.RawData.lookup shard offset = some row →
      DifferentialStatement interpretation.presentation row
  sphereAndCofiberTheorems : Computation.SphereAndCofiber.E2InterpretationCorrect interpretation.sphereAndCofiberCoordinates
    interpretation.sphereClasses literature.sources.tmfLabels
  sphere_comparison_eq : ∀ (s t : ℕ) (ht : t ≤ 261) (x : LinE2.E2At s t),
    interpretation.sphereAndCofiberCoordinates.sphere s t x = interpretation.presentation.comparison s t ht x

/-- The common coordinate interpretation and all required computation
theorems, dependent on the specified literature sources. -/
structure ComputationHypotheses (literature : LiteratureHypotheses) where
  interpretation : ComputationInterpretation literature
  theorems : ComputationTheorems literature interpretation

/-- The computation theorems for the fixed Adams/synthetic model and the
distinguished sphere and tmf classes used in Section 7. -/
noncomputable def ComputationHypotheses.sphereAndCofiber {literature : LiteratureHypotheses}
    (computation : ComputationHypotheses literature) : Computation.SphereAndCofiber.AdamsComputationTheorems
    standardAdamsComparison computation.interpretation.sphereClasses literature.sources.tmfLabels :=
  computation.theorems.sphereAndCofiberTheorems.toComputationTheorems

end KIP126.ExternalHypotheses
