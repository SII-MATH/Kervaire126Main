module

public import KIP126.Def.SpectralSequence.PageLevel.Data
public import KIP126.Def.ClassicalAdams.Grading.Data
public import KIP126.Def.Algebra.Coefficients.Data
public import Mathlib.Algebra.Homology.SpectralSequence.Basic

@[expose] public section

/-! Classical Adams page grading, differential shape, and Mathlib sequence type. -/
namespace KIP126.Classical.Adams

open CategoryTheory
open KIP126.Algebra
open KIP126.SpectralSequence

/-- AIM 约定下有效 Adams 页的微分次数。 -/
def classicalAdamsShift (r : AdamsPage) : Bidegree :=
  (r.toInt, r.toInt - 1)

/-- 有效 Adams 页微分的目标双次数。 -/
def classicalAdamsTarget (r : AdamsPage) (b : Bidegree) : Bidegree :=
  b + classicalAdamsShift r

/-- 把有效 Adams 页送入 Mathlib 所需的整数页形状。 -/
def classicalAdamsShapeAt (r : AdamsPage) : ComplexShape Bidegree :=
  classicalAdamsShape r.toInt

def classicalAdamsPageLevel : PageLevelConvention where
  firstPage := 2
  admissibleFrom := 2
  page := fun r => r
  cycleLevel := fun r => r - 1
  quotientExponent := fun r => r - 1
  page_first := by norm_num
  page_succ := by intro r; norm_num
  cycle_succ := by intro r; omega
  quotient_succ := by intro r; omega
  cycleLevel_eq_quotientExponent := by intro r; rfl

@[simp] theorem classicalAdamsShift_two :
    classicalAdamsShift AdamsPage.two = (2, 1) := by
  norm_num [classicalAdamsShift, AdamsPage.two, AdamsPage.toInt]

@[simp] theorem classicalAdamsTarget_two (b : Bidegree) :
    classicalAdamsTarget AdamsPage.two b = (b.1 + 2, b.2 + 1) := by
  apply Prod.ext <;>
    simp [classicalAdamsTarget, classicalAdamsShift, AdamsPage.two, AdamsPage.toInt]

@[simp] theorem classicalAdamsShape_two_rel (b : Bidegree) :
    (classicalAdamsShape 2).Rel b (classicalAdamsTarget AdamsPage.two b) := by
  simp [classicalAdamsShape, classicalAdamsTarget, classicalAdamsShift,
    AdamsPage.two, AdamsPage.toInt]

/-- A mod-2 classical Adams spectral sequence, with the differential shape
fixed to `(r,r-1)` and displayed from `E₂`. -/
abbrev ClassicalAdamsSpectralSequence :=
  CategoryTheory.SpectralSequence F2ModuleCat classicalAdamsShape 2

/-! ### Stable-homotopy structures and Adams pages -/

end KIP126.Classical.Adams
