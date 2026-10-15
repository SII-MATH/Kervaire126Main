module

public import KIP126.Computation.Tmf.Model.Data
public import KIP126.Computation.Tmf.CsvE2.Multiplication.Data
public import KIP126.Def.ClassicalAdams.Tmf.Multiplication.SecondCycles.Data
public import KIP126.Def.ClassicalAdams.Suspension.Data

@[expose] public section

/-!
# Multiplicative conditions on the fixed tmf coordinate comparison

The underlying comparison remains the given linear equivalence. These
conditions bind its coordinate product and unit to the same algebra object
and its actual Adams tower. They assert neither a realization of tmf nor
compatibility with later pages or convergence.
-/

namespace KIP126.Classical.Adams.Tmf

open CategoryTheory MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {H : Mod2EilenbergMacLane (C := C)} {T : Mon C}

/-- The coordinate unit is the class of the actual algebra-object unit. -/
def E2Presentation.RespectsUnit (P : E2Presentation H T) : Prop :=
  P.comparison 0 0 (by decide) CsvE2.one =
    Suspension.classOfSecondCycle H T.X 0 0 (unitSecondCycle H T)

variable [BraidedCategory C] (R : Mod2RingStructure H)
  [∀ A : C, (tensorRight A).CommShift ℤ]
  [∀ A : C, (tensorRight A).IsTriangulated]
  [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]
  [(mod2UnitNatTrans H).CommShift ℤ] [MonoidalPreadditive C]

/-- For every actual pair of second-cycle representatives of coordinate
classes, the actual layer product represents their fixed quotient-ring
product. The output bound also bounds both inputs. No arbitrary page product
or selected family of representatives is an input. -/
def E2Presentation.RespectsMultiplication (P : E2Presentation H T) : Prop :=
  ∀ (s t s' t' : ℕ) (h : t + t' ≤ 261)
    (x : CsvE2.E2At s t) (y : CsvE2.E2At s' t')
    (a : adamsCycles H.unit T.X 2 (by decide) s t)
    (b : adamsCycles H.unit T.X 2 (by decide) s' t'),
    Suspension.classOfSecondCycle H T.X s t a =
        P.comparison s t (by omega) x →
    Suspension.classOfSecondCycle H T.X s' t' b =
        P.comparison s' t' (by omega) y →
    Suspension.classOfSecondCycle H T.X
        ((s + s' : ℕ) : ℤ) ((t + t' : ℕ) : ℤ)
        (secondCycleMultiplication H T R s t s' t' a b) =
      P.comparison (s + s') (t + t') h (CsvE2.mul x y)

end KIP126.Classical.Adams.Tmf
