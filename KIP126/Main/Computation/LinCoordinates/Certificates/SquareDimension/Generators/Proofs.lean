module

public import KIP126.Computation.WellFormedness.LinCoordinates.GeneratorDegrees

public import KIP126.Computation.LinCoordinates.Model.Classes.Data
public import Mathlib.Data.Finsupp.Order
public import Mathlib.Data.ZMod.Basic

@[expose] public section

/-! The degree-(2,128) component is spanned by the specified square.
This is proved from the actual generator degrees, without assuming the
archived additive catalogue is a basis or a reduction algorithm is complete. -/

namespace KIP126.LinE2

open KIP126.Algebra

/-- The small-filtration part of the actual generator table is exhaustive.
The finite certificate is checked by the Lean kernel. -/
theorem generatorDegree_low_filtration (i : Generator) :
    0 < (generatorDegree i).1 ∧
      ((generatorDegree i).1 ≤ 2 → (generatorDegree i).2 ≤ 128 →
        i.val ∈ [0, 1, 2, 3, 7, 18, 69, 324]) := by
  rw [generatorDegree_eq_row]
  have h : ∀ i : Fin RawData.generatorCount,
      0 < (RawData.generatorRow i.val).2.1 ∧
        ((RawData.generatorRow i.val).2.1 ≤ 2 →
          (RawData.generatorRow i.val).2.2 ≤ 128 →
            i.val ∈ [0, 1, 2, 3, 7, 18, 69, 324]) := by
    decide +kernel
  exact h i

end KIP126.LinE2
