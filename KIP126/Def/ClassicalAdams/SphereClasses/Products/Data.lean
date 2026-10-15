module

public import KIP126.Def.ClassicalAdams.SphereClasses.Product.Data
public import KIP126.Def.ClassicalAdams.SphereClasses.Hi.Internal.Data

@[expose] public section


/-! Specified products of the standard Milnor classes on the actual internal E₂.
The product is the existing cobar cup product followed by its canonical
comparison with the same Adams tower. No new page classes or products are chosen. -/

namespace KIP126.Classical.Adams.Sphere.Internal

noncomputable section
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  (H : Mod2EilenbergMacLane (C := C)) (M : MilnorCooperations H)

/-- The actual class `hᵢ hⱼ`, obtained from the specified cobar product. -/
def hiProduct (i j : ℕ) :
    (adamsTowerInternalSpectralSequence H.unit SphereSpectrum).Page 2
      (2, ((2 ^ i + 2 ^ j : ℕ) : ℤ)) :=
  MilnorCohomology.comparison H M 2 (2 ^ i + 2 ^ j)
    (MilnorCohomology.cup H M (MilnorCohomology.hi H M i) (MilnorCohomology.hi H M j))

/-- The actual one-line differential target `h₀ hᵢ²`, with no asserted nonvanishing. -/
def h0HiSquare (i : ℕ) :
    (adamsTowerInternalSpectralSequence H.unit SphereSpectrum).Page 2
      (3, ((1 + 2 ^ (i + 1) : ℕ) : ℤ)) :=
  MilnorCohomology.comparison H M 3 (1 + 2 ^ (i + 1))
    (MilnorCohomology.cup H M (MilnorCohomology.hi H M 0)
      (MilnorCohomology.hiSquare H M i))

/-- Internal degree of a word of standard `hᵢ` classes. -/
def hWordDegree : List ℕ → ℕ
  | [] => 0
  | i :: is => 2 ^ i + hWordDegree is

/-- Product of a nonempty word of standard classes.

`hProduct H M i is` represents the code `i :: is`; for example,
`hProduct H M 0 [3, 3]` is the code `[0, 3, 3]`. -/
def hProduct (i : ℕ) : (is : List ℕ) →
    (adamsTowerInternalSpectralSequence H.unit SphereSpectrum).Page 2
      (1 + is.length, ((2 ^ i + hWordDegree is : ℕ) : ℤ))
  | [] => hi H M i
  | j :: js =>
      reindex H
        (by simp [Nat.add_comm, Nat.add_left_comm])
        (by simp [hWordDegree])
        (product H M (hi H M i) (hProduct j js))

/-- A nonempty list represents a right-associated product of standard classes.

Repeated indices are repeated factors: `[0, 3, 3]` represents `h₀ h₃ h₃`.
The nonempty condition is discharged automatically for concrete nonempty lists. -/
def hMonomial (indices : List ℕ) (hne : indices ≠ [] := by decide) :
    (adamsTowerInternalSpectralSequence H.unit SphereSpectrum).Page 2
      (indices.length, ((hWordDegree indices : ℕ) : ℤ)) :=
  match indices with
  | [] => False.elim (hne rfl)
  | i :: is =>
      reindex H (by simp [Nat.add_comm]) rfl (hProduct H M i is)

end
end KIP126.Classical.Adams.Sphere.Internal
