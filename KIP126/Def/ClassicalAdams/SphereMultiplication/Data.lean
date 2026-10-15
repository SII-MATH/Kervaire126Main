module

public import KIP126.Def.ClassicalAdams.TowerSmash.Pairing.Layer.Multiplication.Homotopy.Data
public import KIP126.Def.ClassicalAdams.TowerDifferential.Value.Data

@[expose] public section

/-!
The existing actual sphere-layer product in the natural-number bidegrees
used by finite coordinate presentations. Only degree transports are added;
the tower pairing, HF₂ multiplication, layer maps and sphere comparison are
the ones in `adamsSphereE1Product`. No quotient product or cycle-closure
assertion is supplied here.
-/

namespace KIP126.Classical.Adams.Sphere.Multiplication

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  (H : Mod2EilenbergMacLane (C := C))

/-- The actual identity of the sphere, projected from tower stage zero into
second cycles. The source uses the specified zero-shift comparison. -/
def unitSecondCycle : adamsCycles H.unit (SphereSpectrum : C) 2 (by decide) 0 0 :=
  adamsJToCycles H.unit SphereSpectrum 2 (by decide) 0 0
    ((shiftFunctorZero C ℤ).hom.app (𝟙_ C))

variable [BraidedCategory C] [MonoidalPreadditive C]
  (R : Mod2RingStructure H)
  [∀ Y : C, (tensorRight Y).CommShift ℤ]
  [∀ Y : C, (tensorRight Y).IsTriangulated]

/-- The prescribed first-layer product, with only its target bidegree
rewritten from sums of integer casts to casts of natural-number sums. -/
def firstProduct (s t s' t' : ℕ) :
    adamsE1 H.unit (SphereSpectrum : C) s t →ₗ[ℤ]
      adamsE1 H.unit (SphereSpectrum : C) s' t' →ₗ[ℤ]
        adamsE1 H.unit (SphereSpectrum : C)
          ((s + s' : ℕ) : ℤ) ((t + t' : ℕ) : ℤ) := by
  rw [Nat.cast_add, Nat.cast_add]
  exact adamsSphereE1Product H R s s' (t : ℤ) (t' : ℤ)

end
end KIP126.Classical.Adams.Sphere.Multiplication
