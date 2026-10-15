module

public import KIP126.Def.AdamsSynthetic.Comparison.Data

@[expose] public section

namespace KIP126.AdamsSynthetic
open CategoryTheory CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology KIP126.Synthetic.Context
universe u v w
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} (D : AdamsComparisonData H Syn)

/-- Reexpress a positive-source shift as a negative-target shift, using only
the specified suspension comparisons. -/
def negativeLift {X Y : Syn} (k : ℕ)
    (f : (SyntheticCategory.biShift (0,(k : ℤ))).obj X ⟶ Y) :
    X ⟶ (SyntheticCategory.biShift (0,-(k : ℤ))).obj Y :=
  SyntheticCategory.biShift_zero.inv.app X ≫
    eqToHom (congrArg (fun p => (SyntheticCategory.biShift p).obj X)
      (show ((0 : ℤ),(0 : ℤ)) = (0,(k : ℤ))+(0,-(k : ℤ)) from by ext <;> simp)) ≫
    (SyntheticCategory.biShift_comp (0,(k : ℤ)) (0,-(k : ℤ))).inv.app X ≫
    (SyntheticCategory.biShift (0,-(k : ℤ))).map f

/-- The precise connecting arrow of the normalized triangle. Its target is
Σ Σ^(0,e(f))νX; the exponent equation accounts for the single suspension. -/
def normalizedConnecting (T : ClassicalCofiberTriangle D.hopfAndDetector)
    (he : (normalizedExponent H T.f : ℤ) + normalizedExponent H T.g +
      normalizedExponent H T.h = 1) :
    (SyntheticCategory.biShift (0,-(normalizedExponent H T.g : ℤ))).obj
      (D.nu.functor.obj (T.Z.obj D.hopfAndDetector)) ⟶
    ((SyntheticCategory.biShift (0,(normalizedExponent H T.f : ℤ))).obj
      (D.nu.functor.obj (T.X.obj D.hopfAndDetector)))⟦(1 : ℤ)⟧ :=
  let eg : ℤ := normalizedExponent H T.g
  let eh : ℤ := normalizedExponent H T.h
  let X := D.nu.functor.obj (T.X.obj D.hopfAndDetector)
  (SyntheticCategory.biShift (0,-eg)).map
      (negativeLift (normalizedExponent H T.h)
        (D.normalizedMap T.Z (.shift 1 T.X) T.h).map) ≫
    (SyntheticCategory.biShift (0,-eg)).map
      ((SyntheticCategory.biShift (0,-eh)).map (D.nu.suspensionIso (T.X.obj D.hopfAndDetector)).hom) ≫
    (SyntheticCategory.biShift (0,-eg)).map
      ((SyntheticCategory.biShift_comp (1,1) (0,-eh)).hom.app X) ≫
    (SyntheticCategory.biShift_comp ((1,1)+(0,-eh)) (0,-eg)).hom.app X ≫
    eqToHom (congrArg (fun p => (SyntheticCategory.biShift p).obj X)
      (show ((1,1)+(0,-eh))+(0,-eg) = (0,(normalizedExponent H T.f : ℤ))+(1,0) from by
        dsimp [eg, eh]; ext <;> simp only []; omega)) ≫
    (SyntheticCategory.biShift_comp (0,(normalizedExponent H T.f : ℤ)) (1,0)).inv.app X ≫
    (SyntheticCategory.biShift_compat (Syn := Syn) 1).hom.app _

/-- All three arrows are derived from the specified normalized maps.
This definition does not assert that the resulting triangle is distinguished. -/
def normalizedTriangle (T : ClassicalCofiberTriangle D.hopfAndDetector)
    (he : (normalizedExponent H T.f : ℤ) + normalizedExponent H T.g +
      normalizedExponent H T.h = 1) : Triangle Syn :=
  Triangle.mk (D.normalizedMap T.X T.Y T.f).map
    (negativeLift (normalizedExponent H T.g) (D.normalizedMap T.Y T.Z T.g).map)
    (normalizedConnecting D T he)
end
end KIP126.AdamsSynthetic
