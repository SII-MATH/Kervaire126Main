module

public import KIP126.AdamsSynthetic.Comparisons
public import KIP126.AdamsSynthetic.Tower

@[expose] section
namespace KIP126.AdamsSynthetic
open CategoryTheory KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.Classical.Adams
universe u v w
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w,v} Syn]
  {H : C} {unit : SphereSpectrum ⟶ H} {A : ClassicalAdamsFamily C}

/-- Actual factorization through the target tower of this system. -/
public def MapFiltrationAtLeast (P : ClassicalTowerPresentation unit A)
    {X Y : C} (f : X ⟶ Y) (k : ℕ) : Prop :=
  ∃ lift : X ⟶ (P.tower Y).stageAt k,
    lift ≫ (P.tower Y).projection k = f

/-- The paper's normalization exponent, determined by the same target tower. -/
public def normalizedExponent (P : ClassicalTowerPresentation unit A)
    {X Y : C} (f : X ⟶ Y) : ℕ := by
  classical
  exact if MapFiltrationAtLeast P f 1 then 1 else 0

public theorem normalizedExponent_le_one (P : ClassicalTowerPresentation unit A)
    {X Y : C} (f : X ⟶ Y) : normalizedExponent P f ≤ 1 := by
  classical
  unfold normalizedExponent
  split <;> decide

/-- Positive-target form of the actual λ power. -/
public def lambdaToPositivePow (k : ℕ) (X : Syn) :
    X ⟶ (SyntheticCategory.biShift (0, (k : ℤ))).obj X := by
  have h : ((0 : ℤ), (k : ℤ)) + ((0 : ℤ), -(k : ℤ)) = (0, 0) := by
    ext <;> simp
  exact SyntheticCategory.biShift_zero.inv.app X ≫
    eqToHom (congrArg (fun p => (SyntheticCategory.biShift p).obj X) h.symm) ≫
    (SyntheticCategory.biShift_comp (0, (k : ℤ)) (0, -(k : ℤ))).inv.app X ≫
    lambdaPow k ((SyntheticCategory.biShift (0, (k : ℤ))).obj X)

/-- A normalized lift of this very classical map, with its factorization.
Its existence remains an input, never an axiom or an automatically chosen map. -/
public structure NormalizedSyntheticMap (P : ClassicalTowerPresentation unit A)
    (N : NuFunctorData C Syn) {X Y : C} (f : X ⟶ Y) where
  map : (SyntheticCategory.biShift (0, (normalizedExponent P f : ℤ))).obj
    (N.functor.obj X) ⟶ N.functor.obj Y
  factorization : lambdaToPositivePow (normalizedExponent P f) (N.functor.obj X) ≫
    map = N.functor.map f

end
end KIP126.AdamsSynthetic
