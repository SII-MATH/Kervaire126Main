module

public import KIP126.Literature.Applicability
import all KIP126.Literature.Applicability
public import KIP126.Literature.Classical
import all KIP126.Literature.Classical

/-! BHS consumer language on the one supplied system. Adapted from
Def/Kervaire/Route/SourceLanguage.lean and Interface/Challenge/Literature/Source.lean,
bbac1fc05843 (Apache-2.0). Finite lifts allow zero and boundaries; untruncated
source results retain nilpotent completeness and strong convergence.
Transport from complete source objects to the selected route is a separate
comparison obligation, not an assertion that the ordinary sphere is complete. -/

@[expose] section
namespace KIP126.Literature
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.AdamsSynthetic
open KIP126.Classical.Adams KIP126.Core.SpectralSequence KIP126.Kervaire.Route
universe u v w
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w,v} Syn]
  [HasFunctorialCofiber (C := Syn)] (D : Model C Syn)

public abbrev nuZero (X : ClassicalObject) :=
  (SyntheticCategory.biShift (0,0)).obj (D.nu.functor.obj (X.obj D.auxiliary))

public def firstLabel (X : ClassicalObject) (s t : ℤ)
    (x : (D.classical.obj (X.obj D.auxiliary)).Page 2 (s,t)) :
    BiHom (t-s) t (XModLambdaN (nuZero D X) 1) := by
  simpa only [add_zero] using (D.firstQuotient X 0 s t).symm x

/-- A single common infinite-cycle representative; no nonzero assertion. -/
public def ClassicalPermanentCycle (X : ClassicalObject) (p : ℤ × ℤ)
    (x : (D.classical.obj (X.obj D.auxiliary)).Page 2 p) : Prop :=
  let E := D.classical.obj (X.obj D.auxiliary)
  ∃ z : (Subobject.underlying.obj ((E.ssData p).Z ⊤) : ModuleCat ℤ),
    (Subobject.ofLE _ _ ((E.ssData p).Z_anti le_top) ≫
      (E.ssData p).pageπ (↑(2-E.r₀).toNat : WithTop ℕ)) z = x

public def bocksteinArrow (X : ClassicalObject) (q : ℕ) (hq : 0 < q) :
    XModLambdaN (nuZero D X) q ⟶
      (SyntheticCategory.biShift (1,-(q : ℤ))).obj (XModLambdaN (nuZero D X) 1) :=
  ((D.quotients.tower (nuZero D X)).triangle hq (Nat.lt_succ_self q)).delta ≫
    (SyntheticCategory.biShift_compat (Syn := Syn) 1).inv.app _ ≫
    (SyntheticCategory.biShift_comp (0,-(q : ℤ)) (1,0)).hom.app _ ≫
    eqToHom (by congr 1 <;> simp)

public def bocksteinLabel (X : ClassicalObject) (q : ℕ) (hq : 0 < q) (s t : ℤ)
    (a : BiHom (t-s) t (XModLambdaN (nuZero D X) q)) :
    (D.classical.obj (X.obj D.auxiliary)).Page 2 (s+q+1,t+q) := by
  let b : BiHom (t-s-1) (t+q) (XModLambdaN (nuZero D X) 1) :=
    (susp_invariance (t-s-1) (t+q) 1 (-(q : ℤ)) _).symm
      (homotopyRegrade (by omega) (by omega) (a ≫ bocksteinArrow D X q hq))
  exact D.firstQuotient X 0 (s+q+1) (t+q)
    (homotopyRegrade (by omega) (by omega) b)

/-- BHS A.1(1): reaching E_(q+1), with zero permitted, is exactly the
existence of a lift through this actual λ^q quotient and actual restriction. -/
public def FiniteLiftCriterion : Prop :=
  ∀ (X : ClassicalObject) (q : ℕ) (hq : 0 < q) (s t : ℤ)
    (x : (D.classical.obj (X.obj D.auxiliary)).Page 2 (s,t)),
    (ReachesPage (D.classical.obj (X.obj D.auxiliary)) (q+1) (s,t) x ↔
      ∃ a : BiHom (t-s) t (XModLambdaN (nuZero D X) q),
        a ≫ (D.quotients.tower (nuZero D X)).rho 1 q hq = firstLabel D X s t x)

public def BocksteinDifferential : Prop :=
  ∀ (X : ClassicalObject) (q : ℕ) (hq : 0 < q) (s t : ℤ)
    (x : (D.classical.obj (X.obj D.auxiliary)).Page 2 (s,t)),
    ReachesPage (D.classical.obj (X.obj D.auxiliary)) (q+1) (s,t) x →
    ∃ a : BiHom (t-s) t (XModLambdaN (nuZero D X) q),
      a ≫ (D.quotients.tower (nuZero D X)).rho 1 q hq = firstLabel D X s t x ∧
      HasDifferential (D.classical.obj (X.obj D.auxiliary))
        (q+1) (s,t) (s+q+1,t+q) x (bocksteinLabel D X q hq s t a)

public def PermanentLiftAt (X : ClassicalObject) : Prop :=
  ∀ (s t : ℤ) (x : (D.classical.obj (X.obj D.auxiliary)).Page 2 (s,t)),
    (ClassicalPermanentCycle D X (s,t) x ↔
      ∃ a : BiHom (t-s) t (nuZero D X), quotientClass 1 a = firstLabel D X s t x)

public def LambdaDivisible (X : ClassicalObject) (m w s : ℤ) (h : w-m ≤ s)
    (a : BiHom m w (D.nu.functor.obj (X.obj D.auxiliary))) : Prop :=
  ∃ b : BiHom m (m+s) (D.nu.functor.obj (X.obj D.auxiliary)),
    homotopyRegrade rfl (by rw [Int.toNat_of_nonneg (by omega)]; omega)
      (lambdaMultiply (m+s-w).toNat b) = a

public def FiltrationLambdaAt (X : ClassicalObject) : Prop :=
  ∀ (m w s : ℤ) (h : w-m ≤ s)
    (a : BiHom m w (D.nu.functor.obj (X.obj D.auxiliary))),
    FiltrationAtLeast D.syntheticTower s a ↔ LambdaDivisible D X m w s h a

/-- Actual labeled differential equivalence, with the λ exponent on the
target increased by r-1 so both sides have exactly the same weight. -/
public def DifferentialRigidity : Prop :=
  ∀ (X : ClassicalObject) (a s t : ℤ) (r k : ℕ), 2 ≤ r →
    ∀ (x : (D.classical.obj (X.obj D.auxiliary)).Page 2 (s,t))
      (y : (D.classical.obj (X.obj D.auxiliary)).Page 2 (s+r,t+r-1)),
    (HasDifferential (D.classical.obj (X.obj D.auxiliary)) r
        (s,t) (s+r,t+r-1) x y ↔
      SyntheticHasDifferential
        (D.family.obj ((SyntheticCategory.biShift (0,a)).obj
          (D.nu.functor.obj (X.obj D.auxiliary)))) r
        (s,t,t+a-k) (s+r,t+r-1,(t+r-1)+a-(k+(r-1) : ℕ))
        (D.comparison.nuE2 X a s t k x)
        (D.comparison.nuE2 X a (s+r) (t+r-1) (k+(r-1)) y))

/-- λ-localization kernel on the existing object closure. A producer must
transport the full source category's compactness argument to this exact
realization; compactness of the hypercomplete sphere is not assumed. -/
public def RealizationKernel : Prop :=
  ∀ (X : SyntheticObject) (m w : ℤ) (a : BiHom m w (X.obj D.nu D.auxiliary)),
    (D.recovery.realization.map a = 0 ↔ ∃ k : ℕ, lambdaMultiply k a = 0)

private structure BHSResults : Prop where
  finite_lift : FiniteLiftCriterion D
  bockstein : BocksteinDifferential D
  differentials : DifferentialRigidity D
  permanent_lift : ∀ (X : ClassicalObject) (products : HasProductsOfShape ℕ C),
    BHSObjectApplicability D products (X.obj D.auxiliary) → PermanentLiftAt D X
  filtration_lambda : ∀ (X : ClassicalObject) (products : HasProductsOfShape ℕ C),
    BHSObjectApplicability D products (X.obj D.auxiliary) → FiltrationLambdaAt D X

/-- These selected-object laws are explicit source-to-model comparison
obligations, distinct from the conditional source theorem above. The source
completion and comparison construction is deferred with the producer. -/
private structure BHSSelectedComparisons : Prop where
  permanent_lift : ∀ X : ClassicalObject, PermanentLiftAt D X
  filtration_lambda : ∀ X : ClassicalObject, FiltrationLambdaAt D X
  realization_kernel : RealizationKernel D

/-- Canonical realization on νX with the zero shift removed. -/
public def realizeNuZero (R : RealizationCoordinates D) (X : ClassicalObject)
    {m w : ℤ} (a : BiHom m w (nuZero D X)) : HomotopyGroup m (X.obj D.auxiliary) :=
  (R.sphere m w).hom ≫ D.recovery.realization.map a ≫
    D.recovery.realization.map (SyntheticCategory.biShift_zero.hom.app _) ≫
    D.recovery.nuRealizationIso.hom.app _

/-- BHS realization results with every source applicability condition. The
boundary lift is existential: it never asserts a formula for an arbitrary lift. -/
private structure BHSRealizationResults (R : RealizationCoordinates D) : Prop where
  lifetime : ∀ (X : ClassicalObject) (products : HasProductsOfShape ℕ C),
    BHSObjectApplicability D products (X.obj D.auxiliary) →
    ∀ (s t : ℤ) (r : ℕ), 1 ≤ r →
    ∀ (x : (D.classical.obj (X.obj D.auxiliary)).Page 2 (s,t))
      (a : BiHom (t-s) t (nuZero D X)),
    ClassicalPermanentCycle D X (s,t) x →
    SurvivesTo (D.classical.obj (X.obj D.auxiliary)) (r+1) (s,t) x →
    quotientClass 1 a = firstLabel D X s t x → lambdaMultiply (r-1) a ≠ 0
  detection : ∀ (X : ClassicalObject) (products : HasProductsOfShape ℕ C),
    BHSObjectApplicability D products (X.obj D.auxiliary) →
    ∀ (s t : ℤ) (x : (D.classical.obj (X.obj D.auxiliary)).Page 2 (s,t))
      (a : BiHom (t-s) t (nuZero D X)),
    NonzeroSurvival (D.classical.obj (X.obj D.auxiliary)) (s,t) x →
    quotientClass 1 a = firstLabel D X s t x →
    ClassicalDetects (D.classicalConvergence X) (s,t) x (realizeNuZero D R X a)
  prescribed_lift : ∀ (X : ClassicalObject) (products : HasProductsOfShape ℕ C),
    BHSObjectApplicability D products (X.obj D.auxiliary) →
    ∀ (s t : ℤ) (x : (D.classical.obj (X.obj D.auxiliary)).Page 2 (s,t))
      (a : HomotopyGroup (t-s) (X.obj D.auxiliary)),
    NonzeroSurvival (D.classical.obj (X.obj D.auxiliary)) (s,t) x →
    ClassicalDetects (D.classicalConvergence X) (s,t) x a →
    ∃ b : BiHom (t-s) t (nuZero D X), quotientClass 1 b = firstLabel D X s t x ∧
      realizeNuZero D R X b = a
  boundary_lift : ∀ (X : ClassicalObject) (products : HasProductsOfShape ℕ C),
    BHSObjectApplicability D products (X.obj D.auxiliary) →
    ∀ (s t : ℤ) (r : ℕ), 2 ≤ r →
    ∀ y : (D.classical.obj (X.obj D.auxiliary)).Page 2 (s,t),
    ClassicalPermanentCycle D X (s,t) y →
    HitOnPage (D.classical.obj (X.obj D.auxiliary)) r (s,t) y →
    ∃ a : BiHom (t-s) t (nuZero D X), quotientClass 1 a = firstLabel D X s t y ∧
      lambdaMultiply (r-1) a = 0

end
end KIP126.Literature
