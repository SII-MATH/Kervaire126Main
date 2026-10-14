module

public import KIP126.Def.AdamsSynthetic

/-! Pstrągowski Lemma 4.23 and BHS Lemma 9.15 on the same supplied
coefficient object, ν functor and Adams tower. Fixed migration source:
bbac1fc05843bdf2d56057e6114a38839e939378,
`Def/StableHomotopy/Implementation/Data.lean:474–559`.
These general source contracts are distinct from selected normalized lifts
and from realization of a particular compatible ν-cofiber triangle. -/

@[expose] section
namespace KIP126.Literature
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.AdamsSynthetic
open KIP126.Kervaire.Route
universe u v w
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w,v} Syn]
  [HasFunctorialCofiber (C := Syn)] (D : Model C Syn)

/-- The first two arrows are precisely the ν images of this triangle's
arrows; only the synthetic connecting map is existential. -/
public def NuImageIsCofiber (T : Triangle C) : Prop :=
  ∃ δ : D.nu.functor.obj T.obj₃ ⟶ (D.nu.functor.obj T.obj₁)⟦(1 : ℤ)⟧,
    Triangle.mk (D.nu.functor.map T.mor₁) (D.nu.functor.map T.mor₂) δ ∈ distTriang Syn

/-- Pstrągowski's full bidirectional criterion, without added finiteness,
connectivity or completeness assumptions. -/
public def NuCofiberCriterion : Prop :=
  ∀ T : Triangle C, T ∈ distTriang C →
    (NuImageIsCofiber D T ↔ HomologyShortExact D.coefficients T)

/-- The forward preservation input is obtained from the same full source
criterion, with exactly the shared short-exactness predicate. -/
public def NuCofiberCriterion.toNuExactTriangleInput (h : NuCofiberCriterion D) :
    NuExactTriangleInput D.coefficients D.nu where
  preserves T hT hH := (h T hT).mpr hH

/-- An actual λᵏ factorization of νf in the negative-target convention. -/
public structure SyntheticFullLift {X Y : C} (f : X ⟶ Y) (k : ℕ) where
  map : D.nu.functor.obj X ⟶
    (SyntheticCategory.biShift (0,-(k : ℤ))).obj (D.nu.functor.obj Y)
  factorization : map ≫ lambdaPow k (D.nu.functor.obj Y) = D.nu.functor.map f

/-- BHS full lift for every pair of classical objects and every filtration
bound. The premise is factorization through D's actual target tower. -/
public def SyntheticLiftComparison : Prop :=
  ∀ {X Y : C} (f : X ⟶ Y) (k : ℕ),
    MapFiltrationAtLeast D.classicalTower f k → Nonempty (SyntheticFullLift D f k)

/-- One triangle lift binds factorization and distinguishedness to the same
connecting arrow, using the given ν suspension comparison. -/
public structure SyntheticTriangleLift (T : Triangle C) where
  connecting : D.nu.functor.obj T.obj₃ ⟶
    (SyntheticCategory.biShift (0,-1)).obj (D.nu.functor.obj (T.obj₁⟦(1 : ℤ)⟧))
  factorization : connecting ≫ SyntheticCategory.lam.app
    (D.nu.functor.obj (T.obj₁⟦(1 : ℤ)⟧)) = D.nu.functor.map T.mor₃
  distinguished : Triangle.mk (D.nu.functor.map T.mor₁) (D.nu.functor.map T.mor₂)
    (connecting ≫ (D.nu.boundaryLandingIso T.obj₁).hom) ∈ distTriang Syn

/-- Actual λ torsion in a Hom group, not vanishing of one page coordinate. -/
public def LambdaTorsion {X Y : Syn} (f : X ⟶ Y) : Prop :=
  ∃ n : ℕ, lambdaPow n X ≫ f = 0

/-- Reduce a full lift to one λ division. This operation does not assert
that the result is a distinguished triangle's connecting arrow. -/
public def SyntheticFullLift.normalizedMap {X Y : C} {f : X ⟶ Y} {k : ℕ}
    (L : SyntheticFullLift D f k) (hk : 1 ≤ k) :
    D.nu.functor.obj X ⟶ (SyntheticCategory.biShift (0,-1)).obj (D.nu.functor.obj Y) := by
  have hdegree : ((0 : ℤ), -(k : ℤ)) =
      ((0 : ℤ), -1) + ((0 : ℤ), -((k-1 : ℕ) : ℤ)) := by
    ext <;> simp
    omega
  exact L.map ≫ eqToHom (congrArg
    (fun p : ℤ × ℤ => (SyntheticCategory.biShift p).obj (D.nu.functor.obj Y)) hdegree) ≫
    (SyntheticCategory.biShift_comp (0,-1) (0,-((k-1 : ℕ) : ℤ))).inv.app
      (D.nu.functor.obj Y) ≫
    lambdaPow (k-1) ((SyntheticCategory.biShift (0,-1)).obj (D.nu.functor.obj Y))

/-- Arbitrary full lifts agree with the selected triangle component only
modulo λ torsion. No strict equality or universal distinguishedness is added. -/
public def SyntheticTriangleLift.FullLiftComparison {T : Triangle C}
    (L : SyntheticTriangleLift D T) : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k) (F : SyntheticFullLift D T.mor₃ k),
    LambdaTorsion (L.connecting - F.normalizedMap D hk)

/-- BHS triangle lifting, retaining positive filtration and all short-exact
conditions. All objects range over the full classical category. -/
public def SyntheticTriangleLiftComparison : Prop :=
  ∀ T : Triangle C, T ∈ distTriang C →
    MapFiltrationAtLeast D.classicalTower T.mor₃ 1 → HomologyShortExact D.coefficients T →
      ∃ L : SyntheticTriangleLift D T, L.FullLiftComparison D

/-- The three source leaves use the same background. Their delivery does
not identify arbitrary previously selected normalized maps with these lifts. -/
private structure LiftSourceResults : Prop where
  nu_cofiber : NuCofiberCriterion D
  lift : SyntheticLiftComparison D
  triangle_lift : SyntheticTriangleLiftComparison D

end
end KIP126.Literature
