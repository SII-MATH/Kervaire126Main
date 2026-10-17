module

public import KIP126.Literature.BHS
import all KIP126.Literature.BHS

/-! Source-to-selected-model realization comparisons. Adapted from
`Def/Kervaire/Route/SourceLanguage.lean`'s `BHSRealizationComparison`,
bbac1fc05843bdf2d56057e6114a38839e939378.

The source BHS statements retain their actual completion hypotheses in
`BHSRealizationResults`. These four comparisons specify their transported
consumer form on the selected object closure. They are explicit model
comparison inputs, not unconditional literature theorems asserting that
these selected objects are themselves complete.

A future producer must construct the completed objects and their actual
maps q, prove the source applicability, preserve survival and hitting under
the E₂ maps of q, commute the first quotient with νq and realization with
q, compare detection, and reflect the prescribed homotopy class or the
specified finite λ exponent. This compressed consumer contract does not
construct those data or discharge any of those proof responsibilities. -/

@[expose] section
namespace KIP126.Literature
open CategoryTheory KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
universe u v w
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w,v} Syn]
  [HasFunctorialCofiber (C := Syn)] (D : Model C Syn)

section AbsorbedSourceTransport
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
open CategoryTheory.Limits

/-! Actual source-transport calculations adapted from a484b981,
Main/Literature/SourceComparisons/BHS and AdamsSynthetic/Theorems.
These private lemmas prove operations on the existing model and do not
assert completion/applicability or the selected public conclusions. -/

/-- The same actual lambda action is natural under postcomposition. -/
private theorem bhsLambdaMultiplyPostcompose {X Y : Syn} (g : X ⟶ Y)
    {m w : ℤ} (a : BiHom m w X) (k : ℕ) :
    lambdaMultiply k (a ≫ g) = lambdaMultiply k a ≫ g := by
  dsimp only [lambdaMultiply]
  simp (config := { congrConsts := false }) only [Category.assoc]

private theorem bhsHomotopyRegradePostcompose {X Y : Syn} (g : X ⟶ Y)
    {m m' w w' : ℤ} (hm : m=m') (hw : w=w') (a : BiHom m w X) :
    homotopyRegrade hm hw (a ≫ g) = homotopyRegrade hm hw a ≫ g := by
  cases hm
  cases hw
  rfl

/-- The realization square is forced by the existing nu recovery and zero
shift naturality, for the same actual classical map. -/
private theorem bhsRealizeNuZeroNatural (R : RealizationCoordinates D)
    (X Y : ClassicalObject) (f : X.obj D.auxiliary ⟶ Y.obj D.auxiliary)
    {m w : ℤ} (a : BiHom m w (nuZero D X)) :
    realizeNuZero D R Y
        (a ≫ (SyntheticCategory.biShift (0,0)).map (D.nu.functor.map f)) =
      realizeNuZero D R X a ≫ f := by
  have hz := SyntheticCategory.biShift_zero.hom.naturality (D.nu.functor.map f)
  have hr := D.recovery.nuRealizationIso.hom.naturality f
  dsimp only [Functor.comp_map, Functor.id_map] at hz hr
  have hmap := congrArg
    (fun z => D.recovery.realization.map z ≫
      D.recovery.nuRealizationIso.hom.app (Y.obj D.auxiliary)) hz
  simp (config := { congrConsts := false }) only [Functor.map_comp, Category.assoc] at hmap
  rw [hr] at hmap
  unfold realizeNuZero
  rw [Functor.map_comp]
  simpa (config := { congrConsts := false }) only [Category.assoc] using congrArg
    (fun z => (R.sphere m w).hom ≫ D.recovery.realization.map a ≫ z) hmap

/-- No compactness is needed for the torsion-to-zero direction.  It uses
the prescribed realization coordinates for the same lambda powers. -/
private theorem bhsRealizationLambdaAction (R : RealizationCoordinates D)
    {X : Syn} (m w : ℤ) (k : ℕ) (a : BiHom m w X) :
    (R.sphere m (w-k)).hom ≫ D.recovery.realization.map (lambdaMultiply k a) =
      (R.sphere m w).hom ≫ D.recovery.realization.map a := by
  have hf : lambdaMultiply k a =
      lambdaMultiply k (𝟙 (Smn (Syn := Syn) m w)) ≫ a := by
    dsimp only [lambdaMultiply]
    simp (config := { congrConsts := false }) only [Category.assoc, Category.comp_id]
  rw [hf, Functor.map_comp, ← Category.assoc, R.lambda]

private theorem bhsRealizationZeroOfLambdaTorsion (R : RealizationCoordinates D)
    {X : Syn} {m w : ℤ} (a : BiHom m w X)
    (ha : ∃ k : ℕ, lambdaMultiply k a = 0) :
    D.recovery.realization.map a = 0 := by
  letI := R.additive
  obtain ⟨k,hk⟩ := ha
  have h := bhsRealizationLambdaAction D R m w k a
  rw [hk, Functor.map_zero, comp_zero] at h
  apply (cancel_epi (R.sphere m w).hom).mp
  simpa (config := { congrConsts := false }) only [comp_zero] using h.symm

/-- An actual lambda-power nonzero image reflects nonvanishing without
assuming injectivity of the completion map or replacing its source. -/
private theorem bhsLambdaNonzeroOfPostcompose {X Y : Syn} (g : X ⟶ Y)
    {m w : ℤ} (a : BiHom m w X) (k : ℕ)
    (ha : lambdaMultiply k (a ≫ g) ≠ 0) : lambdaMultiply k a ≠ 0 := by
  intro hz
  apply ha
  rw [bhsLambdaMultiplyPostcompose, hz, zero_comp]

/-- Tower maps transport actual filtration witnesses.  No completeness or
separation is inferred from convergence. -/
private theorem bhsFiltrationPostcompose {X Y : Syn} (g : X ⟶ Y)
    {m w : ℤ} (s : ℤ) (a : BiHom m w X)
    (ha : FiltrationAtLeast D.syntheticTower s a) :
    FiltrationAtLeast D.syntheticTower s (a ≫ g) := by
  obtain ⟨b,hb⟩ := ha
  change b ≫ (D.syntheticTower.tower X).projection s = a at hb
  refine ⟨b ≫ (D.syntheticTower.map g).stage s.toNat, ?_⟩
  change (b ≫ (D.syntheticTower.map g).stage s.toNat) ≫
      (D.syntheticTower.tower Y).projection s = a ≫ g
  rw [Category.assoc, TowerMap.projection, ← Category.assoc, hb]

/-- The actual same nu map carries a lambda-division witness to its image. -/
private theorem bhsLambdaDivisiblePostcompose
    (X Y : ClassicalObject) (f : X.obj D.auxiliary ⟶ Y.obj D.auxiliary)
    (m w s : ℤ) (h : w-m ≤ s)
    (a : BiHom m w (D.nu.functor.obj (X.obj D.auxiliary)))
    (ha : LambdaDivisible D X m w s h a) :
    LambdaDivisible D Y m w s h (a ≫ D.nu.functor.map f) := by
  obtain ⟨b,hb⟩ := ha
  refine ⟨b ≫ D.nu.functor.map f, ?_⟩
  have hs : m+s - ((m+s-w).toNat : ℤ) = w := by
    rw [Int.toNat_of_nonneg (by omega)]
    omega
  change homotopyRegrade rfl hs
      (lambdaMultiply (m+s-w).toNat (b ≫ D.nu.functor.map f)) = a ≫ D.nu.functor.map f
  rw [bhsLambdaMultiplyPostcompose]
  rw [bhsHomotopyRegradePostcompose, hb]

/-- Pointwise version of a48's permanent-lift transport: it records every
required actual comparison instead of assuming the selected conclusion. -/
private theorem bhsPermanentLiftTransport
    (X Y : ClassicalObject) (f : X.obj D.auxiliary ⟶ Y.obj D.auxiliary)
    (s t : ℤ) (x : (D.classical.obj (X.obj D.auxiliary)).Page 2 (s,t))
    (source : PermanentLiftAt D Y)
    (cycles : ClassicalPermanentCycle D X (s,t) x ↔
      ClassicalPermanentCycle D Y (s,t) ((D.classical.map f).pageMap 2 (s,t) x))
    (lifts : (∃ b : BiHom (t-s) t (nuZero D Y),
        quotientClass 1 b = firstLabel D Y s t ((D.classical.map f).pageMap 2 (s,t) x)) ↔
      ∃ a : BiHom (t-s) t (nuZero D X), quotientClass 1 a = firstLabel D X s t x) :
    ClassicalPermanentCycle D X (s,t) x ↔
      ∃ a : BiHom (t-s) t (nuZero D X), quotientClass 1 a = firstLabel D X s t x :=
  cycles.trans ((source s t _).trans lifts)

/-- The source BHS filtration formula transports only with BOTH actual
filtration comparison and lambda-divisibility reflection. -/
private theorem bhsFiltrationLambdaTransport
    (X Y : ClassicalObject) (f : X.obj D.auxiliary ⟶ Y.obj D.auxiliary)
    (m w s : ℤ) (h : w-m ≤ s)
    (a : BiHom m w (D.nu.functor.obj (X.obj D.auxiliary)))
    (source : FiltrationLambdaAt D Y)
    (filtration : FiltrationAtLeast D.syntheticTower s a ↔
      FiltrationAtLeast D.syntheticTower s (a ≫ D.nu.functor.map f))
    (divisibility : LambdaDivisible D Y m w s h (a ≫ D.nu.functor.map f) ↔
      LambdaDivisible D X m w s h a) :
    FiltrationAtLeast D.syntheticTower s a ↔ LambdaDivisible D X m w s h a :=
  filtration.trans ((source m w s h _).trans divisibility)


end AbsorbedSourceTransport

/-- The transported BHS conclusions for one given realization and the same
selected towers, classes and first-quotient labels. The complete-source
comparison is a binding obligation; no arbitrary θ₅ choice theorem is a field. -/
private structure BHSSelectedRealizationComparisons (R : RealizationCoordinates D) : Prop where
  lifetime : ∀ (X : ClassicalObject) (s t : ℤ) (r : ℕ), 1 ≤ r →
    ∀ (x : (D.classical.obj (X.obj D.auxiliary)).Page 2 (s,t))
      (a : BiHom (t-s) t (nuZero D X)),
    ClassicalPermanentCycle D X (s,t) x →
    SurvivesTo (D.classical.obj (X.obj D.auxiliary)) (r+1) (s,t) x →
    quotientClass 1 a = firstLabel D X s t x → lambdaMultiply (r-1) a ≠ 0
  detection : ∀ (X : ClassicalObject) (s t : ℤ)
    (x : (D.classical.obj (X.obj D.auxiliary)).Page 2 (s,t))
    (a : BiHom (t-s) t (nuZero D X)),
    NonzeroSurvival (D.classical.obj (X.obj D.auxiliary)) (s,t) x →
    quotientClass 1 a = firstLabel D X s t x →
    ClassicalDetects (D.classicalConvergence X) (s,t) x (realizeNuZero D R X a)
  prescribed_lift : ∀ (X : ClassicalObject) (s t : ℤ)
    (x : (D.classical.obj (X.obj D.auxiliary)).Page 2 (s,t))
    (a : HomotopyGroup (t-s) (X.obj D.auxiliary)),
    NonzeroSurvival (D.classical.obj (X.obj D.auxiliary)) (s,t) x →
    ClassicalDetects (D.classicalConvergence X) (s,t) x a →
    ∃ b : BiHom (t-s) t (nuZero D X), quotientClass 1 b = firstLabel D X s t x ∧
      realizeNuZero D R X b = a
  boundary_lift : ∀ (X : ClassicalObject) (s t : ℤ) (r : ℕ), 2 ≤ r →
    ∀ y : (D.classical.obj (X.obj D.auxiliary)).Page 2 (s,t),
    ClassicalPermanentCycle D X (s,t) y →
    HitOnPage (D.classical.obj (X.obj D.auxiliary)) r (s,t) y →
    ∃ a : BiHom (t-s) t (nuZero D X), quotientClass 1 a = firstLabel D X s t y ∧
      lambdaMultiply (r-1) a = 0

end
end KIP126.Literature
