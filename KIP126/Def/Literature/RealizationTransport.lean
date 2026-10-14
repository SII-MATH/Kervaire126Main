module

public import KIP126.Def.Literature.BHS
import all KIP126.Def.Literature.BHS

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
