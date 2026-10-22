module

import KIP126.Main

/-! Ordinary consumers call the paper theorems directly. The final theorem
accepts a standard-class family and concludes nonzero E∞ survival of its actual
h₆ product on the fixed sphere. -/
namespace Tests.Main
open KIP126.Core.SpectralSequence
open KIP126.AdamsSynthetic.Standard (model)
open KIP126.Main

example :
    ((H6SquarePermanent ∧ ¬ H6SquareSupportsD12) ∨ (H6SquareSupportsD12 ∧ ¬ H6SquarePermanent)) ∧
      (H6SquareSupportsD12 ↔ Stem126D6Vanishes ∧ Theta5SquareNonzeroDetection ∧ EtaExtensionDetection) := h6_square_differential_dichotomy_and_criterion

example (hc3 : Stem126D6Vanishes) : ¬ EtaExtensionDetection := eta_extension_excluded_of_d6_vanishes hc3

example : NonzeroSurvival model.classical.sphere (2,128)
    model.standardClasses.standardH6Square := h6_sq_permanent model.standardClasses

example : NonzeroSurvival model.classical.sphere (2,128)
    (model.sphereAlgebra.product (1,64) (1,64)
      model.standardClasses.standardH6 model.standardClasses.standardH6) := by
  change NonzeroSurvival model.classical.sphere (2,128)
    model.standardClasses.standardH6Square
  exact h6_sq_permanent model.standardClasses

example (H : KIP126.Classical.Adams.StandardSphereClasses
    model.classical model.sphereAlgebra) :
    NonzeroSurvival model.classical.sphere (2,128)
      (model.sphereAlgebra.product (1,64) (1,64) (H.hi 6) (H.hi 6)) :=
  h6_sq_permanent H

example (hd : H6SquareSupportsD12) : ¬ H6SquarePermanent ∧ Stem126D6Vanishes := by
  obtain ⟨cases, criterion⟩ := h6_square_differential_dichotomy_and_criterion
  refine ⟨?_, (criterion.mp hd).1⟩
  rcases cases with hp | hn
  · exact False.elim (hp.2 hd)
  · exact hn.2

/-- The paper's final reasoning consumes the two intermediate theorems
without requesting a construction or a delivery package from the caller. -/
theorem paperConclusion : H6SquarePermanent := by
  obtain ⟨cases, criterion⟩ := h6_square_differential_dichotomy_and_criterion
  rcases cases with hp | hd
  · exact hp.1
  · obtain ⟨h3, _, h5⟩ := criterion.mp hd.1
    exact False.elim (eta_extension_excluded_of_d6_vanishes h3 h5)

open CategoryTheory KIP126.Synthetic.Context
open KIP126.AdamsSynthetic.Standard (SyntheticSpectrum)

/-- Remark 7.4 is available through an ordinary Main import, in both
directions and also at the zero-length endpoint. -/
example (n : ℕ) (a : BiHom 125 130 (S_0_0 : SyntheticSpectrum)) :
    quotientClass n a = 0 ↔ quotientClass (n+1) (lambdaMultiply 1 a) = 0 :=
  normalized_quotient n a

example (a : BiHom 125 130 (S_0_0 : SyntheticSpectrum)) :
    quotientClass 1 (lambdaMultiply 1 a) = 0 → quotientClass 0 a = 0 :=
  (normalized_quotient 0 a).mpr

/-- Remark 7.5 compares any two admissible choices without exposing the
private filtration and detector calculations. -/
example (theta theta' : BiHom 62 64 (S_0_0 : SyntheticSpectrum))
    (htheta : ThetaChoice theta) (htheta' : ThetaChoice theta') :
    KIP126.Literature.Standard.lambdaEtaThetaSquare theta =
      KIP126.Literature.Standard.lambdaEtaThetaSquare theta' := by
  exact (lambda_eta_theta_square_independent theta htheta).trans
    (lambda_eta_theta_square_independent theta' htheta').symm

/-- A normal consumer obtains the Q9 alpha-one representative from the
compatible Q11 construction, without importing its private implementation. -/
example : ∃ a : BiHom 123 132 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9),
    Paper.FiniteDetected 9 (by decide) 9 132 0 KIP126.Computation.Standard.V a := by
  obtain ⟨a11,_,ha9,_⟩ := Paper.lemma_x1239
  exact ⟨a11 ≫ (model.quotients.tower S_0_0).rho 9 11 (by decide),ha9⟩

/-- The actual nu-extension supplies a nonzero detected X representative. -/
example : ∃ x : BiHom 122 126 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9),
    Paper.FiniteDetected 9 (by decide) 8 130 4 KIP126.Computation.Standard.X x := by
  obtain ⟨x,y,hx,_⟩ := Paper.lemma_nuext125
  exact ⟨x,hx⟩

/-- Statement-only consumer check for the original Lemma 7.16. Its single
alpha-one witness supplies both Q11 and Q9 detection and the conclusion for
every member of its actual right-module bracket. This check consumes the
registered pending proof. -/
example (hc3 : Stem126D6Vanishes) (hc5 : EtaExtensionDetection) :
    ∃ a11 : BiHom 123 132 (XModLambdaN (S_0_0 : SyntheticSpectrum) 11),
      let a9 := a11 ≫ (model.quotients.tower S_0_0).rho 9 11 (by decide)
      let bracket := fun z : BiHom 125 132 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9) =>
        KIP126.StableHomotopy.Toda.Relation
          ((KIP126.Literature.Route.tripleTodaSource 1 2 0 1 123 129).inv ≫ z)
          ((SyntheticCategory.biShift (123,130)).map KIP126.Literature.Standard.eta)
          ((SyntheticCategory.biShift_comp (0,1) (123,129)).inv.app S_0_0 ≫
            (SyntheticCategory.biShift (123,129)).map KIP126.Literature.Standard.syntheticH0)
          (lambdaMultiply 3 a9)
      Paper.FiniteDetected 11 (by decide) 9 132 0 KIP126.Computation.Standard.V a11 ∧
      Paper.FiniteDetected 9 (by decide) 9 132 0 KIP126.Computation.Standard.V a9 ∧
      (∃ z, bracket z) ∧
        ∀ z, bracket z →
          Paper.FiniteDetected 9 (by decide) 11 136 4 KIP126.Computation.Standard.Y z ∧
          z ≠ 0 := by
  obtain ⟨a11, ha, hnonempty, hall⟩ := Paper.lemma_toda2ext hc3 hc5
  exact ⟨a11, ha.1, ha.2.1, hnonempty, hall⟩

/-- Statement-only consumer check for the original Corollary 7.18.
This deliberately consumes a registered pending proof; it does not certify
the mathematical conclusion. Every detected source has its own target in Q9. -/
example (hc3 : Stem126D6Vanishes) (hc5 : EtaExtensionDetection) :
    ∀ y : BiHom 125 132 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9),
      Paper.FiniteDetected 9 (by decide) 11 136 4 KIP126.Computation.Standard.Y y →
      ∃ t : BiHom 125 139 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9),
        Paper.FiniteDetected 9 (by decide) 14 139 0 KIP126.Computation.Standard.T t ∧
        sphereAction KIP126.Literature.Standard.syntheticH0 y = lambdaMultiply 6 t ∧
        lambdaMultiply 6 t ≠ 0 :=
  Paper.corollary_2ext125 hc3 hc5

/-- The complete classification is callable without an upstream package. -/
example : AdamsTwoLineClassification := adams_two_line_classification

example (t : ℤ) (x : model.classical.sphere.Page 2 (2,t)) :
    NonzeroSurvival model.classical.sphere (2,t) x ↔ AdamsTwoLineListed t x :=
  adams_two_line_classification t x

/-- The proposition and theorem use the same fixed sphere and conventions. -/
example (h : AdamsTwoLineClassification) (t : ℤ)
    (x : model.classical.sphere.Page 2 (2,t)) :
    NonzeroSurvival model.classical.sphere (2,t) x ↔ AdamsTwoLineListed t x := h t x

/-- Ordinary consumers obtain both supported square branches. -/
example : NonzeroSurvival model.classical.sphere (2,64)
    (model.standardClasses.standardHiSquare 5) :=
  (adams_two_line_known_squares 5 (Or.inl rfl)).1

example : AdamsTwoLineListed 128 model.standardClasses.standardH6Square :=
  (adams_two_line_known_squares 6 (Or.inr rfl)).2

example (x : model.classical.sphere.Page 2 (2,128))
    (hx : NonzeroSurvival model.classical.sphere (2,128) x) :
    x = model.standardClasses.standardH6Square :=
  (adams_two_line_stem126 x).mp hx

end Tests.Main
