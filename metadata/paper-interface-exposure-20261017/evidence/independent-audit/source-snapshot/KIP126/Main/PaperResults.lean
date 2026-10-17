module

public import KIP126.Main.Conditions
import all KIP126.Main.SectionSeven.Predicates
import all KIP126.Main.SectionSeven.AlphaOne
import all KIP126.Main.SectionSeven.NormalizedNu
import all KIP126.Main.Internal.AlphaOne.Existence
import all KIP126.Main.Internal.NuNinth.Assembly

/-! Complete local statements from Section 7 of AimPaper. The public
detection predicates retain the fixed quotient maps and nonzero associated
graded classes. The proofs call the existing constructions on those objects. -/

@[expose] section
namespace KIP126.Main.Paper
open CategoryTheory KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.AdamsSynthetic.Standard (model SyntheticSpectrum)
open KIP126.Literature.Standard (eta syntheticH0)
noncomputable section

/-- Nonzero detection of the specified sphere class in its actual finite
lambda quotient, using the page map of the quotient projection. -/
public def FiniteDetected (n : ℕ) (_hn : 0 < n) (s t : ℤ) (k : ℕ)
    (x : KIP126.AdamsSynthetic.Standard.sphereSequence.Page 2 (s,t))
    (a : BiHom (t-s) (t-k) (XModLambdaN (S_0_0 : SyntheticSpectrum) n)) : Prop :=
  DetectsNonzero (model.convergence (.quotient n .sphere)) (s,t,t-k)
    ((KIP126.AdamsSynthetic.Standard.family.quotientProjection
      KIP126.AdamsSynthetic.Standard.syntheticSphere n).pageMap 2 (s,t,t-k)
        (KIP126.AdamsSynthetic.Standard.comparison.sphereE2 s t k x)) a

/-- Nonzero detection in the fixed untruncated synthetic sphere. -/
public def SphereDetected (s t : ℤ) (k : ℕ)
    (x : KIP126.AdamsSynthetic.Standard.sphereSequence.Page 2 (s,t))
    (a : BiHom (t-s) (t-k) (S_0_0 : SyntheticSpectrum)) : Prop :=
  DetectsNonzero (model.convergence .sphere) (s,t,t-k)
    (KIP126.AdamsSynthetic.Standard.comparison.sphereE2 s t k x) a

/-- AimPaper Lemma 7.14 (`lem:x1239`). One Q11 representative supplies
the compatible Q9 alpha-one class, its two correction identities for every
untruncated U representative, and its exact h0 annihilation relation. -/
public theorem lemma_x1239 :
    ∃ a11 : BiHom 123 132 (XModLambdaN (S_0_0 : SyntheticSpectrum) 11),
      let a9 := a11 ≫ (model.quotients.tower S_0_0).rho 9 11 (by decide)
      FiniteDetected 11 (by decide) 9 132 0 KIP126.Computation.Standard.V a11 ∧
      FiniteDetected 9 (by decide) 9 132 0 KIP126.Computation.Standard.V a9 ∧
      (∀ u : BiHom 124 134 (S_0_0 : SyntheticSpectrum),
        SphereDetected 10 134 0 KIP126.Computation.Standard.U u →
        ∃ (a2 : BiHom 124 137 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9))
          (a3 : BiHom 125 140 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9)),
          lambdaMultiply 3 (sphereAction eta a9) =
            (show BiHom 124 131 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9) from
              lambdaMultiply 3 (quotientClass 9 u)) +
            (show BiHom 124 131 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9) from
              lambdaMultiply 6 a2) ∧
          sphereAction eta a2 = lambdaMultiply 1 a3) ∧
      lambdaMultiply 3 (sphereAction syntheticH0 a9) = 0 := by
  exact KIP126.Main.Internal.AlphaOne.alpha_one_exists

/-- AimPaper Lemma 7.20 (`lem:nuext125`). The normalized Hopf element
acts on an existential representative of lambda^4 X by lambda times an
existential representative of lambda^5 Y in the same actual Q9. -/
public theorem lemma_nuext125 :
    ∃ (x : BiHom 122 126 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9))
      (y : BiHom 125 131 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9)),
      FiniteDetected 9 (by decide) 8 130 4 KIP126.Computation.Standard.X x ∧
      FiniteDetected 9 (by decide) 11 136 5 KIP126.Computation.Standard.Y y ∧
      sphereAction (KIP126.Literature.normalizedNu model
        KIP126.Literature.Standard.nuCofiber_nu_exponent) x = lambdaMultiply 1 y := by
  exact KIP126.Main.Internal.NuNinth.nu_extension_in_ninth_quotient

end
end KIP126.Main.Paper
