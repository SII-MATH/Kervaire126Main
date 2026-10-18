module

import all KIP126.Main.SectionSeven.Predicates
/-! The compatible alpha₁ language in the paper's Section 7.
Adapted from Kervaire126 bbac1fc05843,
Def/Kervaire/Route/Section7/AlphaOne.lean (MIT; see the retained source LICENSE).
These are predicates for paper deductions; no existence or correction
identity is added to the upstream model. -/

@[expose] section
namespace KIP126.Main.SectionSeven
open CategoryTheory
open KIP126.Synthetic.Context KIP126.AdamsSynthetic
open KIP126.AdamsSynthetic.Standard
open KIP126.Core.SpectralSequence
noncomputable section

/-- One common infinite representative generates the entire nonzero
classical E∞ component. The specified E₂ class is retained. -/
private def ClassicalInfinityGenerated (s t : ℤ)
    (x : sphereSequence.Page 2 (s,t)) : Prop :=
  let P := sphereSequence.ssData (s,t)
  let n : WithTop ℕ := ↑(2-sphereSequence.r₀).toNat
  ∃ z : (Subobject.underlying.obj (P.Z ⊤) : ModuleCat ℤ),
    (Subobject.ofLE (P.Z ⊤) (P.Z n) (P.Z_anti le_top) ≫ P.pageπ n) z = x ∧
    P.pageπ ⊤ z ≠ 0 ∧ ∀ y : P.eInfty, y = 0 ∨ y = P.pageπ ⊤ z

/-- An actual finite-quotient differential with common representatives and
nonzero target on the stated page, not just nonzero E₂ coordinates. -/
private def FiniteNonzeroDifferential (q : ℕ) (r s t s' t' : ℤ) (k k' : ℕ)
    (x : sphereSequence.Page 2 (s,t)) (y : sphereSequence.Page 2 (s',t')) : Prop :=
  let A := family.quotient syntheticSphere q
  ∃ h : (s,t,t-k) + A.sequence.diffDeg r = (s',t',t'-k'),
    ∃ (xr : A.Page r (s,t,t-k)) (yr : A.Page r (s',t',t'-k')),
      SyntheticRepresentsOnPage A r (s,t,t-k)
        ((family.quotientProjection syntheticSphere q).pageMap 2 (s,t,t-k)
          (comparison.sphereE2 s t k x)) xr ∧
      SyntheticRepresentsOnPage A r (s',t',t'-k')
        ((family.quotientProjection syntheticSphere q).pageMap 2 (s',t',t'-k')
          (comparison.sphereE2 s' t' k' y)) yr ∧
      (A.sequence.d r (s,t,t-k) ≫ eqToHom (congrArg (A.Page r) h)) xr = yr ∧ yr ≠ 0

/-- One Q11 representative and its actual Q9 image; correction choices may
vary with the untruncated U representative. The final relation is exact. -/
private def AlphaOneProperties
    (a11 : BiHom 123 132 (XModLambdaN (S_0_0 : SyntheticSpectrum) 11)) : Prop :=
  let a9 := a11 ≫ (model.quotients.tower S_0_0).rho 9 11 (by decide)
  FiniteDetected 11 (by decide) 9 132 0 KIP126.Computation.Standard.V a11 ∧
  FiniteDetected 9 (by decide) 9 132 0 KIP126.Computation.Standard.V a9 ∧
  (∀ u : BiHom 124 134 (S_0_0 : SyntheticSpectrum),
    SphereDetected 10 134 0 KIP126.Computation.Standard.U u →
    ∃ (a2 : BiHom 124 137 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9))
      (a3 : BiHom 125 140 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9)),
      lambdaMultiply 3 (sphereAction KIP126.Literature.Standard.eta a9) =
        (show BiHom 124 131 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9) from
          lambdaMultiply 3 (quotientClass 9 u)) +
        (show BiHom 124 131 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9) from
          lambdaMultiply 6 a2) ∧
      sphereAction KIP126.Literature.Standard.eta a2 = lambdaMultiply 1 a3) ∧
  lambdaMultiply 3 (sphereAction KIP126.Literature.Standard.syntheticH0 a9) = 0

end
end KIP126.Main.SectionSeven
