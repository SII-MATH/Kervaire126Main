module

public import KIP126.Def.AdamsSynthetic.SectionSeven.Predicates

@[expose] public section

/-! Pure statement language for the compatible alpha1 used in Section 7.
The underlying Adams comparison contains no existence or local calculation
assertion for these classes. -/
namespace KIP126.AdamsSynthetic.SectionSeven
open CategoryTheory
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.SpectralSequence
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
universe u v w
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H}
  (D : AdamsComparison H M Syn)

/-- The whole classical E-infinity component consists of zero and the
nonzero image of one common infinite-cycle representative of x. This is
stronger than just saying that x survives nontrivially. -/
def ClassicalInfinityGenerated (s t : ℤ) (x : E2 H SphereSpectrum s t) : Prop :=
  let E := adamsTowerInternalSpectralSequence H.unit SphereSpectrum
  let P := E.ssData (s,t)
  ∃ z : (Subobject.underlying.obj (P.Z ⊤) : ModuleCat ℤ),
    (Subobject.ofLE (P.Z ⊤) (P.Z 0) (P.Z_anti le_top) ≫ P.pageπ 0) z = x ∧
    P.pageπ ⊤ z ≠ 0 ∧ ∀ y : P.eInfty, y = 0 ∨ y = P.pageπ ⊤ z

/-- A nonzero differential in the actual finite quotient, including
common page representatives of both prescribed weighted E2 labels. -/
def FiniteNonzeroDifferential (q : ℕ) (r s t s' t' : ℤ) (k k' : ℕ)
    (x : E2 H SphereSpectrum s t) (y : E2 H SphereSpectrum s' t') : Prop :=
  let A := D.family.quotient (S_0_0 : Syn) q
  ∃ h : syntheticAdamsDifferentialTarget r (s,t,t-k) = (s',t',t'-k'),
    ∃ (xr : A.Page r (s,t,t-k)) (yr : A.Page r (s',t',t'-k')),
      KIP126.Synthetic.SpectralSequence.RepresentsOnPage A r (s,t,t-k)
        (D.quotientLabel q s t k x) xr ∧
      KIP126.Synthetic.SpectralSequence.RepresentsOnPage A r (s',t',t'-k')
        (D.quotientLabel q s' t' k' y) yr ∧
      (A.d r (s,t,t-k) ≫ eqToHom (congrArg (A.Page r) h)) xr = yr ∧ yr ≠ 0

/-- Lemma `lem:x_123_9` uses one Q11 representative and its actual Q9
image. For every untruncated U representative the correction choices may
vary. The correction alpha2 has weight137; it is its lambda^6 multiple,
not alpha2 itself, which can have the weight131 detector lambda^6 E. -/
def AlphaOneProperties (η : BiHom 1 2 (S_0_0 : Syn))
    (h0 : BiHom 0 1 (S_0_0 : Syn))
    (U : E2 H SphereSpectrum 10 134) (V : E2 H SphereSpectrum 9 132)
    (a11 : BiHom 123 132 (XModLambdaN (S_0_0 : Syn) 11)) : Prop :=
  let a9 := a11 ≫ (D.quotientTower S_0_0).rho 9 11 (by decide)
  FiniteDetected D 11 (by decide) 9 132 0 V a11 ∧
  FiniteDetected D 9 (by decide) 9 132 0 V a9 ∧
  (∀ u : BiHom 124 134 (S_0_0 : Syn), SphereDetected D 10 134 0 U u →
    ∃ (a2 : BiHom 124 137 (XModLambdaN (S_0_0 : Syn) 9))
      (a3 : BiHom 125 140 (XModLambdaN (S_0_0 : Syn) 9)),
      lambdaMultiply 3 (sphereAction η a9) =
        (show BiHom 124 131 (XModLambdaN (S_0_0 : Syn) 9) from
          lambdaMultiply 3 (quotientClass 9 u)) +
        (show BiHom 124 131 (XModLambdaN (S_0_0 : Syn) 9) from
          lambdaMultiply 6 a2) ∧
      sphereAction η a2 = lambdaMultiply 1 a3) ∧
  lambdaMultiply 3 (sphereAction h0 a9) = 0

end
end KIP126.AdamsSynthetic.SectionSeven
