module

public import KIP126.Def.Synthetic.Sphere.Homotopy.Data
public import KIP126.Def.Synthetic.QuotientFunctor.Data
public import KIP126.Def.ClassicalAdams.PageRepresentatives.Data

@[expose] public section

/-! The first-quotient homotopy comparison identifies the homotopy groups
of νX/λ with classical Adams E₂. The sphere specialization uses this
comparison, the ν unit isomorphism and the same cofiber functor. -/
namespace KIP126.Comparison.ClassicalSynthetic
open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Synthetic.Context KIP126.Classical.Adams.PageRepresentatives
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn]
  [HasFunctorialCofiber (C := Syn)]

/-- Actual homotopy groups of shifted νX/λ compared with the actual E₂ of X.
Construction, naturality and compatibility with other comparisons remain
separate obligations; an arbitrary equivalence is not evidence of these laws. -/
abbrev FirstQuotientHomotopyComparison (H : Mod2EilenbergMacLane (C := C))
    (N : NuFunctorData C Syn) (X : C) := ∀ (a s t : ℤ),
  BiHom (t - s) (t + a)
    (XModLambdaN ((SyntheticCategory.biShift (0, a)).obj (N.functor.obj X)) 1) ≃+
      Ambient H X (s, t)

/-- The sphere specialization has no CSV labels or freely chosen Adams sequence. -/
abbrev SphereFirstQuotientComparison (H : Mod2EilenbergMacLane (C := C))
    (Syn : Type w) [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)] :=
  ∀ s t : ℤ, BiHom (t - s) t (XModLambdaN (S_0_0 : Syn) 1) ≃+
    Ambient H SphereSpectrum (s, t)

/-- Transport the supplied ν-sphere comparison through its specified unit iso.
Cofiber coherence is required to map this iso through the actual quotient. -/
noncomputable def sphereFirstQuotientComparison
    (H : Mod2EilenbergMacLane (C := C)) (N : NuFunctorData C Syn)
    (cofib : FunctorialCofiberCoherence Syn)
    (comparison : FirstQuotientHomotopyComparison H N SphereSpectrum) :
    SphereFirstQuotientComparison H Syn := by
  intro s t
  let e : (SyntheticCategory.biShift (0, 0)).obj (N.functor.obj SphereSpectrum) ≅
      (S_0_0 : Syn) :=
    SyntheticCategory.biShift_zero.app _ ≪≫ N.unitIso
  let q := (XModLambdaN.functor cofib 1).mapIso e
  have c : BiHom (t - s) t
      (XModLambdaN ((SyntheticCategory.biShift (0, 0)).obj
        (N.functor.obj SphereSpectrum)) 1) ≃+ Ambient H SphereSpectrum (s, t) :=
    Eq.mp (congrArg (fun z : ℤ =>
      BiHom (t - s) z (XModLambdaN ((SyntheticCategory.biShift (0, 0)).obj
        (N.functor.obj SphereSpectrum)) 1) ≃+ Ambient H SphereSpectrum (s, t))
      (Int.add_zero t)) (comparison 0 s t)
  exact (biHomTargetIso (t - s) t q.symm).trans c

end KIP126.Comparison.ClassicalSynthetic
