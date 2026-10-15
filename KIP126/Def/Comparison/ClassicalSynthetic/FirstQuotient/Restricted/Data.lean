module

public import KIP126.Def.Comparison.ClassicalSynthetic.FirstQuotient.Data
public import KIP126.Def.Synthetic.QuotientFunctor.Restricted.Construction.Data

@[expose] public section

namespace KIP126.Comparison.ClassicalSynthetic
open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Synthetic.Context KIP126.Classical.Adams.PageRepresentatives
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]

/-- The same sphere specialization, requiring functoriality only for the
actual λ quotients, not for arbitrary chosen cones. -/
noncomputable def sphereFirstQuotientOfLambdaFunctor
    (H : Mod2EilenbergMacLane (C := C)) (N : NuFunctorData C Syn)
    (Q : LambdaQuotientFunctoriality (Syn := Syn))
    (comparison : FirstQuotientHomotopyComparison H N SphereSpectrum) :
    SphereFirstQuotientComparison H Syn := by
  intro s t
  let e : (SyntheticCategory.biShift (0, 0)).obj (N.functor.obj SphereSpectrum) ≅
      (S_0_0 : Syn) := SyntheticCategory.biShift_zero.app _ ≪≫ N.unitIso
  let q := (Q.functor 1).mapIso e
  have c : BiHom (t - s) t
      (XModLambdaN ((SyntheticCategory.biShift (0, 0)).obj (N.functor.obj SphereSpectrum)) 1) ≃+
        Ambient H SphereSpectrum (s, t) :=
    Eq.mp (congrArg (fun z : ℤ =>
      BiHom (t - s) z (XModLambdaN ((SyntheticCategory.biShift (0, 0)).obj
        (N.functor.obj SphereSpectrum)) 1) ≃+ Ambient H SphereSpectrum (s, t))
      (Int.add_zero t)) (comparison 0 s t)
  exact (biHomTargetIso (t - s) t q.symm).trans c
end KIP126.Comparison.ClassicalSynthetic
