module

public import KIP126.Def.Comparison.ClassicalSynthetic.FirstQuotient.Data
public import KIP126.Def.ClassicalAdams.SphereClasses.Hi.Internal.Data

@[expose] public section

/-!
# Bigraded θ₅ expressions on the actual synthetic sphere

All operations below are derived from the same synthetic category, cofibers
and suspensions. The classical labels are the standard Milnor classes on the
same Adams tower determined by H and M, independently of the external computations.
The comparison is explicit data; this file neither constructs it nor asserts
that an arbitrary equivalence has the required geometric compatibility.
-/
namespace KIP126.Kervaire.SyntheticTheta5
open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Synthetic.Context KIP126.Comparison.ClassicalSynthetic
open KIP126.Classical.Adams
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn]
  [HasFunctorialCofiber (C := Syn)]

/-- θ₅ itself has bidegree (62,64), not that of its square. -/
abbrev Theta (Syn : Type w) [SyntheticCategory.{w, v} Syn] := BiHom 62 64 (S_0_0 : Syn)

/-- A candidate η representative has bidegree (1,2). Its detection is a
separate predicate, rather than inferred from the name of a parameter. -/
abbrev Eta (Syn : Type w) [SyntheticCategory.{w, v} Syn] := BiHom 1 2 (S_0_0 : Syn)

noncomputable def thetaSquare (θ : Theta Syn) : BiHom 124 128 (S_0_0 : Syn) :=
  sphereProduct θ θ

noncomputable def etaThetaSquare (η : Eta Syn) (θ : Theta Syn) :
    BiHom 125 130 (S_0_0 : Syn) := sphereProduct η (thetaSquare θ)

noncomputable def lambdaEtaThetaSquare (η : Eta Syn) (θ : Theta Syn) :
    BiHom 125 129 (S_0_0 : Syn) := lambdaAction 125 130 S_0_0 (etaThetaSquare η θ)

/-- The total boundary of the standard h₆² label. The inverse comparison
lands in S/λ and the actual cofiber boundary lands in bidegree (125,129). -/
noncomputable def deltaH6Square (H : Mod2EilenbergMacLane (C := C))
    (M : MilnorCooperations H) (comparison : SphereFirstQuotientComparison H Syn) :
    BiHom 125 129 (S_0_0 : Syn) :=
  h6TotalBoundary ((comparison 2 128).symm (Sphere.Internal.hiSquare H M 6))

end KIP126.Kervaire.SyntheticTheta5
