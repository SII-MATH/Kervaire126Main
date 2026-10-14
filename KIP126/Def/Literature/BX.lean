module

public import KIP126.Def.Literature.Classical
import all KIP126.Def.Literature.Classical

/-! BX Proposition 7.19 at one distinguished source choice. Migrated from
Def/Kervaire/Theta5/Synthetic and Route/SourceLanguage at bbac1fc05843,
Apache-2.0. The normalized formula and arbitrary-choice statements of
the present paper are deliberately left as downstream proof obligations. -/

@[expose] section
namespace KIP126.Literature
open CategoryTheory KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.Core.SpectralSequence KIP126.Kervaire.Route
universe u v w
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w,v} Syn]
  [HasFunctorialCofiber (C := Syn)] (D : Model C Syn)

public def etaThetaSquare (η : BiHom 1 2 (S_0_0 : Syn))
    (θ : BiHom 62 64 (S_0_0 : Syn)) : BiHom 125 130 (S_0_0 : Syn) :=
  sphereProduct η (sphereProduct θ θ)

public def lambdaEtaThetaSquare (η : BiHom 1 2 (S_0_0 : Syn))
    (θ : BiHom 62 64 (S_0_0 : Syn)) : BiHom 125 129 (S_0_0 : Syn) :=
  lambdaMultiply 1 (etaThetaSquare η θ)

public def sphereTotalBoundary : XModLambdaN (S_0_0 : Syn) 1 ⟶ Smn 1 (-1) :=
  XModLambdaN.proj S_0_0 1 ≫
    (SyntheticCategory.biShift_compat (Syn := Syn) 1).inv.app
      ((SyntheticCategory.biShift (0,-1)).obj S_0_0) ≫
    (SyntheticCategory.biShift_comp (0,-1) (1,0)).hom.app S_0_0

public def deltaH6Square : BiHom 125 129 (S_0_0 : Syn) :=
  (susp_invariance 125 129 1 (-1) (S_0_0 : Syn)).symm
    ((sphereFirstQuotient D 2 128).symm D.standardClasses.standardH6Square ≫
      sphereTotalBoundary)

/-- All three statements use this same θ. The last clause is an equivalence,
not a proof of its zero right-hand side or of the final permanence target. -/
private structure BXSourceResults (η : BiHom 1 2 (S_0_0 : Syn))
    (θ : BiHom 62 64 (S_0_0 : Syn)) : Prop where
  eta_label : sphereFirstQuotient D 1 2 (quotientClass 1 η) = D.standardClasses.standardHi 1
  theta_label : Theta5Detected D θ
  order_two : θ + θ = 0
  finite : ∀ r : ℕ, 1 ≤ r →
    (SurvivesTo D.classical.sphere ((r : ℤ)+3) (2,128)
      D.standardClasses.standardH6Square ↔ quotientClass r (etaThetaSquare η θ) = 0)
  total_boundary : deltaH6Square D = lambdaEtaThetaSquare η θ
  untruncated : D.H6SquarePermanent ↔ lambdaEtaThetaSquare η θ = 0

/-- A single common source choice; no theorem for every detected θ is assumed. -/
private def BXDistinguishedInput (η : BiHom 1 2 (S_0_0 : Syn)) : Prop :=
  ∃ θ : BiHom 62 64 (S_0_0 : Syn), BXSourceResults D η θ

end
end KIP126.Literature
