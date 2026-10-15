module

public import KIP126.Def.Synthetic.AdamsSequence.Data
public import KIP126.Def.ClassicalAdams.Tower.Proofs
public import Mathlib.Algebra.Category.ModuleCat.Subobject

@[expose] public section

/-! The actual νHF₂ tower filtration on synthetic homotopy.
The definition works in every bidegree; it assumes neither boundedness nor
convergence. In particular it does not require a finite filtration on π₀. -/
namespace KIP126.Synthetic.SpectralSequence
open CategoryTheory CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Classical.Adams
universe u v w
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn]

/-- The coefficient unit is the image of the *same* classical HF₂ unit. -/
def nuCoefficientUnit {H : C} (unit : 𝟙_ C ⟶ H) (N : NuFunctorData C Syn) :
    S_0_0 ⟶ N.functor.obj H := N.unitIso.inv ≫ N.functor.map unit

variable [HasFunctorialCofiber (C := Syn)]

/-- Actual tower projection on bigraded homotopy. -/
def towerHomotopyMap {H : Syn} (unit : S_0_0 ⟶ H) (X : Syn)
    (s : ℕ) (p : ℤ × ℤ) :
    BiHom p.1 p.2 (adamsTower unit X s) →ₗ[ℤ] BiHom p.1 p.2 X :=
  (Preadditive.rightComp (Smn p.1 p.2)
    (adamsTowerMap unit X 0 s (Nat.zero_le s))).toIntLinearMap

/-- Membership means a lift to stage `max(s,0)` of the coefficient tower. -/
def towerFiltrationSubmodule {H : Syn} (unit : S_0_0 ⟶ H) (X : Syn)
    (s : ℤ) (p : ℤ × ℤ) : Submodule ℤ (BiHom p.1 p.2 X) :=
  LinearMap.range (towerHomotopyMap unit X s.toNat p)
end
end KIP126.Synthetic.SpectralSequence
