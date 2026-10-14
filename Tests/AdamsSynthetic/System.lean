module

import KIP126.Def.AdamsSynthetic


/-! The same coherent model supplies every comparison and extension witness. -/

open CategoryTheory KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.Classical.Adams KIP126.Synthetic.SpectralSequence
open KIP126.Core.SpectralSequence KIP126.AdamsSynthetic KIP126.Kervaire.Route

universe u v w
noncomputable section

section SameModel
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  (D : Model C Syn)

-- The final target is the class produced by this model's actual E₂ product.
example : D.H6SquarePermanent ↔
    NonzeroSurvival D.classical.sphere (2,128)
      (D.sphereAlgebra.product (1,64) (1,64)
        D.standardClasses.standardH6 D.standardClasses.standardH6) := by
  rw [Model.H6SquarePermanent, D.standardClasses.standardH6Square_eq_product]

example (s t : ℤ) (k : ℕ) (x : BiHom (t-s) t (S_0_0 : Syn)) :
    Detects (D.convergence .sphere) (s,t,t-k)
      (D.comparison.sphereE2 s t k
        (sphereFirstQuotient D.nu D.quotients.functoriality D.firstQuotient s t
          (quotientClass 1 x))) (lambdaMultiply k x) :=
  D.sphereDetectionCompatible.homotopy_lambda s t k x

-- An element consumer gets the actual zero-length E∞ action without
-- supplying any projective-object or extra-lift hypothesis.
example (X Y : SyntheticObject) (g : X.obj D.nu D.auxiliary ⟶ Y.obj D.nu D.auxiliary)
    (p : ℤ × ℤ) (s : ℤ)
    (x : ((D.family.obj (X.obj D.nu D.auxiliary)).sequence.ssData
      (s,p.1+s,p.2)).eInfty) :
    TowerExtensionEquation (D.convergentMap X Y g) p s 0 x
      ((eqToHom (by simp) :
        ((D.family.obj (Y.obj D.nu D.auxiliary)).sequence.ssData (s,p.1+s,p.2)).eInfty ⟶
        ((D.family.obj (Y.obj D.nu D.auxiliary)).sequence.ssData (s+0,p.1+(s+0),p.2)).eInfty)
        ((D.family.map g).eInftyMap (s,p.1+s,p.2) x)) :=
  towerExtensionEquation_zero (D.convergentMap X Y g) p s x

variable (X Y : ClassicalObject) (f : X.obj D.auxiliary ⟶ Y.obj D.auxiliary)
  (r : ℕ) (n s t : ℤ)
  (x : (D.classical.obj (X.obj D.auxiliary)).Page 2 (s,t))
  (y : (D.classical.obj (Y.obj D.auxiliary)).Page 2 (s+n,t+n))

example (W : FiniteExtensionWitness D X Y f r n s t x y) :
    (normalizedExponent D.classicalTower f : ℤ) ≤ n ∧
      n ≤ (r : ℤ)-2+normalizedExponent D.classicalTower f :=
  ⟨W.length_lower, W.length_upper⟩

example (W : InfiniteExtensionWitness D X Y f n s t x y) :
    IsPermanentCycle (D.classical.obj (X.obj D.auxiliary)) (s,t) x :=
  W.source_cycle

-- Reaching a finite quotient does not silently provide an infinite witness.
#check_failure (fun (W : FiniteExtensionWitness D X Y f r n s t x y) =>
  (W : InfiniteExtensionWitness D X Y f n s t x y))
end SameModel
end
