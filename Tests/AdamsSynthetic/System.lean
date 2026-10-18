module

import KIP126.AdamsSynthetic

/-! Ordinary-import consumers of the fixed project background.
Only actual objects, maps, classes and mathematical hypotheses are parameters. -/
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.Classical.Adams KIP126.Synthetic.SpectralSequence
open KIP126.Core.SpectralSequence KIP126.AdamsSynthetic KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
-- The final target is the class produced by this model's actual E₂ product.
example : Standard.H6SquarePermanent ↔
    NonzeroSurvival model.classical.sphere (2,128)
      (model.sphereAlgebra.product (1,64) (1,64)
        model.standardClasses.standardH6 model.standardClasses.standardH6) := by
  rw [Standard.H6SquarePermanent, Standard.standardH6Square_eq_product]
  rfl

example (s t : ℤ) (k : ℕ) (x : BiHom (t-s) t (S_0_0 : SyntheticSpectrum)) :
    Detects (model.convergence .sphere) (s,t,t-k)
      (model.comparison.sphereE2 s t k
        (sphereFirstQuotient model.nu model.quotients.functoriality model.firstQuotient s t
          (quotientClass 1 x))) (lambdaMultiply k x) :=
  sphere_homotopy_lambda s t k x

-- An element consumer gets the actual zero-length E∞ action without
-- supplying any projective-object or extra-lift hypothesis.
example (X Y : SyntheticObject) (g : X.obj model.nu model.auxiliary ⟶ Y.obj model.nu model.auxiliary)
    (p : ℤ × ℤ) (s : ℤ)
    (x : ((model.family.obj (X.obj model.nu model.auxiliary)).sequence.ssData
      (s,p.1+s,p.2)).eInfty) :
    TowerExtensionEquation (model.convergentMap X Y g) p s 0 x
      ((eqToHom (by simp) :
        ((model.family.obj (Y.obj model.nu model.auxiliary)).sequence.ssData (s,p.1+s,p.2)).eInfty ⟶
        ((model.family.obj (Y.obj model.nu model.auxiliary)).sequence.ssData (s+0,p.1+(s+0),p.2)).eInfty)
        ((model.family.map g).eInftyMap (s,p.1+s,p.2) x)) :=
  towerExtensionEquation_zero (model.convergentMap X Y g) p s x

variable (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
  (r : ℕ) (n s t : ℤ)
  (x : (model.classical.obj (X.obj model.auxiliary)).Page 2 (s,t))
  (y : (model.classical.obj (Y.obj model.auxiliary)).Page 2 (s+n,t+n))

example (W : FiniteExtensionWitness model X Y f r n s t x y) :
    (normalizedExponent model.classicalTower f : ℤ) ≤ n ∧
      n ≤ (r : ℤ)-2+normalizedExponent model.classicalTower f :=
  ⟨W.length_lower, W.length_upper⟩

example (W : InfiniteExtensionWitness model X Y f n s t x y) :
    IsPermanentCycle (model.classical.obj (X.obj model.auxiliary)) (s,t) x :=
  W.source_cycle

-- Reaching a finite quotient does not silently provide an infinite witness.
#check_failure (fun (W : FiniteExtensionWitness model X Y f r n s t x y) =>
  (W : InfiniteExtensionWitness model X Y f n s t x y))

end
