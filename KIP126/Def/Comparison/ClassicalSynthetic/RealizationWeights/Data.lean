module

public import KIP126.Def.Synthetic.Localization.Recovery.Data
public import KIP126.Def.Synthetic.Context.Coherence.Predicates
public import KIP126.Def.Synthetic.AdamsFiltration.Data
public import KIP126.Def.StableHomotopy.Cohomology.Data

@[expose] public section

/-! Weight comparisons for the SAME lambda-inversion realization.
Their zero value and every successive weight map are fixed, so this is
not a family of unrelated isomorphisms of objects of the same dimension.
The coefficient comparison is the already specified nu-recovery map.
-/
namespace KIP126.Comparison.ClassicalSynthetic
open CategoryTheory CategoryTheory.Functor
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Synthetic.Context
open KIP126.Synthetic.SpectralSequence
universe u v w
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  {Syn : Type w} [SyntheticCategory.{w,v} Syn]
  (N : NuFunctorData C Syn) (L : LambdaRecovery N)

def weightObject (X : C) (a : ℤ) : Syn :=
  (SyntheticCategory.biShift (0,a)).obj (N.functor.obj X)

/-- The actual lambda arrow, with only its integer-index identity removed. -/
def weightLambdaArrow (X : C) (a : ℤ) :
    weightObject N X (a-1) ⟶ weightObject N X a :=
  eqToHom (by simp [weightObject, Prod.mk_add_mk, sub_eq_add_neg]) ≫
    (SyntheticCategory.biShift_comp (0,a) (0,-1)).inv.app (N.functor.obj X) ≫
      SyntheticCategory.lam.app (weightObject N X a)

structure RealizationWeightComparison where
  iso : ∀ (X : C) (a : ℤ), L.realization.obj (weightObject N X a) ≅ X
  zero : ∀ X,
    (iso X 0).hom = L.realization.map (SyntheticCategory.biShift_zero.hom.app
      (N.functor.obj X)) ≫ L.nuRealizationIso.hom.app X
  lambda : ∀ X a,
    L.realization.map (weightLambdaArrow N X a) ≫ (iso X a).hom = (iso X (a-1)).hom
  naturality : ∀ {X Y : C} (f : X ⟶ Y) a,
    L.realization.map ((SyntheticCategory.biShift (0,a)).map (N.functor.map f)) ≫
      (iso Y a).hom = (iso X a).hom ≫ f

/-- The two shifts appearing in a fixed-weight Adams tower use this SAME
comparison and the existing biShift_comp. No new basepoint iso is selected. -/
def RealizationWeightComparison.doubleShift
    (W : RealizationWeightComparison N L) (X : C) (a b : ℤ) :
    L.realization.obj ((SyntheticCategory.biShift (0,b)).obj (weightObject N X a)) ≅ X :=
  L.realization.mapIso ((SyntheticCategory.biShift_comp (0,a) (0,b)).app
    (N.functor.obj X)) ≪≫ W.iso X (a+b)

end
end KIP126.Comparison.ClassicalSynthetic
