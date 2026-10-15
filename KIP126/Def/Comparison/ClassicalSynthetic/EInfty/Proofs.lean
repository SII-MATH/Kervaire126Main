module

public import KIP126.Def.Comparison.ClassicalSynthetic.EInfty.Data
public import KIP126.Def.ClassicalAdams.PageRepresentatives.Quotient.Proofs

@[expose] public section

namespace KIP126.Comparison

open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
  KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
  KIP126.Classical.Adams.PageRepresentatives

universe u v w

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  (H : Mod2EilenbergMacLane (C := C)) (N : NuFunctorData C Syn)
  (F : SyntheticAdamsFamily Syn)
  (P : KIP126.Comparison.SyntheticEInftyPresentation H N F) (S : EInftyWeightShift F)
  (T : ∀ X : C, FiniteLambdaQuotientTower (N.functor.obj X))
  (K : KIP126.Comparison.SyntheticEInftyMapCompatibility H N F P S T)

include K

/-- Finite reduction is injective in the target's valid window because the
boundary cutoff is unchanged and the cycle submodule is included. -/
theorem syntheticEInfty_rho_finite_injective
    (X : C) (i j : ℕ) (hi : 0 < i) (hij : i ≤ j) (p : ℤ × ℤ) (w : ℤ)
    (hw : 0 ≤ p.2 - w ∧ p.2 - w < i) :
    Function.Injective
      (((F.functor.map ((T X).rho i j hij)).eInftyMap (p.1, p.2, w)).hom) := by
  intro a b hab
  apply (P.finiteWindow X j (by omega) p w (by constructor <;> omega)).injective
  apply quotientMap_cycle_injective H X
    (c := (j : ℤ) - p.2 + w) (c' := (i : ℤ) - p.2 + w)
    (by omega) (1 + p.2 - w) p
  exact (K.rho_finite X i j hi hij p w hw a).symm.trans
    ((congrArg (fun x => P.finiteWindow X i hi p w hw x) hab).trans
      (K.rho_finite X i j hi hij p w hw b))

omit K
include P

/-- Outside the ν window, the actual E∞ group is zero through the full-weight
presentation. No global statement about negative weights is used. -/
theorem syntheticEInfty_nu_subsingleton_of_outside
    (X : C) (p : ℤ × ℤ) (w : ℤ) (hw : ¬ w ≤ p.2) :
    Subsingleton (((F.nu N X).sequence.ssData (p.1, p.2, w)).eInfty) := by
  have hzero : Subsingleton (nuEInftyModel H X p w) := by
    simp only [nuEInftyModel, if_neg hw]
    infer_instance
  constructor
  intro a b
  exact (P.nu X p w).injective (hzero.elim _ _)

/-- The actual E∞ of every positive finite quotient is zero outside its
specified window, including the separately presented special fiber q=1. -/
theorem syntheticEInfty_finite_subsingleton_of_outside
    (X : C) (q : ℕ) (hq : 0 < q) (p : ℤ × ℤ) (w : ℤ)
    (hw : ¬ (0 ≤ p.2 - w ∧ p.2 - w < q)) :
    Subsingleton (((F.nuQuotient N X q).sequence.ssData (p.1, p.2, w)).eInfty) := by
  have hzero : Subsingleton (finiteEInftyModel H X q p w) := by
    simp only [finiteEInftyModel, if_neg hw]
    infer_instance
  constructor
  intro a b
  exact (P.finite X q hq p w).injective (hzero.elim _ _)

end KIP126.Comparison
