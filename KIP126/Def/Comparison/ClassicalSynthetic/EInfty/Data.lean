module

public import KIP126.Def.Synthetic.EInfty.Presentation.Predicates
public import KIP126.Def.ClassicalAdams.PageRepresentatives.Quotient.Window.Data

@[expose] public section
/-!
# Classical/synthetic E-infinity comparison

These definitions specify comparison maps and their compatibility with
representatives, differentials and products on the given mathematical objects.
-/

namespace KIP126.Comparison

open CategoryTheory CategoryTheory.MonoidalCategory
open Classical.Adams SpectralSequence

universe u v w

section SyntheticEInfty

open StableHomotopy StableHomotopy.Cohomology Synthetic.Context Synthetic.SpectralSequence
open Classical.Adams.PageRepresentatives

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  (H : Mod2EilenbergMacLane (C := C)) (N : NuFunctorData C Syn)
  (F : SyntheticAdamsFamily Syn)

/-- Comparisons of classical cycles and boundaries with the synthetic E∞ page,
together with compatibility under λ and quotient restriction maps. -/
abbrev NuEInftyFormula := KIP126.Synthetic.SpectralSequence.NuEInftyFormula H N F
abbrev FiniteEInftyFormula := KIP126.Synthetic.SpectralSequence.FiniteEInftyFormula H N F
abbrev SyntheticEInftyPresentation :=
  KIP126.Synthetic.SpectralSequence.SyntheticEInftyPresentation H N F
abbrev SyntheticEInftyMapCompatibility :=
  KIP126.Synthetic.SpectralSequence.SyntheticEInftyMapCompatibility H N F
namespace SyntheticEInftyPresentation
variable {H N F}

/-- 仅使用已有两个指数范围的比较；不在每次使用时重新选择同构。 -/
noncomputable def finite (P : SyntheticEInftyPresentation H N F)
    (X : C) (q : ℕ) (hq : 0 < q) (p : ℤ × ℤ) (w : ℤ) :
    ((F.nuQuotient N X q).sequence.ssData (p.1, p.2, w)).eInfty ≃ₗ[ℤ]
      finiteEInftyModel H X q p w := by
  by_cases hq1 : q = 1
  · subst q
    exact P.specialFiber X p w
  · exact P.quotient X q (by omega) p w

noncomputable def nuWindow (P : SyntheticEInftyPresentation H N F)
    (X : C) (p : ℤ × ℤ) (w : ℤ) (hw : w ≤ p.2) :
    ((F.nu N X).sequence.ssData (p.1, p.2, w)).eInfty ≃ₗ[ℤ]
      PermanentQuotient H X (1 + p.2 - w) p :=
  (P.nu X p w).trans (nuEInftyWindow H X p w hw)

noncomputable def finiteWindow (P : SyntheticEInftyPresentation H N F)
    (X : C) (q : ℕ) (hq : 0 < q) (p : ℤ × ℤ) (w : ℤ)
    (hw : 0 ≤ p.2 - w ∧ p.2 - w < q) :
    ((F.nuQuotient N X q).sequence.ssData (p.1, p.2, w)).eInfty ≃ₗ[ℤ]
      CycleQuotient H X (q - p.2 + w) (1 + p.2 - w) p :=
  (P.finite X q hq p w).trans (finiteEInftyWindow H X q p w hw)

end SyntheticEInftyPresentation

end SyntheticEInfty

end KIP126.Comparison
