module

public import KIP126.Def.ClassicalAdams.PageRepresentatives.Order.Proofs
public import KIP126.Def.Algebra.NestedQuotient.Data

@[expose] public section

namespace KIP126.Classical.Adams.PageRepresentatives

open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Algebra

universe u v
noncomputable section

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  (H : Mod2EilenbergMacLane (C := C)) (X : C)

/-- The actual paper subquotient Z_c/B_b for positive indices. -/
abbrev CycleQuotient (c b : ℤ) (p : ℤ × ℤ) :=
  NestedQuotient.Space (cycles H X c p) (boundaries H X b p)

/-- The actual permanent-cycle quotient Z∞/B_b for positive b. -/
abbrev PermanentQuotient (b : ℤ) (p : ℤ × ℤ) :=
  NestedQuotient.Space (permanentCycles H X p) (boundaries H X b p)

/-- Change of finite cycle and boundary cutoffs, preserving the ambient E₂ label. -/
def quotientMap {c c' b b' : ℤ} (hc : c' ≤ c) (hb : b ≤ b') (p : ℤ × ℤ) :
    CycleQuotient H X c b p →ₗ[ℤ] CycleQuotient H X c' b' p :=
  NestedQuotient.map (cycles_antitone H X p hc) (boundaries_monotone H X p hb)

def permanentQuotientMap {b b' : ℤ} (hb : b ≤ b') (p : ℤ × ℤ) :
    PermanentQuotient H X b p →ₗ[ℤ] PermanentQuotient H X b' p :=
  NestedQuotient.map (le_refl (permanentCycles H X p)) (boundaries_monotone H X p hb)

/-- Reduction includes permanent cycles into a finite cycle submodule. -/
def permanentToFinite (c b : ℤ) (p : ℤ × ℤ) :
    PermanentQuotient H X b p →ₗ[ℤ] CycleQuotient H X c b p :=
  NestedQuotient.map (permanentCycles_le_cycles H X p c) (le_refl (boundaries H X b p))

/-- The classical side of the νX E∞ formula, with the paper's zero convention. -/
def nuEInftyModel (p : ℤ × ℤ) (w : ℤ) : ModuleCat.{v} ℤ :=
  if w ≤ p.2 then ModuleCat.of ℤ (PermanentQuotient H X (1 + p.2 - w) p)
  else ModuleCat.of ℤ PUnit.{v + 1}

/-- The classical side of the finite λ-quotient formula. Invalid cycle or
boundary indices give the zero module, rather than a clamped cycle module. -/
def finiteEInftyModel (q : ℕ) (p : ℤ × ℤ) (w : ℤ) : ModuleCat.{v} ℤ :=
  if 0 ≤ p.2 - w ∧ p.2 - w < q then
    ModuleCat.of ℤ (CycleQuotient H X (q - p.2 + w) (1 + p.2 - w) p)
  else ModuleCat.of ℤ PUnit.{v + 1}

end
end KIP126.Classical.Adams.PageRepresentatives
