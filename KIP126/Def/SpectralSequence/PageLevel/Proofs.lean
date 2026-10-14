module

public import KIP126.Def.SpectralSequence.PageLevel.Data
public import Lean.Elab.Tactic.Omega

@[expose] public section

namespace KIP126.Core.SpectralSequence

namespace AdamsPage

/-- 有效 Adams 页转换成整数后仍满足第二页下界。 -/
theorem two_le_toInt (r : AdamsPage) : (2 : ℤ) ≤ r.toInt := by
  rcases r with ⟨r, hr⟩
  change (2 : ℤ) ≤ (r : ℤ)
  exact_mod_cast hr

end AdamsPage

namespace PageLevelConvention

theorem page_ge (P : PageLevelConvention) {r : ℕ}
    (h : P.firstPage ≤ r) : P.admissibleFrom ≤ P.page r := by
  induction r, h using Nat.le_induction with
  | base => simp [P.page_first]
  | succ r _ ih => rw [P.page_succ]; omega

theorem cycleLevel_ge (P : PageLevelConvention) {r : ℕ}
    (h : P.firstPage ≤ r) :
    P.cycleLevel P.firstPage ≤ P.cycleLevel r := by
  induction r, h using Nat.le_induction with
  | base => omega
  | succ r _ ih => rw [P.cycle_succ]; omega

theorem quotientExponent_ge (P : PageLevelConvention) {r : ℕ}
    (h : P.firstPage ≤ r) :
    P.quotientExponent P.firstPage ≤ P.quotientExponent r := by
  induction r, h using Nat.le_induction with
  | base => omega
  | succ r _ ih => rw [P.quotient_succ]; omega

end PageLevelConvention

end KIP126.Core.SpectralSequence
