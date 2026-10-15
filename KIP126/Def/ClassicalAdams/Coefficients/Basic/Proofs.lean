module

public import KIP126.Def.StableHomotopy.Cohomology.Coefficients.Basic.Proofs
public import KIP126.Def.ClassicalAdams.TowerLayer.Proofs
public import KIP126.Def.ClassicalAdams.TowerVanishing.Proofs

@[expose] public section

/-! Mod-two scalar structures derived from the specified H-ring and additive tensor.
No page, differential, scalar action, or Milnor coordinates are postulated. -/

namespace KIP126.Classical.Adams

noncomputable section

open CategoryTheory MonoidalCategory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology

universe u v

set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [MonoidalPreadditive C] [HasFunctorialCofiber (C := C)]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H) (X : C)

include R in
/-- The actual first group is two-torsion in every filtration, including negative ones. -/
theorem adamsE1_two_nsmul_zero (s t : ℤ) (x : adamsE1 H.unit X s t) : 2 • x = 0 := by
  by_cases hs : 0 ≤ s
  · have h (n : ℕ) (hn : (n : ℤ) = s) : 2 • x = 0 := by
      subst s
      apply (adamsE1HomologyEquiv H.unit X n t).injective
      simpa only [map_nsmul, map_zero] using
        mod2Homology_two_nsmul_zero H R (t - n) (adamsTower H.unit X n)
          (adamsE1HomologyEquiv H.unit X n t x)
    exact h s.toNat (by omega)
  · have hx : x = 0 := (adamsLayerAt_isZero_of_negative H.unit X s (by omega)).eq_of_tgt x 0
    simp only [hx, smul_zero]

include R in
/-- Every finite tower quotient inherits two-torsion from its first-group representatives. -/
theorem adamsPage_two_nsmul_zero (r : ℕ) (hr : 1 ≤ r) (s t : ℤ)
    (x : adamsPage H.unit X r hr s t) : 2 • x = 0 := by
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    change 2 • (adamsCycleBoundaries H.unit X r hr s t).mkQ x = 0
    rw [← map_nsmul]
    have hx : 2 • x = 0 := by
      apply Subtype.ext
      exact adamsE1_two_nsmul_zero H R X s t x.val
    rw [hx, map_zero]

end

end KIP126.Classical.Adams
