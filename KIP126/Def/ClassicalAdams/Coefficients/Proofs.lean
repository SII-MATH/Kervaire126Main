module

public import KIP126.Def.ClassicalAdams.Coefficients.Data

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

/-- The internal F₂-linear view does not change the differential. -/
theorem adamsInternalDifferentialF2_apply (r : ℤ) (p : ℤ × ℤ)
    (x : (adamsTowerInternalSpectralSequence H.unit X).Page r p) :
    adamsInternalDifferentialF2 H R X r p x = (adamsTowerInternalSpectralSequence H.unit X).d r p x := rfl

/-- Square-zero is inherited from the existing internal differential. -/
theorem adamsInternalDifferentialF2_comp (r : ℤ) (p : ℤ × ℤ)
    (x : (adamsTowerInternalSpectralSequence H.unit X).Page r p) :
    adamsInternalDifferentialF2 H R X r (p + (adamsTowerInternalSpectralSequence H.unit X).diffDeg r)
      (adamsInternalDifferentialF2 H R X r p x) = 0 := by
  have h := congrArg (fun f => f.hom x)
    ((adamsTowerInternalSpectralSequence H.unit X).d_comp_d r p)
  exact h

/-- The F₂-linear view does not change the raw quotient differential. -/
theorem adamsDifferentialF2_apply (r : ℕ) (hr : 1 ≤ r) (s t : ℤ)
    (x : adamsPage H.unit X r hr s t) :
    adamsDifferentialF2 H R X r hr s t x = adamsDifferential H.unit X r hr s t x := rfl

/-- The F₂-linear first-page comparison preserves the original representative map. -/
theorem adamsPageOneHomologyF2Equiv_apply (s : ℕ) (t : ℤ)
    (x : adamsPage H.unit X 1 le_rfl s t) :
    adamsPageOneHomologyF2Equiv H R X s t x = adamsPageOneHomologyEquiv H.unit X s t x := rfl

variable [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]

/-- The F₂-linear splitting retains the actual action and boundary maps. -/
theorem adamsHomologySplitF2Equiv_apply (n : ℤ)
    (x : Mod2Homology H n (H.HF2 ⊗ X)) :
    adamsHomologySplitF2Equiv H R X n x =
      (adamsHomologyAction H R X n x, adamsHomologyBoundary H X n x) := rfl

/-- The F₂-linear kernel comparison is the restriction of the actual boundary. -/
theorem adamsHomologyKernelF2Equiv_apply (n : ℤ)
    (x : LinearMap.ker (adamsHomologyAction H R X n)) :
    adamsHomologyKernelF2Equiv H R X n x = adamsHomologyBoundary H X n x := rfl

end

end KIP126.Classical.Adams
