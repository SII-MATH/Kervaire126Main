module

public import KIP126.Def.ClassicalAdams.Coefficients.Basic.Proofs
public import KIP126.Def.StableHomotopy.Cohomology.Coefficients.Data
public import KIP126.Def.ClassicalAdams.TowerHomology.Normalized.Data
public import KIP126.Def.ClassicalAdams.TowerHomology.Splitting.Data

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

/-- Derived F₂ scalars on the unchanged actual tower quotient. -/
abbrev adamsPageF2Module (r : ℕ) (hr : 1 ≤ r) (s t : ℤ) :
    Module (ZMod 2) (adamsPage H.unit X r hr s t) :=
  AddCommGroup.zmodModule (adamsPage_two_nsmul_zero H R X r hr s t)

/-- Derived F₂ scalars on the unchanged internal finite page. -/
abbrev adamsInternalPageF2Module (r s t : ℤ) :
    Module (ZMod 2) ((adamsTowerInternalSpectralSequence H.unit X).Page r (s, t)) :=
  AddCommGroup.zmodModule (adamsInternalPage_two_nsmul_zero H R X r s t)

/-- The already constructed quotient differential, with F₂ linearity made explicit. -/
def adamsDifferentialF2 (r : ℕ) (hr : 1 ≤ r) (s t : ℤ) :
    letI := adamsPageF2Module H R X r hr s t
    letI := adamsPageF2Module H R X r hr (s + r) (t + r - 1)
    adamsPage H.unit X r hr s t →ₗ[ZMod 2] adamsPage H.unit X r hr (s + r) (t + r - 1) :=
  letI := adamsPageF2Module H R X r hr s t
  letI := adamsPageF2Module H R X r hr (s + r) (t + r - 1)
  (adamsDifferential H.unit X r hr s t).toAddMonoidHom.toZModLinearMap 2

/-- The existing first-page homology comparison, now as an F₂-linear equivalence. -/
def adamsPageOneHomologyF2Equiv (s : ℕ) (t : ℤ) :
    letI := adamsPageF2Module H R X 1 le_rfl s t
    letI := mod2HomologyModule H R (t - s) (adamsTower H.unit X s)
    adamsPage H.unit X 1 le_rfl s t ≃ₗ[ZMod 2]
      Mod2Homology H (t - s) (adamsTower H.unit X s) :=
  letI := adamsPageF2Module H R X 1 le_rfl s t
  letI := mod2HomologyModule H R (t - s) (adamsTower H.unit X s)
  { (adamsPageOneHomologyEquiv H.unit X s t).toAddEquiv with
    map_smul' := ZMod.map_smul (adamsPageOneHomologyEquiv H.unit X s t).toAddEquiv }

/-- The existing internal SSData differential with its derived F₂ linearity. -/
def adamsInternalDifferentialF2 (r : ℤ) (p : ℤ × ℤ) :
    let E := adamsTowerInternalSpectralSequence H.unit X
    let q := p + E.diffDeg r
    letI := adamsInternalPageF2Module H R X r p.1 p.2
    letI := adamsInternalPageF2Module H R X r q.1 q.2
    E.Page r p →ₗ[ZMod 2] E.Page r q :=
  let E := adamsTowerInternalSpectralSequence H.unit X
  let q := p + E.diffDeg r
  letI := adamsInternalPageF2Module H R X r p.1 p.2
  letI := adamsInternalPageF2Module H R X r q.1 q.2
  (E.d r p).hom.toAddMonoidHom.toZModLinearMap 2

variable [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]

/-- The derived splitting of the actual smashed unit sequence is F₂-linear. -/
def adamsHomologySplitF2Equiv (n : ℤ) :
    letI := mod2HomologyModule H R n X
    letI := mod2HomologyModule H R n (H.HF2 ⊗ X)
    letI := mod2HomologyModule H R (n - 1) (fiber (adamsUnit H.unit X))
    Mod2Homology H n (H.HF2 ⊗ X) ≃ₗ[ZMod 2]
      Mod2Homology H n X × Mod2Homology H (n - 1) (fiber (adamsUnit H.unit X)) :=
  letI := mod2HomologyModule H R n X
  letI := mod2HomologyModule H R n (H.HF2 ⊗ X)
  letI := mod2HomologyModule H R (n - 1) (fiber (adamsUnit H.unit X))
  { (adamsHomologySplitEquiv H R X n).toAddEquiv with
    map_smul' := ZMod.map_smul (adamsHomologySplitEquiv H R X n).toAddEquiv }

/-- The normalized next-stage homology comparison upgraded to F₂ scalars.
The map is still the actual connecting homomorphism. -/
def adamsHomologyKernelF2Equiv (n : ℤ) :
    letI := mod2HomologyModule H R n X
    letI := mod2HomologyModule H R n (H.HF2 ⊗ X)
    letI := mod2HomologyModule H R (n - 1) (fiber (adamsUnit H.unit X))
    LinearMap.ker ((adamsHomologyAction H R X n).toAddMonoidHom.toZModLinearMap 2) ≃ₗ[ZMod 2]
      Mod2Homology H (n - 1) (fiber (adamsUnit H.unit X)) :=
  letI := mod2HomologyModule H R n X
  letI := mod2HomologyModule H R n (H.HF2 ⊗ X)
  letI := mod2HomologyModule H R (n - 1) (fiber (adamsUnit H.unit X))
  { (adamsHomologyKernelEquiv H R X n).toAddEquiv with
    map_smul' := ZMod.map_smul (adamsHomologyKernelEquiv H R X n).toAddEquiv }

end

end KIP126.Classical.Adams
