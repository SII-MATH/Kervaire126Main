module

public import KIP126.Def.ClassicalAdams.Context.Data
public import KIP126.Def.ClassicalAdams.TowerSSData.Sequence.Data
public import KIP126.Def.ClassicalAdams.SphereClasses.Product.Data
public import KIP126.Def.ClassicalAdams.SphereMultiplication.Data
public import KIP126.Def.ClassicalAdams.Suspension.Data
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.Algebra.DirectSum.Algebra

@[expose] public section

/-! Homogeneous pieces and operations for the specified sphere E₂ algebra.
The page and product are fixed before any native presentation is supplied.
The scalar action is transported along the existing canonical cobar comparison;
it preserves the actual page's additive group. -/

namespace KIP126.Classical.Adams.Sphere.Algebra

open KIP126.Algebra KIP126.StableHomotopy
noncomputable section

variable {Q : KIP126.StableHomotopy.Spectra.CompletionModel} (c : KIP126.HF2AdamsContext Q)

/-- The existing fixed sphere second page, in every nonnegative bidegree.
This is a definitionally equal type alias: keeping it as a `def` prevents
scalar-instance search from unfolding the entire fixed spectral sequence. -/
def ActualE2At (p : ℕ × ℕ) : Type := (adamsTowerInternalSpectralSequence c.foundation.hf2.unit SphereSpectrum).Page 2 ((p.1 : ℤ), (p.2 : ℤ))

instance actualE2AtAddCommGroup (p : ℕ × ℕ) : AddCommGroup ((ActualE2At c) p) :=
  inferInstanceAs (AddCommGroup ((adamsTowerInternalSpectralSequence c.foundation.hf2.unit SphereSpectrum).Page 2 ((p.1 : ℤ), (p.2 : ℤ))))

instance actualE2AtIntModule (p : ℕ × ℕ) : Module ℤ ((ActualE2At c) p) :=
  inferInstanceAs (Module ℤ ((adamsTowerInternalSpectralSequence c.foundation.hf2.unit SphereSpectrum).Page 2 ((p.1 : ℤ), (p.2 : ℤ))))

/-- The fixed cobar comparison, read from the actual page to cobar cohomology. -/
def actualE2ToCobarInt (p : ℕ × ℕ) : (ActualE2At c) p ≃ₗ[ℤ]
    MilnorCohomology.Cohomology c.foundation.hf2 c.milnor p.1 p.2 :=
  (MilnorCohomology.comparison c.foundation.hf2 c.milnor p.1 p.2).symm

instance actualE2AtModule (p : ℕ × ℕ) : Module F2 ((ActualE2At c) p) :=
  ((actualE2ToCobarInt c) p).toAddEquiv.module F2

instance actualE2AtScalarTower (p : ℕ × ℕ) :
    @IsScalarTower ℤ F2 ((ActualE2At c) p)
      (inferInstance : Module ℤ F2).toSMul
      (inferInstance : Module F2 ((ActualE2At c) p)).toSMul
      (inferInstance : Module ℤ ((ActualE2At c) p)).toSMul :=
  ((actualE2ToCobarInt c) p).isScalarTower F2

instance actualE2AtIntSMulComm (p : ℕ × ℕ) :
    @SMulCommClass ℤ ℤ ((ActualE2At c) p)
      (inferInstance : Module ℤ ((ActualE2At c) p)).toSMul
      (inferInstance : Module ℤ ((ActualE2At c) p)).toSMul :=
  @smulCommClass_self ℤ ((ActualE2At c) p) _
    (inferInstance : Module ℤ ((ActualE2At c) p)).toMulAction

/-- The same fixed comparison, now with its induced F₂-linearity. -/
def actualE2ToCobar (p : ℕ × ℕ) : (ActualE2At c) p ≃ₗ[F2]
    MilnorCohomology.Cohomology c.foundation.hf2 c.milnor p.1 p.2 :=
  ((actualE2ToCobarInt c) p).toAddEquiv.linearEquiv F2

/-- The previously fixed actual product, bundled as an F₂-bilinear map. -/
def actualE2Product (p q : ℕ × ℕ) :
    (ActualE2At c) p →ₗ[F2] (ActualE2At c) q →ₗ[F2] (ActualE2At c) (p + q) where
  toFun x := ((actualE2ToCobar c) (p + q)).symm.toLinearMap.comp
    ((MilnorCohomology.cup c.foundation.hf2 c.milnor
      ((actualE2ToCobar c) p x)).comp ((actualE2ToCobar c) q).toLinearMap)
  map_add' x y := by
    ext z
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, map_add,
      LinearMap.add_apply]
  map_smul' r x := by
    ext z
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, map_smul,
      LinearMap.smul_apply, RingHom.id_apply]

/-- The actual second-cycle class of the sphere identity, in degree (0,0). -/
def actualE2Unit : (ActualE2At c) 0 :=
  Suspension.classOfSecondCycle c.foundation.hf2 SphereSpectrum 0 0
    (Sphere.Multiplication.unitSecondCycle c.foundation.hf2)

end
end KIP126.Classical.Adams.Sphere.Algebra
