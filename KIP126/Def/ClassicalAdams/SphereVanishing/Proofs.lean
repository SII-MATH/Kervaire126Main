module

public import KIP126.Def.ClassicalAdams.TowerVanishing.Proofs
public import KIP126.Def.ClassicalAdams.TowerLayer.Proofs
public import KIP126.Def.StableHomotopy.Cohomology.Data

@[expose] public section

namespace KIP126.Classical.Adams

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.MonoidalCategory
  KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
  KIP126.SpectralSequence
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  (H : Mod2EilenbergMacLane (C := C))

/-- In filtration zero the actual first sphere page is the homotopy of `H`.
Its vanishing in every nonzero degree follows from the Eilenberg--Mac Lane
property, without Milnor coordinates or any computation table. -/
theorem sphereAdamsPageOne_filtration_zero_subsingleton (t : ℤ) (ht : t ≠ 0) :
    Subsingleton (adamsPage H.unit SphereSpectrum 1 (by decide) 0 t) := by
  haveI := H.homotopy_vanishes t ht
  let e : HomotopyGroup t (H.HF2 ⊗ SphereSpectrum) ≃+ HomotopyGroup t H.HF2 :=
    ((homotopyGroupFunctor t).mapIso (ρ_ H.HF2)).addCommGroupIsoToAddEquiv
  have hcoeff : Subsingleton (HomotopyGroup t (H.HF2 ⊗ SphereSpectrum)) :=
    e.injective.subsingleton
  haveI : Subsingleton (HomotopyGroup (t - (0 : ℕ))
      (H.HF2 ⊗ adamsTower H.unit SphereSpectrum 0)) := by
    simpa only [Nat.cast_zero, sub_zero, adamsTower] using hcoeff
  exact (adamsPageOneHomologyEquiv H.unit SphereSpectrum 0 t).injective.subsingleton

/-- The sphere tower vanishes in filtration zero and positive internal degree
on every finite page, by the Eilenberg--Mac Lane property and propagation. -/
theorem sphereAdamsPage_filtration_zero_subsingleton (r : ℕ) (hr : 1 ≤ r)
    (t : ℕ) (ht : t ≠ 0) :
    Subsingleton (adamsPage H.unit SphereSpectrum r hr 0 t) := by
  have hone : Subsingleton (adamsPage H.unit SphereSpectrum 1 (by decide) 0 t) :=
    sphereAdamsPageOne_filtration_zero_subsingleton H t (by exact_mod_cast ht)
  exact adamsPage_subsingleton_of_le H.unit SphereSpectrum 1 r (by decide) hr hr 0 t hone

/-- The same filtration-zero vanishing on the internal quotient pages. -/
theorem sphereAdamsInternal_filtration_zero_subsingleton (r : ℤ)
    (t : ℕ) (ht : t ≠ 0) :
    Subsingleton ((adamsTowerInternalSpectralSequence H.unit SphereSpectrum).Page r (0, t)) := by
  haveI := sphereAdamsPage_filtration_zero_subsingleton H ((r - 2).toNat + 2)
    (by omega) t ht
  exact (adamsTowerSSDataPageIso H.unit SphereSpectrum 0 t (r - 2).toNat).toLinearEquiv.injective.subsingleton

end
end KIP126.Classical.Adams
