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

/-- Every possible source of an incoming differential to bidegree `(2,128)`
is zero: filtration zero for `r=2`, negative filtration for `r>2`. -/
theorem sphereAdamsInternal_h6_incoming_source_subsingleton (r : ℤ) (hr : 2 ≤ r) :
    Subsingleton ((adamsTowerInternalSpectralSequence H.unit SphereSpectrum).Page r
      ((2, 128) - (adamsTowerInternalSpectralSequence H.unit SphereSpectrum).diffDeg r)) := by
  have hdeg : ((2, 128) : ℤ × ℤ) -
      (adamsTowerInternalSpectralSequence H.unit SphereSpectrum).diffDeg r =
        (2 - r, 129 - r) := by
    change ((2, 128) : ℤ × ℤ) - (r, r - 1) = _
    apply Prod.ext <;> dsimp
    omega
  rw [hdeg]
  by_cases h : r = 2
  · subst r
    exact sphereAdamsInternal_filtration_zero_subsingleton H 2 127 (by decide)
  · exact adamsTowerInternal_page_subsingleton_of_negative H.unit SphereSpectrum
      r (2 - r) (129 - r) (by omega)

/-- No page differential can hit bidegree `(2,128)` in the internal sphere tower.
This says nothing yet about the outgoing differentials of its classes. -/
theorem sphereAdamsInternal_h6_incoming_d_eq_zero (r : ℤ) (hr : 2 ≤ r) :
    (adamsTowerInternalSpectralSequence H.unit SphereSpectrum).d r
      ((2, 128) - (adamsTowerInternalSpectralSequence H.unit SphereSpectrum).diffDeg r) = 0 := by
  haveI := sphereAdamsInternal_h6_incoming_source_subsingleton H r hr
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hx : x = 0 := Subsingleton.elim _ _
  simp only [hx, map_zero]

/-- The raw tower quotient has the same zero incoming source. -/
theorem sphereAdamsPage_h6_incoming_source_subsingleton (r : ℕ) (hr : 2 ≤ r) :
    Subsingleton (adamsPage H.unit SphereSpectrum r (by omega)
      (2 - r) (129 - r)) := by
  by_cases h : r = 2
  · subst r
    exact sphereAdamsPage_filtration_zero_subsingleton H 2 (by decide) 127 (by decide)
  · exact adamsPage_subsingleton_of_negative H.unit SphereSpectrum r (by omega)
      (2 - r) (129 - r) (by omega)

/-- There are no new boundaries at `(2,128)` after the second page. -/
theorem sphereAdams_h6_boundaries_succ (r : ℕ) (hr : 2 ≤ r) :
    adamsBoundaries H.unit SphereSpectrum (r + 1) (by omega) 2 128 =
      adamsBoundaries H.unit SphereSpectrum r (by omega) 2 128 := by
  have h := adamsBoundaries_succ_eq_of_source_subsingleton H.unit SphereSpectrum
    r (by omega) (2 - r) (129 - r)
    (sphereAdamsPage_h6_incoming_source_subsingleton H r hr)
  have hs : (2 : ℤ) - r + r = 2 := by omega
  have ht : (129 : ℤ) - r + r - 1 = 128 := by omega
  exact hs ▸ ht ▸ h

/-- All finite boundary submodules at the target already occur on page two. -/
theorem sphereAdams_h6_boundaries_eq_two (n : ℕ) :
    adamsBoundaries H.unit SphereSpectrum (n + 2) (by omega) 2 128 =
      adamsBoundaries H.unit SphereSpectrum 2 (by decide) 2 128 := by
  induction n with
  | zero => rfl
  | succ n ih => exact (sphereAdams_h6_boundaries_succ H (n + 2) (by omega)).trans ih

/-- At the h₆² bidegree, initial nonvanishing and liftability through all tower
stages suffice. No separate higher-page nonboundary hypothesis remains. -/
theorem sphereAdams_h6_nonzeroSurvival_iff
    (x : (adamsTowerInternalSpectralSequence H.unit SphereSpectrum).Page 2 (2, 128)) :
    NonzeroSurvival (adamsTowerInternalSpectralSequence H.unit SphereSpectrum) (2, 128) x ↔
      x ≠ 0 ∧ ∃ z : adamsCycleAmbient H.unit SphereSpectrum 2 128,
        (∀ n : ℕ, z.val ∈ adamsCycles H.unit SphereSpectrum (n + 2) (by omega) 2 128) ∧
        (adamsCycleBoundaries H.unit SphereSpectrum 2 (by decide) 2 128).mkQ z =
          (adamsTowerSSDataPageIso H.unit SphereSpectrum 2 128 0).hom x := by
  rw [adamsTower_nonzeroSurvival_iff]
  constructor
  · rintro ⟨z, hz, hb, hx⟩
    refine ⟨?_, z, hz, hx⟩
    intro hx0
    have hq := adamsPage_mk_eq_zero H.unit SphereSpectrum 2 (by decide) 2 128 z
    apply hb 0
    apply hq.mp
    rw [hx, hx0, map_zero]
  · rintro ⟨hne, z, hz, hx⟩
    refine ⟨z, hz, ?_, hx⟩
    intro n hn
    rw [sphereAdams_h6_boundaries_eq_two H n] at hn
    have hq := adamsPage_mk_eq_zero H.unit SphereSpectrum 2 (by decide) 2 128 z
    exact hne ((adamsTowerSSDataPageIso H.unit SphereSpectrum 2 128 0).toLinearEquiv.map_eq_zero_iff.mp
      (hx.symm.trans (hq.mpr hn)))

end
end KIP126.Classical.Adams
