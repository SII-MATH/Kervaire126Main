module

public import KIP126.Def.ClassicalAdams.TowerHomology.Data
public import KIP126.Def.StableHomotopy.Cohomology.Multiplication.Action.Proofs

@[expose] public section

/-! Derived coefficient-homology descriptions of the actual Adams tower.
Tensor exactness and a multiplication are explicit structural arguments;
no global instance, Milnor coordinates, or independently chosen pages are supplied. -/

namespace KIP126.Classical.Adams

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Pretriangulated
  KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology

universe u v

set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  (H : Mod2EilenbergMacLane (C := C))
  [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]

omit [HasFunctorialCofiber (C := C)] [(tensorLeft H.HF2).CommShift ℤ]
    [(tensorLeft H.HF2).IsTriangulated] in
/-- Multiplication retracts the unit on coefficient homology. -/
theorem adamsHomologyAction_unit (R : Mod2RingStructure H) (X : C) (n : ℤ)
    (x : Mod2Homology H n X) :
    adamsHomologyAction H R X n (adamsHomologyUnit H X n x) = x := by
  change (x ≫ _) ≫ _ = x
  rw [Category.assoc, mod2FreeAction_unit, Category.comp_id]

omit [HasFunctorialCofiber (C := C)] [(tensorLeft H.HF2).CommShift ℤ]
    [(tensorLeft H.HF2).IsTriangulated] in
/-- The unit-induced coefficient map is split injective. -/
theorem adamsHomologyUnit_injective (R : Mod2RingStructure H) (X : C) (n : ℤ) :
    Function.Injective (adamsHomologyUnit H X n) :=
  Function.LeftInverse.injective (adamsHomologyAction_unit H R X n)

/-- Exactness at the middle coefficient group, derived from the distinguished triangle. -/
theorem adamsHomologyBoundary_exact (X : C) (n : ℤ)
    (x : Mod2Homology H n (H.HF2 ⊗ X)) :
    adamsHomologyBoundary H X n x = 0 ↔ ∃ y, adamsHomologyUnit H X n y = x :=
  les_homotopy_exact_g (adamsHomologySequence H X) n x

/-- The boundary is onto because the preceding tower map is killed by `H ⊗ -`. -/
theorem adamsHomologyBoundary_surjective (R : Mod2RingStructure H) (X : C) (n : ℤ) :
    Function.Surjective (adamsHomologyBoundary H X n) := by
  intro y
  apply (lesHomotopyExactH (adamsHomologySequence H X) n y).mp
  change y ≫ (H.HF2 ◁ fiberι (adamsUnit H.unit X)) = 0
  rw [mod2_fiberι_eq_zero H R, Limits.comp_zero]

/-- The unit image is killed by the boundary. -/
theorem adamsHomologyBoundary_unit (X : C) (n : ℤ) (x : Mod2Homology H n X) :
    adamsHomologyBoundary H X n (adamsHomologyUnit H X n x) = 0 :=
  (adamsHomologyBoundary_exact H X n _).mpr ⟨x, rfl⟩

/-- The boundary kernel is exactly the unit image. -/
theorem adamsHomologyBoundary_ker (X : C) (n : ℤ) :
    LinearMap.ker (adamsHomologyBoundary H X n) = LinearMap.range (adamsHomologyUnit H X n) := by
  ext x
  exact adamsHomologyBoundary_exact H X n x

/-- Restricting the boundary to the action kernel gives a bijection.
For surjectivity subtract the unit of the action from any boundary lift. -/
theorem adamsHomologyBoundary_ker_action_bijective (R : Mod2RingStructure H) (X : C) (n : ℤ) :
    Function.Bijective ((adamsHomologyBoundary H X n).domRestrict
      (LinearMap.ker (adamsHomologyAction H R X n))) := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    apply sub_eq_zero.mp
    have hzero : adamsHomologyBoundary H X n (x.val - y.val) = 0 := by
      rw [map_sub]
      change adamsHomologyBoundary H X n x.val = adamsHomologyBoundary H X n y.val at hxy
      rw [hxy, sub_self]
    obtain ⟨z, hz⟩ := (adamsHomologyBoundary_exact H X n _).mp hzero
    have hz0 : z = 0 := by
      calc
        z = adamsHomologyAction H R X n (adamsHomologyUnit H X n z) :=
          (adamsHomologyAction_unit H R X n z).symm
        _ = adamsHomologyAction H R X n (x.val - y.val) := congrArg _ hz
        _ = 0 := by rw [map_sub, x.property, y.property, sub_self]
    simpa only [hz0, map_zero] using hz.symm
  · intro y
    obtain ⟨z, hz⟩ := adamsHomologyBoundary_surjective H R X n y
    refine ⟨⟨z - adamsHomologyUnit H X n (adamsHomologyAction H R X n z), ?_⟩, ?_⟩
    · change adamsHomologyAction H R X n (_ - _) = 0
      rw [map_sub, adamsHomologyAction_unit, sub_self]
    · change adamsHomologyBoundary H X n (_ - _) = _
      rw [map_sub, adamsHomologyBoundary_unit, sub_zero, hz]

omit [HasFunctorialCofiber (C := C)] [(tensorLeft H.HF2).CommShift ℤ]
    [(tensorLeft H.HF2).IsTriangulated] in
/-- On the sphere, the free action identifies with cooperation multiplication. -/
theorem adamsHomologyAction_sphere (R : Mod2RingStructure H) :
    mod2FreeAction H R (SphereSpectrum : C) ≫ (ρ_ H.HF2).hom =
      H.HF2 ◁ (ρ_ H.HF2).hom ≫ R.monoid.mul := by
  rw [mod2FreeAction, Category.assoc, rightUnitor_naturality,
    rightUnitor_tensor_hom]
  simp

omit [HasFunctorialCofiber (C := C)] [(tensorLeft H.HF2).CommShift ℤ]
    [(tensorLeft H.HF2).IsTriangulated] in
/-- A class lies in the action kernel exactly when its cooperation image has zero counit. -/
theorem sphereCoefficientHomologyEquiv_ker (R : Mod2RingStructure H) (n : ℤ)
    (x : Mod2Homology H n (H.HF2 ⊗ SphereSpectrum)) :
    adamsHomologyAction H R SphereSpectrum n x = 0 ↔
      cooperationCounit H R n (sphereCoefficientHomologyEquiv H n x) = 0 := by
  change x ≫ mod2FreeAction H R SphereSpectrum = 0 ↔
    (x ≫ H.HF2 ◁ (ρ_ H.HF2).hom) ≫ R.monoid.mul = 0
  rw [← cancel_mono (ρ_ H.HF2).hom]
  simp only [Category.assoc, adamsHomologyAction_sphere, Limits.zero_comp]

omit [HasFunctorialCofiber (C := C)] [(tensorLeft H.HF2).CommShift ℤ]
    [(tensorLeft H.HF2).IsTriangulated] in
/-- The right unitor identifies the action kernel with the cooperation counit kernel. -/
theorem sphereCoefficientHomologyEquiv_map_ker (R : Mod2RingStructure H) (n : ℤ) :
    (LinearMap.ker (adamsHomologyAction H R SphereSpectrum n)).map
      (sphereCoefficientHomologyEquiv H n).toLinearMap =
        LinearMap.ker (cooperationCounit H R n).toIntLinearMap := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (sphereCoefficientHomologyEquiv_ker H R n x).mp hx
  · intro hz
    change cooperationCounit H R n z = 0 at hz
    refine ⟨(sphereCoefficientHomologyEquiv H n).symm z, ?_,
      (sphereCoefficientHomologyEquiv H n).apply_symm_apply z⟩
    apply (sphereCoefficientHomologyEquiv_ker H R n _).mpr
    simpa using hz

end

end KIP126.Classical.Adams
