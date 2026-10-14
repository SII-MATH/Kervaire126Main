module

import all KIP126.Def.SpectralSequence.FilteredDifferential.SquareZero
import all KIP126.Def.SpectralSequence.FilteredDifferential.Cycles
import all KIP126.Def.SpectralSequence.FilteredDifferential.Boundaries

import all KIP126.Def.SpectralSequence.FilteredDifferential.Data

@[expose] section

/-! Proofs for the canonical filtered-complex page differential. -/

namespace KIP126.Core.SpectralSequence.FilteredComplex

open CategoryTheory CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Compute the canonical page differential on a cycle-kernel representative.
If its actual differential is represented by `v` in the target filtration,
the differential of its page class is the page class of `v`. -/
theorem pageDifferential_on_cycle_kernel (FC : FilteredComplex C)
    (s k : ℤ) (n : ℕ) :
    let f := (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1) ≫
      cokernel.π ((FC.filtration.F (s + ↑n) (k - 1)).arrow)
    let g := (FC.filtration.F (s + ↑n) (k - 1)).arrow ≫
      FC.complex.d (k - 1) (k - 1 - 1) ≫
      cokernel.π ((FC.filtration.F (s + ↑n + ↑n) (k - 1 - 1)).arrow)
    let K := kernelSubobject f
    let K' := kernelSubobject g
    ∀ {T : C} (u : T ⟶ Subobject.underlying.obj K)
      (v : T ⟶ Subobject.underlying.obj (FC.filtration.F (s + ↑n) (k - 1)))
      (_hv : u ≫ K.arrow ≫ (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1) =
        v ≫ (FC.filtration.F (s + ↑n) (k - 1)).arrow)
      (hvg : v ≫ g = 0),
      (u ≫ factorThruImageSubobject
        (K.arrow ≫ FC.filtration.toAssociatedGraded s k)) ≫
          FC.pageπ s k (↑n) ≫ FC.pageDifferential s k n =
        (factorThruKernelSubobject g v hvg ≫
          factorThruImageSubobject
            (K'.arrow ≫ FC.filtration.toAssociatedGraded (s + ↑n) (k - 1))) ≫
          FC.pageπ (s + ↑n) (k - 1) (↑n) := by
  dsimp only
  intro T u v hv hvg
  unfold FilteredComplex.pageDifferential
  simp only [Category.assoc]
  erw [cokernel.π_desc, Abelian.comp_epiDesc]
  let f := (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1) ≫
    cokernel.π ((FC.filtration.F (s + ↑n) (k - 1)).arrow)
  let g := (FC.filtration.F (s + ↑n) (k - 1)).arrow ≫
    FC.complex.d (k - 1) (k - 1 - 1) ≫
    cokernel.π ((FC.filtration.F (s + ↑n + ↑n) (k - 1 - 1)).arrow)
  let K := kernelSubobject f
  let K' := kernelSubobject g
  have hfactor : (K.arrow ≫ (FC.filtration.F s k).arrow ≫
      FC.complex.d k (k - 1)) ≫
      cokernel.π ((FC.filtration.F (s + ↑n) (k - 1)).arrow) = 0 := by
    simpa only [f, Category.assoc] using kernelSubobject_arrow_comp f
  let lift_n := Abelian.monoLift (FC.filtration.F (s + ↑n) (k - 1)).arrow
    (K.arrow ≫ (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1)) hfactor
  have hcycle : lift_n ≫ g = 0 := by
    calc
      lift_n ≫ g =
          ((lift_n ≫ (FC.filtration.F (s + ↑n) (k - 1)).arrow) ≫
            FC.complex.d (k - 1) (k - 1 - 1)) ≫
              cokernel.π ((FC.filtration.F (s + ↑n + ↑n) (k - 1 - 1)).arrow) := by
                simp only [g, Category.assoc]
      _ = ((K.arrow ≫ (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1)) ≫
            FC.complex.d (k - 1) (k - 1 - 1)) ≫
              cokernel.π ((FC.filtration.F (s + ↑n + ↑n) (k - 1 - 1)).arrow) := by
                rw [Abelian.monoLift_comp]
      _ = 0 := by
        simp only [Category.assoc, FC.complex.d_comp_d, comp_zero, zero_comp]
  have hlift : u ≫ lift_n = v := by
    apply (cancel_mono (FC.filtration.F (s + ↑n) (k - 1)).arrow).mp
    rw [Category.assoc, Abelian.monoLift_comp]
    exact hv
  have hker : u ≫ factorThruKernelSubobject g lift_n hcycle =
      factorThruKernelSubobject g v hvg := by
    apply (cancel_mono K'.arrow).mp
    calc
      (u ≫ factorThruKernelSubobject g lift_n hcycle) ≫ K'.arrow =
          u ≫ lift_n := by
            rw [Category.assoc, factorThruKernelSubobject_comp_arrow]
      _ = v := hlift
      _ = factorThruKernelSubobject g v hvg ≫ K'.arrow := by
            rw [factorThruKernelSubobject_comp_arrow]
  simpa only [Category.assoc, FilteredComplex.pageπ] using
    congrArg (fun z : T ⟶ Subobject.underlying.obj K' =>
      z ≫ factorThruImageSubobject
        (K'.arrow ≫ FC.filtration.toAssociatedGraded (s + ↑n) (k - 1)) ≫
        FC.pageπ (s + ↑n) (k - 1) (↑n)) hker

/-- A strict filtered differential equation produces compatible source and
target cycle representatives whose quotient classes satisfy the canonical
page differential relation. -/
theorem pageDifferential_of_strict_lifts (FC : FilteredComplex C)
    (s k : ℤ) (n : ℕ) {T : C}
    (xl : T ⟶ Subobject.underlying.obj (FC.filtration.F s k))
    (yl : T ⟶ Subobject.underlying.obj (FC.filtration.F (s + ↑n) (k - 1)))
    (hd : xl ≫ (FC.differential_preserves s k).choose =
      yl ≫ FC.filtration.inclusion (by omega) (k - 1)) :
    ∃ (zx : T ⟶ Subobject.underlying.obj (FC.cycleSubobject s k (↑n)))
      (zy : T ⟶ Subobject.underlying.obj
        (FC.cycleSubobject (s + ↑n) (k - 1) (↑n))),
      zx ≫ (FC.cycleSubobject s k (↑n)).arrow =
        xl ≫ FC.filtration.toAssociatedGraded s k ∧
      zy ≫ (FC.cycleSubobject (s + ↑n) (k - 1) (↑n)).arrow =
        yl ≫ FC.filtration.toAssociatedGraded (s + ↑n) (k - 1) ∧
      zx ≫ FC.pageπ s k (↑n) ≫ FC.pageDifferential s k n =
        zy ≫ FC.pageπ (s + ↑n) (k - 1) (↑n) := by
  let f := (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1) ≫
    cokernel.π ((FC.filtration.F (s + ↑n) (k - 1)).arrow)
  let g := (FC.filtration.F (s + ↑n) (k - 1)).arrow ≫
    FC.complex.d (k - 1) (k - 1 - 1) ≫
    cokernel.π ((FC.filtration.F (s + ↑n + ↑n) (k - 1 - 1)).arrow)
  let K := kernelSubobject f
  let K' := kernelSubobject g
  have hamb : xl ≫ (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1) =
      yl ≫ (FC.filtration.F (s + ↑n) (k - 1)).arrow := by
    calc
      xl ≫ (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1) =
          xl ≫ (FC.differential_preserves s k).choose ≫
            (FC.filtration.F s (k - 1)).arrow := by
              simpa only [Category.assoc] using
                congrArg (fun q => xl ≫ q)
                  (FC.differential_preserves s k).choose_spec.symm
      _ = yl ≫ FC.filtration.inclusion (by omega) (k - 1) ≫
            (FC.filtration.F s (k - 1)).arrow := by
              simpa only [Category.assoc] using
                congrArg (fun q => q ≫ (FC.filtration.F s (k - 1)).arrow) hd
      _ = yl ≫ (FC.filtration.F (s + ↑n) (k - 1)).arrow := by
        simpa only [Category.assoc] using
          congrArg (fun q => yl ≫ q)
            (FC.filtration.inclusion_arrow (by omega) (k - 1))
  have hxl0 : xl ≫ f = 0 := by
    calc
      xl ≫ f =
          (xl ≫ (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1)) ≫
            cokernel.π ((FC.filtration.F (s + ↑n) (k - 1)).arrow) := by
              simp only [f, Category.assoc]
      _ = (yl ≫ (FC.filtration.F (s + ↑n) (k - 1)).arrow) ≫
            cokernel.π ((FC.filtration.F (s + ↑n) (k - 1)).arrow) := by rw [hamb]
      _ = 0 := by rw [Category.assoc, cokernel.condition, comp_zero]
  have hyl0 : yl ≫ g = 0 := by
    calc
      yl ≫ g =
          ((yl ≫ (FC.filtration.F (s + ↑n) (k - 1)).arrow) ≫
            FC.complex.d (k - 1) (k - 1 - 1)) ≫
              cokernel.π ((FC.filtration.F (s + ↑n + ↑n) (k - 1 - 1)).arrow) := by
                simp only [g, Category.assoc]
      _ = ((xl ≫ (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1)) ≫
            FC.complex.d (k - 1) (k - 1 - 1)) ≫
              cokernel.π ((FC.filtration.F (s + ↑n + ↑n) (k - 1 - 1)).arrow) := by
                rw [hamb]
      _ = 0 := by
        simp only [Category.assoc, FC.complex.d_comp_d, comp_zero, zero_comp]
  let u := factorThruKernelSubobject f xl hxl0
  let v := factorThruKernelSubobject g yl hyl0
  let zx := u ≫ factorThruImageSubobject
    (K.arrow ≫ FC.filtration.toAssociatedGraded s k)
  let zy := v ≫ factorThruImageSubobject
    (K'.arrow ≫ FC.filtration.toAssociatedGraded (s + ↑n) (k - 1))
  refine ⟨zx, zy, ?_, ?_, ?_⟩
  · change zx ≫
      (imageSubobject (K.arrow ≫ FC.filtration.toAssociatedGraded s k)).arrow = _
    simp only [zx, Category.assoc, imageSubobject_arrow_comp]
    simpa only [Category.assoc] using
      congrArg (fun q => q ≫ FC.filtration.toAssociatedGraded s k)
        (factorThruKernelSubobject_comp_arrow f xl hxl0)
  · change zy ≫ (imageSubobject
      (K'.arrow ≫ FC.filtration.toAssociatedGraded (s + ↑n) (k - 1))).arrow = _
    simp only [zy, Category.assoc, imageSubobject_arrow_comp]
    simpa only [Category.assoc] using
      congrArg (fun q => q ≫ FC.filtration.toAssociatedGraded (s + ↑n) (k - 1))
        (factorThruKernelSubobject_comp_arrow g yl hyl0)
  · have hv : u ≫ K.arrow ≫ (FC.filtration.F s k).arrow ≫
        FC.complex.d k (k - 1) =
        yl ≫ (FC.filtration.F (s + ↑n) (k - 1)).arrow := by
      calc
        u ≫ K.arrow ≫ (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1) =
            xl ≫ (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1) := by
              simpa only [Category.assoc] using
                congrArg (fun q => q ≫ (FC.filtration.F s k).arrow ≫
                  FC.complex.d k (k - 1))
                  (factorThruKernelSubobject_comp_arrow f xl hxl0)
        _ = yl ≫ (FC.filtration.F (s + ↑n) (k - 1)).arrow := hamb
    exact FC.pageDifferential_on_cycle_kernel s k n u yl hv hyl0

end KIP126.Core.SpectralSequence.FilteredComplex
