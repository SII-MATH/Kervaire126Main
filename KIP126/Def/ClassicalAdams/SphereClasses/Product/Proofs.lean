module

public import KIP126.Def.ClassicalAdams.SphereClasses.Product.Predicates
public import KIP126.Def.ClassicalAdams.MilnorCohomology.Multiplication.Proofs

@[expose] public section


/-! Equality transport, the defining cobar formula, and linearity of the internal E₂ product. -/
namespace KIP126.Classical.Adams.Sphere.Internal
open CategoryTheory
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
universe u v
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  (H : Mod2EilenbergMacLane (C := C)) (M : MilnorCooperations H)

/-- Equality transport commutes with the canonical comparison of the same pages. -/
theorem reindex_comparison {s t s' t' : ℕ} (hs : s = s') (ht : t = t')
    (x : MilnorCohomology.Cohomology H M s t) :
    reindex H hs ht (MilnorCohomology.comparison H M s t x) =
      MilnorCohomology.comparison H M s' t'
        (MilnorCohomology.cohomologyReindex H M hs ht x) := by
  subst s'
  subst t'
  rfl

/-- The transported product of two cobar classes is their cobar cup product. -/
theorem product_comparison {s t s' t' : ℕ}
    (x : MilnorCohomology.Cohomology H M s t)
    (y : MilnorCohomology.Cohomology H M s' t') :
    product H M (MilnorCohomology.comparison H M s t x)
      (MilnorCohomology.comparison H M s' t' y) =
      MilnorCohomology.comparison H M (s + s') (t + t')
        (MilnorCohomology.cup H M x y) := by
  unfold product
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]

theorem product_add_right {s t s' t' : ℕ}
    (x : (adamsTowerInternalSpectralSequence H.unit SphereSpectrum).Page 2 (s,t))
    (y z : (adamsTowerInternalSpectralSequence H.unit SphereSpectrum).Page 2 (s',t')) :
    product H M (s := s) (t := t) (s' := s') (t' := t') x (y+z)=product H M (s := s) (t := t) (s' := s') (t' := t') x y+product H M (s := s) (t := t) (s' := s') (t' := t') x z := by
  unfold product
  rw [map_add,map_add,map_add]

theorem product_zsmul_right {s t s' t' : ℕ}
    (x : (adamsTowerInternalSpectralSequence H.unit SphereSpectrum).Page 2 (s,t))
    (y : (adamsTowerInternalSpectralSequence H.unit SphereSpectrum).Page 2 (s',t')) (n : ℤ) :
    product H M (s := s) (t := t) (s' := s') (t' := t') x (n • y)=n • product H M (s := s) (t := t) (s' := s') (t' := t') x y := by
  unfold product
  rw [map_zsmul,map_zsmul,map_zsmul]

end
end KIP126.Classical.Adams.Sphere.Internal
