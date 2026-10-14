module

public import KIP126.Def.SpectralSequence.Basic.Proofs
public import KIP126.Def.SpectralSequence.Computation.State.Predicates
public import KIP126.Def.SpectralSequence.ModuleSubobject.Proofs

@[expose] public section

/-! Local stabilization and common representatives at infinity. Neither
permanent-cycle membership nor finite-page reachability asserts nonvanishing. -/

namespace KIP126.Core.SpectralSequence

open CategoryTheory CategoryTheory.Limits

universe u v
variable {R : Type u} [Ring R]

/-- Two infinite-cycle representatives with the same class on one page
have the same class at infinity: their difference is already a boundary. -/
theorem SSData.infinity_projection_eq_of_page_projection_eq
    (D : SSData (ModuleCat.{v} R)) (n : WithTop ℕ)
    (z z' : (Subobject.underlying.obj (D.Z ⊤) : ModuleCat R))
    (h : (Subobject.ofLE _ _ (D.Z_anti le_top) ≫ D.pageπ n) z =
      (Subobject.ofLE _ _ (D.Z_anti le_top) ≫ D.pageπ n) z') :
    D.pageπ ⊤ z = D.pageπ ⊤ z' := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply (subobject_cokernel_π_eq_zero_iff (D.B ⊤) (D.Z ⊤) (D.B_le_Z ⊤) _).mpr
  have hz : D.pageπ n ((Subobject.ofLE _ _ (D.Z_anti le_top)) (z - z')) = 0 := by
    change (Subobject.ofLE _ _ (D.Z_anti le_top) ≫ D.pageπ n) (z - z') = 0
    rw [map_sub, h, sub_self]
  have hb := (subobject_cokernel_π_eq_zero_iff (D.B n) (D.Z n) (D.B_le_Z n) _).mp hz
  have heq : (D.Z n).arrow ((Subobject.ofLE _ _ (D.Z_anti le_top)) (z - z')) =
      (D.Z ⊤).arrow (z - z') :=
    ConcreteCategory.congr_hom (Subobject.ofLE_arrow (D.Z_anti le_top)) _
  rw [heq] at hb
  exact (ModuleCat.subobjectModule D.V).monotone (D.B_mono le_top) hb

/-- A common representative on a finite page is permanent when the later
outgoing differentials vanish at its grading. It may still be a boundary. -/
theorem isPermanentCycle_of_reachesPage
    (E : SpectralSequence (ModuleCat.{v} R) (ℤ × ℤ))
    (N : ℤ) (hN : E.r₀ ≤ N) (p : ℤ × ℤ) (x : E.Page 2 p)
    (hx : ReachesPage E N p x)
    (hout : ∀ r : ℤ, N ≤ r → E.d r p = 0) :
    IsPermanentCycle E p x := by
  obtain ⟨xr, hN2, z, hz, _⟩ := hx
  let D := E.ssData p
  let n : WithTop ℕ := ↑(N - E.r₀).toNat
  have hZ : D.Z ⊤ = D.Z n := cycles_top_eq_of_d_eq_zero E N hN p hout
  let zInf := (Subobject.ofLE (D.Z n) (D.Z ⊤) hZ.ge) z
  refine ⟨zInf, ?_⟩
  change (Subobject.ofLE _ _ (D.Z_anti le_top) ≫ D.pageπ _)
    ((Subobject.ofLE (D.Z n) (D.Z ⊤) hZ.ge) z) = x
  rw [← CategoryTheory.comp_apply, ← Category.assoc, Subobject.ofLE_comp_ofLE]
  exact hz

/-- Nonzero survival on a finite page persists at infinity when both later
outgoing and incoming differentials vanish at this grading. -/
theorem nonzeroSurvival_of_survivesTo
    (E : SpectralSequence (ModuleCat.{v} R) (ℤ × ℤ))
    (N : ℤ) (hN : E.r₀ ≤ N) (p : ℤ × ℤ) (x : E.Page 2 p)
    (hx : SurvivesTo E N p x)
    (hout : ∀ r : ℤ, N ≤ r → E.d r p = 0)
    (hin : ∀ r : ℤ, N ≤ r → E.d r (p - E.diffDeg r) = 0) :
    NonzeroSurvival E p x := by
  obtain ⟨xr, ⟨hN2, z, hz, hzr⟩, hne⟩ := hx
  let D := E.ssData p
  let n : WithTop ℕ := ↑(N - E.r₀).toNat
  have hZ : D.Z ⊤ = D.Z n := cycles_top_eq_of_d_eq_zero E N hN p hout
  have hB : D.B ⊤ = D.B n := boundaries_top_eq_of_d_eq_zero E N hN p hin
  let zInf := (Subobject.ofLE (D.Z n) (D.Z ⊤) hZ.ge) z
  refine ⟨zInf, ?_, ?_⟩
  · change (Subobject.ofLE _ _ (D.Z_anti le_top) ≫ D.pageπ _)
      ((Subobject.ofLE (D.Z n) (D.Z ⊤) hZ.ge) z) = x
    rw [← CategoryTheory.comp_apply, ← Category.assoc, Subobject.ofLE_comp_ofLE]
    exact hz
  · intro hzero
    apply hne
    rw [← hzr]
    apply (subobject_cokernel_π_eq_zero_iff (D.B n) (D.Z n) (D.B_le_Z n) z).mpr
    have hb := (subobject_cokernel_π_eq_zero_iff (D.B ⊤) (D.Z ⊤)
      (D.B_le_Z ⊤) zInf).mp hzero
    have heq : (D.Z ⊤).arrow zInf = (D.Z n).arrow z :=
      ConcreteCategory.congr_hom (Subobject.ofLE_arrow hZ.ge) z
    rwa [heq, hB] at hb

end KIP126.Core.SpectralSequence
