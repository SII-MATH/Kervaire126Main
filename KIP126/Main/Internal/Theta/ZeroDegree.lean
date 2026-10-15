module
public import KIP126.Def.Computation.Table.Archive
/-! The one-dimensional degree-zero calculation of the original
Main/Solution/Computation/LowDegrees.lean:72–107, bbac1fc05843 (MIT). -/
@[expose] section
namespace KIP126.Main.Internal.Theta
open KIP126.AdamsSynthetic.Standard KIP126.Computation.Standard
noncomputable section
set_option backward.isDefEq.respectTransparency false
private theorem zero_nonzero_unique :
    ∀ x y : model.classical.sphere.Page 2 (0,0), x≠0 → y≠0 → x=y := by
  classical
  have hd : archive.basisCount 0 0=1 := KIP126.Computation.Table.archive_dimension 0 0 (by decide)
  let e : model.classical.sphere.Page 2 (0,0) ≃ₗ[ℤ] (Fin 1 →₀ ZMod 2) :=
    Eq.mp (congrArg (fun n => model.classical.sphere.Page 2 (0,0) ≃ₗ[ℤ] (Fin n →₀ ZMod 2)) hd)
      (coordinates 0 0 (by decide))
  have hc (x : model.classical.sphere.Page 2 (0,0)) (hx : x≠0) : e x 0=1 := by
    generalize h:e x 0=c
    fin_cases c
    · exfalso
      apply hx
      apply e.injective
      rw [map_zero]
      apply Finsupp.ext
      intro i
      fin_cases i
      exact h
    · rfl
  intro x y hx hy
  apply e.injective
  apply Finsupp.ext
  intro i
  fin_cases i
  exact (hc x hx).trans (hc y hy).symm
end
end KIP126.Main.Internal.Theta
