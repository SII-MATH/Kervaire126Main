module

public import KIP126.Def.Algebra.SimplicialModule.Kan.Proofs
public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex
public import Mathlib.Tactic.FinCases

@[expose] public section

namespace KIP126.Algebra.SimplicialModule

open CategoryTheory Simplicial Opposite

universe u
variable {R : Type u} [Ring R] (A : SimplicialObject (ModuleCat.{u} R))

set_option backward.isDefEq.respectTransparency false

/-- The actual underlying simplicial set of a simplicial module satisfies
all Kan horn-filling conditions, by explicit degeneracy corrections. -/
theorem underlying_isKanComplex : SSet.KanComplex (A ⋙ forget (ModuleCat R)) := by
  classical
  apply SSet.KanComplex.iff.mpr
  intro n k f hf
  cases n with
  | zero =>
    let q : Fin 2 := ⟨1 - k.val,by omega⟩
    have hq : q ≠ k := by
      intro h
      have he := congrArg Fin.val h
      change 1 - k.val = k.val at he
      omega
    let y := (A.σ (0 : Fin 1)).hom (SSet.yonedaEquiv (f q hq))
    refine ⟨SSet.yonedaEquiv.symm y, ?_⟩
    intro j hj
    have hjq : j = q := by
      apply Fin.ext
      have hne : j.val ≠ k.val := fun h => hj (Fin.ext h)
      change j.val = 1 - k.val
      omega
    subst j
    apply SSet.yonedaEquiv.injective
    simp only [CosimplicialObject.δ]
    rw [← SSet.yonedaEquiv_naturality, Equiv.apply_symm_apply]
    change (A.δ q).hom ((A.σ (0 : Fin 1)).hom _) = _
    have h : A.σ (0 : Fin 1) ≫ A.δ q = 𝟙 _ := by
      by_cases hq0 : q = 0
      · rw [hq0]
        exact A.δ_comp_σ_self
      · have hq1 : q = 1 := by
          apply Fin.ext
          have hne : q.val ≠ 0 := fun h => hq0 (Fin.ext h)
          change q.val = 1
          omega
        rw [hq1]
        exact A.δ_comp_σ_succ
    exact ConcreteCategory.congr_hom h _
  | succ n =>
    let x : Fin (n + 3) → A.obj (op ⦋n + 1⦌) :=
      fun j => if hj : j ≠ k then SSet.yonedaEquiv (f j hj) else 0
    have hx : HornFacesCompatible A k x := by
      intro i j hi hj hij
      have h := congrArg SSet.yonedaEquiv (hf i j hi hj hij)
      simp only [CosimplicialObject.δ] at h
      rw [← SSet.yonedaEquiv_naturality, ← SSet.yonedaEquiv_naturality] at h
      change (A.δ _).hom (SSet.yonedaEquiv (f i hi)) =
        (A.δ _).hom (SSet.yonedaEquiv (f j hj)) at h
      simpa only [x,dif_pos hi,dif_pos hj] using h
    obtain ⟨y,hy⟩ := horn_faces_fill A hx
    refine ⟨SSet.yonedaEquiv.symm y, ?_⟩
    intro j hj
    apply SSet.yonedaEquiv.injective
    simp only [CosimplicialObject.δ]
    rw [← SSet.yonedaEquiv_naturality, Equiv.apply_symm_apply]
    change (A.δ j).hom y = _
    simpa only [x,dif_pos hj] using hy j hj

end KIP126.Algebra.SimplicialModule
