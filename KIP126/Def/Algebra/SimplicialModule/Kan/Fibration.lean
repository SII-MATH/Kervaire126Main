module

public import KIP126.Def.Algebra.SimplicialModule.Kan.Filling
public import KIP126.Def.Algebra.SimplicialModule.Kernel.Proofs

@[expose] public section

namespace KIP126.Algebra.SimplicialModule

open CategoryTheory CategoryTheory.Limits Simplicial Opposite HomotopicalAlgebra

universe u
variable {R : Type u} [Ring R]

set_option backward.isDefEq.respectTransparency false

/-- Naturality of an actual simplicial module map on a face element. -/
theorem face_naturality_apply {A B : SimplicialObject (ModuleCat.{u} R)} (p : A ⟶ B)
    {n : ℕ} (j : Fin (n + 2)) (y : A.obj (op ⦋n + 1⦌)) :
    (p.app (op ⦋n⦌)).hom ((A.δ j).hom y) =
      (B.δ j).hom ((p.app (op ⦋n + 1⦌)).hom y) :=
  ConcreteCategory.congr_hom (p.naturality (SimplexCategory.δ j).op) y

/-- A degreewise surjection of actual simplicial modules lifts every
compatible horn over a prescribed target simplex. -/
theorem horn_lift_of_degreewise_surjective
    {A B : SimplicialObject (ModuleCat.{u} R)} (p : A ⟶ B)
    (hp : ∀ n : ℕ, Function.Surjective (p.app (op ⦋n⦌)).hom)
    {n : ℕ} {k : Fin (n + 2)}
    (f : ∀ (j : Fin (n + 2)) (_ : j ≠ k), Δ[n] ⟶ A ⋙ forget (ModuleCat R))
    (hf : SSet.horn.IsCompatible f)
    (g : Δ[n + 1] ⟶ B ⋙ forget (ModuleCat R))
    (hg : ∀ j hj, f j hj ≫ Functor.whiskerRight p (forget (ModuleCat R)) =
      SSet.stdSimplex.δ j ≫ g) :
    ∃ φ : Δ[n + 1] ⟶ A ⋙ forget (ModuleCat R),
      (∀ j hj, SSet.stdSimplex.δ j ≫ φ = f j hj) ∧
      φ ≫ Functor.whiskerRight p (forget (ModuleCat R)) = g := by
  classical
  obtain ⟨z,hz⟩ := hp (n + 1) (SSet.yonedaEquiv g)
  let x (j : Fin (n + 2)) (hj : j ≠ k) : A.obj (op ⦋n⦌) := SSet.yonedaEquiv (f j hj)
  have hres (j : Fin (n + 2)) (hj : j ≠ k) :
      (p.app (op ⦋n⦌)).hom (x j hj - (A.δ j).hom z) = 0 := by
    have h := congrArg SSet.yonedaEquiv (hg j hj)
    rw [SSet.yonedaEquiv_comp] at h
    simp only [CosimplicialObject.δ] at h
    rw [← SSet.yonedaEquiv_naturality] at h
    change (p.app (op ⦋n⦌)).hom (SSet.yonedaEquiv (f j hj)) =
      (B.δ j).hom (SSet.yonedaEquiv g) at h
    change (p.app (op ⦋n⦌)).hom (x j hj) = _ at h
    rw [map_sub,face_naturality_apply,hz,h,sub_self]
  choose a ha using (fun j hj => kernel_exists_element p (op ⦋n⦌)
    (x j hj - (A.δ j).hom z) (hres j hj))
  let fK : ∀ (j : Fin (n + 2)) (_ : j ≠ k),
      Δ[n] ⟶ kernel p ⋙ forget (ModuleCat R) :=
    fun j hj => SSet.yonedaEquiv.symm (a j hj)
  have hfK : SSet.horn.IsCompatible fK := by
    cases n with
    | zero => trivial
    | succ n =>
      intro i j hi hj hij
      apply SSet.yonedaEquiv.injective
      simp only [CosimplicialObject.δ]
      rw [← SSet.yonedaEquiv_naturality, ← SSet.yonedaEquiv_naturality]
      simp only [fK,Equiv.apply_symm_apply]
      change ((kernel p).δ _).hom (a i hi) = ((kernel p).δ _).hom (a j hj)
      apply kernel_inclusion_injective p (op ⦋n⦌)
      rw [face_naturality_apply,face_naturality_apply,ha,ha,map_sub,map_sub]
      have hfaces := congrArg SSet.yonedaEquiv (hf i j hi hj hij)
      simp only [CosimplicialObject.δ] at hfaces
      rw [← SSet.yonedaEquiv_naturality, ← SSet.yonedaEquiv_naturality] at hfaces
      change (A.δ _).hom (SSet.yonedaEquiv (f i hi)) =
        (A.δ _).hom (SSet.yonedaEquiv (f j hj)) at hfaces
      change (A.δ _).hom (x i hi) = (A.δ _).hom (x j hj) at hfaces
      rw [hfaces]
      have hij' : (i.castPred (Fin.ne_last_of_lt hij)).castSucc < j := by simpa using hij
      have hzfaces := ConcreteCategory.congr_hom (A.δ_comp_δ' hij') z
      change (A.δ (i.castPred _)).hom ((A.δ j).hom z) =
        (A.δ (j.pred _)).hom ((A.δ (i.castPred _).castSucc).hom z) at hzfaces
      simpa only [Fin.castSucc_castPred, hzfaces]
  letI : SSet.KanComplex (kernel p ⋙ forget (ModuleCat R)) := underlying_isKanComplex (kernel p)
  obtain ⟨ψ,hψ⟩ := hfK.exists_lift_of_kanComplex
  let v : (kernel p).obj (op ⦋n + 1⦌) := SSet.yonedaEquiv ψ
  let y : A.obj (op ⦋n + 1⦌) := z + ((kernel.ι p).app (op ⦋n + 1⦌)).hom v
  refine ⟨SSet.yonedaEquiv.symm y, ?_, ?_⟩
  · intro j hj
    apply SSet.yonedaEquiv.injective
    simp only [CosimplicialObject.δ]
    rw [← SSet.yonedaEquiv_naturality,Equiv.apply_symm_apply]
    change (A.δ j).hom y = _
    have h := congrArg SSet.yonedaEquiv (hψ j hj)
    simp only [CosimplicialObject.δ] at h
    rw [← SSet.yonedaEquiv_naturality] at h
    simp only [fK,Equiv.apply_symm_apply] at h
    change ((kernel p).δ j).hom v = a j hj at h
    dsimp only [y]
    rw [map_add,← face_naturality_apply,h,ha]
    simp [x]
  · apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp,Equiv.apply_symm_apply]
    change (p.app (op ⦋n + 1⦌)).hom y = _
    have hk := ConcreteCategory.congr_hom
      (NatTrans.congr_app (kernel.condition p) (op ⦋n + 1⦌)) v
    change (p.app (op ⦋n + 1⦌)).hom (((kernel.ι p).app (op ⦋n + 1⦌)).hom v) = 0 at hk
    dsimp only [y]
    rw [map_add,hz,hk,add_zero]

open SSet.modelCategoryQuillen in
/-- A degreewise surjection of simplicial modules is an actual Kan fibration
after forgetting the module structure. -/
theorem underlying_fibration_of_degreewise_surjective
    {A B : SimplicialObject (ModuleCat.{u} R)} (p : A ⟶ B)
    (hp : ∀ n : ℕ, Function.Surjective (p.app (op ⦋n⦌)).hom) :
    Fibration (Functor.whiskerRight p (forget (ModuleCat R))) := by
  rw [SSet.modelCategoryQuillen.fibration_iff]
  intro _ _ _ hf
  simp only [J, MorphismProperty.iSup_iff] at hf
  obtain ⟨n, ⟨k⟩⟩ := hf
  refine ⟨fun {t b} sq ↦ ?_⟩
  obtain ⟨φ,hφ,hpφ⟩ := horn_lift_of_degreewise_surjective p hp _
    (SSet.horn.IsCompatible.of_hom t) b (fun j hj ↦ by
      rw [Category.assoc,sq.w,← Category.assoc,SSet.horn.ι_ι])
  exact ⟨⟨{
    l := φ
    fac_left := SSet.horn.hom_ext' (by simpa using hφ)
    fac_right := hpφ }⟩⟩

end KIP126.Algebra.SimplicialModule
