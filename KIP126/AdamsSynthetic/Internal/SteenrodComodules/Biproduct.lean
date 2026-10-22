module

import all KIP126.AdamsSynthetic.Internal.SteenrodComodules
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts

/-! Finite products for the fixed total-module presentation of graded
Steenrod comodules. The construction adapts the componentwise finite-product
argument in the donor's `GradedComodule/Structure/Basic` to the actual grading
and left coaction used here. All auxiliary declarations remain private. -/

namespace KIP126.AdamsSynthetic.Internal.SteenrodComodules
open CategoryTheory CategoryTheory.Limits
open DirectSum
open scoped TensorProduct
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

private theorem prodGrade_internal (M N : GradedSteenrodComodule) :
    DirectSum.IsInternal (fun n => (M.grade n).prod (N.grade n)) := by
  classical
  letI := M.internal.chooseDecomposition
  letI := N.internal.chooseDecomposition
  let G := fun n => (M.grade n).prod (N.grade n)
  let il : ∀ n, M.grade n →ₗ[F2] G n := fun n =>
    ((LinearMap.inl F2 M.carrier N.carrier).comp (M.grade n).subtype).codRestrict
      (G n) (fun m => ⟨m.property, (N.grade n).zero_mem⟩)
  let ir : ∀ n, N.grade n →ₗ[F2] G n := fun n =>
    ((LinearMap.inr F2 M.carrier N.carrier).comp (N.grade n).subtype).codRestrict
      (G n) (fun m => ⟨(M.grade n).zero_mem, m.property⟩)
  let d : M.carrier × N.carrier →ₗ[F2] ⨁ n, G n :=
    (DirectSum.lmap il ∘ₗ (DirectSum.decomposeLinearEquiv M.grade).toLinearMap ∘ₗ
      LinearMap.fst F2 M.carrier N.carrier) +
    (DirectSum.lmap ir ∘ₗ (DirectSum.decomposeLinearEquiv N.grade).toLinearMap ∘ₗ
      LinearMap.snd F2 M.carrier N.carrier)
  have hl : DirectSum.coeLinearMap G ∘ₗ DirectSum.lmap il =
      LinearMap.inl F2 M.carrier N.carrier ∘ₗ DirectSum.coeLinearMap M.grade := by
    apply DirectSum.linearMap_ext
    intro n
    apply LinearMap.ext
    intro m
    simp only [LinearMap.comp_apply, DirectSum.lmap_lof, DirectSum.coeLinearMap_lof]
    rfl
  have hr : DirectSum.coeLinearMap G ∘ₗ DirectSum.lmap ir =
      LinearMap.inr F2 M.carrier N.carrier ∘ₗ DirectSum.coeLinearMap N.grade := by
    apply DirectSum.linearMap_ext
    intro n
    apply LinearMap.ext
    intro m
    simp only [LinearMap.comp_apply, DirectSum.lmap_lof, DirectSum.coeLinearMap_lof]
    rfl
  have hleft : DirectSum.coeLinearMap G ∘ₗ d = LinearMap.id := by
    apply LinearMap.ext
    intro x
    change (DirectSum.coeLinearMap G)
      (DirectSum.lmap il (DirectSum.decomposeLinearEquiv M.grade x.1) +
       DirectSum.lmap ir (DirectSum.decomposeLinearEquiv N.grade x.2)) = x
    rw [map_add]
    change ((DirectSum.coeLinearMap G ∘ₗ DirectSum.lmap il)
      (DirectSum.decomposeLinearEquiv M.grade x.1)) +
      ((DirectSum.coeLinearMap G ∘ₗ DirectSum.lmap ir)
      (DirectSum.decomposeLinearEquiv N.grade x.2)) = x
    rw [hl, hr]
    change ((DirectSum.decomposeLinearEquiv M.grade).symm
      ((DirectSum.decomposeLinearEquiv M.grade) x.1), (0 : N.carrier)) +
      ((0 : M.carrier), (DirectSum.decomposeLinearEquiv N.grade).symm
      ((DirectSum.decomposeLinearEquiv N.grade) x.2)) = x
    simp
  have hright : d ∘ₗ DirectSum.coeLinearMap G = LinearMap.id := by
    apply DirectSum.linearMap_ext
    intro n
    apply LinearMap.ext
    intro x
    change d (DirectSum.coeLinearMap G (DirectSum.lof F2 ℤ (fun n => G n) n x)) =
      DirectSum.lof F2 ℤ (fun n => G n) n x
    rw [DirectSum.coeLinearMap_lof]
    have h1 := DirectSum.decomposeLinearEquiv_apply_coe M.grade n
      (⟨x.val.1,x.property.1⟩ : M.grade n)
    have h2 := DirectSum.decomposeLinearEquiv_apply_coe N.grade n
      (⟨x.val.2,x.property.2⟩ : N.grade n)
    dsimp only [d, LinearMap.add_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearMap.fst_apply, LinearMap.snd_apply]
    rw [h1,h2,DirectSum.lmap_lof,DirectSum.lmap_lof,← map_add]
    congr 1
    apply Subtype.ext
    simp [il,ir]
  letI := DirectSum.Decomposition.ofLinearMap G d hleft hright
  exact DirectSum.Decomposition.isInternal _

private def counitL (M : Type) [AddCommGroup M] [Module F2 M] :
    DualSteenrod ⊗[F2] M →ₗ[F2] M :=
  (TensorProduct.lid F2 M).toLinearMap ∘ₗ milnorCounit.toLinearMap.rTensor M

private def deltaL (M : Type) [AddCommGroup M] [Module F2 M] :
    DualSteenrod ⊗[F2] M →ₗ[F2] DualSteenrod ⊗[F2] (DualSteenrod ⊗[F2] M) :=
  (TensorProduct.assoc F2 DualSteenrod DualSteenrod M).toLinearMap ∘ₗ
    milnorCoproduct.toLinearMap.rTensor M

private theorem counitL_natural {M N : Type} [AddCommGroup M] [Module F2 M]
    [AddCommGroup N] [Module F2 N] (f : M →ₗ[F2] N) :
    counitL N ∘ₗ f.lTensor DualSteenrod = f ∘ₗ counitL M := by
  ext a m
  simp [counitL]

private theorem deltaL_natural {M N : Type} [AddCommGroup M] [Module F2 M]
    [AddCommGroup N] [Module F2 N] (f : M →ₗ[F2] N) :
    deltaL N ∘ₗ f.lTensor DualSteenrod =
      (f.lTensor DualSteenrod).lTensor DualSteenrod ∘ₗ deltaL M := by
  apply TensorProduct.ext
  apply LinearMap.ext
  intro a
  apply LinearMap.ext
  intro m
  change TensorProduct.assoc F2 DualSteenrod DualSteenrod N
      (milnorCoproduct a ⊗ₜ[F2] f m) =
    (f.lTensor DualSteenrod).lTensor DualSteenrod
      (TensorProduct.assoc F2 DualSteenrod DualSteenrod M (milnorCoproduct a ⊗ₜ[F2] m))
  generalize milnorCoproduct a = z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add u v hu hv => simp [TensorProduct.add_tmul, hu, hv]

private def prodRho (M N : GradedSteenrodComodule) :
    M.carrier × N.carrier →ₗ[F2] DualSteenrod ⊗[F2] (M.carrier × N.carrier) :=
  (((LinearMap.inl F2 M.carrier N.carrier).lTensor DualSteenrod) ∘ₗ M.rho).coprod
    (((LinearMap.inr F2 M.carrier N.carrier).lTensor DualSteenrod) ∘ₗ N.rho)

private theorem prodRho_inl (M N : GradedSteenrodComodule) :
    prodRho M N ∘ₗ LinearMap.inl F2 M.carrier N.carrier =
      (LinearMap.inl F2 M.carrier N.carrier).lTensor DualSteenrod ∘ₗ M.rho := by
  simp [prodRho]

private theorem prodRho_inr (M N : GradedSteenrodComodule) :
    prodRho M N ∘ₗ LinearMap.inr F2 M.carrier N.carrier =
      (LinearMap.inr F2 M.carrier N.carrier).lTensor DualSteenrod ∘ₗ N.rho := by
  simp [prodRho]

private theorem prodRho_counit (M N : GradedSteenrodComodule) :
    counitL (M.carrier × N.carrier) ∘ₗ prodRho M N = LinearMap.id := by
  apply LinearMap.prod_ext
  · rw [LinearMap.comp_assoc, prodRho_inl, ← LinearMap.comp_assoc, counitL_natural,
      LinearMap.comp_assoc]
    have h : counitL M.carrier ∘ₗ M.rho = LinearMap.id := M.counit
    rw [h, LinearMap.comp_id, LinearMap.id_comp]
  · rw [LinearMap.comp_assoc, prodRho_inr, ← LinearMap.comp_assoc, counitL_natural,
      LinearMap.comp_assoc]
    have h : counitL N.carrier ∘ₗ N.rho = LinearMap.id := N.counit
    rw [h, LinearMap.comp_id, LinearMap.id_comp]

private theorem prodRho_coassoc (M N : GradedSteenrodComodule) :
    deltaL (M.carrier × N.carrier) ∘ₗ prodRho M N =
      (prodRho M N).lTensor DualSteenrod ∘ₗ prodRho M N := by
  apply LinearMap.prod_ext
  · rw [LinearMap.comp_assoc, prodRho_inl, ← LinearMap.comp_assoc, deltaL_natural,
      LinearMap.comp_assoc]
    have h : deltaL M.carrier ∘ₗ M.rho = M.rho.lTensor DualSteenrod ∘ₗ M.rho := M.coassoc
    rw [h]
    simp only [LinearMap.comp_assoc, prodRho_inl]
    simpa only [LinearMap.comp_assoc, LinearMap.lTensor_comp] using
      congrArg (fun q => q.lTensor DualSteenrod ∘ₗ M.rho) (prodRho_inl M N).symm
  · rw [LinearMap.comp_assoc, prodRho_inr, ← LinearMap.comp_assoc, deltaL_natural,
      LinearMap.comp_assoc]
    have h : deltaL N.carrier ∘ₗ N.rho = N.rho.lTensor DualSteenrod ∘ₗ N.rho := N.coassoc
    rw [h]
    simp only [LinearMap.comp_assoc, prodRho_inr]
    simpa only [LinearMap.comp_assoc, LinearMap.lTensor_comp] using
      congrArg (fun q => q.lTensor DualSteenrod ∘ₗ N.rho) (prodRho_inr M N).symm

private theorem tensorGrade_map_prod {M N : ModuleCat.{0} F2}
    (gM : ℤ → Submodule F2 M) (gN : ℤ → Submodule F2 N)
    (f : M →ₗ[F2] N) (hf : ∀ n x, x ∈ gM n → f x ∈ gN n)
    (n : ℤ) {z : DualSteenrod ⊗[F2] M} (hz : z ∈ tensorGrade M gM n) :
    f.lTensor DualSteenrod z ∈ tensorGrade N gN n := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨d,a,m,ha,hm,rfl⟩ := hx
    exact Submodule.subset_span ⟨d,a,f m,ha,hf _ _ hm,rfl⟩
  | zero => simpa only [map_zero] using (tensorGrade N gN n).zero_mem
  | add a b _ _ ha hb => simpa using (tensorGrade N gN n).add_mem ha hb
  | smul c a _ ha => simpa using (tensorGrade N gN n).smul_mem c ha

def comoduleProd (M N : GradedSteenrodComodule) : GradedSteenrodComodule where
  carrier := ModuleCat.of F2 (M.carrier × N.carrier)
  grade n := (M.grade n).prod (N.grade n)
  internal := prodGrade_internal M N
  rho := prodRho M N
  counit := prodRho_counit M N
  coassoc := prodRho_coassoc M N
  graded n x hx := by
    apply Submodule.add_mem
    · exact tensorGrade_map_prod (M := M.carrier)
        (N := ModuleCat.of F2 (M.carrier × N.carrier)) M.grade (fun n => (M.grade n).prod (N.grade n))
        (LinearMap.inl F2 M.carrier N.carrier)
        (fun n m hm => ⟨hm,(N.grade n).zero_mem⟩) n (M.graded n x.1 hx.1)
    · exact tensorGrade_map_prod (M := N.carrier)
        (N := ModuleCat.of F2 (M.carrier × N.carrier)) N.grade (fun n => (M.grade n).prod (N.grade n))
        (LinearMap.inr F2 M.carrier N.carrier)
        (fun n m hm => ⟨(M.grade n).zero_mem,hm⟩) n (N.graded n x.2 hx.2)

def comoduleProdFst (M N : GradedSteenrodComodule) : comoduleProd M N ⟶ M where
  linearMap := LinearMap.fst F2 M.carrier N.carrier
  graded _ _ hm := hm.1
  coaction := by
    apply LinearMap.prod_ext <;>
      simp [comoduleProd, prodRho, LinearMap.comp_assoc] <;>
      rw [← LinearMap.comp_assoc, ← LinearMap.lTensor_comp] <;> simp

def comoduleProdSnd (M N : GradedSteenrodComodule) : comoduleProd M N ⟶ N where
  linearMap := LinearMap.snd F2 M.carrier N.carrier
  graded _ _ hm := hm.2
  coaction := by
    apply LinearMap.prod_ext <;>
      simp [comoduleProd, prodRho, LinearMap.comp_assoc] <;>
      rw [← LinearMap.comp_assoc, ← LinearMap.lTensor_comp] <;> simp

def comoduleProdLift {T M N : GradedSteenrodComodule} (f : T ⟶ M) (g : T ⟶ N) :
    T ⟶ comoduleProd M N where
  linearMap := f.linearMap.prod g.linearMap
  graded n x hx := ⟨f.graded n x hx,g.graded n x hx⟩
  coaction := by
    have h : f.linearMap.prod g.linearMap =
        LinearMap.inl F2 M.carrier N.carrier ∘ₗ f.linearMap +
        LinearMap.inr F2 M.carrier N.carrier ∘ₗ g.linearMap := by
      ext x <;> simp
    change (f.linearMap.prod g.linearMap).lTensor DualSteenrod ∘ₗ T.rho =
      prodRho M N ∘ₗ (f.linearMap.prod g.linearMap)
    rw [h, LinearMap.lTensor_add, LinearMap.add_comp, LinearMap.comp_add,
      LinearMap.lTensor_comp, LinearMap.lTensor_comp,
      LinearMap.comp_assoc, LinearMap.comp_assoc, f.coaction, g.coaction]
    simp only [← LinearMap.comp_assoc, prodRho_inl, prodRho_inr]

def comoduleProdIsLimit (M N : GradedSteenrodComodule) :
    IsLimit (BinaryFan.mk (comoduleProdFst M N) (comoduleProdSnd M N)) := by
  apply BinaryFan.IsLimit.mk _ (fun f g => comoduleProdLift f g)
  · intro T f g
    apply GradedSteenrodComodule.Hom.ext
    rfl
  · intro T f g
    apply GradedSteenrodComodule.Hom.ext
    rfl
  · intro T f g m h1 h2
    apply GradedSteenrodComodule.Hom.ext
    apply LinearMap.ext
    intro x
    exact Prod.ext
      (congrArg (fun k => k.linearMap x) h1)
      (congrArg (fun k => k.linearMap x) h2)

instance comoduleHasBinaryProducts : HasBinaryProducts GradedSteenrodComodule := by
  letI : ∀ {M N : GradedSteenrodComodule}, HasLimit (pair M N) :=
    fun {M N} => HasLimit.mk ⟨_, comoduleProdIsLimit M N⟩
  exact hasBinaryProducts_of_hasLimit_pair GradedSteenrodComodule

def comoduleZero : GradedSteenrodComodule where
  carrier := ModuleCat.of F2 PUnit
  grade _ := ⊥
  internal := by
    constructor
    · intro x y _
      exact Subsingleton.elim x y
    · intro x
      exact ⟨0,Subsingleton.elim _ _⟩
  rho := 0
  counit := Subsingleton.elim _ _
  coassoc := by simp
  graded _ _ _ := (tensorGrade _ _ _).zero_mem

instance comoduleHasZeroObject : HasZeroObject GradedSteenrodComodule where
  zero := ⟨comoduleZero, {
    unique_to := fun M => ⟨{
      default := 0
      uniq := fun _ => GradedSteenrodComodule.Hom.ext
        (Subsingleton.elim (α := PUnit →ₗ[F2] M.carrier) _ _)}⟩
    unique_from := fun M => ⟨{
      default := 0
      uniq := fun _ => GradedSteenrodComodule.Hom.ext
        (Subsingleton.elim (α := M.carrier →ₗ[F2] PUnit) _ _)}⟩ }⟩

instance comoduleHasFiniteProducts : HasFiniteProducts GradedSteenrodComodule :=
  hasFiniteProducts_of_has_binary_and_terminal

end
end KIP126.AdamsSynthetic.Internal.SteenrodComodules

