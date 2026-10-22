module
import all KIP126.AdamsSynthetic.Internal.SteenrodComodules
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

set_option backward.isDefEq.respectTransparency false
namespace KIP126.AdamsSynthetic.Internal.SteenrodComodules
/-!
The cokernel of a graded Steenrod-comodule map has the underlying module quotient.
Its homogeneous pieces are the images of the original pieces. The direct-sum
coordinate map and coaction both descend through the range of the map.
-/
namespace CokernelConstruction
open CategoryTheory CategoryTheory.Limits
open scoped DirectSum TensorProduct
noncomputable section

variable {M N : GradedSteenrodComodule} (f : M ⟶ N)

private abbrev Q := N.carrier ⧸ LinearMap.range f.linearMap
private def q : N.carrier →ₗ[F2] Q f := (LinearMap.range f.linearMap).mkQ
private def qgrade (n : ℤ) : Submodule F2 (Q f) := (N.grade n).map (q f)
private def qgradeMap (n : ℤ) : N.grade n →ₗ[F2] qgrade f n :=
  ((q f).comp (N.grade n).subtype).codRestrict (qgrade f n)
    (fun x => ⟨x, x.property, rfl⟩)

private theorem q_comp : (q f) ∘ₗ f.linearMap = 0 := by
  apply LinearMap.ext
  intro x
  exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨x,rfl⟩

private def qdecompRaw : N.carrier →ₗ[F2] ⨁ n : ℤ, qgrade f n := by
  letI := N.internal.chooseDecomposition
  exact (DirectSum.lmap (qgradeMap f)).comp
    (DirectSum.decomposeLinearEquiv N.grade).toLinearMap

private theorem qdecompRaw_homogeneous (n : ℤ) (x : N.grade n) :
    qdecompRaw f x = DirectSum.lof F2 ℤ (fun n => qgrade f n) n (qgradeMap f n x) := by
  letI := N.internal.chooseDecomposition
  simp [qdecompRaw]

private theorem qdecompRaw_comp : (qdecompRaw f) ∘ₗ f.linearMap = 0 := by
  letI := M.internal.chooseDecomposition
  apply LinearMap.ext
  intro x
  induction x using DirectSum.Decomposition.inductionOn M.grade with
  | zero => simp
  | homogeneous x =>
    rename_i n
    change qdecompRaw f (f.linearMap x) = 0
    have h := qdecompRaw_homogeneous f n ⟨f.linearMap x, f.graded n x x.property⟩
    rw [show qdecompRaw f (f.linearMap x) = _ from h]
    have hz : qgradeMap f n ⟨f.linearMap x, f.graded n x x.property⟩ = 0 := by
      apply Subtype.ext
      exact LinearMap.congr_fun (q_comp f) x
    rw [hz, map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]

private def qdecomp : Q f →ₗ[F2] ⨁ n : ℤ, qgrade f n := by
  have h : LinearMap.range f.linearMap ≤ LinearMap.ker (qdecompRaw f) := by
    rintro x ⟨m,rfl⟩
    exact LinearMap.congr_fun (qdecompRaw_comp f) m
  exact Submodule.liftQ (R₂ := F2) (M₂ := ⨁ n : ℤ, qgrade f n)
    (τ₁₂ := RingHom.id F2) (LinearMap.range f.linearMap) (qdecompRaw f) h

private theorem qdecomp_q (x : N.carrier) : qdecomp f (q f x) = qdecompRaw f x := rfl

private theorem qdecomp_left :
    DirectSum.coeLinearMap (qgrade f) ∘ₗ qdecomp f = LinearMap.id := by
  letI := N.internal.chooseDecomposition
  apply LinearMap.ext
  intro x
  obtain ⟨x,rfl⟩ := (LinearMap.range f.linearMap).mkQ_surjective x
  change DirectSum.coeLinearMap (qgrade f) (qdecompRaw f x) = q f x
  induction x using DirectSum.Decomposition.inductionOn N.grade with
  | zero => simp
  | homogeneous x =>
    rename_i n
    rw [qdecompRaw_homogeneous]
    simp [qgradeMap]
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem qdecomp_right :
    qdecomp f ∘ₗ DirectSum.coeLinearMap (qgrade f) = LinearMap.id := by
  apply DirectSum.linearMap_ext
  intro n
  apply LinearMap.ext
  intro x
  obtain ⟨y,hy,he⟩ := x.property
  have hx : x = qgradeMap f n ⟨y,hy⟩ := Subtype.ext he.symm
  subst x
  simp only [LinearMap.comp_apply, DirectSum.coeLinearMap_lof, LinearMap.id_apply]
  change qdecomp f (q f y) = _
  rw [qdecomp_q]
  exact qdecompRaw_homogeneous f n ⟨y,hy⟩

private theorem qinternal : DirectSum.IsInternal (qgrade f) := by
  letI := DirectSum.Decomposition.ofLinearMap (qgrade f) (qdecomp f)
    (qdecomp_left f) (qdecomp_right f)
  exact DirectSum.Decomposition.isInternal _

private def qrhoRaw : N.carrier →ₗ[F2] DualSteenrod ⊗[F2] Q f :=
  (q f).lTensor DualSteenrod ∘ₗ N.rho

private theorem qrhoRaw_comp : qrhoRaw f ∘ₗ f.linearMap = 0 := by
  unfold qrhoRaw
  rw [LinearMap.comp_assoc, ← f.coaction, ← LinearMap.comp_assoc,
    ← LinearMap.lTensor_comp, q_comp, LinearMap.lTensor_zero, LinearMap.zero_comp]

private def qrho : Q f →ₗ[F2] DualSteenrod ⊗[F2] Q f :=
  Submodule.liftQ (τ₁₂ := RingHom.id F2) (LinearMap.range f.linearMap) (qrhoRaw f)
    (LinearMap.range_le_ker_iff.mpr (qrhoRaw_comp f))

private theorem qrho_q (x : N.carrier) :
    qrho f (q f x) = (q f).lTensor DualSteenrod (N.rho x) := rfl

private theorem counit_natural :
    (TensorProduct.lid F2 (Q f)).toLinearMap ∘ₗ
      milnorCounit.toLinearMap.rTensor (Q f) ∘ₗ (q f).lTensor DualSteenrod =
    q f ∘ₗ (TensorProduct.lid F2 N.carrier).toLinearMap ∘ₗ
      milnorCounit.toLinearMap.rTensor N.carrier := by
  apply TensorProduct.ext
  apply LinearMap.ext
  intro a
  apply LinearMap.ext
  intro x
  simp

private theorem qrho_counit :
    (TensorProduct.lid F2 (Q f)).toLinearMap ∘ₗ
      milnorCounit.toLinearMap.rTensor (Q f) ∘ₗ qrho f = LinearMap.id := by
  apply LinearMap.ext
  intro x
  obtain ⟨x,rfl⟩ := (LinearMap.range f.linearMap).mkQ_surjective x
  change ((TensorProduct.lid F2 (Q f)).toLinearMap ∘ₗ
      milnorCounit.toLinearMap.rTensor (Q f) ∘ₗ (q f).lTensor DualSteenrod) (N.rho x) = q f x
  rw [counit_natural]
  exact congrArg (q f) (LinearMap.congr_fun N.counit x)

private theorem delta_natural :
    (TensorProduct.assoc F2 DualSteenrod DualSteenrod (Q f)).toLinearMap ∘ₗ
      milnorCoproduct.toLinearMap.rTensor (Q f) ∘ₗ (q f).lTensor DualSteenrod =
    ((q f).lTensor DualSteenrod).lTensor DualSteenrod ∘ₗ
      (TensorProduct.assoc F2 DualSteenrod DualSteenrod N.carrier).toLinearMap ∘ₗ
      milnorCoproduct.toLinearMap.rTensor N.carrier := by
  apply TensorProduct.ext
  apply LinearMap.ext
  intro a
  apply LinearMap.ext
  intro x
  change TensorProduct.assoc F2 DualSteenrod DualSteenrod (Q f)
      (milnorCoproduct a ⊗ₜ[F2] q f x) =
    ((q f).lTensor DualSteenrod).lTensor DualSteenrod
      (TensorProduct.assoc F2 DualSteenrod DualSteenrod N.carrier
        (milnorCoproduct a ⊗ₜ[F2] x))
  induction milnorCoproduct a using TensorProduct.induction_on with
  | zero => simp
  | tmul b c => simp
  | add y z hy hz => simp only [TensorProduct.add_tmul, map_add, hy, hz]

private theorem qrho_natural : qrho f ∘ₗ q f = (q f).lTensor DualSteenrod ∘ₗ N.rho := rfl

private theorem qrho_coassoc :
    (TensorProduct.assoc F2 DualSteenrod DualSteenrod (Q f)).toLinearMap ∘ₗ
      milnorCoproduct.toLinearMap.rTensor (Q f) ∘ₗ qrho f =
    (qrho f).lTensor DualSteenrod ∘ₗ qrho f := by
  apply LinearMap.ext
  intro x
  obtain ⟨x,rfl⟩ := (LinearMap.range f.linearMap).mkQ_surjective x
  change ((TensorProduct.assoc F2 DualSteenrod DualSteenrod (Q f)).toLinearMap ∘ₗ
      milnorCoproduct.toLinearMap.rTensor (Q f) ∘ₗ (q f).lTensor DualSteenrod) (N.rho x) =
    ((qrho f).lTensor DualSteenrod ∘ₗ (q f).lTensor DualSteenrod) (N.rho x)
  rw [delta_natural, ← LinearMap.lTensor_comp, qrho_natural, LinearMap.lTensor_comp]
  exact congrArg (((q f).lTensor DualSteenrod).lTensor DualSteenrod)
    (LinearMap.congr_fun N.coassoc x)

private theorem tensorGrade_q (n : ℤ) (z : DualSteenrod ⊗[F2] N.carrier)
    (hz : z ∈ tensorGrade N.carrier N.grade n) :
    (q f).lTensor DualSteenrod z ∈ tensorGrade (ModuleCat.of F2 (Q f)) (qgrade f) n := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨d,a,m,ha,hm,rfl⟩ := hz
    apply Submodule.subset_span
    exact ⟨d,a,q f m,ha,⟨m,hm,rfl⟩,rfl⟩
  | zero => simpa only [map_zero] using (tensorGrade (ModuleCat.of F2 (Q f)) (qgrade f) n).zero_mem
  | add z w _ _ hz hw => simpa only [map_add] using Submodule.add_mem _ hz hw
  | smul r z _ hz => simpa only [map_smul] using Submodule.smul_mem _ r hz

private theorem qrho_graded (n : ℤ) (x : Q f) (hx : x ∈ qgrade f n) :
    qrho f x ∈ tensorGrade (ModuleCat.of F2 (Q f)) (qgrade f) n := by
  obtain ⟨x,hx,rfl⟩ := hx
  exact tensorGrade_q f n (N.rho x) (N.graded n x hx)

private def cokernelObject : GradedSteenrodComodule where
  carrier := ModuleCat.of F2 (Q f)
  grade := qgrade f
  internal := qinternal f
  rho := qrho f
  counit := qrho_counit f
  coassoc := qrho_coassoc f
  graded := qrho_graded f

private def cokernelProjection : N ⟶ cokernelObject f where
  linearMap := q f
  graded := fun _ x hx => ⟨x,hx,rfl⟩
  coaction := (qrho_natural f).symm

private theorem cokernel_condition : f ≫ cokernelProjection f = 0 := by
  apply GradedSteenrodComodule.Hom.ext
  exact q_comp f

variable {P : GradedSteenrodComodule}

private def cokernelLiftLinear (g : N ⟶ P) (h : f ≫ g = 0) : Q f →ₗ[F2] P.carrier :=
  Submodule.liftQ (τ₁₂ := RingHom.id F2) (LinearMap.range f.linearMap) g.linearMap
    (LinearMap.range_le_ker_iff.mpr (congrArg GradedSteenrodComodule.Hom.linearMap h))

private theorem cokernelLiftLinear_q (g : N ⟶ P) (h : f ≫ g = 0) :
    cokernelLiftLinear f g h ∘ₗ q f = g.linearMap := rfl

private def cokernelLift (g : N ⟶ P) (h : f ≫ g = 0) : cokernelObject f ⟶ P where
  linearMap := cokernelLiftLinear f g h
  graded := by
    rintro n x ⟨y,hy,rfl⟩
    exact g.graded n y hy
  coaction := by
    apply LinearMap.ext
    intro x
    obtain ⟨x,rfl⟩ := (LinearMap.range f.linearMap).mkQ_surjective x
    change ((cokernelLiftLinear f g h).lTensor DualSteenrod ∘ₗ
        (q f).lTensor DualSteenrod) (N.rho x) = P.rho (g.linearMap x)
    rw [← LinearMap.lTensor_comp, cokernelLiftLinear_q]
    exact LinearMap.congr_fun g.coaction x

private def cokernelCofork : CokernelCofork f :=
  CokernelCofork.ofπ (cokernelProjection f) (cokernel_condition f)

private def cokernelIsColimit : IsColimit (cokernelCofork f) :=
  Cofork.IsColimit.mk _
    (fun s => cokernelLift f s.π (CokernelCofork.condition s))
    (fun s => GradedSteenrodComodule.Hom.ext (cokernelLiftLinear_q f s.π (CokernelCofork.condition s)))
    (fun s m h => by
      apply GradedSteenrodComodule.Hom.ext
      apply LinearMap.ext
      intro x
      obtain ⟨x,rfl⟩ := (LinearMap.range f.linearMap).mkQ_surjective x
      exact LinearMap.congr_fun (congrArg GradedSteenrodComodule.Hom.linearMap h) x)

private theorem hasCokernels : HasCokernels GradedSteenrodComodule :=
  ⟨fun f => HasColimit.mk ⟨_,cokernelIsColimit f⟩⟩

private def forgetCokernelIsColimit : IsColimit ((cokernelCofork f).map
    GradedSteenrodComodule.forget) := by
  exact ModuleCat.cokernelIsColimit (GradedSteenrodComodule.forget.map f)

private theorem forget_preservesCokernel :
    PreservesColimit (parallelPair f 0) GradedSteenrodComodule.forget :=
  preservesColimit_of_preserves_colimit_cocone (cokernelIsColimit f)
    (((cokernelCofork f).isColimitMapCoconeEquiv GradedSteenrodComodule.forget).symm
      (forgetCokernelIsColimit f))

end
end CokernelConstruction
end KIP126.AdamsSynthetic.Internal.SteenrodComodules
