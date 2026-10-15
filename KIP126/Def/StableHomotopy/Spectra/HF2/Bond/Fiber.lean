module

public import KIP126.Def.StableHomotopy.Spectra.HF2.Bond.PathComparison
public import KIP126.Def.Topology.SimplicialRealization.Relative.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Spectra.HF2Bond
open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open scoped unitInterval
set_option backward.isDefEq.respectTransparency false

instance loopSetInclusion_mono (n : ℕ) : Mono (loopSetInclusion n) := by
  haveI : Mono (loopInclusion n) := inferInstanceAs
    (Mono (kernel.ι (decalageProjection (hf2SimplicialModule (n + 1)))))
  haveI (a : SimplexCategoryᵒᵖ) : Mono ((loopSetInclusion n).app a) := by
    change Mono ((forget (ModuleCat (ZMod 2))).map ((loopInclusion n).app a))
    infer_instance
  exact NatTrans.mono_of_mono_app _

/-- The realized actual simplicial loop kernel is a closed subspace of the
realized path object. -/
theorem loopRealizationInclusion_isClosedEmbedding (n : ℕ) :
    _root_.Topology.IsClosedEmbedding (loopRealizationInclusion n) :=
  KIP126.Topology.SimplicialRealization.realization_mono_isClosedEmbedding (loopSetInclusion n)

/-- The actual topological fiber over the specified zero vertex. -/
def pathProjectionFiber (n : ℕ) :=
  {x : pathRealizationLevel (hf2SimplicialModule (n + 1)) //
    SSet.toTop.map (decalageProjection (hf2SimplicialSet (n + 1))) x =
      (hf2RealizationLevel (n + 1)).point}

instance (n : ℕ) : TopologicalSpace (pathProjectionFiber n) :=
  inferInstanceAs (TopologicalSpace (Subtype _))

/-- The actual continuous map from the realized simplicial kernel into the
topological fiber, using the proved endpoint identity. -/
noncomputable def loopFiberComparison (n : ℕ) :
    C(loopRealizationLevel n, pathProjectionFiber n) where
  toFun x := ⟨loopRealizationInclusion n x, loopRealizationInclusion_projection n x⟩
  continuous_toFun := (loopRealizationInclusion n).continuous.subtype_mk _

/-- This fiber comparison is a closed embedding; identifying its image with
the whole fiber is a separate realization theorem. -/
theorem loopFiberComparison_isClosedEmbedding (n : ℕ) :
    _root_.Topology.IsClosedEmbedding (loopFiberComparison n) :=
  (loopRealizationInclusion_isClosedEmbedding n).of_comp _root_.Topology.IsEmbedding.subtypeVal

/-- Every simplex whose endpoint face vanishes lifts to the actual simplicial
kernel, not merely to an isomorphic substitute kernel. -/
theorem loopInclusion_range_iff (n : ℕ) (a : SimplexCategoryᵒᵖ)
    (z : (decalage (hf2SimplicialModule (n + 1))).obj a) :
    (∃ x, (loopInclusion n).app a x = z) ↔
      (decalageProjection (hf2SimplicialModule (n + 1))).app a z = 0 := by
  constructor
  · rintro ⟨x, rfl⟩
    have h := congrArg (fun f : loopModule n ⟶ hf2SimplicialModule (n + 1) => f.app a x)
      (kernel.condition (decalageProjection (hf2SimplicialModule (n + 1))))
    exact h
  · intro hz
    let F := (evaluation SimplexCategoryᵒᵖ (ModuleCat (ZMod 2))).obj a
    let f := decalageProjection (hf2SimplicialModule (n + 1))
    let w : ModuleCat.of (ZMod 2) (LinearMap.ker ((f.app a).hom)) := ⟨z, hz⟩
    refine ⟨(PreservesKernel.iso F f).inv ((ModuleCat.kernelIsoKer (f.app a)).inv w), ?_⟩
    have h := PreservesKernel.iso_inv_ι F f
    have k := ModuleCat.kernelIsoKer_inv_kernel_ι (f.app a)
    exact (ConcreteCategory.congr_hom h ((ModuleCat.kernelIsoKer (f.app a)).inv w)).trans
      (ConcreteCategory.congr_hom k w)

/-- A surjective map of vertices carries strictly positive barycentric
coordinates to strictly positive barycentric coordinates. -/
theorem simplex_map_positive {A B : Type*} [Fintype A] [Fintype B]
    (f : A → B) (hf : Function.Surjective f) (u : stdSimplex ℝ A)
    (hu : ∀ a, 0 < u a) (b : B) : 0 < stdSimplex.map f u b := by
  classical
  obtain ⟨a, rfl⟩ := hf b
  change 0 < FunOnFinite.linearMap ℝ ℝ f u (f a)
  rw [FunOnFinite.linearMap_apply_apply]
  exact lt_of_lt_of_le (hu a) (Finset.single_le_sum
    (fun j hj => stdSimplex.zero_le u j) (by simp))

/-- The adjunction's characteristic map is the same actual map as the
realized Yoneda simplex in the CW construction. -/
theorem realizeSimplex_eq_yoneda (X : SSet.{0}) (n : ℕ) (x : X.obj (op ⦋n⦌))
    (u : stdSimplex ℝ (Fin (n + 1))) :
    realizeSimplex X x u = SSet.toTop.map (SSet.yonedaEquiv.symm x)
      ((SimplexCategory.toTopHomeo ⦋n⦌).symm u) := by
  have h := sSetTopAdj_unit_app_app_down X (op ⦋n⦌) x
  exact congrArg (fun f : SimplexCategory.toTop.obj ⦋n⦌ ⟶ SSet.toTop.obj X => f (ULift.up u)) h

/-- The connecting loop supplied by the actual contraction of the path
object, on its actual topological endpoint fiber. -/
noncomputable def fiberLoopComparison (n : ℕ) :
    C(pathProjectionFiber n,
      Path (hf2RealizationLevel (n + 1)).point (hf2RealizationLevel (n + 1)).point) := by
  letI : Subsingleton ((hf2SimplicialModule (n + 1)).obj (op ⦋0⦌)) :=
    ModuleCat.subsingleton_of_isZero
      (hf2SimplicialModule_isZero_below (n + 1) 0 (Nat.zero_lt_succ n))
  exact
    { toFun x :=
        { toContinuousMap := (coneEvaluation (hf2SimplicialSet (n + 1))).curry x.val
          source' := coneEvaluation_zero (hf2SimplicialModule (n + 1)) x.val
          target' := (coneEvaluation_one _ x.val).trans x.property }
      continuous_toFun := Path.continuous_uncurry_iff.mp
        ((coneEvaluation (hf2SimplicialSet (n + 1))).continuous.comp
          ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)) }

/-- The simplicial loop comparison factors through the actual topological
fiber with the very same continuous loop parametrization. -/
theorem fiberLoopComparison_loopFiberComparison (n : ℕ) (x : loopRealizationLevel n) :
    fiberLoopComparison n (loopFiberComparison n x) = loopComparison n x := by
  apply Path.ext
  funext t
  rfl

/-- The actual topological fiber's loop is obtained by projecting its
contraction path in the actual contractible total space. -/
theorem fiberLoopComparison_contraction (n : ℕ) (x : pathProjectionFiber n) (t : I) :
    fiberLoopComparison n x t =
      SSet.toTop.map (decalageProjection (hf2SimplicialSet (n + 1)))
        (pathContraction (hf2SimplicialModule (n + 1)) (x.val, t)) :=
  (pathContraction_projection _ _ t).symm

end KIP126.StableHomotopy.Spectra.HF2Bond
