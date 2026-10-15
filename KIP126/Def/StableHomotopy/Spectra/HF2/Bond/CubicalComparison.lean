module

public import KIP126.Def.StableHomotopy.Spectra.HF2.Bond.FiberIdentification
public import KIP126.Def.StableHomotopy.Spectra.HF2.Bond.LoopCubical
public import KIP126.Def.Topology.HomotopyFiber.Contraction.Comparison.Proofs

@[expose] public section

section

namespace KIP126.StableHomotopy.Spectra.HF2Bond
open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open scoped unitInterval
set_option backward.isDefEq.respectTransparency false

/-- The actual realized endpoint map of the specified simplicial path object. -/
noncomputable def hf2PathProjection (n : ℕ) :
    C(pathRealizationLevel (hf2SimplicialModule (n+1)), hf2RealizationLevel (n+1)) :=
  (SSet.toTop.map (decalageProjection (hf2SimplicialSet (n+1)))).hom

/-- The source of the bond is the actual topological endpoint fiber, through
the exact normalized coefficient isomorphism and realized kernel inclusion. -/
noncomputable def coefficientFiberHomeomorph (n : ℕ) :
    hf2RealizationLevel n ≃ₜ pathProjectionFiber n :=
  (coefficientLoopRealizationHomeomorph n).trans (loopFiberHomeomorph n)

end KIP126.StableHomotopy.Spectra.HF2Bond

end

section

namespace KIP126.StableHomotopy.Spectra.HF2Bond
open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open scoped unitInterval
set_option backward.isDefEq.respectTransparency false

@[simp] theorem hf2PathProjection_point (n : ℕ) :
    hf2PathProjection n (pathRealizationLevel (hf2SimplicialModule (n+1))).point =
      (hf2RealizationLevel (n+1)).point := (pathProjectionFiberPoint n).property

@[simp] theorem coefficientFiberHomeomorph_point (n : ℕ) :
    coefficientFiberHomeomorph n (hf2RealizationLevel n).point = pathProjectionFiberPoint n := by
  change loopFiberHomeomorph n (coefficientLoopRealizationHomeomorph n (hf2RealizationLevel n).point) = _
  rw [coefficientLoopRealizationHomeomorph_point,loopFiberHomeomorph_point]

/-- This is the concrete projected contraction formula for the actual bond adjoint. -/
theorem bondAdjoint_contraction (n : ℕ) (x : hf2RealizationLevel n) (t : I) :
    bondAdjoint n x t = hf2PathProjection n
      (pathContraction (hf2SimplicialModule (n+1)) ((coefficientFiberHomeomorph n x).val,t)) := by
  exact (pathContraction_loop_projection n (coefficientLoopRealizationHomeomorph n x) t).symm

/-- Once the actual endpoint projection has relative cubical lifting, the
given bond adjoint is bijective on genuine cubical homotopy sets. -/
theorem bondAdjointHomotopyMap_bijective_of_lifting (n r : ℕ)
    (hf : KIP126.Topology.HomotopyLifting.HasCubicalLifting (hf2PathProjection n)) :
    Function.Bijective (bondAdjointHomotopyMap n r) := by
  letI : Subsingleton ((hf2SimplicialModule (n+1)).obj (op ⦋0⦌)) :=
    ModuleCat.subsingleton_of_isZero (hf2SimplicialModule_isZero_below (n+1) 0 (Nat.zero_lt_succ n))
  exact KIP126.Topology.continuousHomotopyMap_bijective_of_fiber_contraction
    (hf2PathProjection n) (pathRealizationLevel (hf2SimplicialModule (n+1))).point
    (hf2RealizationLevel (n+1)).point (hf2PathProjection_point n)
    (pathContractionHomotopy (hf2SimplicialModule (n+1)))
    (pathContraction_point (hf2SimplicialModule (n+1))) hf
    (coefficientFiberHomeomorph n) (hf2RealizationLevel n).point
    (congrArg Subtype.val (coefficientFiberHomeomorph_point n))
    (bondAdjoint n) (bondAdjoint_point n) (bondAdjoint_contraction n) r

/-- The specified structure map, with the prespectrum's exact first-coordinate
convention, is a homotopy isomorphism under the actual endpoint lifting property. -/
theorem bondHomotopyMap_bijective_of_lifting (n r : ℕ)
    (hf : KIP126.Topology.HomotopyLifting.HasCubicalLifting (hf2PathProjection n)) :
    Function.Bijective (bondHomotopyMap n r) :=
  (cubicalHomotopyLoopEquiv (hf2RealizationLevel (n+1)) r).bijective.comp
    (bondAdjointHomotopyMap_bijective_of_lifting n r hf)

end KIP126.StableHomotopy.Spectra.HF2Bond

end
