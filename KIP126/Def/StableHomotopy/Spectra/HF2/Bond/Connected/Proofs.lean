module

public import KIP126.Def.StableHomotopy.Spectra.HF2.Bond.FiberIdentification

@[expose] public section

namespace KIP126.StableHomotopy.Spectra.HF2Bond
open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open scoped unitInterval
set_option backward.isDefEq.respectTransparency false

/-- Every point of a realization with a single module vertex is joined
to its specified zero vertex by an actual realized simplex path. -/
theorem moduleRealization_joined_point (A : SimplicialObject (ModuleCat.{0} (ZMod 2)))
    [Subsingleton (A.obj (op ⦋0⦌))] (x : |A ⋙ forget (ModuleCat (ZMod 2))|) :
    Joined (moduleRealizationPoint A) x := by
  obtain ⟨n,s,t,_,he⟩ := KIP126.Topology.SimplicialRealization.exists_nondegenerate_interior
    (A ⋙ forget (ModuleCat (ZMod 2))) x
  let u := SimplexCategory.toTopHomeo ⦋n⦌ t
  have hx : realizeSimplex (A ⋙ forget (ModuleCat (ZMod 2))) s.val u = x := by
    rw [realizeSimplex_eq_yoneda]
    exact ((congrArg (SSet.toTop.map (SSet.yonedaEquiv.symm s.val))
      ((SimplexCategory.toTopHomeo ⦋n⦌).symm_apply_apply t))).trans he
  have hp : Joined
      (realizeSimplex (A ⋙ forget (ModuleCat (ZMod 2))) s.val (stdSimplex.vertex 0))
      (realizeSimplex (A ⋙ forget (ModuleCat (ZMod 2))) s.val u) :=
    ⟨(PathConnectedSpace.somePath (stdSimplex.vertex 0) u).map
      (realizeSimplex (A ⋙ forget (ModuleCat (ZMod 2))) s.val).continuous⟩
  rwa [realizeSimplex_vertex_zero,hx] at hp

/-- The actual positive-degree coefficient spaces are path connected. -/
instance hf2RealizationLevel_pathConnectedSpace (n : ℕ) :
    PathConnectedSpace (hf2RealizationLevel (n+1)) := by
  letI : Subsingleton ((hf2SimplicialModule (n+1)).obj (op ⦋0⦌)) :=
    ModuleCat.subsingleton_of_isZero (hf2SimplicialModule_isZero_below (n+1) 0 (Nat.zero_lt_succ n))
  exact ⟨⟨(hf2RealizationLevel (n+1)).point⟩,fun x y =>
    (moduleRealization_joined_point (hf2SimplicialModule (n+1)) x).symm.trans
      (moduleRealization_joined_point (hf2SimplicialModule (n+1)) y)⟩

/-- The zeroth genuine cubical homotopy set of every positive coefficient
level is a singleton, independently of the still pending projection lifting theorem. -/
instance coefficientPositivePiZero_subsingleton (n : ℕ) :
    Subsingleton (HomotopyGroup.Pi 0 (hf2RealizationLevel (n+1))
      (hf2RealizationLevel (n+1)).point) :=
  HomotopyGroup.pi0EquivZerothHomotopy.injective.subsingleton

end KIP126.StableHomotopy.Spectra.HF2Bond
