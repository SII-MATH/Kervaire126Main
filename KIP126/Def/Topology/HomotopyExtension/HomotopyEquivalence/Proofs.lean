module

public import KIP126.Def.Topology.HomotopyExtension.CylinderCorner.Extension.Proofs
public import Mathlib.Topology.Homotopy.Equiv
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic

@[expose] public section

namespace KIP126.Topology.HomotopyExtension
open CategoryTheory Set _root_.Topology
open scoped unitInterval
universe u
set_option backward.isDefEq.respectTransparency false

/-- A closed homotopy-extension map that is an actual homotopy equivalence
has an actual retraction and a deformation fixing its entire image. -/
theorem HasHomotopyExtension.exists_strong_deformation_retraction
    {A B : TopCat.{u}} {i : A ⟶ B} (hi : HasHomotopyExtension i)
    (he : IsClosedEmbedding i) (e : ContinuousMap.HomotopyEquiv A B)
    (hei : e.toFun = i.hom) :
    ∃ r : C(B,A), r.comp i.hom = ContinuousMap.id A ∧
      ∃ H : (ContinuousMap.id B).Homotopy (i.hom.comp r),
        ∀ (t : I) (a : A), H (t,i a) = i a := by
  obtain ⟨L⟩ := e.left_inv
  obtain ⟨R⟩ := e.right_inv
  rw [hei] at L R
  obtain ⟨E,hE,hEi⟩ := hi A e.invFun
    (L.toContinuousMap.comp ContinuousMap.prodSwap) (fun a => L.apply_zero a)
  let r : C(B,A) := E.comp ((ContinuousMap.id _).prodMk (ContinuousMap.const _ 1))
  have hri : r.comp i.hom = ContinuousMap.id A := by
    ext a
    exact (hEi a 1).trans (L.apply_one a)
  have hriv (a : A) : r (i a) = a := ContinuousMap.congr_fun hri a
  let J : e.invFun.Homotopy r := {
    toContinuousMap := E.comp ContinuousMap.prodSwap
    map_zero_left := hE
    map_one_left := fun _ => rfl }
  let H := R.symm.trans ((ContinuousMap.Homotopy.refl i.hom).comp J)
  have hiR : (i.hom.comp r).comp (i.hom.comp r) = i.hom.comp r := by
    ext b
    exact congrArg i (ContinuousMap.congr_fun hri (r b))
  let K := H.trans ((H.compContinuousMap (i.hom.comp r)).symm.cast hiR rfl)
  let γ (a : A) : Path (i a) (i a) := {
    toFun := fun t => H (t,i a)
    continuous_toFun := H.continuous.comp (continuous_id.prodMk continuous_const)
    source' := H.apply_zero (i a)
    target' := (H.apply_one (i a)).trans (congrArg i (ContinuousMap.congr_fun hri a)) }
  let p : C((A × I) × I,B) := ⟨fun z =>
    (Path.Homotopy.reflTransSymm (γ z.1.1)).symm (z.2,z.1.2),by
      change Continuous (fun z : (A × I) × I =>
        H (⟨Path.Homotopy.reflTransSymmAux (unitInterval.symm z.2,z.1.2),_⟩,i z.1.1))
      fun_prop⟩
  have hp (a : A) (t : I) : p ((a,t),0) = K (t,i a) := by
    change (Path.Homotopy.reflTransSymm (γ a)).symm (0,t) = _
    rw [(Path.Homotopy.reflTransSymm (γ a)).symm.apply_zero]
    change (γ a |>.trans (γ a).symm) t = _
    dsimp only [K]
    rw [ContinuousMap.Homotopy.trans_apply]
    rw [Path.trans_apply]
    split_ifs
    · rfl
    · change H (unitInterval.symm _,i a) = H (unitInterval.symm _,i (r (i a)))
      rw [hriv a]
  obtain ⟨Q,hQ,hQa,hQ0,hQ1⟩ := hi.exists_endpoint_extension he B
    (K.toContinuousMap.comp ContinuousMap.prodSwap) p hp
    (fun a s => ((Path.Homotopy.reflTransSymm (γ a)).symm.eval s).source.trans
      (K.apply_zero (i a)).symm)
    (fun a s => by
      change (Path.Homotopy.reflTransSymm (γ a)).symm (s,1) = K (1,i a)
      exact ((Path.Homotopy.reflTransSymm (γ a)).symm.eval s).target.trans
        ((K.apply_one (i a)).trans (congrArg i (hriv a))).symm)
  let T : (ContinuousMap.id B).Homotopy (i.hom.comp r) := {
    toContinuousMap := Q.comp ⟨fun z => ((z.2,z.1),1),
      (continuous_snd.prodMk continuous_fst).prodMk continuous_const⟩
    map_zero_left := fun b => (hQ0 b 1).trans (K.apply_zero b)
    map_one_left := fun b => (hQ1 b 1).trans (K.apply_one b) }
  refine ⟨r,hri,T,?_⟩
  intro t a
  exact (hQa a t 1).trans ((Path.Homotopy.reflTransSymm (γ a)).symm.apply_one t)

end KIP126.Topology.HomotopyExtension
