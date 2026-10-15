module
import all KIP126.Def.ProofTools.GeneralizedMahowald.KernelTriangles
import all KIP126.Def.ProofTools.GeneralizedMahowald.BoundaryLambda
/-! Original actual rho-kernel correction, bbac1fc05843 Mahowald 655–1477 (MIT).
All constituent calculations are proved; no geometric obligation occurs here. -/
@[expose] section
namespace KIP126.ProofTools.Internal.Mahowald
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
theorem finite_target_boundary_lambda_zero_reindex 
    (X : ClassicalObject)
    (r i q : ℕ) (hi : 0 < i) (hir : i < r) (hqi : r-i=q) (s t : ℤ)
    (y : KIP126.Literature.cycles model X ((q:ℤ)-t+(t-(q-1:ℕ))) (s,t))
    (hy : y.val ∈ KIP126.Literature.boundaries model X r (s,t))
    (b : BiHom (t-s) (t-(q-1:ℕ))
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
    (hb : Detects (model.convergence (.quotient q (.nu X)))
      (s,t,t-(q-1:ℕ)) (finiteTargetLabel model X q s t (q-1) y.val) b) :
    (SyntheticCategory.biShift (0,-(i:ℤ))).map b ≫
      Eq.mp (congrArg (fun j => (SyntheticCategory.biShift (0,-(i:ℤ))).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) j) ⟶
          XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) r) hqi)
        ((model.quotients.tower (model.nu.functor.obj (X.obj model.auxiliary))).triangle hi hir).lambdaMap = 0 := by
  subst q
  exact finite_target_boundary_lambda_zero X r i hi hir s t y hy b hb

theorem actual_rho_kernel_correction
    (X : ClassicalObject)
    (d q : ℕ) (hd : 0 < d) (hq : 0 < q) (s t : ℤ)
    (y : KIP126.Literature.cycles model X ((q:ℤ)-t+(t-(q-1:ℕ))) (s,t))
    (hy : y.val ∈ KIP126.Literature.boundaries model X (d+q:ℕ) (s,t))
    (c : BiHom (t-s) (t-(q-1:ℕ))
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
    (hc : Detects (model.convergence (.quotient q (.nu X)))
      (s,t,t-(q-1:ℕ)) (finiteTargetLabel model X q s t (q-1) y.val) c) :
    let A := model.nu.functor.obj (X.obj model.auxiliary)
    let δ1 : XModLambdaN A (d+1) ⟶
        ((SyntheticCategory.biShift (0,-((d+1:ℕ):ℤ))).obj (XModLambdaN A q))⟦(1:ℤ)⟧ := by
      simpa only [Nat.add_sub_cancel_left] using
        ((model.quotients.tower A).triangle (by omega : 0<d+1)
          (show d+1<d+1+q by omega)).delta
    ∃ a : BiHom ((t-s)+1) ((t-(q-1:ℕ))-((d+1:ℕ):ℤ)) (XModLambdaN A (d+1)),
      a ≫ (model.quotients.tower A).rho 1 (d+1) (by omega) = 0 ∧
      homotopyRegrade (by omega) (by omega)
        (biSuspensionHomEquiv ((t-s)+1) ((t-(q-1:ℕ))-((d+1:ℕ):ℤ)) ((d+1:ℕ):ℤ)
          (XModLambdaN A q) (a≫δ1)) = c := by
  dsimp only
  let A := model.nu.functor.obj (X.obj model.auxiliary)
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-1)
  letI := model.exactness.shiftCommShift (0,-1)
  letI := model.exactness.shiftExact (0,-1)
  let T0 := (model.quotients.tower A).triangle hd (show d<d+q by omega)
  let l : F.obj (XModLambdaN A d) ⟶ XModLambdaN A (d+1) := by
    simpa only [F,Nat.add_sub_cancel,Nat.cast_one] using
      ((model.quotients.tower A).triangle (by omega : 0<1) (by omega : 1<d+1)).lambdaMap
  let δ0 : XModLambdaN A d ⟶
      ((SyntheticCategory.biShift (0,-(d:ℤ))).obj (XModLambdaN A q))⟦(1:ℤ)⟧ := by
    simpa only [Nat.add_sub_cancel_left] using T0.delta
  let δ1 : XModLambdaN A (d+1) ⟶
      ((SyntheticCategory.biShift (0,-((d+1:ℕ):ℤ))).obj (XModLambdaN A q))⟦(1:ℤ)⟧ := by
    simpa only [Nat.add_sub_cancel_left] using
      ((model.quotients.tower A).triangle (by omega : 0<d+1)
        (show d+1<d+1+q by omega)).delta
  let L0 : (SyntheticCategory.biShift (0,-(d:ℤ))).obj (XModLambdaN A q) ⟶
      XModLambdaN A (d+q) := by
    simpa only [Nat.add_sub_cancel_left] using T0.lambdaMap
  have hz : (SyntheticCategory.biShift (0,-(d:ℤ))).map c≫L0=0 :=
    finite_target_boundary_lambda_zero_reindex X (d+q) d q hd (by omega)
      (Nat.add_sub_cancel_left d q) s t y hy c hc
  have regrade_zero {m m' v v' : ℤ} (hm:m=m') (hv:v=v')
      (b : BiHom m v (XModLambdaN A q)) :
      (SyntheticCategory.biShift (0,-(d:ℤ))).map (homotopyRegrade hm hv b)≫L0=0 ↔
        (SyntheticCategory.biShift (0,-(d:ℤ))).map b≫L0=0 := by
    subst m'; subst v'; rfl
  let c' : BiHom (((t-s)+1)-1) (((t-(q-1:ℕ))-((d+1:ℕ):ℤ))+((d+1:ℕ):ℤ))
      (XModLambdaN A q) := homotopyRegrade (by omega) (by omega) c
  have pre := successor_shifted_delta_preimage_reindex d (d+q) q (Nat.add_sub_cancel_left d q)
    T0 ((t-s)+1) ((t-(q-1:ℕ))-((d+1:ℕ):ℤ))
  obtain ⟨β,hβ⟩ := pre c' ((regrade_zero (by omega) (by omega) c).mpr hz)
  have heval := successor_delta_lambda_evaluation X d q hd hq
    ((t-s)+1) ((t-(q-1:ℕ))-((d+1:ℕ):ℤ)) β
  have hδ : (β≫l)≫δ1 =
      (biSuspensionHomEquiv ((t-s)+1) ((t-(q-1:ℕ))-((d+1:ℕ):ℤ)) ((d+1:ℕ):ℤ)
        (XModLambdaN A q)).symm c' := by
    simpa only [Category.assoc] using heval.trans hβ
  refine ⟨β≫l,?_,?_⟩
  · rw [Category.assoc]
    have hl0 : ((model.quotients.tower A).triangle (by omega : 0<1)
        (by omega : 1<d+1)).lambdaMap ≫
        (model.quotients.tower A).rho 1 (d+1) (by omega) = 0 := by
      rw [← (model.quotients.tower A).triangle_rho (by omega : 0<1) (by omega : 1<d+1)]
      exact comp_distTriang_mor_zero₁₂ _
        ((model.quotients.tower A).triangle (by omega : 0<1) (by omega : 1<d+1)).distinguished
    have source_transport (Q : ℕ → SyntheticSpectrum) {B C : SyntheticSpectrum} {j j' : ℕ}
        (hj : j=j') (g : Q j ⟶ B) (f : B ⟶ C) (hz : g≫f=0) :
        Eq.mp (congrArg (fun k => Q k ⟶ B) hj) g ≫ f = 0 := by
      subst j'; exact hz
    have hl : l ≫ (model.quotients.tower A).rho 1 (d+1) (by omega) = 0 :=
      source_transport (fun j => F.obj (XModLambdaN A j)) (Nat.add_sub_cancel d 1) _ _ hl0
    rw [hl,comp_zero]
  · change homotopyRegrade _ _
      (biSuspensionHomEquiv ((t-s)+1) ((t-(q-1:ℕ))-((d+1:ℕ):ℤ)) ((d+1:ℕ):ℤ)
        (XModLambdaN A q) ((β≫l)≫δ1)) = c
    rw [hδ,AddEquiv.apply_symm_apply]
    have regrade_inverse {m m' v v' : ℤ} (hm:m=m') (hv:v=v')
        (b : BiHom m v (XModLambdaN A q)) :
        homotopyRegrade hm.symm hv.symm (homotopyRegrade hm hv b)=b := by
      subst m'; subst v'; rfl
    exact regrade_inverse (by omega) (by omega) c
end
end KIP126.ProofTools.Internal.Mahowald
