module
import all KIP126.ProofTools.GeneralizedLeibniz.LevelLanguage
import all KIP126.ProofTools.GeneralizedLeibniz.RightEdge
import all KIP126.ProofTools.GeneralizedMahowald.BoundaryLambda
/-! Zero-level compatibility of actual finite extension witnesses. The
existing witness equation is transported unchanged; only its labels are
compared. No crossing condition is converted or assumed. -/

@[expose] section
namespace KIP126.ProofTools.Internal.Leibniz
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Standard
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
private theorem finite_witness_native_source_zero (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (page : ℕ) (m s t : ℤ)
    (x : Ambient model X (s,t)) (y : Ambient model Y (s+m,t+m))
    (W : FiniteExtensionWitness model X Y f page m s t x y) :
    ∃ z : ((model.family.obj ((SyntheticObject.quotient (page-1) (.nu X)).obj
        model.nu model.auxiliary)).sequence.ssData (s,t,t-(0:ℕ))).eInfty,
      HasInfinityRepresentative _ 2 (s,t,t-(0:ℕ))
        (finiteTargetLabel model X (page-1) s t 0 x) z := by
  have hpage := W.page_ge_two
  have hx : x∈cycles model X ((page-1:ℕ)-t+(t-(0:ℕ))) (s,t) := by
    have h := ((isCycle_iff_reaches model X page (by omega) (s,t) x).mpr W.source_cycle).2
    convert h using 1
    congr 1
    omega
  let C := KIP126.Literature.Standard.infinityFiniteWindow X (page-1)
    (by omega) (s,t) (t-(0:ℕ)) (by constructor <;> omega)
  let z := C.symm (subquotientClass _ (boundaries model X (1+t-(t-(0:ℕ))) (s,t)) ⟨x,hx⟩)
  refine ⟨z,(finite_target_label_iff X (page-1) (by omega) s t 0 (by omega) ⟨x,hx⟩ z).mpr ?_⟩
  exact C.apply_symm_apply _

private theorem level_zero_projected_weight_heq (X : ClassicalObject) (q : ℕ)
    (s t w w' : ℤ) (hw : w=w') (hwt : w≤t) (hw't : w'≤t)
    (x : Ambient model X (s,t)) :
    HEq ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) q).pageMap
      2 (s,t,w) (nuWeightLabel model X s t w hwt x))
      ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) q).pageMap
        2 (s,t,w') (nuWeightLabel model X s t w' hw't x)) := by
  subst w'
  rfl

private theorem level_finite_target_zero_heq (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (q : ℕ) (m s t : ℤ)
    (hm : (normalizedExponent model.classicalTower f : ℤ)≤m)
    (y : Ambient model Y (s+m,t+m)) :
    HEq (levelFiniteTargetLabel X Y f q 0 m s t hm y)
      (finiteTargetForExtension model X Y f q m s t hm y) := by
  have h := finite_extension_target_weight_label X Y f q m s t hm y
  apply (regradeE2_heq _ _).trans
  exact (level_zero_projected_weight_heq Y q (s+m) (t+m)
    (t+normalizedExponent model.classicalTower f-(0:ℕ))
    (t+normalizedExponent model.classicalTower f) (by omega) (by omega) (by omega) y).trans
      ((heq_of_eq h).symm.trans (regradeE2_heq _ _))

/-- Preserve the actual zero-level finite extension, with the source label
calibrated by the native finite window and the selected quotient shift. -/
private def level_finite_extension_of_zero (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (page : ℕ) (m s t : ℤ)
    (x : Ambient model X (s,t)) (y : Ambient model Y (s+m,t+m))
    (W : FiniteExtensionWitness model X Y f page m s t x y) :
    LevelFiniteExtensionWitness X Y f page 0 m s t x y := by
  let e : ℤ := normalizedExponent model.classicalTower f
  let q := page-1
  have hq : 0<q := by dsimp [q]; have := W.page_ge_two; omega
  have he : e=0 ∨ e=1 := by
    have h := normalizedExponent_le_one model.classicalTower f
    dsimp [e]
    omega
  have hps : (s,(t-s)+s,t+e)=(s,(t-s)+s,t+e-(0:ℕ)) := by simp
  have hpt : (s+m,(t-s)+(s+m),t+e)=(s+m,(t-s)+(s+m),t+e-(0:ℕ)) := by simp
  let zS := (eqToHom (congrArg (fun i => ((model.family.obj
    ((SyntheticObject.quotient q (extensionSourceObject model X Y f)).obj
      model.nu model.auxiliary)).sequence.ssData i).eInfty) hps)) W.source
  let zT := (eqToHom (congrArg (fun i => ((model.family.obj
    ((SyntheticObject.quotient q (.nu Y)).obj
      model.nu model.auxiliary)).sequence.ssData i).eInfty) hpt)) W.target
  have hsourceOld : HasInfinityRepresentative _ 2 (s,(t-s)+s,t+e-(0:ℕ))
      (regradeE2 (by simp) (finiteNuLabel model X q e s t 0 x)) zS := by
    have H := representative_transport hps _ _ W.source_rep
    simpa only [finiteSourceForExtension,normalized_regrade_trans,q,e,zS,
      extensionSourceObject] using H
  let z := Classical.choose (finite_witness_native_source_zero X Y f page m s t x y W)
  have hz := Classical.choose_spec (finite_witness_native_source_zero X Y f page m s t x y W)
  have hsourceEq := level_finite_source_zero_compatible X q hq e s t he x z hz zS hsourceOld
  have hsource : HasInfinityRepresentative _ 2 (s,(t-s)+s,t+e-(0:ℕ))
      (levelFiniteSourceLabel X q e s t 0 x) zS := by
    rw [←hsourceEq]
    exact level_finite_source_representative X q e s t 0 x z hz
  have htarget : HasInfinityRepresentative _ 2 (s+m,(t-s)+(s+m),t+e-(0:ℕ))
      (levelFiniteTargetLabel X Y f q 0 m s t W.length_lower y) zT := by
    have H := representative_transport hpt _ _ W.target_rep
    have hlabel : regradeE2 hpt (finiteTargetForExtension model X Y f q m s t W.length_lower y) =
        levelFiniteTargetLabel X Y f q 0 m s t W.length_lower y :=
      eq_of_heq ((regradeE2_heq _ _).trans
        (level_finite_target_zero_heq X Y f q m s t W.length_lower y).symm)
    rw [hlabel] at H
    exact H
  refine ⟨W.page_ge_two,W.length_lower,W.length_upper,zS,zT,hsource,htarget,?_⟩
  exact left_extension_heq (.quotient q (extensionSourceObject model X Y f))
    (.quotient q (.nu Y)) (finiteExtensionMap model X Y f q)
    (t-s,t+e) (t-s,t+e-(0:ℕ)) (by simp) s m W.source zS W.target zT
    (eqToHom_apply_heq _ W.source).symm (eqToHom_apply_heq _ W.target).symm W.equation

end
end KIP126.ProofTools.Internal.Leibniz
