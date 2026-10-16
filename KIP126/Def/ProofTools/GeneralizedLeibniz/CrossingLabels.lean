module
import KIP126.Def.ProofTools.Language

/-! Label and boundary comparisons for AimPaper Proposition `prop:cross-f-Er`.
These private lemmas identify actual E∞ representatives and the precise
boundary indeterminacy after multiplication by λ. They do not assert that
a strict extension equation lifts through a λ map. -/
@[expose] section
namespace KIP126.ProofTools.Internal.CrossingLabels
open CategoryTheory KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.Synthetic.SpectralSequence KIP126.Classical.Adams KIP126.AdamsSynthetic
open KIP126.Core.SpectralSequence KIP126.Kervaire.Route KIP126.Literature
open KIP126.AdamsSynthetic.Standard
noncomputable section
set_option backward.isDefEq.respectTransparency false

private theorem subquotient_rep {R A : Type*} [Ring R] [AddCommGroup A] [Module R A]
    (Z B : Submodule R A) (e : E2Subquotient Z B) :
    ∃ y : Z, subquotientClass Z B y = e :=
  Submodule.Quotient.mk_surjective _ e

private theorem subquotient_zero_iff {R A : Type*} [Ring R] [AddCommGroup A] [Module R A]
    (Z B : Submodule R A) (y : Z) : subquotientClass Z B y = 0 ↔ y.val ∈ B :=
  Submodule.Quotient.mk_eq_zero _

private theorem nu_grade_label (X : ClassicalObject) (s t w : ℤ) (hw : w ≤ t)
    (e : ((model.family.nu model.nu (X.obj model.auxiliary)).sequence.ssData (s,t,w)).eInfty) :
    ∃ y : Ambient model X (s,t), y ∈ permanentCycles model X (s,t) ∧
      HasInfinityRepresentative _ 2 (s,t,w) (nuWeightLabel model X s t w hw y) e ∧
      (y ∈ boundaries model X (1+t-w) (s,t) ↔ e = 0) := by
  obtain ⟨y,hy⟩ := subquotient_rep (permanentCycles model X (s,t)) (boundaries model X (1+t-w) (s,t))
    (KIP126.Literature.Standard.infinityNuWindow X (s,t) w hw e)
  have hrep : HasInfinityRepresentative _ 2 (s,t,w)
      (nuWeightLabel model X s t w hw y.val) e := by
    apply (KIP126.Literature.Standard.eInfinity_nu_labels X s t w hw y.val e).mpr
    exact ⟨y.property,hy.symm⟩
  refine ⟨y.val,y.property,hrep,?_⟩
  have hz : y.val ∈ boundaries model X (1+t-w) (s,t) ↔
      KIP126.Literature.Standard.infinityNuWindow X (s,t) w hw e = 0 := by
    rw [←hy]
    exact (subquotient_zero_iff _ _ y).symm
  exact hz.trans (map_eq_zero_iff _ (KIP126.Literature.Standard.infinityNuWindow X (s,t) w hw).injective)

private theorem finite_grade_label (X : ClassicalObject) (q : ℕ) (hq : 0 < q)
    (s t w : ℤ) (hw : 0 ≤ t-w ∧ t-w < q)
    (e : ((model.family.quotient (model.nu.functor.obj (X.obj model.auxiliary)) q).sequence.ssData (s,t,w)).eInfty) :
    ∃ y : Ambient model X (s,t), y ∈ cycles model X (q-t+w) (s,t) ∧
      HasInfinityRepresentative _ 2 (s,t,w)
        ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) q).pageMap 2 (s,t,w)
          (nuWeightLabel model X s t w (by omega) y)) e ∧
      (y ∈ boundaries model X (1+t-w) (s,t) ↔ e = 0) := by
  obtain ⟨y,hy⟩ := subquotient_rep (cycles model X (q-t+w) (s,t)) (boundaries model X (1+t-w) (s,t))
    (KIP126.Literature.Standard.infinityFiniteWindow X q hq (s,t) w hw e)
  have hrep : HasInfinityRepresentative _ 2 (s,t,w)
      ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) q).pageMap 2 (s,t,w)
        (nuWeightLabel model X s t w (by omega) y.val)) e := by
    apply (KIP126.Literature.Standard.eInfinity_finite_labels X q hq s t w hw y.val e).mpr
    exact ⟨y.property,hy.symm⟩
  refine ⟨y.val,y.property,hrep,?_⟩
  have hz : y.val ∈ boundaries model X (1+t-w) (s,t) ↔
      KIP126.Literature.Standard.infinityFiniteWindow X q hq (s,t) w hw e = 0 := by
    rw [←hy]
    exact (subquotient_zero_iff _ _ y).symm
  exact hz.trans (map_eq_zero_iff _ (KIP126.Literature.Standard.infinityFiniteWindow X q hq (s,t) w hw).injective)

private theorem lambda_nu_label_nonzero (X : ClassicalObject) (k : ℕ)
    (s t w : ℤ) (hw : w ≤ t) (y : Ambient model X (s,t))
    (e : ((model.family.nu model.nu (X.obj model.auxiliary)).sequence.ssData (s,t,w)).eInfty)
    (he : HasInfinityRepresentative _ 2 (s,t,w) (nuWeightLabel model X s t w hw y) e) :
    KIP126.Literature.Standard.infinityLambda (.nu X) k (s,t) w e ≠ 0 ↔
      y ∉ boundaries model X (1+t-(w-k)) (s,t) := by
  obtain ⟨hy,hlabel⟩ := (KIP126.Literature.Standard.eInfinity_nu_labels X s t w hw y e).mp he
  have hlam := KIP126.Literature.Standard.eInfinity_lambda_nu X k (s,t) w hw e
  rw [hlabel] at hlam
  change KIP126.Literature.Standard.infinityNuWindow X (s,t) (w-k) (by omega)
      (KIP126.Literature.Standard.infinityLambda (.nu X) k (s,t) w e) =
    subquotientClass (permanentCycles model X (s,t))
      (boundaries model X (1+t-(w-k)) (s,t)) ⟨y,hy⟩ at hlam
  apply not_congr
  constructor
  · intro hzero
    rw [hzero,map_zero] at hlam
    exact (subquotient_zero_iff _ _ ⟨y,hy⟩).mp hlam.symm
  · intro hboundary
    apply (KIP126.Literature.Standard.infinityNuWindow X (s,t) (w-k) (by omega)).injective
    rw [map_zero,hlam]
    exact (subquotient_zero_iff _ _ ⟨y,hy⟩).mpr hboundary

private theorem subquotient_map_class_zero_iff {R A : Type*} [Ring R] [AddCommGroup A] [Module R A]
    {Z Z' B B' : Submodule R A} (hZ : Z ≤ Z') (hB : B ≤ B') (y : Z) :
    subquotientMap hZ hB (subquotientClass Z B y) = 0 ↔ y.val ∈ B' :=
  subquotient_zero_iff Z' B' (Submodule.inclusion hZ y)

private theorem lambda_finite_label_nonzero (X : ClassicalObject) (q k : ℕ) (hkq : k < q)
    (s t w : ℤ) (hw : 0 ≤ t-w ∧ t-w < (q-k:ℕ)) (y : Ambient model X (s,t))
    (e : ((model.family.quotient (model.nu.functor.obj (X.obj model.auxiliary)) (q-k)).sequence.ssData (s,t,w)).eInfty)
    (he : HasInfinityRepresentative _ 2 (s,t,w)
      ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) (q-k)).pageMap 2 (s,t,w)
        (nuWeightLabel model X s t w (by omega) y)) e) :
    KIP126.Literature.Standard.infinityFiniteLambda X q k hkq (s,t) w e ≠ 0 ↔
      y ∉ boundaries model X (1+t-(w-k)) (s,t) := by
  obtain ⟨hy,hlabel⟩ := (KIP126.Literature.Standard.eInfinity_finite_labels X (q-k) (by omega)
    s t w hw y e).mp he
  have hlam := KIP126.Literature.Standard.eInfinity_lambda_finite X q k hkq (s,t) w hw e
  rw [hlabel] at hlam
  have hz := subquotient_map_class_zero_iff
    (cycles_antitone model X (s,t) (show (q:ℤ)-t+(w-k) ≤ (q-k:ℕ)-t+w by omega))
    (boundaries_monotone model X (s,t) (show 1+t-w ≤ 1+t-(w-k) by omega)) ⟨y,hy⟩
  apply not_congr
  constructor
  · intro hzero
    rw [hzero,map_zero] at hlam
    exact hz.mp hlam.symm
  · intro hboundary
    apply (KIP126.Literature.Standard.infinityFiniteWindow X q (by omega) (s,t) (w-k) (by omega)).injective
    rw [map_zero,hlam]
    exact hz.mpr hboundary

end
end KIP126.ProofTools.Internal.CrossingLabels
