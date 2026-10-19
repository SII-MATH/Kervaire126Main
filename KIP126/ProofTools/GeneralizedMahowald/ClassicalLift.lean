module

public import KIP126.AdamsSynthetic.Quotients
public import KIP126.ProofTools.Language
import all KIP126.ProofTools.DetectionOperations
import all KIP126.ProofTools.GeneralizedLeibniz.CrossingLabels
import all KIP126.ProofTools.FiniteFiltration

/-! The exact obstruction to lifting a finite MH representative while retaining
both prescribed leading terms. The correction subgroup is the intersection of
the next source filtration and the inverse image of the next target filtration.
The actual lambda quotient case uses its chosen cofiber connecting arrow. -/

@[expose] section
namespace KIP126.ProofTools

section Additive

variable {G GN HN D : Type*}
  [AddCommGroup G] [AddCommGroup GN] [AddCommGroup HN] [AddCommGroup D]

/-- Exactness detects a lift of some representative in the specified affine
family. The originally selected representative need not itself lift. -/
private theorem classical_lift_obstruction_iff
    (p : G →+ GN) (δ : GN →+ D)
    (hExact : AddMonoidHom.range p = AddMonoidHom.ker δ)
    (V : AddSubgroup GN) (c₀ : GN) :
    δ c₀ ∈ V.map δ ↔ ∃ v ∈ V, ∃ α : G, p α = c₀ + v := by
  constructor
  · rintro ⟨v, hv, hδ⟩
    have hz : c₀ - v ∈ AddMonoidHom.ker δ := by
      change δ (c₀ - v) = 0
      rw [map_sub, hδ, sub_self]
    obtain ⟨α, hα⟩ := hExact.symm ▸ hz
    refine ⟨-v, V.neg_mem hv, α, ?_⟩
    simpa only [sub_eq_add_neg] using hα
  · rintro ⟨v, hv, α, hα⟩
    have hz : δ (p α) = 0 := by
      have hmem : p α ∈ AddMonoidHom.range p := ⟨α, rfl⟩
      have hker : p α ∈ AddMonoidHom.ker δ := hExact ▸ hmem
      exact hker
    rw [hα, map_add] at hz
    refine ⟨-v, V.neg_mem hv, ?_⟩
    rw [map_neg]
    exact (eq_neg_iff_add_eq_zero.mpr hz).symm

/-- Source-filtration reflection makes the obstruction criterion equivalent
to a full lift retaining the actual source and target heads. No permanence
assumption on the prescribed target label enters this criterion. -/
private theorem classical_lift_obstruction_filtered_iff
    (p : G →+ GN) (δ : GN →+ D) (φN : GN →+ HN)
    (hExact : AddMonoidHom.range p = AddMonoidHom.ker δ)
    (F : AddSubgroup G) (source : AddSubgroup GN)
    (sourceHigher : AddSubgroup GN) (targetHigher : AddSubgroup HN)
    (hHigher : sourceHigher ≤ source)
    (hReflect : ∀ α : G, p α ∈ source → α ∈ F)
    (c₀ : GN) (hc₀ : c₀ ∈ source) :
    δ c₀ ∈ (sourceHigher ⊓ targetHigher.comap φN).map δ ↔
      ∃ α : G, α ∈ F ∧ p α - c₀ ∈ sourceHigher ∧
        φN (p α) - φN c₀ ∈ targetHigher := by
  rw [classical_lift_obstruction_iff p δ hExact]
  constructor
  · rintro ⟨v, hv, α, hα⟩
    have hsource : p α - c₀ ∈ sourceHigher := by
      rw [hα, add_sub_cancel_left]
      exact hv.1
    refine ⟨α, hReflect α ?_, hsource, ?_⟩
    · rw [hα]
      exact source.add_mem hc₀ (hHigher hv.1)
    · rw [hα, map_add, add_sub_cancel_left]
      exact hv.2
  · rintro ⟨α, _, hs, ht⟩
    refine ⟨p α - c₀, ⟨hs, ?_⟩, α, ?_⟩
    · change φN (p α - c₀) ∈ targetHigher
      rwa [map_sub]
    · abel

/-- The filtered lift criterion is exactly nonempty intersection of the
target-preserving affine family with the image of the full source filtration. -/
private theorem classical_lift_obstruction_affine_iff
    (p : G →+ GN) (δ : GN →+ D) (φN : GN →+ HN)
    (hExact : AddMonoidHom.range p = AddMonoidHom.ker δ)
    (F : AddSubgroup G) (source : AddSubgroup GN)
    (sourceHigher : AddSubgroup GN) (targetHigher : AddSubgroup HN)
    (hHigher : sourceHigher ≤ source)
    (hReflect : ∀ α : G, p α ∈ source → α ∈ F)
    (c₀ : GN) (hc₀ : c₀ ∈ source) :
    δ c₀ ∈ (sourceHigher ⊓ targetHigher.comap φN).map δ ↔
      ({c : GN | c - c₀ ∈ sourceHigher ∧ φN c - φN c₀ ∈ targetHigher} ∩
        (F.map p : Set GN)).Nonempty := by
  rw [classical_lift_obstruction_filtered_iff p δ φN hExact F source
    sourceHigher targetHigher hHigher hReflect c₀ hc₀]
  constructor
  · rintro ⟨α, hα, hs, ht⟩
    exact ⟨p α, ⟨hs, ht⟩, α, hα, rfl⟩
  · rintro ⟨c, ⟨hs, ht⟩, α, hα, rfl⟩
    exact ⟨α, hα, hs, ht⟩

end Additive

section LambdaQuotient

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context

universe u v
variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]
  [HasFunctorialCofiber (C := Syn)]

/-- Exactness on the actual finite lambda quotient, obtained from the chosen
cofiber triangle. This does not use lambda localization or a spectral sequence. -/
private theorem lambda_quotient_range_eq_ker (A : Syn) (N : ℕ) (m w : ℤ) :
    AddMonoidHom.range (Preadditive.rightComp (Smn m w) (XModLambdaN.incl A N)) =
      AddMonoidHom.ker (Preadditive.rightComp (Smn m w) (XModLambdaN.proj A N)) := by
  ext c
  constructor
  · rintro ⟨α, rfl⟩
    change (α ≫ XModLambdaN.incl A N) ≫ XModLambdaN.proj A N = 0
    rw [Category.assoc, XModLambdaN.incl_comp_proj, comp_zero]
  · intro hc
    change c ≫ XModLambdaN.proj A N = 0 at hc
    obtain ⟨α, hα⟩ := (XModLambdaN.cofiberTriangle A N).coyoneda_exact₃
      (XModLambdaN.cofiberTriangle_distinguished A N) c hc
    exact ⟨α, hα.symm⟩

/-- A finite MH affine family contains a full synthetic lift exactly when
its fixed connecting obstruction is a connecting image of an allowed
correction. Both maps are the actual lambda-power cofiber maps. -/
private theorem lambda_quotient_lift_obstruction_iff
    (A : Syn) (N : ℕ) (m w : ℤ)
    (V : AddSubgroup (BiHom m w (XModLambdaN A N)))
    (c₀ : BiHom m w (XModLambdaN A N)) :
    c₀ ≫ XModLambdaN.proj A N ∈
        V.map (Preadditive.rightComp (Smn m w) (XModLambdaN.proj A N)) ↔
      ∃ v ∈ V, ∃ α : BiHom m w A, α ≫ XModLambdaN.incl A N = c₀ + v := by
  exact classical_lift_obstruction_iff
    (Preadditive.rightComp (Smn m w) (XModLambdaN.incl A N))
    (Preadditive.rightComp (Smn m w) (XModLambdaN.proj A N))
    (lambda_quotient_range_eq_ker A N m w) V c₀

/-- The actual lambda-cofiber obstruction with both source and target leading
terms retained. In an application `sourceHigher` and `targetHigher` are the
filtrations immediately above the fixed source and target labels. -/
public theorem lambda_quotient_target_preserving_lift_iff
    (A B : Syn) (N : ℕ) (m w : ℤ)
    (φN : XModLambdaN A N ⟶ XModLambdaN B N)
    (F : AddSubgroup (BiHom m w A))
    (source sourceHigher : AddSubgroup (BiHom m w (XModLambdaN A N)))
    (targetHigher : AddSubgroup (BiHom m w (XModLambdaN B N)))
    (hHigher : sourceHigher ≤ source)
    (hReflect : ∀ α : BiHom m w A, α ≫ XModLambdaN.incl A N ∈ source → α ∈ F)
    (c₀ : BiHom m w (XModLambdaN A N)) (hc₀ : c₀ ∈ source) :
    c₀ ≫ XModLambdaN.proj A N ∈
        (sourceHigher ⊓ targetHigher.comap (Preadditive.rightComp (Smn m w) φN)).map
          (Preadditive.rightComp (Smn m w) (XModLambdaN.proj A N)) ↔
      ∃ α : BiHom m w A, α ∈ F ∧
        α ≫ XModLambdaN.incl A N - c₀ ∈ sourceHigher ∧
        (α ≫ XModLambdaN.incl A N) ≫ φN - c₀ ≫ φN ∈ targetHigher := by
  exact classical_lift_obstruction_filtered_iff
    (Preadditive.rightComp (Smn m w) (XModLambdaN.incl A N))
    (Preadditive.rightComp (Smn m w) (XModLambdaN.proj A N))
    (Preadditive.rightComp (Smn m w) φN)
    (lambda_quotient_range_eq_ker A N m w) F source sourceHigher targetHigher
    hHigher hReflect c₀ hc₀

end LambdaQuotient

section PermanentTarget

open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard KIP126.Literature
open KIP126.ProofTools.Internal
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

private theorem boundary_is_permanent (X : ClassicalObject) (b : ℤ) (p : ℤ × ℤ) :
    KIP126.Literature.boundaries model X b p ≤
      KIP126.Literature.permanentCycles model X p := by
  rintro y ⟨z, rfl⟩
  let E := (model.classical.obj (X.obj model.auxiliary)).ssData p
  refine ⟨(Subobject.ofLE (E.B (↑(b-1).toNat)) (E.Z ⊤)
    ((E.B_mono le_top).trans (E.B_le_Z ⊤))) z, ?_⟩
  change (Subobject.ofLE _ _ _ ≫ cycleLabel model X ⊤ p) z =
    boundaryLabel model X (↑(b-1).toNat) p z
  unfold cycleLabel boundaryLabel
  simp only [← Category.assoc, Subobject.ofLE_comp_ofLE]

/-- A specified visible finite target label is permanent when the same actual
finite target is the projection of a full representative in its prescribed
filtration. The conclusion concerns the original label, with no quotient by
short extension images and no permanence hypothesis on that label. -/
private theorem finite_target_from_full_filtered_lift_is_permanent
    (X : ClassicalObject) (N : ℕ) (hN : 0 < N) (s t w : ℤ)
    (hw : 0 ≤ t-w ∧ t-w < N) (y : Ambient model X (s,t))
    (β : BiHom (t-s) w (model.nu.functor.obj (X.obj model.auxiliary)))
    (hβ : FiltrationAtLeast model.syntheticTower s β)
    (hfinite : Detects (model.convergence (.quotient N (.nu X))) (s,t,w)
      ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) N).pageMap
        2 (s,t,w) (nuWeightLabel model X s t w (by omega) y))
      (β ≫ XModLambdaN.incl _ N)) :
    IsPermanent model X (s,t) y := by
  obtain ⟨e, he, a, ha, hga⟩ := hfinite
  obtain ⟨b, hb⟩ := filtration_representative_exists model.syntheticTower
    (model.nu.functor.obj (X.obj model.auxiliary)) (t-s,w) s β hβ
  let eβ := ((model.convergence (.nu X)).identification (s,t,w)).inv
    ((model.syntheticTower.filtration (model.nu.functor.obj (X.obj model.auxiliary))).toAssociatedGraded
      s (t-s,w) b)
  have hg := grade_natural (.nu X) (.quotient N (.nu X)) (XModLambdaN.incl _ N)
    (s,t,w) b a (by
      exact (congrArg (fun z => z ≫ XModLambdaN.incl _ N) hb).trans ha.symm)
  have heq : (model.family.quotientProjection
      (model.nu.functor.obj (X.obj model.auxiliary)) N).eInftyMap (s,t,w) eβ = e := by
    have hi : ((model.convergence (.quotient N (.nu X))).identification (s,t,w)).inv
        ((model.syntheticTower.filtration
          (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) N)).toAssociatedGraded
            s (t-s,w) a) = e := by
      exact (congrArg ((model.convergence (.quotient N (.nu X))).identification
        (s,t,w)).inv hga.symm).trans
          (((model.convergence (.quotient N (.nu X))).identification
            (s,t,w)).toLinearEquiv.symm_apply_apply e)
    exact hg.symm.trans hi
  obtain ⟨hy, hycl⟩ := (KIP126.Literature.Standard.eInfinity_finite_labels
    X N hN s t w hw y e).mp he
  obtain ⟨z, hz⟩ := CrossingLabels.subquotient_rep
    (KIP126.Literature.permanentCycles model X (s,t))
    (KIP126.Literature.boundaries model X (1+t-w) (s,t))
    (KIP126.Literature.Standard.infinityNuWindow X (s,t) w (by omega) eβ)
  have hr := KIP126.Literature.Standard.eInfinity_rho_nu X N hN (s,t) w hw eβ
  rw [heq, hycl, ← hz] at hr
  have hzc : z.val ∈ KIP126.Literature.cycles model X (N-t+w) (s,t) :=
    permanentCycles_le_cycles model X (s,t) (N-t+w) z.property
  have hclass : subquotientClass (KIP126.Literature.cycles model X (N-t+w) (s,t))
      (KIP126.Literature.boundaries model X (1+t-w) (s,t)) ⟨y, hy⟩ =
    subquotientClass (KIP126.Literature.cycles model X (N-t+w) (s,t))
      (KIP126.Literature.boundaries model X (1+t-w) (s,t)) ⟨z.val, hzc⟩ := hr
  have hzero : subquotientClass (KIP126.Literature.cycles model X (N-t+w) (s,t))
      (KIP126.Literature.boundaries model X (1+t-w) (s,t))
        (⟨y, hy⟩ - ⟨z.val, hzc⟩) = 0 := by
    rw [map_sub, hclass, sub_self]
  have hboundary : y-z.val ∈ KIP126.Literature.boundaries model X (1+t-w) (s,t) :=
    (CrossingLabels.subquotient_zero_iff _ _ _).mp hzero
  have hp := (KIP126.Literature.permanentCycles model X (s,t)).add_mem
    (boundary_is_permanent X (1+t-w) (s,t) hboundary) z.property
  change y ∈ KIP126.Literature.permanentCycles model X (s,t)
  simpa only [sub_add_cancel] using hp

private theorem nu_projection_infinity_injective (X : ClassicalObject)
    (N : ℕ) (hN : 0 < N) (s t w : ℤ) (hw : t-w < N) :
    Function.Injective ((model.family.quotientProjection
      (model.nu.functor.obj (X.obj model.auxiliary)) N).eInftyMap (s,t,w)) := by
  by_cases hlow : 0 ≤ t-w
  · intro x y hxy
    apply (KIP126.Literature.Standard.infinityNuWindow X (s,t) w (by omega)).injective
    apply subquotientMap_injective (permanentCycles_le_cycles model X (s,t) (N-t+w))
    have hx := KIP126.Literature.Standard.eInfinity_rho_nu X N hN (s,t) w ⟨hlow, hw⟩ x
    have hy := KIP126.Literature.Standard.eInfinity_rho_nu X N hN (s,t) w ⟨hlow, hw⟩ y
    rw [hxy] at hx
    exact hx.symm.trans hy
  · haveI : Subsingleton (nuEInftyModel model X (s,t) w) := by
      simp only [nuEInftyModel, show ¬w ≤ t by omega, ite_false]
      infer_instance
    have hsub : Subsingleton (((model.family.nu model.nu
        (X.obj model.auxiliary)).sequence.ssData (s,t,w)).eInfty) :=
      (KIP126.Literature.Standard.eInfinity_nu X (s,t) w).injective.subsingleton
    intro x y _
    exact @Subsingleton.elim _ hsub x y

private theorem full_projection_reflects_filtration (X : ClassicalObject)
    (N : ℕ) (hN : 0 < N) (s m w : ℤ) (hw : m+s-w < N)
    (β : BiHom m w (model.nu.functor.obj (X.obj model.auxiliary)))
    (hβ : FiltrationAtLeast model.syntheticTower s (β ≫ XModLambdaN.incl _ N)) :
    FiltrationAtLeast model.syntheticTower s β := by
  let A := model.nu.functor.obj (X.obj model.auxiliary)
  let p : ℤ × ℤ := (m,w)
  have hzero : FiltrationAtLeast model.syntheticTower 0 β := by
    refine ⟨β ≫ (model.syntheticTower.tower A).zeroIso.inv, ?_⟩
    change (β ≫ (model.syntheticTower.tower A).zeroIso.inv) ≫
      (model.syntheticTower.tower A).projection 0 = β
    simp only [AbstractAdamsTower.projection, Int.toNat_zero,
      (model.syntheticTower.tower A).map_self]
    erw [Category.assoc, Category.id_comp, Iso.inv_hom_id, Category.comp_id]
  by_cases hs : s ≤ 0
  · exact model.syntheticTower.filtrationSubmodule_antitone A p hs hzero
  · let L : ℤ → AddSubgroup (BiHom m w A) := fun k =>
      (model.syntheticTower.filtrationSubmodule A k p).toAddSubgroup
    let E : ℤ → AddSubgroup (BiHom m w (XModLambdaN A N)) := fun k =>
      (model.syntheticTower.filtrationSubmodule (XModLambdaN A N) k p).toAddSubgroup
    have hsN : (0:ℤ) + (s.toNat:ℤ) = s := by omega
    have hpβ : (Preadditive.rightComp (Smn m w) (XModLambdaN.incl A N)) β ∈
        E (0+s.toNat) := by
      change β ≫ XModLambdaN.incl A N ∈ E (0+s.toNat)
      rw [hsN]
      exact hβ
    have hh := finite_filtration_reflection
      (Preadditive.rightComp (Smn m w) (XModLambdaN.incl A N)) L E
      (fun k l hkl a ha => model.syntheticTower.filtrationSubmodule_antitone _ p hkl ha)
      0 s.toNat
      (fun k hk hks a ha hpa => next_filtration_of_infinity_injective
        (model.convergentMap (.nu X) (.quotient N (.nu X)) (XModLambdaN.incl A N))
        p k (nu_projection_infinity_injective X N hN k (m+k) w (by omega)) a ha hpa)
      β hzero hpβ
    rw [hsN] at hh
    exact hh

/-- A full lift of the actual finite target makes the specified visible
classical label permanent. Its full filtration follows from projection
reflection in the retained finite window; it is not an extra hypothesis. -/
public theorem finite_target_from_full_lift_is_permanent
    (X : ClassicalObject) (N : ℕ) (hN : 0 < N) (s t w : ℤ)
    (hw : 0 ≤ t-w ∧ t-w < N) (y : Ambient model X (s,t))
    (β : BiHom (t-s) w (model.nu.functor.obj (X.obj model.auxiliary)))
    (hfinite : Detects (model.convergence (.quotient N (.nu X))) (s,t,w)
      ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) N).pageMap
        2 (s,t,w) (nuWeightLabel model X s t w (by omega) y))
      (β ≫ XModLambdaN.incl _ N)) :
    IsPermanent model X (s,t) y := by
  have hfiniteF : FiltrationAtLeast model.syntheticTower s (β ≫ XModLambdaN.incl _ N) := by
    obtain ⟨_, _, a, ha, _⟩ := hfinite
    have hmem : (β ≫ XModLambdaN.incl _ N) ∈ ModuleCat.subobjectModule _
        ((model.syntheticTower.filtration
          (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) N)).F s (t-s,w)) :=
      ⟨a, ha⟩
    simpa only [SyntheticTowerPresentation.filtration, OrderIso.apply_symm_apply,
      FiltrationAtLeast] using hmem
  have hfull := full_projection_reflects_filtration X N hN s (t-s) w (by omega) β
    hfiniteF
  exact finite_target_from_full_filtered_lift_is_permanent X N hN s t w hw y β hfull hfinite

end
end PermanentTarget
end KIP126.ProofTools
