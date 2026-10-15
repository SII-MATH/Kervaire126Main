module
public import KIP126.Def.ProofTools.Representatives
import all KIP126.Main.Internal.Selected.NuErrorData
import all KIP126.Main.Internal.DetectionLabels
import all KIP126.Main.Internal.QuotientCalculus
import all KIP126.Main.Internal.PageCalculus
import all KIP126.Main.SectionSeven.NuTargetFiniteGap
/-! NuNinth:44–267,1695–1773, bbac1fc05843 (MIT). Reuses the same
proved cumulative-boundary and finite-frame operations. -/
@[expose] section
namespace KIP126.Main.Internal.NuNinth
open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence KIP126.AdamsSynthetic
open KIP126.Core.SpectralSequence KIP126.Core.SpectralSequence.FinitePageCalculus
open KIP126.Kervaire.Route KIP126.Literature KIP126.ProofTools
open KIP126.AdamsSynthetic.Standard (model SyntheticSpectrum)
open KIP126.ProofTools.Operations KIP126.Main.Internal
open KIP126.Main.Internal.Selected.NuError KIP126.Main.SectionSeven.Internal
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
private theorem nu9_not_boundary (X : ClassicalObject) (p : ℤ×ℤ)
    (x : Ambient model X p) (hx : x≠0)
    (hn : NeverHit (model.classical.obj (X.obj model.auxiliary)) p x)
    (b : ℤ) (hb : 1≤b) : x∉boundaries model X b p := by
  intro h
  have hp : IsPermanentCycle (model.classical.obj (X.obj model.auxiliary)) p x := by
    apply (permanent_cycle_iff_mem X p x).mpr
    obtain ⟨y,hy⟩ := h
    let D := (model.classical.obj (X.obj model.auxiliary)).ssData p
    have le : D.B (↑(b-1).toNat)≤D.Z ⊤ := (D.B_mono le_top).trans (D.B_le_Z ⊤)
    refine ⟨(Subobject.ofLE _ _ le) y,?_⟩
    change (Subobject.ofLE _ _ le ≫ cycleLabel model X ⊤ p) y=x
    simpa only [cycleLabel,boundaryLabel,D,←Category.assoc,Subobject.ofLE_comp_ofLE] using hy
  have hs := permanent_survives_of_no_early_hit (by rw [model.classical.firstPage])
    (b+1).toNat (by omega) hp hx (fun r hr _=>hn.not_hit hr)
  have hnat : ((b+1).toNat:ℤ)=b+1 := by omega
  rw [hnat] at hs
  obtain ⟨v,hv,hvn⟩ := hs
  have hz : RepresentsOnPage (model.classical.obj (X.obj model.auxiliary)) (b+1) p x 0 :=
    representsOnPage_of_congruent model X (by omega) (RepresentsOnPage.zero (by omega))
      ⟨by omega,by simpa only [add_sub_cancel_right,sub_zero] using h⟩
  exact hvn (represents_unique hv hz)

private theorem sphere_finite_detection_exists_weak (q k : ℕ) (hq : 0<q) (hk : k<q)
    (s t : ℤ) (x : cycles model .sphere ((q:ℤ)-t+(t-k)) (s,t)) :
    ∃ a : BiHom (t-s) (t-k) (XModLambdaN (S_0_0:SyntheticSpectrum) q),
      Detects (model.convergence (.quotient q .sphere)) (s,t,t-k)
        (quotientLabel q s t k x.val) a := by
  let P := KIP126.Literature.Standard.infinityFiniteWindow .sphere q hq (s,t) (t-k)
    (by constructor <;> omega)
  let en := P.symm (subquotientClass _ _ x)
  have hn := (finite_target_label_iff .sphere q hq s t k hk x en).mpr (P.apply_symm_apply _)
  let f := XModLambdaN.map model.nu.unitIso.hom q
  let e := (model.family.map f).eInftyMap (s,t,t-k) en
  have he : HasInfinityRepresentative (model.family.quotient (S_0_0:SyntheticSpectrum) q) 2 (s,t,t-k)
      (quotientLabel q s t k x.val) e := by
    have hh := family_infinity_representative_map f (s,t,t-k) _ _ hn
    erw [sphere_quotient_label_from_nu q k s t x.val] at hh
    exact hh
  let F := model.syntheticTower.filtration (XModLambdaN (S_0_0:SyntheticSpectrum) q)
  haveI : Epi (F.toAssociatedGraded s (t-s,t-k)) := inferInstanceAs (Epi (cokernel.π _))
  obtain ⟨a,ha⟩ := (ModuleCat.epi_iff_surjective (F.toAssociatedGraded s (t-s,t-k))).mp
    inferInstance (((model.convergence (.quotient q .sphere)).identification (s,t,t-k)).hom e)
  exact ⟨(F.F s (t-s,t-k)).arrow a,e,he,a,rfl,ha.symm⟩

private theorem nu_nine_af12_gap (a : BiHom 125 130 (XModLambdaN (S_0_0:SyntheticSpectrum) 9)) :
    FiltrationAtLeast model.syntheticTower 12 a ↔ FiltrationAtLeast model.syntheticTower 13 a := by
  apply filtration_iff_of_infinity_zero (model.convergence (.quotient 9 .sphere))
    12 13 125 130 (by decide)
  intro j hj hj'
  have : j=12 := by omega
  subst j
  exact finite_sphere_zero_of_classical_quotient 9 (by decide) 12 137 130 (by norm_num)
    nu9_error_data.1

private theorem nu_nine_af13_frame :
    ∀ e : ((model.family.quotient (S_0_0:SyntheticSpectrum) 9).sequence.ssData (13,138,130)).eInfty,
      e=0 ∨ HasInfinityRepresentative (model.family.quotient (S_0_0:SyntheticSpectrum) 9) 2 (13,138,130)
        (quotientLabel 9 13 138 8 (KIP126.Computation.Table.basis .sphere 13 138 1)) e := by
  have hc := nu9_error_data.2.1
  let x : cycles model .sphere ((9:ℤ)-138+(138-(8:ℕ))) (13,138) :=
    ⟨KIP126.Computation.Table.basis .sphere 13 138 1,
      cycles_antitone model .sphere (13,138) (by decide : (1:ℤ)≤2) hc⟩
  apply finite_sphere_frame 9 8 (by decide) (by decide) 13 138 x
  intro y
  obtain ⟨y,rfl⟩ := Quotient.exists_rep y
  rcases nu9_error_data.2.2 y.val with hy|hy
  · exact Or.inl ((subquotientClass_eq_zero_iff _ _ y).mpr hy)
  · right
    apply sub_eq_zero.mp
    change subquotientClass _ _ y-subquotientClass _ _ x=0
    exact (map_sub (subquotientClass _ _) y x).symm.trans
      ((subquotientClass_eq_zero_iff _ _ (y-x)).mpr hy)
end
end KIP126.Main.Internal.NuNinth
