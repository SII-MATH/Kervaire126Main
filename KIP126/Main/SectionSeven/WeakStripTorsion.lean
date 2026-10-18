module
public import KIP126.ProofTools.Representatives
import all KIP126.Main.SectionSeven.NuTargetWindows
/-! The boundary-lift induction of WeakRepresentative.lean:78–222,
bbac1fc05843 (MIT). Incoming detection is obtained through the generic
finite-page theorem instead of opening the quotient implementation. -/
@[expose] section
namespace KIP126.Main.SectionSeven.Internal
open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence KIP126.AdamsSynthetic
open KIP126.Core.SpectralSequence KIP126.Core.SpectralSequence.FinitePageCalculus
open KIP126.AdamsSynthetic.Standard KIP126.Literature KIP126.Kervaire.Route
open KIP126.Main.Internal KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

private theorem sphere_boundary_hit_or_previous (r : ℤ) (hr : 2≤r) (p : ℤ×ℤ)
    (x : model.classical.sphere.Page 2 p) (hx : x∈boundaries model .sphere r p) :
    x∈boundaries model .sphere (r-1) p ∨ HitOnPage model.classical.sphere r p x := by
  let E := model.classical.sphere
  have hrep : RepresentsOnPage E (r+1) p x 0 :=
    KIP126.ProofTools.representsOnPage_of_congruent model .sphere (by omega)
      (RepresentsOnPage.zero (by omega)) ⟨by omega,by simpa only [add_sub_cancel_right,sub_zero] using hx⟩
  obtain ⟨a,ha⟩ := represents_before hr (by omega : r≤r+1) hrep
  by_cases haz : a=0
  · left
    rw [haz] at ha
    exact represents_zero_mem_boundary model .sphere r p x ha
  · right
    let q := p-E.diffDeg r
    have hq : q+E.diffDeg r=p := sub_add_cancel _ _
    have incoming : ∃ u : E.Page r q,
        (E.d r q ≫ eqToHom (congrArg (E.Page r) hq)) u = a := by
      by_contra h
      have hn := represents_next_nonzero_of_not_incoming_at hq
        (by dsimp only [E]; rw [model.classical.firstPage]; exact hr) hr hrep ha
        (fun u hu => h ⟨u,hu⟩)
      exact hn rfl
    obtain ⟨u,hu⟩ := incoming
    exact ⟨q,hq,u,a,ha,haz,hu⟩

private theorem sphere_boundary_torsion_lift (s t : ℤ) (r : ℕ) (hr : 2≤r)
    (x : model.classical.sphere.Page 2 (s,t))
    (hp : x∈permanentCycles model .sphere (s,t))
    (hx : HitOnPage model.classical.sphere r (s,t) x) :
    ∃ a : BiHom (t-s) t (S_0_0 : SyntheticSpectrum),
      sphereFirstQuotient model s t (quotientClass 1 a)=x ∧ lambdaMultiply (r-1) a=0 := by
  have hc : ClassicalPermanentCycle model .sphere (s,t) x := by
    exact (permanent_cycle_iff_mem .sphere (s,t) x).mpr hp
  obtain ⟨a,ha,hat⟩ := KIP126.Literature.Standard.selected_realization_boundary_lift .sphere s t r hr x hc hx
  let e := SyntheticCategory.biShift_zero.hom.app (model.nu.functor.obj SphereSpectrum) ≫ model.nu.unitIso.hom
  refine ⟨a≫e,?_,?_⟩
  · have he : quotientClass 1 (a≫e)=quotientClass 1 a≫XModLambdaN.map e 1 := by
      unfold quotientClass
      simp only [Category.assoc]
      exact congrArg (fun h => a≫h) (XModLambdaN.incl_naturality e 1)
    rw [he,ha]
    exact sphere_first_quotient_label s t x
  · simpa only [lambdaMultiply,Category.assoc,zero_comp] using congrArg (fun f => f≫e) hat

private theorem lambda_multiply_zero_mono {A : SyntheticSpectrum} (a b : ℕ) (hab : a≤b)
    {m w : ℤ} (x : BiHom m w A) (hx : lambdaMultiply a x=0) : lambdaMultiply b x=0 := by
  simp only [lambdaMultiply,comp_eq_zero_iff_of_epi] at hx ⊢
  rw [lambdaPow_add graded_coherence (b-a) a b (Nat.sub_add_cancel hab)]
  simp only [Category.assoc,hx,comp_zero]

theorem sphere_boundary_submodule_torsion_lift (s t : ℤ) (r : ℕ) (hr : 1≤r)
    (x : model.classical.sphere.Page 2 (s,t))
    (hx : x∈boundaries model .sphere r (s,t)) :
    ∃ a : BiHom (t-s) t (S_0_0 : SyntheticSpectrum),
      sphereFirstQuotient model s t (quotientClass 1 a)=x ∧ lambdaMultiply (r-1) a=0 := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    by_cases hr1 : r=1
    · subst r
      have hx0 : x=0 := by simpa only [Nat.cast_one,boundaries_one,Submodule.mem_bot] using hx
      subst x
      refine ⟨0,?_,?_⟩ <;> simp only [quotientClass,lambdaMultiply,zero_comp,comp_zero,map_zero]
    · have hr2 : 2≤r := by omega
      rcases sphere_boundary_hit_or_previous r (by omega) (s,t) x hx with hp|hh
      · have hprev : x∈boundaries model .sphere ((r-1:ℕ):ℤ) (s,t) := by
          simpa only [Nat.cast_sub hr,Nat.cast_one] using hp
        obtain ⟨a,ha,hat⟩ := ih (r-1) (by omega) (by omega) hprev
        exact ⟨a,ha,lambda_multiply_zero_mono (r-1-1) (r-1) (by omega) a hat⟩
      · exact sphere_boundary_torsion_lift s t r hr2 x
          (boundaries_le_permanent_cycles .sphere (s,t) r hx) hh

end
end KIP126.Main.SectionSeven.Internal
