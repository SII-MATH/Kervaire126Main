module

public import KIP126.Main.Conditions
public import KIP126.ProofTools.Operations
public import KIP126.ProofTools.Representatives
import all KIP126.Main.Internal.DetectionLabels
import all KIP126.Main.Internal.QuotientCalculus
import all KIP126.Main.Internal.Selected.SphereDetection

/-! The permanent quotient and synthetic infinity frames used in Proposition
7.8. Source: Selected/DetectionData:1131–1306,1307–1370,1413–1476 at
bbac1fc05843 (MIT), with repeated page-zero arguments shared. -/
@[expose] section
namespace KIP126.Main.Internal.Selected
open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence KIP126.AdamsSynthetic
open KIP126.Core.SpectralSequence KIP126.Kervaire.Route KIP126.Literature
open KIP126.AdamsSynthetic.Standard (model SyntheticSpectrum)
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

private theorem permanent_reaches (X : ClassicalObject) (r : ℤ) (hr : 2≤r) (p : ℤ × ℤ)
    (x : (model.classical.obj (X.obj model.auxiliary)).Page 2 p)
    (hx : x ∈ permanentCycles model X p) :
    ReachesPage (model.classical.obj (X.obj model.auxiliary)) r p x :=
  (KIP126.ProofTools.isCycle_iff_reaches model X r hr p x).mp
    ⟨by omega, permanentCycles_le_cycles model X p (r-1) hx⟩

private theorem permanent_quotient_zero_of_page_zero
    (X : ClassicalObject) (r b : ℤ) (hr : 2≤r) (hb : r-1≤b) (p : ℤ × ℤ)
    (hp : Subsingleton ((model.classical.obj (X.obj model.auxiliary)).Page r p)) :
    Subsingleton (PermanentQuotient model X b p) := by
  have hall (a : PermanentQuotient model X b p) : a=0 := by
    obtain ⟨x,rfl⟩ := Quotient.exists_rep a
    obtain ⟨yr,hy⟩ := permanent_reaches X r hr p x.val x.property
    have hz : yr=0 := hp.elim _ _
    rw [hz] at hy
    have hm := represents_zero_mem_boundary model X r p x.val hy
    exact (subquotientClass_eq_zero_iff _ _ _).mpr (boundaries_monotone model X p hb hm)
  exact ⟨fun a b => (hall a).trans (hall b).symm⟩

private theorem permanent_quotient_frame_of_page
    (r b : ℤ) (hr : 2≤r) (hb : r-1≤b) (s t : ℤ)
    (x : model.classical.sphere.Page 2 (s,t))
    (hx : IsPermanentCycle model.classical.sphere (s,t) x)
    (a : model.classical.sphere.Page r (s,t))
    (ha : RepresentsOnPage model.classical.sphere r (s,t) x a)
    (hall : ∀ y : model.classical.sphere.Page r (s,t), y=0 ∨ y=a) :
    ∃ x' : permanentCycles model .sphere (s,t), x'.val=x ∧
      ∀ q : PermanentQuotient model .sphere b (s,t),
        q=0 ∨ q=subquotientClass _ _ x' := by
  let x' : permanentCycles model .sphere (s,t) :=
    ⟨x,(permanent_cycle_iff_mem .sphere (s,t) x).mp hx⟩
  refine ⟨x',rfl,?_⟩
  intro q
  obtain ⟨y,rfl⟩ := Quotient.exists_rep q
  obtain ⟨yr,hy⟩ := permanent_reaches .sphere r hr (s,t) y.val y.property
  rcases hall yr with h0|h1
  · left
    rw [h0] at hy
    exact (subquotientClass_eq_zero_iff _ _ _).mpr
      (boundaries_monotone model .sphere (s,t) hb
        (represents_zero_mem_boundary model .sphere r (s,t) y.val hy))
  · right
    apply sub_eq_zero.mp
    change subquotientClass _ _ y-subquotientClass _ _ x'=0
    rw [←map_sub]
    apply (subquotientClass_eq_zero_iff _ _ _).mpr
    have hsub := FinitePageCalculus.represents_sub hy ha
    rw [h1,sub_self] at hsub
    exact boundaries_monotone model .sphere (s,t) hb
      (represents_zero_mem_boundary model .sphere r (s,t) _ hsub)

private theorem sphere_frame_of_permanent_quotient
    (s t : ℤ) (k : ℕ) (x : model.classical.sphere.Page 2 (s,t))
    (hq : ∃ x' : permanentCycles model .sphere (s,t), x'.val=x ∧
      ∀ q : PermanentQuotient model .sphere (1+t-(t-k)) (s,t),
        q=0 ∨ q=subquotientClass _ _ x') :
    ∀ e : (model.family.sphere.sequence.ssData (s,t,t-k)).eInfty,
      e=0 ∨ HasInfinityRepresentative model.family.sphere 2 (s,t,t-k)
        (model.comparison.sphereE2 s t k x) e := by
  obtain ⟨x',hx',hframe⟩ := hq
  intro e
  let i : Tridegree := (s,t,t-k)
  let f := (model.family.map model.nu.unitIso.hom).eInftyMap i
  let g := (model.family.map model.nu.unitIso.inv).eInftyMap i
  have hfg : g ≫ f = 𝟙 _ := by
    dsimp only [f,g]
    rw [←SpectralSequenceMorphism.eInftyMap_comp,←SyntheticAdamsFamily.map_comp,Iso.inv_hom_id,
      SyntheticAdamsFamily.map_id,SpectralSequenceMorphism.eInftyMap_id]
  have hback : f (g e)=e := ConcreteCategory.congr_hom hfg e
  let P := KIP126.Literature.Standard.infinityNuWindow .sphere (s,t) (t-k) (by omega)
  rcases hframe (P (g e)) with h0|h1
  · left
    have hg0 : g e=0 := P.injective (h0.trans (map_zero P).symm)
    rw [←hback,hg0,map_zero]
  · right
    have hn := (nu_target_label_iff s t k x'.val (g e)).mpr ⟨x'.property,h1⟩
    have hh := family_infinity_representative_map model.nu.unitIso.hom i _ _ hn
    change HasInfinityRepresentative model.family.sphere 2 i _ (f (g e)) at hh
    rw [hback,sphere_label_from_nu,hx'] at hh
    exact hh

private theorem target_infinity_frame
    (hframe6 : ∃ a : model.classical.sphere.Page 6 (14,139),
      RepresentsOnPage model.classical.sphere 6 (14,139) KIP126.Computation.Standard.T a ∧
      ∀ y : model.classical.sphere.Page 6 (14,139), y=0 ∨ y=a) :
    ∀ e : (model.family.sphere.sequence.ssData (14,139,133)).eInfty,
      e=0 ∨ HasInfinityRepresentative model.family.sphere 2 (14,139,133)
        (model.comparison.sphereE2 14 139 6 KIP126.Computation.Standard.T) e := by
  obtain ⟨a,ha,hall⟩ := hframe6
  exact sphere_frame_of_permanent_quotient 14 139 6 KIP126.Computation.Standard.T
    (permanent_quotient_frame_of_page 6 7 (by decide) (by decide) 14 139
      KIP126.Computation.Standard.T KIP126.Computation.Standard.t_permanent_cycle a ha hall)

private theorem sphere_infinity_zero_of_permanent_quotient_zero
    (s t w : ℤ) (hw : w≤t)
    (h : Subsingleton (PermanentQuotient model .sphere (1+t-w) (s,t))) :
    IsZero ((model.family.sphere.sequence.ssData (s,t,w)).eInfty) := by
  let P := KIP126.Literature.Standard.infinityNuWindow .sphere (s,t) w hw
  haveI := h
  haveI : Subsingleton (((model.family.nu model.nu SphereSpectrum).sequence.ssData (s,t,w)).eInfty) :=
    P.injective.subsingleton
  let hnu := ModuleCat.isZero_of_subsingleton
    (((model.family.nu model.nu SphereSpectrum).sequence.ssData (s,t,w)).eInfty)
  let f := (model.family.map model.nu.unitIso.hom).eInftyMap (s,t,w)
  let g := (model.family.map model.nu.unitIso.inv).eInftyMap (s,t,w)
  have hfg : g ≫ f = 𝟙 _ := by
    dsimp only [f,g]
    rw [←SpectralSequenceMorphism.eInftyMap_comp,←SyntheticAdamsFamily.map_comp,Iso.inv_hom_id,
      SyntheticAdamsFamily.map_id,SpectralSequenceMorphism.eInftyMap_id]
  apply (IsZero.iff_id_eq_zero _).mpr
  exact hfg.symm.trans (by rw [hnu.eq_of_src f 0,comp_zero])

private theorem stem125_filtration_twelve_to_fourteen
    (w : ℤ) (hw : w≤133) (a : BiHom 125 w (S_0_0 : SyntheticSpectrum))
    (ha : FiltrationAtLeast model.syntheticTower 12 a) :
    FiltrationAtLeast model.syntheticTower 14 a := by
  apply (filtration_iff_of_infinity_zero (model.convergence .sphere)
    12 14 125 w (by decide) ?_ a).mp ha
  intro j hj hj'
  apply sphere_infinity_zero_of_permanent_quotient_zero j (125+j) w (by omega)
  interval_cases j
  · exact permanent_quotient_zero_of_page_zero .sphere 4 (1+137-w) (by decide) (by omega) (12,137)
      KIP126.Computation.Standard.e4_stem125_af12
  · exact permanent_quotient_zero_of_page_zero .sphere 5 (1+138-w) (by decide) (by omega) (13,138)
      KIP126.Computation.Standard.e5_stem125_af13

end
end KIP126.Main.Internal.Selected
