module

import KIP126.AdamsCalculations
import KIP126.AdamsCalculations.Table
import KIP126.E2Computation.Table.Values
import KIP126.SpectralSequence.FinitePageCalculus.Proofs

/-! Cofiber finite-page consumers use the actual Adams calculation entry. -/
namespace Tests.AdamsCalculations.SourceConsumers
open CategoryTheory KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.AdamsSynthetic.Standard KIP126.Computation.Standard

theorem cofiberFiniteSurvival :
    SurvivesTo nuCofiberSequence 6 (14,139) (bottom 14 139 T) ∧
      NeverHitOnWindow nuCofiberSequence 2 5 (14,139) (bottom 14 139 T) :=
  ⟨cofiber_target_to_e6, cofiber_target_not_hit_through5⟩

#check_failure KIP126.Computation.ComputationResults
#check_failure KIP126.Computation.Bindings

end Tests.AdamsCalculations.SourceConsumers

/-! The two archived candidates for d₃(x₁₂₆,₆) are genuinely different on
E₃, rather than different E₂ representatives of the same class. The proofs
use only registered upstream interfaces; they introduce no local proof holes.
The exact choice of differential remains unresolved. -/
open CategoryTheory KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.AdamsSynthetic.Standard KIP126.Computation.Standard
open KIP126.Computation.Table KIP126.Core.SpectralSequence.FinitePageCalculus
open KIP126.Core.Algebra
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace Tests.AdamsCalculations.D3X1266
noncomputable section
private abbrev E := model.classical.sphere

private theorem source_zero_d2 : E.d 2 (7,133)=0 := by
  have hs : E.r₀≤2 := by rw [model.classical.firstPage]
  have hr0 : ReachesPage E 18 (7,133) (basis .sphere 7 133 0) := by
    obtain ⟨a,ha,h⟩ := result ⟨.sphere,.reaches,18,7,133,[0],7,133,[],"S0_AdamsE2_ss",2632⟩
      (List.mem_of_getElem? (i:=186) (by rfl))
    dsimp only [Statement] at h
    have hv : Raw.coordinatesValid Raw.degrees .sphere 7 133 [0]=true := rfl
    simp only [decode,hv,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      add_zero,Option.some.injEq] at ha
    rwa [←ha] at h
  have hz0 : E.d 2 (7,133) (basis .sphere 7 133 0)=0 :=
    represents_d_zero_of_later hs (by decide : (2:ℤ)<18)
      (represents_two_self _) hr0
  have hz1 : E.d 2 (7,133) (basis .sphere 7 133 1)=0 := by
    obtain ⟨a,ha,b,hb,hd⟩ := result ⟨.sphere,.equation,2,5,132,[0],7,133,[1],"S0_AdamsE2_ss",2575⟩
      (List.mem_of_getElem? (i:=165) (by rfl))
    dsimp only [Statement] at hd
    have vx : Raw.coordinatesValid Raw.degrees .sphere 5 132 [0]=true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 7 133 [1]=true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at hd
    obtain ⟨z,hz,hdz⟩ := differential_target_cycle hd
    rwa [←hz.eq_on_page_two] at hdz
  obtain ⟨f,hf⟩ := basis_correct ⟨.sphere,7,133,["1,1,69,1,76,1","0,5,69,2"]⟩ (by
    exact List.mem_of_getElem? (i:=150) (by rfl))
  change E.Page 2 (7,133) ≃ₗ[ℤ] (Fin 2 →₀ F2) at f
  change ∀ i : Fin 2, f.symm (Finsupp.single i 1)=basis .sphere 7 133 i.val at hf
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hx := finite_basis_expansion f x
  rw [hx,map_sum]
  apply Finset.sum_eq_zero
  intro i hi
  split_ifs
  · exact map_zero _
  · rw [hf]
    fin_cases i
    · exact hz0
    · exact hz1

private theorem difference_nonzero_e3
    {z : E.Page 3 (9,134)}
    (hz : RepresentsOnPage E 3 (9,134) (basis .sphere 9 134 2) z) : z≠0 := by
  have hs : E.r₀≤2 := by rw [model.classical.firstPage]
  have hdeg : (7,133)+E.diffDeg 2=(9,134) := by
    simp only [E,ClassicalAdamsFamily.sphere,ClassicalAdamsFamily.obj,
      model.classical.differentialDegree,Prod.mk_add_mk,Int.reduceAdd,Int.reduceSub]
  apply represents_next_nonzero_of_incoming_zero_at (hdeg:=hdeg) hs (by decide)
    source_zero_d2 hz (represents_two_self _)
  · obtain ⟨f,hf⟩ := basis_correct ⟨.sphere,9,134,["391,1","390,1","69,1,82,1","18,1,190,1","0,1,375,1"]⟩ (by
      exact List.mem_of_getElem? (i:=173) (by rfl))
    have hh := hf (2:Fin 5)
    intro he
    have eq := congrArg f (hh.trans he)
    exact one_ne_zero (by simpa only [LinearEquiv.apply_symm_apply,map_zero,
      Finsupp.single_eq_zero] using eq)

private theorem difference_binding :
    basis .sphere 9 134 2=product (r:=(9,134)) h6 (atom .b) := by
  have h := basis_value ⟨.mul (.named .h6) (.named .b),2⟩ (by decide)
  simpa only [Expression.value,Expression.degree,atom_h6] using h

private theorem candidates_distinct_e3
    {a b : E.Page 3 (9,134)}
    (ha : RepresentsOnPage E 3 (9,134) d3Candidate a)
    (hb : RepresentsOnPage E 3 (9,134) d3OtherCandidate b) : a≠b := by
  have hr : ReachesPage E 1000 (9,134) (basis .sphere 9 134 2) := by
    obtain ⟨z,hz,h⟩ := result ⟨.sphere,.reaches,1000,9,134,[2],9,134,[],"S0_AdamsE2_ss",2695⟩
      (List.mem_of_getElem? (i:=224) (by rfl))
    dsimp only [Statement] at h
    have hv : Raw.coordinatesValid Raw.degrees .sphere 9 134 [2]=true := rfl
    simp only [decode,hv,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      add_zero,Option.some.injEq] at hz
    rwa [←hz] at h
  obtain ⟨z,hz⟩ := reaches_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤1000) hr
  have hs := represents_add_tail ha hz
  rw [difference_binding] at hs
  change RepresentsOnPage E 3 (9,134) d3OtherCandidate (a+z) at hs
  have he := represents_unique hs hb
  intro hab
  have hzero : z=0 := by simpa only [hab,add_eq_left] using he
  exact difference_nonzero_e3 hz hzero

private theorem candidates_exist_and_distinct :
    ∃ a b : E.Page 3 (9,134),
      RepresentsOnPage E 3 (9,134) d3Candidate a ∧
      RepresentsOnPage E 3 (9,134) d3OtherCandidate b ∧ a≠b := by
  have hreach (n i row idx : ℕ)
      (hc : (⟨.sphere,.reaches,n,9,134,[i],9,134,[],"S0_AdamsE2_ss",row⟩ : Raw.Claim) ∈ Raw.claims)
      (hv : Raw.coordinatesValid Raw.degrees .sphere 9 134 [i]=true) :
      ReachesPage E n (9,134) (basis .sphere 9 134 i) := by
    obtain ⟨z,hz,h⟩ := result _ hc
    dsimp only [Statement] at h
    simp only [decode,hv,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      add_zero,Option.some.injEq] at hz
    rwa [←hz] at h
  obtain ⟨a,ha⟩ := reaches_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤7)
    (hreach 7 3 2696 225 (List.mem_of_getElem? (i:=225) (by rfl)) rfl)
  obtain ⟨z,hz⟩ := reaches_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤1000)
    (hreach 1000 2 2695 224 (List.mem_of_getElem? (i:=224) (by rfl)) rfl)
  have hc : basis .sphere 9 134 3=d3Candidate := by
    have h := basis_value ⟨.mul (.named .h5) (.named .x_94_8),3⟩ (by decide)
    simpa only [d3Candidate,Expression.value,Expression.degree,atom_h5] using h
  rw [hc] at ha
  have hb := represents_add_tail ha hz
  rw [difference_binding] at hb
  change RepresentsOnPage E 3 (9,134) d3OtherCandidate (a+z) at hb
  exact ⟨a,a+z,ha,hb,candidates_distinct_e3 ha hb⟩

private theorem differential_candidates_exclusive :
    ¬ (HasNonzeroDifferential E 3 (6,132) (9,134) (atom .x_126_6) d3Candidate ∧
      HasNonzeroDifferential E 3 (6,132) (9,134) (atom .x_126_6) d3OtherCandidate) := by
  rintro ⟨h,k⟩
  obtain ⟨dg,x,y,hx,hy,hd,_⟩ := h
  obtain ⟨dg',x',y',hx',hy',hd',_⟩ := k
  have hxx : x=x' := represents_unique hx hx'
  have hyy : y=y' := by
    rw [hxx] at hd
    exact hd.symm.trans hd'
  exact candidates_distinct_e3 hy hy' hyy

end
end Tests.AdamsCalculations.D3X1266

/-! Cν coordinate checks for the independent cofiber route. These assertions
concern the fixed table basis. The identification with the actual bottom-cell
map is an explicit hypothesis below: raw monomial strings do not prove it. -/
namespace Tests.AdamsCalculations.CofiberD3X1266
noncomputable section
private abbrev N := KIP126.Computation.Table.sequence .nuCofiber

private theorem incoming_zero_d2 : N.d 2 (7,133)=0 := by
  have hs : N.r₀≤2 := by rw [model.classical.firstPage]
  have hr : ReachesPage N 1000 (7,133) (basis .nuCofiber 7 133 0) := by
    obtain ⟨a,ha,h⟩ := result ⟨.nuCofiber,.reaches,1000,7,133,[0],7,133,[],"Cnu_AdamsE2_ss",3782⟩
      (List.mem_of_getElem? (i:=22) (by rfl))
    dsimp only [Statement] at h
    have hv : Raw.coordinatesValid Raw.degrees .nuCofiber 7 133 [0]=true := rfl
    simp only [decode,hv,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      add_zero,Option.some.injEq] at ha
    rwa [←ha] at h
  have hz0 : N.d 2 (7,133) (basis .nuCofiber 7 133 0)=0 :=
    represents_d_zero_of_later hs (by decide : (2:ℤ)<1000) (represents_two_self _) hr
  have hz1 : N.d 2 (7,133) (basis .nuCofiber 7 133 1)=0 := by
    obtain ⟨a,ha,b,hb,hd⟩ := result ⟨.nuCofiber,.equation,2,5,132,[0],7,133,[1],"Cnu_AdamsE2_ss",3781⟩
      (List.mem_of_getElem? (i:=21) (by rfl))
    dsimp only [Statement] at hd
    have vx : Raw.coordinatesValid Raw.degrees .nuCofiber 5 132 [0]=true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .nuCofiber 7 133 [1]=true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at hd
    obtain ⟨z,hz,hdz⟩ := differential_target_cycle hd
    rwa [←hz.eq_on_page_two] at hdz
  obtain ⟨f,hf⟩ := basis_correct ⟨.nuCofiber,7,133,["1,1,69,1,76,1,0","0,5,69,2,0"]⟩
    (List.mem_of_getElem? (i:=25) (by rfl))
  change N.Page 2 (7,133) ≃ₗ[ℤ] (Fin 2 →₀ F2) at f
  change ∀ i : Fin 2, f.symm (Finsupp.single i 1)=basis .nuCofiber 7 133 i.val at hf
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rw [finite_basis_expansion f x,map_sum]
  apply Finset.sum_eq_zero
  intro i hi
  split_ifs
  · exact map_zero _
  · rw [hf]
    fin_cases i
    · exact hz0
    · exact hz1

private theorem difference_nonzero_e3
    {z : N.Page 3 (9,134)}
    (hz : RepresentsOnPage N 3 (9,134) (basis .nuCofiber 9 134 3) z) : z≠0 := by
  have hs : N.r₀≤2 := by rw [model.classical.firstPage]
  have hdeg : (7,133)+N.diffDeg 2=(9,134) := by
    simp only [N,KIP126.Computation.Table.sequence,model.classical.differentialDegree,
      Prod.mk_add_mk,Int.reduceAdd,Int.reduceSub]
  apply represents_next_nonzero_of_incoming_zero_at (hdeg:=hdeg) hs (by decide)
    incoming_zero_d2 hz (represents_two_self _)
  obtain ⟨f,hf⟩ := basis_correct ⟨.nuCofiber,9,134,
    ["67,1,69,1,1","391,1,0","390,1,0","69,1,82,1,0","18,1,190,1,0","0,1,375,1,0"]⟩
    (List.mem_of_getElem? (i:=33) (by rfl))
  have hh := hf (3:Fin 6)
  intro he
  have eq := congrArg f (hh.trans he)
  exact one_ne_zero (by simpa only [LinearEquiv.apply_symm_apply,map_zero,
    Finsupp.single_eq_zero] using eq)

private theorem difference_reaches_e3 :
    ReachesPage N 3 (9,134) (basis .nuCofiber 9 134 3) := by
  obtain ⟨a,ha,h⟩ := result ⟨.nuCofiber,.reaches,1000,9,134,[3],9,134,[],"Cnu_AdamsE2_ss",3863⟩
    (List.mem_of_getElem? (i:=41) (by rfl))
  dsimp only [Statement] at h
  have hv : Raw.coordinatesValid Raw.degrees .nuCofiber 9 134 [3]=true := rfl
  simp only [decode,hv,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    add_zero,Option.some.injEq] at ha
  rw [←ha] at h
  exact reaches_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤1000) h

private theorem candidates_distinct_e3
    {a b : N.Page 3 (9,134)}
    (ha : RepresentsOnPage N 3 (9,134) (basis .nuCofiber 9 134 4) a)
    (hb : RepresentsOnPage N 3 (9,134)
      (basis .nuCofiber 9 134 4+basis .nuCofiber 9 134 3) b) : a≠b := by
  obtain ⟨z,hz⟩ := difference_reaches_e3
  have he := represents_unique (represents_add_tail ha hz) hb
  intro hab
  have hz0 : z=0 := by simpa only [hab,add_eq_left] using he
  exact difference_nonzero_e3 hz hz0

private theorem difference_not_d2_boundary :
    ¬ IsBoundaryBy N 2 (9,134) (basis .nuCofiber 9 134 3) := by
  obtain ⟨z,hz⟩ := difference_reaches_e3
  intro hb
  have hz0 : z=0 := (RepresentsOnPage.eq_zero_iff_isBoundaryBy
    (E:=N) (r:=2) (p:=(9,134)) (by decide) hz).mpr hb
  exact difference_nonzero_e3 hz hz0

/-- The calibration is deliberately not asserted by this test. Once supplied
by the E₂ layer, it witnesses failure of the proposed bottom-map NC2 test. -/
private theorem bottom_difference_not_d2_boundary
    (hcal : bottom 9 134 (product (r:=(9,134)) h6 (atom .b))=
      basis .nuCofiber 9 134 3) :
    ¬ IsBoundaryBy N 2 (9,134)
      (bottom 9 134 (product (r:=(9,134)) h6 (atom .b))) := by
  rw [hcal]
  exact difference_not_d2_boundary

end
end Tests.AdamsCalculations.CofiberD3X1266
