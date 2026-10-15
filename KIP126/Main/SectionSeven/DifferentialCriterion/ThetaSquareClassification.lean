module

public import KIP126.Def.AdamsSynthetic.SectionSeven.AlphaOne
public import KIP126.Computation.LinCoordinates.Certificates.Model.BasisCatalogue.FiniteCertificates
public import KIP126.Main.SectionSeven.Lambda
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Legacy

@[expose] public section

namespace KIP126.Main.SectionSeven.DifferentialCriterion
open KIP126.SpectralSequence.FinitePageCalculus
open CategoryTheory CategoryTheory.Limits KIP126.Algebra
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.SpectralSequence KIP126.Classical.Adams.PageRepresentatives
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.AdamsSynthetic.SectionSeven
open KIP126.Literature.AdamsSynthetic KIP126.Algebra
open KIP126.LinE2 KIP126.Computation.Near126 KIP126.Computation.SphereAndCofiber
noncomputable section
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u,v} C] [HasFunctorialCofiber (C:=C)]
  {Syn : Type w} [SyntheticCategory.{w,v} Syn] [HasFunctorialCofiber (C:=Syn)]
  {H : Mod2EilenbergMacLane (C:=C)} {M : MilnorCooperations H} {D : AdamsComparison H M Syn}
  {L : SphereAdamsClasses H} {G : TmfDetectionClasses H} {η : BiHom 1 2 (S_0_0:Syn)}
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local irreducible] KIP126.LinE2.homogeneousPart adamsTowerSSData adamsTowerInternalD
private theorem stem124_finite_pages_low124_d2_10 (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G) : (sequence D .sphere).d 2 (10,134) = 0 := by
  classical
  let E := sequence D .sphere
  have hrep2 {p : ℤ × ℤ} (x : E.Page 2 p) : RepresentsOnPage E 2 p x x := by
    exact represents_two_self _
  have h171 : HasDifferential E 4 (6,131) (10,134)
      (I.interpretation.basis .sphere 6 131 0) (I.interpretation.basis .sphere 10 134 0 + I.interpretation.basis .sphere 10 134 3) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,4,6,131,[0],10,134,[0, 3],"S0_AdamsE2_ss",2492⟩ (by
      exact List.mem_of_getElem? (i := 171) (by rfl))
    dsimp only [AdamsStatement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 4 (6,131) (10,134) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 6 131 [0] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 10 134 [0, 3] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [← ha,← hb] at h
    simpa only [add_assoc] using h
  have h172 : HasDifferential E 4 (6,131) (10,134)
      (I.interpretation.basis .sphere 6 131 1) (I.interpretation.basis .sphere 10 134 0 + I.interpretation.basis .sphere 10 134 1 + I.interpretation.basis .sphere 10 134 3 + I.interpretation.basis .sphere 10 134 4) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,4,6,131,[1],10,134,[0, 1, 3, 4],"S0_AdamsE2_ss",2493⟩ (by
      exact List.mem_of_getElem? (i := 172) (by rfl))
    dsimp only [AdamsStatement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 4 (6,131) (10,134) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 6 131 [1] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 10 134 [0, 1, 3, 4] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [← ha,← hb] at h
    simpa only [add_assoc] using h
  have h201 : HasDifferential E 2 (8,133) (10,134)
      (I.interpretation.basis .sphere 8 133 1) (I.interpretation.basis .sphere 10 134 2 + I.interpretation.basis .sphere 10 134 4) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,2,8,133,[1],10,134,[2, 4],"S0_AdamsE2_ss",2630⟩ (by
      exact List.mem_of_getElem? (i := 201) (by rfl))
    dsimp only [AdamsStatement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 2 (8,133) (10,134) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 8 133 [1] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 10 134 [2, 4] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [← ha,← hb] at h
    simpa only [add_assoc] using h
  have h250 : HasDifferential E 5 (10,134) (15,138)
      (I.interpretation.basis .sphere 10 134 3) (I.interpretation.basis .sphere 15 138 1) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,5,10,134,[3],15,138,[1],"S0_AdamsE2_ss",2694⟩ (by
      exact List.mem_of_getElem? (i := 250) (by rfl))
    dsimp only [AdamsStatement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 5 (10,134) (15,138) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 10 134 [3] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 15 138 [1] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [← ha,← hb] at h
    simpa only [add_assoc] using h
  have h249 : ReachesPage E 1000 (10,134) (I.interpretation.basis .sphere 10 134 4) := by
    have hrow := I.adamsStatements ⟨.sphere,.reaches,1000,10,134,[4],10,134,[],"S0_AdamsE2_ss",2693⟩ (by
      exact List.mem_of_getElem? (i := 249) (by rfl))
    dsimp only [AdamsStatement] at hrow
    obtain ⟨a,ha,h⟩ := hrow
    have vx : Raw.coordinatesValid Raw.degrees .sphere 10 134 [4] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha
    rw [← ha] at h
    exact h
  have d03 := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4)
    (hrep2 _) (show ReachesPage E 4 (10,134) _ from ⟨h171.choose_spec.choose_spec.choose, h171.choose_spec.choose_spec.choose_spec.2.1⟩)
  have d0134 : E.d 2 (10,134) (I.interpretation.basis .sphere 10 134 0 + I.interpretation.basis .sphere 10 134 1 + I.interpretation.basis .sphere 10 134 3 + I.interpretation.basis .sphere 10 134 4) = 0 := by
    obtain ⟨_,xr,yr,hxr,hyr,_⟩ := h172
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4) (hrep2 _) ⟨yr,hyr⟩
  have d24 : E.d 2 (10,134) (I.interpretation.basis .sphere 10 134 2 + I.interpretation.basis .sphere 10 134 4) = 0 := by
    obtain ⟨_,hd⟩ := h201.eq_on_page_two
    change E.d 2 (8,133) (I.interpretation.basis .sphere 8 133 1) = _ at hd
    rw [← hd]
    exact congrArg (fun f => f (I.interpretation.basis .sphere 8 133 1)) (E.d_comp_d 2 (8,133))
  have d4 := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<1000) (hrep2 _) h249
  have d3 : E.d 2 (10,134) (I.interpretation.basis .sphere 10 134 3) = 0 := by
    obtain ⟨_,xr,yr,hxr,hyr,_⟩ := h250
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<5) (hrep2 _) ⟨xr,hxr⟩
  have d0 : E.d 2 (10,134) (I.interpretation.basis .sphere 10 134 0) = 0 := by simpa only [map_add,d3,add_zero] using d03
  have d1 : E.d 2 (10,134) (I.interpretation.basis .sphere 10 134 1) = 0 := by simpa only [map_add,d0,d3,d4,zero_add,add_zero] using d0134
  have d2 : E.d 2 (10,134) (I.interpretation.basis .sphere 10 134 2) = 0 := by simpa only [map_add,d4,add_zero] using d24
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,10,134,["389,1","388,1","1,1,366,1","0,1,373,1","0,2,367,1"]⟩ (by
    exact List.mem_of_getElem? (i := 181) (by rfl))
  change E.Page 2 (10,134) ≃ₗ[ℤ] (Fin 5 →₀ KIP126.Algebra.F2) at e
  change ∀i : Fin 5, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 10 134 i.val at he
  have hone (i : Fin 5) : E.d 2 (10,134) (e.symm (Finsupp.single i 1)) = 0 := by
    rw [he]
    fin_cases i
    · exact d0
    · exact d1
    · exact d2
    · exact d3
    · exact d4
  have hall (f : Fin 5 →₀ KIP126.Algebra.F2) : E.d 2 (10,134) (e.symm f) = 0 := by
    induction f using Finsupp.induction with
    | zero => simp
    | @single_add i a f hi ha ih =>
      rw [map_add,map_add,ih,add_zero]
      fin_cases a
      · simp
      · exact hone i
  ext x
  simpa only [LinearEquiv.symm_apply_apply,ModuleCat.hom_zero,LinearMap.zero_apply] using hall (e x)

private theorem stem124_finite_pages_f2_three (f : Fin 3 →₀ F2) :
    f = 0 ∨ f = Finsupp.single 0 1 ∨ f = Finsupp.single 1 1 ∨
    f = Finsupp.single 2 1 ∨ f = Finsupp.single 0 1 + Finsupp.single 1 1 ∨
    f = Finsupp.single 0 1 + Finsupp.single 2 1 ∨
    f = Finsupp.single 1 1 + Finsupp.single 2 1 ∨
    f = Finsupp.single 0 1 + Finsupp.single 1 1 + Finsupp.single 2 1 := by
  classical
  have hf : f = Finsupp.single 0 (f 0) + Finsupp.single 1 (f 1) + Finsupp.single 2 (f 2) := by
    ext i
    fin_cases i <;> simp
  generalize h0 : f 0 = a at hf
  generalize h1 : f 1 = b at hf
  generalize h2 : f 2 = c at hf
  fin_cases a <;> fin_cases b <;> fin_cases c
  all_goals simp only [show (⟨0,by decide⟩ : F2) = 0 from rfl, show (⟨1,by decide⟩ : F2) = 1 from rfl, Finsupp.single_zero, zero_add, add_zero] at hf
  all_goals subst f; tauto

private theorem stem124_finite_pages_low124_af9_four (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 4 (9,133)) ∧
    (∀ y : (sequence D .sphere).Page 4 (12,135),
      RepresentsOnPage (sequence D .sphere) 4 (12,135) (I.interpretation.basis .sphere 12 135 2) y → y ≠ 0) ∧
    ∀ x : (sequence D .sphere).Page 2 (9,133), (sequence D .sphere).d 2 (9,133) x = 0 ∨
      (sequence D .sphere).d 2 (9,133) x = I.interpretation.basis .sphere 11 134 4 := by
  classical
  let E := sequence D .sphere
  have hrep2 {p : ℤ × ℤ} (x : E.Page 2 p) : RepresentsOnPage E 2 p x x := by
    exact represents_two_self _
  have hadd {r : ℤ} {p : ℤ × ℤ} {x y : E.Page 2 p} {xr yr : E.Page r p}
      (hx : RepresentsOnPage E r p x xr) (hy : RepresentsOnPage E r p y yr) :
      RepresentsOnPage E r p (x+y) (xr+yr) := by
    exact represents_add_tail (by assumption) (by assumption)
  have h221 : HasDifferential E 3 (9,133) (12,135)
      (I.interpretation.basis .sphere 9 133 1 + I.interpretation.basis .sphere 9 133 2) (I.interpretation.basis .sphere 12 135 0) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,3,9,133,[1, 2],12,135,[0],"S0_AdamsE2_ss",2626⟩ (by
      exact List.mem_of_getElem? (i := 221) (by rfl))
    dsimp only [AdamsStatement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 3 (9,133) (12,135) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 9 133 [1, 2] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 12 135 [0] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [← ha,← hb] at h
    simpa only [add_assoc] using h
  have h222 : HasDifferential E 3 (9,133) (12,135)
      (I.interpretation.basis .sphere 9 133 0 + I.interpretation.basis .sphere 9 133 2) (I.interpretation.basis .sphere 12 135 1 + I.interpretation.basis .sphere 12 135 2) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,3,9,133,[0, 2],12,135,[1, 2],"S0_AdamsE2_ss",2627⟩ (by
      exact List.mem_of_getElem? (i := 222) (by rfl))
    dsimp only [AdamsStatement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 3 (9,133) (12,135) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 9 133 [0, 2] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 12 135 [1, 2] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [← ha,← hb] at h
    simpa only [add_assoc] using h
  have h223 : HasDifferential E 2 (9,133) (11,134)
      (I.interpretation.basis .sphere 9 133 2) (I.interpretation.basis .sphere 11 134 4) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,2,9,133,[2],11,134,[4],"S0_AdamsE2_ss",2628⟩ (by
      exact List.mem_of_getElem? (i := 223) (by rfl))
    dsimp only [AdamsStatement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 2 (9,133) (11,134) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 9 133 [2] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 11 134 [4] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [← ha,← hb] at h
    simpa only [add_assoc] using h
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,9,133,["374,1", "373,1", "0,1,367,1"]⟩ (by
    exact List.mem_of_getElem? (i := 172) (by rfl))
  change E.Page 2 (9,133) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e
  change ∀ i : Fin 3, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 9 133 i.val at he
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,11,134,["387,1", "386,1", "18,1,189,1", "0,1,69,1,80,1", "0,2,366,1"]⟩ (by
    exact List.mem_of_getElem? (i := 190) (by rfl))
  change E.Page 2 (11,134) ≃ₗ[ℤ] (Fin 5 →₀ F2) at f
  change ∀ i : Fin 5, f.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 11 134 i.val at hf
  obtain ⟨g,hg⟩ := I.basis ⟨.sphere,12,135,["408,1", "0,1,386,1", "0,2,69,1,80,1"]⟩ (by
    exact List.mem_of_getElem? (i := 199) (by rfl))
  change E.Page 2 (12,135) ≃ₗ[ℤ] (Fin 3 →₀ F2) at g
  change ∀ i : Fin 3, g.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 12 135 i.val at hg
  have e0 : e.symm (Finsupp.single 0 1) = I.interpretation.basis .sphere 9 133 0 := he 0
  have e1 : e.symm (Finsupp.single 1 1) = I.interpretation.basis .sphere 9 133 1 := he 1
  have e2 : e.symm (Finsupp.single 2 1) = I.interpretation.basis .sphere 9 133 2 := he 2
  have f4 : f.symm (Finsupp.single 4 1) = I.interpretation.basis .sphere 11 134 4 := hf 4
  have g0 : g.symm (Finsupp.single 0 1) = I.interpretation.basis .sphere 12 135 0 := hg 0
  have g1 : g.symm (Finsupp.single 1 1) = I.interpretation.basis .sphere 12 135 1 := hg 1
  have g2 : g.symm (Finsupp.single 2 1) = I.interpretation.basis .sphere 12 135 2 := hg 2
  have ht2 : I.interpretation.basis .sphere 11 134 4 + I.interpretation.basis .sphere 11 134 4 = 0 := by
    rw [← f4,← f.symm.map_add,← Finsupp.single_add,show (1:F2)+1=0 from rfl,Finsupp.single_zero,map_zero]
  have he22 : I.interpretation.basis .sphere 9 133 2 + I.interpretation.basis .sphere 9 133 2 = 0 := by
    rw [← e2,← e.symm.map_add,← Finsupp.single_add,show (1:F2)+1=0 from rfl,Finsupp.single_zero,map_zero]
  have htne : I.interpretation.basis .sphere 11 134 4 ≠ 0 := by
    intro h
    have hh := congrArg (fun x => f x 4) h
    rw [← f4,LinearEquiv.apply_symm_apply] at hh
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
  obtain ⟨_,v,a,hv,ha,dv⟩ := h221
  obtain ⟨_,w,b,hw,hb,dw⟩ := h222
  have d2v := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) (hrep2 _) ⟨v,hv⟩
  have d2w := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) (hrep2 _) ⟨w,hw⟩
  have d22 : E.d 2 (9,133) (I.interpretation.basis .sphere 9 133 2) = I.interpretation.basis .sphere 11 134 4 := by
    obtain ⟨_,hd⟩ := h223.eq_on_page_two
    exact hd
  have d20 : E.d 2 (9,133) (I.interpretation.basis .sphere 9 133 0) = I.interpretation.basis .sphere 11 134 4 := by
    have hh := congrArg (fun z => z + I.interpretation.basis .sphere 11 134 4) d2w
    simpa only [map_add,d22,add_assoc,ht2,add_zero,zero_add] using hh
  have d21 : E.d 2 (9,133) (I.interpretation.basis .sphere 9 133 1) = I.interpretation.basis .sphere 11 134 4 := by
    have hh := congrArg (fun z => z + I.interpretation.basis .sphere 11 134 4) d2v
    simpa only [map_add,d22,add_assoc,ht2,add_zero,zero_add] using hh
  have hker2 (x : E.Page 2 (9,133)) (hx : E.d 2 (9,133) x = 0) :
      x = 0 ∨ x = I.interpretation.basis .sphere 9 133 1 + I.interpretation.basis .sphere 9 133 2 ∨
      x = I.interpretation.basis .sphere 9 133 0 + I.interpretation.basis .sphere 9 133 2 ∨
      x = (I.interpretation.basis .sphere 9 133 1 + I.interpretation.basis .sphere 9 133 2) +
        (I.interpretation.basis .sphere 9 133 0 + I.interpretation.basis .sphere 9 133 2) := by
    rcases stem124_finite_pages_f2_three (e x) with h|h|h|h|h|h|h|h
    all_goals have hh := congrArg e.symm h
    all_goals simp only [LinearEquiv.symm_apply_apply,map_zero,map_add,e0,e1,e2] at hh
    · exact Or.inl hh
    · exact (htne (by simpa only [hh,d20] using hx)).elim
    · exact (htne (by simpa only [hh,d21] using hx)).elim
    · exact (htne (by simpa only [hh,d22] using hx)).elim
    · right; right; right
      rw [hh]
      calc
        _ = (I.interpretation.basis .sphere 9 133 0 + I.interpretation.basis .sphere 9 133 1) +
          (I.interpretation.basis .sphere 9 133 2 + I.interpretation.basis .sphere 9 133 2) := by rw [he22,add_zero]
        _ = _ := by abel
    · exact Or.inr (Or.inr (Or.inl hh))
    · exact Or.inr (Or.inl hh)
    · exact (htne (by simpa only [hh,map_add,d20,d21,d22,ht2,zero_add] using hx)).elim
  have frame (x : E.Page 3 (9,133)) : x=0 ∨ x=v ∨ x=w ∨ x=v+w := by
    let A := E.ssData (9,133)
    haveI : Epi (A.pageπ 1) := inferInstanceAs (Epi (cokernel.π _))
    obtain ⟨z,hz⟩ := (ModuleCat.epi_iff_surjective (A.pageπ 1)).mp inferInstance x
    let x0 : E.Page 2 (9,133) := (Subobject.ofLE (A.Z 1) (A.Z 0) (A.Z_anti (by decide)) ≫ A.pageπ 0) z
    have hr : RepresentsOnPage E 3 (9,133) x0 x := ⟨by decide,z,rfl,hz⟩
    have hd0 : E.d 2 (9,133) x0 = 0 := by
      change x0 ∈ LinearMap.ker (E.d 2 (9,133)).hom
      rw [← subobjectModule_kernel,E.Z_succ 2 (9,133) (by change (2:ℤ)≤2; omega),subobjectModule_image]
      exact ⟨z,rfl⟩
    rcases hker2 x0 hd0 with h0|h0|h0|h0
    · exact Or.inl (represents_unique (E := E) (h0 ▸ hr) (RepresentsOnPage.zero (by decide)))
    · exact Or.inr (Or.inl (represents_unique (E := E) (h0 ▸ hr) hv))
    · exact Or.inr (Or.inr (Or.inl (represents_unique (E := E) (h0 ▸ hr) hw)))
    · exact Or.inr (Or.inr (Or.inr (represents_unique (E := E) (h0 ▸ hr) (hadd hv hw))))
  have reflect {x : E.Page 2 (12,135)} {y : E.Page 3 (12,135)}
      (h : RepresentsOnPage E 3 (12,135) x y) (hy : y=0) : x=0 := by
    obtain ⟨_,z,hx,hz⟩ := h
    have hp := (next_projection_zero_iff_incoming E 2 (by change (2:ℤ)≤2; omega) (10,134) z).mp (hz.trans hy)
    change (Subobject.ofLE _ _ ((E.ssData (12,135)).Z_anti bot_le) ≫ (E.ssData (12,135)).pageπ 0) z ∈ LinearMap.range (E.d 2 (10,134)).hom at hp
    change (Subobject.ofLE _ _ ((E.ssData (12,135)).Z_anti bot_le) ≫ (E.ssData (12,135)).pageπ 0) z = x at hx
    rw [hx] at hp
    obtain ⟨u,hu⟩ := hp
    rw [stem124_finite_pages_low124_d2_10 I] at hu
    exact hu.symm
  have ane : a ≠ 0 := by
    intro hz
    have hh := congrArg (fun x => g x 0) (reflect ha hz)
    rw [← g0,LinearEquiv.apply_symm_apply] at hh
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
  have bne : b ≠ 0 := by
    intro hz
    have hh := congrArg (fun x => g x 1) (reflect hb hz)
    rw [← g1,← g2,map_add,LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply] at hh
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
  have abne : a+b ≠ 0 := by
    intro hz
    have hh := congrArg (fun x => g x 0) (reflect (hadd ha hb) hz)
    rw [← g0,← g1,← g2,map_add,map_add,LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply] at hh
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
  have dv' : E.d 3 (9,133) v = a := dv
  have dw' : E.d 3 (9,133) w = b := dw
  have hker3 (x : E.Page 3 (9,133)) (hx : E.d 3 (9,133) x=0) : x=0 := by
    rcases frame x with h|h|h|h
    · exact h
    · exact (ane (by simpa only [h,dv'] using hx)).elim
    · exact (bne (by simpa only [h,dw'] using hx)).elim
    · exact (abne (by simpa only [h,map_add,dv',dw'] using hx)).elim
  let S := E.pageShortComplex 3 ((9,133)-E.diffDeg 3)
  have hs : S.Exact := S.moduleCat_exact_iff.mpr (by
    intro x hx
    exact ⟨0,by rw [hker3 x hx,map_zero]⟩)
  refine ⟨ModuleCat.subsingleton_of_isZero ((pageHomologyIso E 3 (9,133)
    (by change (2:ℤ)≤3; omega)).isZero_iff.mpr ((S.exact_iff_isZero_homology).mp hs)), ?_, ?_⟩
  intro y hrep hy
  obtain ⟨_,z,hx,hz⟩ := hrep
  let A := E.ssData (12,135)
  let z1 := (Subobject.ofLE (A.Z 2) (A.Z 1) (A.Z_anti (by decide))) z
  have hr3 : RepresentsOnPage E 3 (12,135) (I.interpretation.basis .sphere 12 135 2) (A.pageπ 1 z1) := by
    refine ⟨by decide,z1,?_,rfl⟩
    change (Subobject.ofLE (A.Z 1) (A.Z 0) (A.Z_anti bot_le) ≫ A.pageπ 0) z1 = _
    dsimp only [z1]
    rw [← CategoryTheory.comp_apply,← Category.assoc,Subobject.ofLE_comp_ofLE]
    exact hx
  have hi := (next_projection_zero_iff_incoming E 3 (by change (2:ℤ)≤3; omega) (9,133) z).mp (hz.trans hy)
  change ∃ u, E.d 3 (9,133) u = A.pageπ 1 z1 at hi
  obtain ⟨u,hu⟩ := hi
  have hsub {x x' : E.Page 2 (12,135)} {a a' : E.Page 3 (12,135)}
      (hx : RepresentsOnPage E 3 (12,135) x a) (hx' : RepresentsOnPage E 3 (12,135) x' a') :
      RepresentsOnPage E 3 (12,135) (x-x') (a-a') := by
    exact represents_sub_tail (by assumption) (by assumption)
  rcases frame u with hu0|hu0|hu0|hu0
  · have hn := reflect hr3 (by rw [← hu,hu0,map_zero])
    have hh := congrArg (fun x => g x 2) hn
    rw [← g2,LinearEquiv.apply_symm_apply] at hh
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
  · have hn := reflect (hsub hr3 ha) (sub_eq_zero.mpr (by rw [← hu,hu0,dv']))
    have hh := congrArg (fun x => g x 2) hn
    rw [← g2,← g0,map_sub,LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply] at hh
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
  · have hn := reflect (hsub hr3 hb) (sub_eq_zero.mpr (by rw [← hu,hu0,dw']))
    have hh := congrArg (fun x => g x 1) hn
    rw [← g2,← g1,map_sub,map_add,LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply] at hh
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
  · have hn := reflect (hsub hr3 (hadd ha hb)) (sub_eq_zero.mpr (by rw [← hu,hu0,map_add,dv',dw']))
    have hh := congrArg (fun x => g x 0) hn
    rw [← g2,← g1,← g0,map_sub,map_add,map_add,LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply] at hh
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
  intro x
  change E.d 2 (9,133) x = 0 ∨ E.d 2 (9,133) x = I.interpretation.basis .sphere 11 134 4
  rcases stem124_finite_pages_f2_three (e x) with h|h|h|h|h|h|h|h
  all_goals have hh := congrArg e.symm h
  all_goals simp only [LinearEquiv.symm_apply_apply,map_zero,map_add,e0,e1,e2] at hh
  all_goals simp only [hh,map_zero,map_add,d20,d21,d22,ht2,zero_add]; tauto

private theorem stem124_finite_pages_s8_d2 (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G) :
    (sequence D .sphere).d 2 (8,132) (I.interpretation.basis .sphere 8 132 0) =
      I.interpretation.basis .sphere 10 133 2 := by
  classical
  let E := sequence D .sphere
  have hrow := I.adamsStatements
    ⟨.sphere, .equation, 2, 8, 132, [0], 10, 133, [2], "S0_AdamsE2_ss", 2571⟩ (by
      exact List.mem_of_getElem? (i := 199) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x, hx, y, hy, h⟩ := hrow
  change I.interpretation.coordinateSum .sphere 8 132 [0] = some x at hx
  change I.interpretation.coordinateSum .sphere 10 133 [2] = some y at hy
  change HasDifferential E 2 (8,132) (10,133) x y at h
  have hx' : x = I.interpretation.basis .sphere 8 132 0 := by
    have hv : Raw.coordinatesValid Raw.degrees .sphere 8 132 [0] = true := by decide
    exact Option.some.inj (hx.symm.trans (by simp [E2Interpretation.coordinateSum, hv]))
  have hy' : y = I.interpretation.basis .sphere 10 133 2 := by
    have hv : Raw.coordinatesValid Raw.degrees .sphere 10 133 [2] = true := by decide
    exact Option.some.inj (hy.symm.trans (by simp [E2Interpretation.coordinateSum, hv]))
  have hd : E.d 2 (8,132) (I.interpretation.basis .sphere 8 132 0) =
      I.interpretation.basis .sphere 10 133 2 := by
    obtain ⟨_, hd⟩ := h.eq_on_page_two
    have hd' : E.d 2 (8,132) x = y := by exact hd
    rw [hx', hy'] at hd'
    exact hd'
  exact hd

private theorem stem124_finite_pages_s8_basis (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G) : ∃ e : (sequence D .sphere).Page 2 (8,132) ≃ₗ[ℤ] (Fin 1 →₀ KIP126.Algebra.F2), ∀i, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 8 132 i.val := by
  classical
  let E := sequence D .sphere
  obtain ⟨e, he⟩ := I.basis ⟨.sphere, 8, 132, ["367,1"]⟩ (by
      exact List.mem_of_getElem? (i := 160) (by rfl))
  change E.Page 2 (8,132) ≃ₗ[ℤ] (Fin 1 →₀ KIP126.Algebra.F2) at e
  change ∀ i : Fin 1, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 8 132 i.val at he
  exact ⟨e,he⟩

private theorem stem124_finite_pages_s10_basis (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G) : ∃ f : (sequence D .sphere).Page 2 (10,133) ≃ₗ[ℤ] (Fin 3 →₀ KIP126.Algebra.F2), ∀i, f.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 10 133 i.val := by
  classical
  let E := sequence D .sphere
  obtain ⟨f, hf⟩ := I.basis ⟨.sphere, 10, 133, ["372,1", "69,1,80,1", "0,1,366,1"]⟩ (by
      exact List.mem_of_getElem? (i := 180) (by rfl))
  change E.Page 2 (10,133) ≃ₗ[ℤ] (Fin 3 →₀ KIP126.Algebra.F2) at f
  change ∀ i : Fin 3, f.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 10 133 i.val at hf
  exact ⟨f,hf⟩

private theorem stem124_finite_pages_low124_af8_three (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G) : Subsingleton ((sequence D .sphere).Page 3 (8,132)) := by
  classical
  let E := sequence D .sphere
  have hd := stem124_finite_pages_s8_d2 I
  obtain ⟨e, he⟩ := stem124_finite_pages_s8_basis I
  obtain ⟨f,hf⟩ := stem124_finite_pages_s10_basis I
  have hf2 : f.symm (Finsupp.single 2 1) = I.interpretation.basis .sphere 10 133 2 := hf 2
  have he0 : e.symm (Finsupp.single 0 1) = I.interpretation.basis .sphere 8 132 0 := he 0
  have hn : I.interpretation.basis .sphere 10 133 2 ≠ 0 := by
    rw [← hf2]
    intro hzero
    have hz := congrArg (fun y => f y 2) hzero
    simp at hz
  have hde : ∀ z, E.d 2 (8,132) (e.symm z) = 0 → z = 0 := by
    intro z hz
    have hzrepr : z = Finsupp.single 0 (z 0) := by
      apply Finsupp.ext
      intro i
      fin_cases i
      simp
    rw [hzrepr] at hz
    have hc : z 0 = 0 ∨ z 0 = 1 := by generalize z 0 = a; fin_cases a <;> simp
    rcases hc with hc | hc
    · rw [hzrepr, hc, Finsupp.single_zero]
    · rw [hc, he0, hd] at hz
      exact (hn hz).elim
  have hinj : Function.Injective (E.d 2 (8,132)) := by
    apply (injective_iff_map_eq_zero _).mpr
    intro z hz
    apply e.injective
    simpa using hde (e z) (by simpa using hz)
  let S := E.pageShortComplex 2 ((8,132)-E.diffDeg 2)
  have hs : Function.Injective S.g := hinj
  have hsex : S.Exact := S.moduleCat_exact_iff.mpr (by
    intro z hz
    have hz0 : z = 0 := hs (hz.trans (map_zero _).symm)
    exact ⟨0, by simp [hz0]⟩)
  have hzero := (S.exact_iff_isZero_homology).mp hsex
  exact ModuleCat.subsingleton_of_isZero ((pageHomologyIso E 2 (8,132)
    (by change (2:ℤ)≤2; omega)).isZero_iff.mpr hzero)

private theorem stem124_finite_pages_low124_s7_four (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G) :
    ∃ b : (sequence D .sphere).Page 4 (7,131),
      RepresentsOnPage (sequence D .sphere) 4 (7,131) (I.interpretation.basis .sphere 7 131 1) b ∧
      (∀ a : (sequence D .sphere).Page 4 (7,131), a=0 ∨ a=b) ∧
      (sequence D .sphere).d 4 (7,131) = 0 := by
  classical
  let E := sequence D .sphere
  have h163 : HasDifferential E 2 (5,130) (7,131)
      (I.interpretation.basis .sphere 5 130 0) (I.interpretation.basis .sphere 7 131 2) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,2,5,130,[0],7,131,[2],"S0_AdamsE2_ss",2435⟩ (by
      exact List.mem_of_getElem? (i := 163) (by rfl))
    dsimp only [AdamsStatement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 2 (5,130) (7,131) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 5 130 [0] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 7 131 [2] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [← ha,← hb] at h
    simpa only [add_assoc] using h
  have h182 : HasDifferential E 5 (7,131) (12,135)
      (I.interpretation.basis .sphere 7 131 1) (I.interpretation.basis .sphere 12 135 2) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,5,7,131,[1],12,135,[2],"S0_AdamsE2_ss",2490⟩ (by
      exact List.mem_of_getElem? (i := 182) (by rfl))
    dsimp only [AdamsStatement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 5 (7,131) (12,135) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 7 131 [1] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 12 135 [2] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [← ha,← hb] at h
    simpa only [add_assoc] using h
  have h183 : HasDifferential E 3 (7,131) (10,133)
      (I.interpretation.basis .sphere 7 131 0) (I.interpretation.basis .sphere 10 133 0 + I.interpretation.basis .sphere 10 133 1) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,3,7,131,[0],10,133,[0, 1],"S0_AdamsE2_ss",2491⟩ (by
      exact List.mem_of_getElem? (i := 183) (by rfl))
    dsimp only [AdamsStatement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 3 (7,131) (10,133) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 7 131 [0] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 10 133 [0, 1] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [← ha,← hb] at h
    simpa only [add_assoc] using h
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,7,131,["353,1", "69,1,75,1", "0,1,339,1"]⟩ (by
    exact List.mem_of_getElem? (i := 148) (by rfl))
  change E.Page 2 (7,131) ≃ₗ[ℤ] (Fin 3 →₀ KIP126.Algebra.F2) at e
  change ∀ i : Fin 3, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 7 131 i.val at he
  obtain ⟨f,hf⟩ := stem124_finite_pages_s8_basis I
  obtain ⟨g,hg⟩ := stem124_finite_pages_s10_basis I
  have g0 : g.symm (Finsupp.single 0 1) = I.interpretation.basis .sphere 10 133 0 := hg 0
  have g1 : g.symm (Finsupp.single 1 1) = I.interpretation.basis .sphere 10 133 1 := hg 1
  have g2 : g.symm (Finsupp.single 2 1) = I.interpretation.basis .sphere 10 133 2 := hg 2
  obtain ⟨_,a,c,ha,hc,hd⟩ := h183
  obtain ⟨_,b5,z5,hb5,hz5,hd5⟩ := h182
  obtain ⟨b,hb⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤5) hb5
  have htzero : RepresentsOnPage E 3 (7,131) (I.interpretation.basis .sphere 7 131 2) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) h163
  have hcn : c ≠ 0 := by
    intro hc0
    obtain ⟨_,z,hx,hz⟩ := hc
    have hin := (next_projection_zero_iff_incoming E 2 (by change (2:ℤ)≤2; omega) (8,132) z).mp (hz.trans hc0)
    change ∃ u, E.d 2 (8,132) u = (Subobject.ofLE _ _ ((E.ssData (10,133)).Z_anti bot_le) ≫ (E.ssData (10,133)).pageπ 0) z at hin
    change (Subobject.ofLE _ _ ((E.ssData (10,133)).Z_anti bot_le) ≫ (E.ssData (10,133)).pageπ 0) z = _ at hx
    rw [hx] at hin
    obtain ⟨u,hu⟩ := hin
    have hrepr : f u = Finsupp.single 0 ((f u) 0) := by
      apply Finsupp.ext
      intro i
      fin_cases i
      simp
    have hu0 : u = f.symm (Finsupp.single 0 ((f u) 0)) := by
      rw [← hrepr,LinearEquiv.symm_apply_apply]
    rw [hu0] at hu
    generalize hcoef : (f u) 0 = v at hu
    fin_cases v
    · simp only [show (⟨0,by decide⟩ : KIP126.Algebra.F2)=0 from rfl,Finsupp.single_zero,map_zero] at hu
      have hh := congrArg (fun q => g q 0) hu
      rw [← g0,← g1,map_add,LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change E.d 2 (8,132) (f.symm (Finsupp.single 0 1)) = _ at hu
      have f0 : f.symm (Finsupp.single 0 1) = I.interpretation.basis .sphere 8 132 0 := hf 0
      have hs8 : E.d 2 (8,132) (I.interpretation.basis .sphere 8 132 0) = I.interpretation.basis .sphere 10 133 2 := stem124_finite_pages_s8_d2 I
      rw [f0,hs8] at hu
      have hh := congrArg (fun q => g q 0) hu
      rw [← g0,← g1,← g2,map_add,LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
  have frame3 (x : E.Page 3 (7,131)) : x=0 ∨ x=a ∨ x=b ∨ x=a+b := by
    let v : Fin 3 → E.Page 3 (7,131) := ![a,b,0]
    have hv (i : Fin 3) : RepresentsOnPage E 3 (7,131) (e.symm (Finsupp.single i 1)) (v i) := by
      rw [he i]
      fin_cases i
      · exact ha
      · exact hb
      · exact htzero
    obtain ⟨coeff,hcoeff⟩ := page_generated_from_representatives (by decide : (2:ℤ)≤3) e v hv x
    simp only [Fin.sum_univ_three] at hcoeff
    change x = (if coeff 0=0 then 0 else a) + (if coeff 1=0 then 0 else b) + (if coeff 2=0 then 0 else 0) at hcoeff
    by_cases h0 : coeff 0 = 0 <;> by_cases h1 : coeff 1 = 0
    all_goals simp only [h0,h1,ite_true,ite_false,ite_self,add_zero,zero_add] at hcoeff
    · exact Or.inl hcoeff
    · exact Or.inr (Or.inr (Or.inl hcoeff))
    · exact Or.inr (Or.inl hcoeff)
    · exact Or.inr (Or.inr (Or.inr hcoeff))
  have hda : E.d 3 (7,131) a = c := hd
  have hdb : E.d 3 (7,131) b = 0 :=
    represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<5) hb ⟨b5,hb5⟩
  have ker3 (x : E.Page 3 (7,131)) (hx : E.d 3 (7,131) x=0) : x=0 ∨ x=b := by
    rcases frame3 x with h|h|h|h
    · exact Or.inl h
    · exact (hcn (by simpa only [h,hda] using hx)).elim
    · exact Or.inr h
    · exact (hcn (by simpa only [h,map_add,hda,hdb,add_zero] using hx)).elim
  obtain ⟨b4,hb4⟩ := represents_before (by decide : (2:ℤ)≤4) (by decide : (4:ℤ)≤5) hb5
  have hb4save := hb4
  obtain ⟨_,z,hz,hzb⟩ := hb4
  have hz3 : RepresentsOnPage E 3 (7,131) (I.interpretation.basis .sphere 7 131 1)
      ((Subobject.ofLE _ _ ((E.ssData (7,131)).Z_anti (by decide : (1:WithTop ℕ)≤2)) ≫ (E.ssData (7,131)).pageπ 1) z) := by
    refine ⟨by decide, (Subobject.ofLE _ _ ((E.ssData (7,131)).Z_anti (by decide : (1:WithTop ℕ)≤2))) z, ?_,rfl⟩
    change ((Subobject.ofLE _ _ ((E.ssData (7,131)).Z_anti (by decide : (1:WithTop ℕ)≤2))) ≫ Subobject.ofLE _ _ _ ≫ (E.ssData (7,131)).pageπ 0) z = _
    rw [← Category.assoc,Subobject.ofLE_comp_ofLE]
    exact hz
  have frame4 (x : E.Page 4 (7,131)) : x=0 ∨ x=b4 := by
    have h := next_page_two_of_kernel E 3 (by change (2:ℤ)≤3; omega) (7,131) z (by
      intro q hq
      have hk := ker3 q hq
      rwa [represents_unique (E := E) hb hz3] at hk) x
    change x=0 ∨ x=(E.ssData (7,131)).pageπ 2 z at h
    change (E.ssData (7,131)).pageπ 2 z=b4 at hzb
    rwa [hzb] at h
  refine ⟨b4,hb4save,frame4,?_⟩
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rcases frame4 x with hx|hx
  · simp only [hx,map_zero]
  · rw [hx]
    exact represents_d_zero_of_later (by change (2:ℤ)≤4; omega) (by decide : (4:ℤ)<5) hb4save ⟨b5,hb5⟩

private theorem stem124_finite_pages_low124_s7_six (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G)
    (h8 : Subsingleton ((sequence D .sphere).Page 4 (8,132)))
    (htarget : ∀ y : (sequence D .sphere).Page 4 (12,135),
      RepresentsOnPage (sequence D .sphere) 4 (12,135) (I.interpretation.basis .sphere 12 135 2) y → y ≠ 0) :
    Subsingleton ((sequence D .sphere).Page 6 (7,131)) := by
  classical
  let E := sequence D .sphere
  obtain ⟨b4,hb4,frame4,hd4⟩ := stem124_finite_pages_low124_s7_four I
  have h182 : HasDifferential E 5 (7,131) (12,135)
      (I.interpretation.basis .sphere 7 131 1) (I.interpretation.basis .sphere 12 135 2) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,5,7,131,[1],12,135,[2],"S0_AdamsE2_ss",2490⟩ (by
      exact List.mem_of_getElem? (i := 182) (by rfl))
    dsimp only [AdamsStatement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 5 (7,131) (12,135) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 7 131 [1] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 12 135 [2] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [← ha,← hb] at h
    simpa only [add_assoc] using h
  obtain ⟨_,b5,c5,hb5,hc5,hd5⟩ := h182
  obtain ⟨c4,hc4⟩ := represents_before (by decide : (2:ℤ)≤4) (by decide : (4:ℤ)≤5) hc5
  have hc4n : c4 ≠ 0 := htarget c4 hc4
  have hin : E.d 4 ((12,135)-E.diffDeg 4) = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change E.d 4 (8,132) x = 0
    rw [h8.elim x 0,map_zero]
  have hc5n : c5 ≠ 0 := represents_next_nonzero_of_incoming_zero
    (by change (2:ℤ)≤4; omega) (by decide : (2:ℤ)≤4) hin hc5 hc4 hc4n
  have hb5save := hb5
  obtain ⟨_,z,hz,hzb⟩ := hb5
  have hz4 : RepresentsOnPage E 4 (7,131) (I.interpretation.basis .sphere 7 131 1)
      ((Subobject.ofLE _ _ ((E.ssData (7,131)).Z_anti (by decide : (2:WithTop ℕ)≤3)) ≫ (E.ssData (7,131)).pageπ 2) z) := by
    refine ⟨by decide, (Subobject.ofLE _ _ ((E.ssData (7,131)).Z_anti (by decide : (2:WithTop ℕ)≤3))) z, ?_,rfl⟩
    change ((Subobject.ofLE _ _ ((E.ssData (7,131)).Z_anti (by decide : (2:WithTop ℕ)≤3))) ≫ Subobject.ofLE _ _ _ ≫ (E.ssData (7,131)).pageπ 0) z = _
    rw [← Category.assoc,Subobject.ofLE_comp_ofLE]
    exact hz
  have frame5 (x : E.Page 5 (7,131)) : x=0 ∨ x=b5 := by
    have h := next_page_two_of_kernel E 4 (by change (2:ℤ)≤4; omega) (7,131) z (by
      intro q hq
      have hk := frame4 q
      rwa [represents_unique (E := E) hb4 hz4] at hk) x
    change x=0 ∨ x=(E.ssData (7,131)).pageπ 3 z at h
    change (E.ssData (7,131)).pageπ 3 z=b5 at hzb
    rwa [hzb] at h
  have hd5' : E.d 5 (7,131) b5=c5 := hd5
  have ker5 (x : E.Page 5 (7,131)) (hx : E.d 5 (7,131) x=0) : x=0 := by
    rcases frame5 x with hx0|hxb
    · exact hx0
    · exact (hc5n (by simpa only [hxb,hd5'] using hx)).elim
  let S := E.pageShortComplex 5 ((7,131)-E.diffDeg 5)
  have hex : S.Exact := S.moduleCat_exact_iff.mpr (by
    intro x hx
    exact ⟨0,by rw [ker5 x hx,map_zero]⟩)
  exact ModuleCat.subsingleton_of_isZero ((pageHomologyIso E 5 (7,131)
    (by change (2:ℤ)≤5; omega)).isZero_iff.mpr ((S.exact_iff_isZero_homology).mp hex))

private theorem stem124_finite_pages_low124_af6_six (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G)
    (h74 : (sequence D .sphere).d 4 (7,131) = 0) : Subsingleton ((sequence D .sphere).Page 6 (6,130)) := by
  classical
  let E := sequence D .sphere
  have hrow := I.adamsStatements ⟨.sphere,.equation,5,6,130,[0],11,134,[2],"S0_AdamsE2_ss",2434⟩ (by
    exact List.mem_of_getElem? (i := 170) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,h⟩ := hrow
  change HasDifferential E 5 (6,130) (11,134) x y at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 6 130 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 11 134 [2] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [← hx,← hy] at h
  obtain ⟨_,x5,y5,hx5,hy5,hd5⟩ := h
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,6,130,["339,1"]⟩ (by
    exact List.mem_of_getElem? (i := 136) (by rfl))
  change E.Page 2 (6,130) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e
  change ∀ i : Fin 1, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 6 130 i.val at he
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,11,134,["387,1", "386,1", "18,1,189,1", "0,1,69,1,80,1", "0,2,366,1"]⟩ (by
    exact List.mem_of_getElem? (i := 190) (by rfl))
  change E.Page 2 (11,134) ≃ₗ[ℤ] (Fin 5 →₀ F2) at f
  change ∀ i : Fin 5, f.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 11 134 i.val at hf
  have f2 : f.symm (Finsupp.single 2 1) = I.interpretation.basis .sphere 11 134 2 := hf 2
  have f4 : f.symm (Finsupp.single 4 1) = I.interpretation.basis .sphere 11 134 4 := hf 4
  have target3 (z3 : E.Page 3 (11,134))
      (h3 : RepresentsOnPage E 3 (11,134) (I.interpretation.basis .sphere 11 134 2) z3) : z3 ≠ 0 := by
    intro hz3
    obtain ⟨_,z,hz,hzp⟩ := h3
    have hi := (next_projection_zero_iff_incoming E 2 (by change (2:ℤ)≤2; omega) (9,133) z).mp (hzp.trans hz3)
    change ∃ u, E.d 2 (9,133) u = (Subobject.ofLE _ _ ((E.ssData (11,134)).Z_anti bot_le) ≫ (E.ssData (11,134)).pageπ 0) z at hi
    obtain ⟨u,hu⟩ := hi
    have hlabel : E.d 2 (9,133) u = I.interpretation.basis .sphere 11 134 2 := hu.trans hz
    rcases (stem124_finite_pages_low124_af9_four I).2.2 u with hu0|hu4
    · have hh := congrArg (fun x => f x 2) (hu0.symm.trans hlabel)
      rw [← f2,LinearEquiv.apply_symm_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · have hh := congrArg (fun x => f x 2) (hu4.symm.trans hlabel)
      rw [← f2,← f4,LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
  obtain ⟨y3,hy3⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤5) hy5
  obtain ⟨y4,hy4⟩ := represents_before (by decide : (2:ℤ)≤4) (by decide : (4:ℤ)≤5) hy5
  have hin3 : E.d 3 ((11,134)-E.diffDeg 3) = 0 := by
    ext z
    change E.d 3 (8,132) z = 0
    rw [(stem124_finite_pages_low124_af8_three I).elim z 0,map_zero]
  have hy4ne := represents_next_nonzero_of_incoming_zero (by change (2:ℤ)≤3; omega)
    (by decide : (2:ℤ)≤3) hin3 hy4 hy3 (target3 y3 hy3)
  have hin4 : E.d 4 ((11,134)-E.diffDeg 4) = 0 := h74
  have hy5ne := represents_next_nonzero_of_incoming_zero (by change (2:ℤ)≤4; omega)
    (by decide : (2:ℤ)≤4) hin4 hy5 hy4 hy4ne
  have he0 : e.symm (Finsupp.single 0 1) = I.interpretation.basis .sphere 6 130 0 := he 0
  have hbas (i : Fin 1) : RepresentsOnPage E 5 (6,130) (e.symm (Finsupp.single i 1)) x5 := by
    have hi : i=0 := Fin.eq_zero i
    subst i
    exact he0.symm ▸ hx5
  have frame (z : E.Page 5 (6,130)) : z=0 ∨ z=x5 := by
    obtain ⟨c,hc⟩ := page_generated_from_representatives (E := E) (r := 5) (p := (6,130))
      (by decide) e (fun _ => x5) hbas z
    simp only [Fin.sum_univ_one] at hc
    split_ifs at hc <;> tauto
  have hd5' : E.d 5 (6,130) x5 = y5 := hd5
  have hker5 (z : E.Page 5 (6,130)) (hz : E.d 5 (6,130) z=0) : z=0 := by
    rcases frame z with hz0|hzx
    · exact hz0
    · exact (hy5ne (by simpa only [hzx,hd5'] using hz)).elim
  let S := E.pageShortComplex 5 ((6,130)-E.diffDeg 5)
  have hs : S.Exact := S.moduleCat_exact_iff.mpr (by
    intro z hz
    exact ⟨0,by rw [hker5 z hz,map_zero]⟩)
  exact ModuleCat.subsingleton_of_isZero ((pageHomologyIso E 5 (6,130)
    (by change (2:ℤ)≤5; omega)).isZero_iff.mpr ((S.exact_iff_isZero_homology).mp hs))

private theorem stem124_finite_pages
    {C : Type u} [StableHomotopyCategory.{u,v} C] [HasFunctorialCofiber (C:=C)]
    {Syn : Type w} [SyntheticCategory.{w,v} Syn] [HasFunctorialCofiber (C:=Syn)]
    {H : Mod2EilenbergMacLane (C:=C)} {M : MilnorCooperations H} {D : AdamsComparison H M Syn}
    {L : SphereAdamsClasses H} {G : KIP126.Literature.AdamsSynthetic.TmfDetectionClasses H} (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 6 (6,130)) ∧
    Subsingleton ((sequence D .sphere).Page 6 (7,131)) ∧
    Subsingleton ((sequence D .sphere).Page 3 (8,132)) ∧
    Subsingleton ((sequence D .sphere).Page 4 (9,133)) := by
  classical
  classical
  obtain ⟨b,hb,hcases,h74⟩ := stem124_finite_pages_low124_s7_four I
  have h8 := stem124_finite_pages_low124_af8_three I
  have h9 := stem124_finite_pages_low124_af9_four I
  have h8four := adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum 3 4 8 132
    (by omega) (by omega) h8
  exact ⟨stem124_finite_pages_low124_af6_six I h74, stem124_finite_pages_low124_s7_six I h8four h9.2.1, h8, h9.1⟩

private theorem stem124_weight128_filtration_ten_permanent_quotient_zero_of_stable_boundaries
    (X : C) (p : ℤ×ℤ) (b : ℤ)
    (hzero : Subsingleton ((adamsTowerInternalSpectralSequence H.unit X).ssData p).eInfty)
    (hB : ((adamsTowerInternalSpectralSequence H.unit X).ssData p).B ⊤ =
      ((adamsTowerInternalSpectralSequence H.unit X).ssData p).B ↑(b-1).toNat) :
    Subsingleton (PermanentQuotient H X b p) := by
  classical
  let E := (adamsTowerInternalSpectralSequence H.unit X).ssData p
  have heq : LinearMap.range (boundaryMap H X ⊤ p).hom = boundaries H X b p := by
    have hh (B B' : Subobject E.V) (h : B ≤ E.Z 0) (h' : B' ≤ E.Z 0)
        (he : B = B') :
        LinearMap.range (Subobject.ofLE B _ h ≫ E.pageπ 0).hom =
          LinearMap.range (Subobject.ofLE B' _ h' ≫ E.pageπ 0).hom := by
      subst B'
      rfl
    exact hh _ _ _ _ hB
  have hcycles : permanentCycles H X p ≤ boundaries H X b p := by
    rintro x ⟨z,hz⟩
    have hz0 : E.pageπ ⊤ z = 0 := hzero.elim _ _
    obtain ⟨y,hy⟩ := (cokernel_π_eq_zero_iff_mem_range
      (Subobject.ofLE (E.B ⊤) (E.Z ⊤) (E.B_le_Z ⊤)) z).mp hz0
    rw [← heq]
    refine ⟨y,?_⟩
    have hfactor : Subobject.ofLE (E.B ⊤) (E.Z ⊤) (E.B_le_Z ⊤) ≫
        cycleMap H X ⊤ p = boundaryMap H X ⊤ p := by
      dsimp only [cycleMap,boundaryMap,E]
      rw [← Category.assoc,Subobject.ofLE_comp_ofLE]
    change boundaryMap H X ⊤ p y = x
    rw [← hfactor,CategoryTheory.comp_apply,hy]
    exact hz
  have hall (a : PermanentQuotient H X b p) : a = 0 := by
    obtain ⟨x⟩ := a
    exact (KIP126.Algebra.NestedQuotient.projection_eq_zero x).mpr (hcycles x.property)
  exact ⟨fun a b => (hall a).trans (hall b).symm⟩

private theorem stem124_weight128_filtration_ten_nu124_low_zero
    (A : KIP126.Literature.AdamsSynthetic.SyntheticComparisonTheorems D) (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G)
    (s : ℤ) (hs : s < 10)
    (hz : Subsingleton ((adamsTowerInternalSpectralSequence H.unit SphereSpectrum).ssData
      (s,124+s)).eInfty) :
    Subsingleton (((D.family.nu D.nu SphereSpectrum).sequence.ssData (s,124+s,128)).eInfty) := by
  classical
  by_cases hw : 128 ≤ 124+s
  · let E := adamsTowerInternalSpectralSequence H.unit (SphereSpectrum (C := C))
    have hin (r : ℤ) (hr : s-2 ≤ r) : E.d r ((s,124+s)-E.diffDeg r) = 0 := by
      have hi : (s,124+s)-E.diffDeg r = (s-r,(s-r)+125) := by
        change (s,124+s)-(r,r-1) = _
        ext <;> dsimp; omega
      rw [hi]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro a
      exact no_outgoing_stem125_low I (s-r) (by omega) r (by omega) a
    have hB := boundaries_top_eq_of_d_eq_zero E (s-2) (by change (2:ℤ)≤s-2; omega)
      (s,124+s) hin
    have hB' : (E.ssData (s,124+s)).B ⊤ =
        (E.ssData (s,124+s)).B ↑(1+(124+s)-128-1).toNat := by
      change (E.ssData (s,124+s)).B ⊤ = (E.ssData (s,124+s)).B ↑(s-2-2).toNat at hB
      simpa only [show s-2-2 = 1+(124+s)-128-1 by omega] using hB
    haveI := stem124_weight128_filtration_ten_permanent_quotient_zero_of_stable_boundaries SphereSpectrum (s,124+s)
      (1+(124+s)-128) hz hB'
    exact (A.eInfty.presentation.nuWindow SphereSpectrum (s,124+s) 128 hw).injective.subsingleton
  · haveI : Subsingleton (nuEInftyModel H (SphereSpectrum (C := C)) (s,124+s) 128) := by
      simp only [nuEInftyModel,hw,ite_false]
      infer_instance
    exact (A.eInfty.presentation.nu SphereSpectrum (s,124+s) 128).injective.subsingleton

private theorem stem124_weight128_filtration_ten
    (A : KIP126.Literature.AdamsSynthetic.SyntheticComparisonTheorems D) (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G)
    (hc : ∀ s : ℤ, s < 10 → Subsingleton
      ((adamsTowerInternalSpectralSequence H.unit SphereSpectrum).ssData (s,s+124)).eInfty)
    (a : BiHom 124 128 (S_0_0 : Syn)) :
    FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 10 a := by
  classical
  classical
  apply (D.sphereConvergence.filtrationAtLeast_iff_of_eInfty_isZero
    0 10 124 128 (by omega) ?_ a).mp
  · refine ⟨a,?_⟩
    change a ≫ adamsTowerMap (nuCoefficientUnit H.unit D.nu) _ 0 0 _ = a
    rw [adamsTowerMap_self]
    change a ≫ 𝟙 _ = a
    exact Category.comp_id a
  · intro s hs hs10
    have hz : Subsingleton
        ((adamsTowerInternalSpectralSequence H.unit SphereSpectrum).ssData (s,124+s)).eInfty := by
      simpa only [add_comm] using hc s hs10
    haveI := stem124_weight128_filtration_ten_nu124_low_zero A I s hs10 hz
    let hnu := ModuleCat.isZero_of_subsingleton
      (((D.family.nu D.nu SphereSpectrum).sequence.ssData (s,124+s,128)).eInfty)
    let f := (D.family.functor.map D.nu.unitIso.hom).eInftyMap (s,124+s,128)
    let g := (D.family.functor.map D.nu.unitIso.inv).eInftyMap (s,124+s,128)
    have hfg : g ≫ f = 𝟙 _ := by
      dsimp only [f,g]
      rw [← SpectralSequenceMorphism.eInftyMap_comp,← Functor.map_comp,Iso.inv_hom_id,
        CategoryTheory.Functor.map_id,SpectralSequenceMorphism.eInftyMap_id]
    apply (CategoryTheory.Limits.IsZero.iff_id_eq_zero _).mpr
    exact hfg.symm.trans (by rw [hnu.eq_of_src f 0,CategoryTheory.Limits.comp_zero])

private theorem stem124_af13_exhaustion_af13_labels (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G) :
    I.interpretation.sphere 13 137 correction = I.interpretation.basis .sphere 13 137 1 ∧
    I.interpretation.sphere 13 137 (mulAt (atom .h4) (atom .x_109_12)) = I.interpretation.basis .sphere 13 137 2 := by
  classical
  have hmem : (⟨.sphere,13,137,["76,1,82,1", "9,1,251,1", "7,1,275,1", "0,5,367,1"]⟩ : Raw.Degree) ∈ Raw.degrees := by
    exact List.mem_of_getElem? (i := 208) (by rfl)
  have hc := I.monomials _ hmem rfl
  constructor
  · obtain ⟨z,hz,he⟩ := hc (1 : Fin 4)
    have heq : correction = z := by
      apply Subtype.ext
      rw [hz]
      change generator ⟨9, by decide⟩ * generator ⟨251, by decide⟩ = projection (monomialOfString "9,1,251,1")
      have hs : "9,1,251,1" ≠ "" := by decide
      have hp : (("9,1,251,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [9,1,251,1] := by
        have split : "9,1,251,1".splitOn "," = ["9", "1", "251", "1"] := by
          simp +decide [String.splitOn,String.splitOnAux]
        rw [split]
        simp +decide [String.toNat?, String.Slice.toNat?, String.Slice.isNat,
          String.Slice.forIn_eq_forIn_toList, String.Slice.foldl_eq_foldl_toList]
      simp only [monomialOfString, if_neg hs, hp]
      norm_num [polynomialOfPowers, RawData.generatorCount, generator, map_mul]
    rw [heq]
    exact he
  · obtain ⟨z,hz,he⟩ := hc (2 : Fin 4)
    have heq : mulAt (atom .h4) (atom .x_109_12) = z := by
      apply Subtype.ext
      rw [hz]
      change generator ⟨7, by decide⟩ * generator ⟨275, by decide⟩ = projection (monomialOfString "7,1,275,1")
      have hs : "7,1,275,1" ≠ "" := by decide
      have hp : (("7,1,275,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [7,1,275,1] := by
        have split : "7,1,275,1".splitOn "," = ["7", "1", "275", "1"] := by
          simp +decide [String.splitOn,String.splitOnAux]
        rw [split]
        simp +decide [String.toNat?, String.Slice.toNat?, String.Slice.isNat,
          String.Slice.forIn_eq_forIn_toList, String.Slice.foldl_eq_foldl_toList]
      simp only [monomialOfString, if_neg hs, hp]
      norm_num [polynomialOfPowers, RawData.generatorCount, generator, map_mul]
    rw [heq]
    exact he

private theorem stem124_af13_exhaustion
    {C : Type u} [StableHomotopyCategory.{u,v} C] [HasFunctorialCofiber (C:=C)]
    {Syn : Type w} [SyntheticCategory.{w,v} Syn] [HasFunctorialCofiber (C:=Syn)]
    {H : Mod2EilenbergMacLane (C:=C)} {M : MilnorCooperations H} {D : AdamsComparison H M Syn}
    {L : SphereAdamsClasses H} {G : KIP126.Literature.AdamsSynthetic.TmfDetectionClasses H} (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G)
    (facts : Derived.SphereFacts I.interpretation) :
    KIP126.AdamsSynthetic.SectionSeven.ClassicalInfinityGenerated 13 137
      (I.interpretation.sphere 13 137 correction) := by
  classical
  classical
  let E := sequence D .sphere
  let A := E.ssData (13,137)
  obtain ⟨hl1,hl2⟩ := stem124_af13_exhaustion_af13_labels I
  obtain ⟨z,hz,hzn⟩ := facts.correction_permanent
  change (Subobject.ofLE (A.Z ⊤) (A.Z 0) (A.Z_anti le_top) ≫ A.pageπ 0) z = _ at hz
  change A.pageπ ⊤ z ≠ 0 at hzn
  have h321 : HasDifferential E 2 (11,136) (13,137)
      (I.interpretation.basis .sphere 11 136 4) (I.interpretation.basis .sphere 13 137 3) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,2,11,136,[4],13,137,[3],"S0_AdamsE2_ss",2914⟩ (by
      exact List.mem_of_getElem? (i := 321) (by rfl))
    dsimp only [AdamsStatement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 2 (11,136) (13,137) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 11 136 [4] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 13 137 [3] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    exact h
  have h322 : HasDifferential E 3 (10,135) (13,137)
      (I.interpretation.basis .sphere 10 135 0) (I.interpretation.basis .sphere 13 137 0) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,3,10,135,[0],13,137,[0],"S0_AdamsE2_ss",2915⟩ (by
      exact List.mem_of_getElem? (i := 322) (by rfl))
    dsimp only [AdamsStatement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 3 (10,135) (13,137) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 10 135 [0] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 13 137 [0] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    exact h
  obtain ⟨_,incoming,a,hincoming,ha,hda⟩ := h322
  have hd2 := facts.d3_h4_x_109_12
  change HasNonzeroDifferential E 3 (13,137) (16,139)
    (I.interpretation.sphere 13 137 (mulAt (atom .h4) (atom .x_109_12))) _ at hd2
  rw [hl2] at hd2
  obtain ⟨_,c,t,hc,ht,hdc,htn⟩ := hd2
  have hdc' : E.d 3 (13,137) c = t := hdc
  have hda' : E.d 3 (10,135) incoming = a := hda
  let down (r : ℤ) := Subobject.ofLE (A.Z ⊤) (A.Z ↑(r-2).toNat) (A.Z_anti le_top)
  let val (r : ℤ) := down r ≫ A.pageπ ↑(r-2).toNat
  have rep (r : ℤ) (hr : 2 ≤ r) (q : (Subobject.underlying.obj (A.Z ⊤) : ModuleCat.{v} ℤ)) :
      RepresentsOnPage E r (13,137) (val 2 q) (val r q) := by
    refine ⟨hr, down r q, ?_, rfl⟩
    change (Subobject.ofLE _ _ _ ≫ A.pageπ 0) ((down r) q) = val 2 q
    dsimp only [val, down]
    rw [← CategoryTheory.comp_apply, ← Category.assoc, Subobject.ofLE_comp_ofLE]
    rfl
  let b : E.Page 3 (13,137) := val 3 z
  have hb : RepresentsOnPage E 3 (13,137) (I.interpretation.basis .sphere 13 137 1) b := by
    have h := rep 3 (by decide) z
    change val 2 z = _ at hz
    rw [hz,hl1] at h
    exact h
  have hthree : RepresentsOnPage E 3 (13,137) (I.interpretation.basis .sphere 13 137 3) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) h321
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,13,137,["76,1,82,1", "9,1,251,1", "7,1,275,1", "0,5,367,1"]⟩ (by
    exact List.mem_of_getElem? (i := 208) (by rfl))
  change E.Page 2 (13,137) ≃ₗ[ℤ] (Fin 4 →₀ F2) at e
  change ∀i : Fin 4, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 13 137 i.val at he
  have hbzero : E.d 3 (13,137) b = 0 := by
    apply represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<4) (rep 3 (by decide) z)
    exact ⟨val 4 z,rep 4 (by decide) z⟩
  have hazero : E.d 3 (13,137) a = 0 := by
    exact IsPageBoundary.d_eq_zero (E:=E) (r:=3) (p:=(10,135)) ⟨incoming,hda'⟩
  have hkernel (q : E.Page 3 (13,137)) (hq : E.d 3 (13,137) q=0) :
      q=0 ∨ q=a ∨ q=b ∨ q=a+b := by
    let vv : Fin 4 → E.Page 3 (13,137) := ![a,b,c,0]
    have hv (i : Fin 4) : RepresentsOnPage E 3 (13,137) (e.symm (Finsupp.single i 1)) (vv i) := by
      rw [he i]
      fin_cases i
      · exact ha
      · exact hb
      · exact hc
      · exact hthree
    obtain ⟨coef,hcoef⟩ := page_generated_from_representatives (by decide : (2:ℤ)≤3) e vv hv q
    simp only [Fin.sum_univ_succ] at hcoef
    change q = (if coef 0=0 then 0 else a) + ((if coef 1=0 then 0 else b) + ((if coef 2=0 then 0 else c) + ((if coef 3=0 then 0 else 0) + 0))) at hcoef
    have hczero : coef 2 = 0 := by
      by_contra hh
      have hd := congrArg (E.d 3 (13,137)) hcoef
      simp only [hq,map_add,apply_ite,map_zero,hazero,hbzero,hdc',hh,ite_false,ite_self,zero_add,add_zero] at hd
      exact htn hd.symm
    by_cases h0 : coef 0=0 <;> by_cases h1 : coef 1=0
    all_goals simp only [h0,h1,hczero,ite_true,ite_false,ite_self,add_zero,zero_add] at hcoef
    · exact Or.inl hcoef
    · exact Or.inr (Or.inr (Or.inl hcoef))
    · exact Or.inr (Or.inl hcoef)
    · exact Or.inr (Or.inr (Or.inr hcoef))
  have kill (q : (Subobject.underlying.obj (A.Z ⊤) : ModuleCat.{v} ℤ)) (hq : val 3 q=0 ∨ val 3 q=a) : A.pageπ ⊤ q=0 := by
    have hfour : A.pageπ 2 (down 4 q)=0 := by
      apply (next_projection_zero_iff_incoming E 3 (by change (2:ℤ)≤3; omega) (10,135) (down 4 q)).mpr
      have hdown : (Subobject.ofLE (A.Z 2) (A.Z 1) (A.Z_anti (by decide : (1:WithTop ℕ)≤2)) ≫ A.pageπ 1) (down 4 q) = val 3 q := by
        change (Subobject.ofLE (A.Z 2) (A.Z 1) _ ≫ A.pageπ 1)
          ((Subobject.ofLE (A.Z ⊤) (A.Z 2) _) q) =
          (Subobject.ofLE (A.Z ⊤) (A.Z 1) _ ≫ A.pageπ 1) q
        rw [← CategoryTheory.comp_apply, ← Category.assoc, Subobject.ofLE_comp_ofLE]
      change ∃ x, E.d 3 (10,135) x = (Subobject.ofLE (A.Z 2) (A.Z 1) _ ≫ A.pageπ 1) (down 4 q)
      rw [hdown]
      rcases hq with hq|hq
      · exact ⟨0, by rw [hq,map_zero]⟩
      · exact ⟨incoming, hda'.trans hq.symm⟩
    change (A.pageπ 2) ((Subobject.ofLE (A.Z ⊤) (A.Z 2) _) q)=0 at hfour
    have heq := A.infinity_projection_eq_of_page_projection_eq 2 q 0 (by simpa only [CategoryTheory.comp_apply,map_zero] using hfour)
    simpa only [map_zero] using heq
  refine ⟨z,hz,hzn,?_⟩
  intro y
  haveI : Epi (A.pageπ ⊤) := inferInstanceAs (Epi (cokernel.π _))
  obtain ⟨q,rfl⟩ := (ModuleCat.epi_iff_surjective (A.pageπ ⊤)).mp inferInstance y
  have hqzero : E.d 3 (13,137) (val 3 q)=0 := by
    exact represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<4)
      (rep 3 (by decide) q) ⟨val 4 q,rep 4 (by decide) q⟩
  rcases hkernel (val 3 q) hqzero with hq|hq|hq|hq
  · exact Or.inl (kill q (Or.inl hq))
  · exact Or.inl (kill q (Or.inr hq))
  · apply Or.inr
    change A.pageπ ⊤ q = A.pageπ ⊤ z
    apply sub_eq_zero.mp
    rw [← map_sub]
    apply kill (q-z)
    left
    simp only [map_sub,hq,b,sub_self]
  · apply Or.inr
    change A.pageπ ⊤ q = A.pageπ ⊤ z
    apply sub_eq_zero.mp
    rw [← map_sub]
    apply kill (q-z)
    right
    simp only [map_sub,hq,b,add_sub_cancel_right]

set_option maxHeartbeats 800000 in
private theorem stem124_af10_exhaustion
    {C : Type u} [StableHomotopyCategory.{u,v} C] [HasFunctorialCofiber (C:=C)]
    {Syn : Type w} [SyntheticCategory.{w,v} Syn] [HasFunctorialCofiber (C:=Syn)]
    {H : Mod2EilenbergMacLane (C:=C)} {M : MilnorCooperations H} {D : AdamsComparison H M Syn}
    {L : SphereAdamsClasses H} {G : KIP126.Literature.AdamsSynthetic.TmfDetectionClasses H} (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G) (V : SphereVanishingLine H) :
    KIP126.AdamsSynthetic.SectionSeven.ClassicalInfinityGenerated 10 134
      (I.interpretation.sphere 10 134 U) := by
  classical
  let E := sequence D .sphere
  obtain ⟨e10_134,he10_134⟩ := I.basis ⟨.sphere, 10, 134, ["389,1", "388,1", "1,1,366,1", "0,1,373,1", "0,2,367,1"]⟩ (by
    exact List.mem_of_getElem? (i := 181) (by rfl))
  change E.Page 2 (10,134) ≃ₗ[ℤ] (Fin 5 →₀ F2) at e10_134
  change ∀i : Fin 5, e10_134.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 10 134 i.val at he10_134
  have he10_134_0 : e10_134.symm (Finsupp.single 0 1) = I.interpretation.basis .sphere 10 134 0 := he10_134 0
  have he10_134_1 : e10_134.symm (Finsupp.single 1 1) = I.interpretation.basis .sphere 10 134 1 := he10_134 1
  have he10_134_2 : e10_134.symm (Finsupp.single 2 1) = I.interpretation.basis .sphere 10 134 2 := he10_134 2
  have he10_134_3 : e10_134.symm (Finsupp.single 3 1) = I.interpretation.basis .sphere 10 134 3 := he10_134 3
  have he10_134_4 : e10_134.symm (Finsupp.single 4 1) = I.interpretation.basis .sphere 10 134 4 := he10_134 4
  obtain ⟨e11_135,he11_135⟩ := I.basis ⟨.sphere, 11, 135, ["411,1", "410,1", "409,1", "0,1,389,1", "0,3,367,1"]⟩ (by
    exact List.mem_of_getElem? (i := 191) (by rfl))
  change E.Page 2 (11,135) ≃ₗ[ℤ] (Fin 5 →₀ F2) at e11_135
  change ∀i : Fin 5, e11_135.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 11 135 i.val at he11_135
  have he11_135_0 : e11_135.symm (Finsupp.single 0 1) = I.interpretation.basis .sphere 11 135 0 := he11_135 0
  have he11_135_1 : e11_135.symm (Finsupp.single 1 1) = I.interpretation.basis .sphere 11 135 1 := he11_135 1
  have he11_135_2 : e11_135.symm (Finsupp.single 2 1) = I.interpretation.basis .sphere 11 135 2 := he11_135 2
  have he11_135_3 : e11_135.symm (Finsupp.single 3 1) = I.interpretation.basis .sphere 11 135 3 := he11_135 3
  have he11_135_4 : e11_135.symm (Finsupp.single 4 1) = I.interpretation.basis .sphere 11 135 4 := he11_135 4
  obtain ⟨e12_136,he12_136⟩ := I.basis ⟨.sphere, 12, 136, ["1,1,387,1", "0,1,410,1", "0,1,409,1", "0,2,389,1", "0,4,367,1"]⟩ (by
    exact List.mem_of_getElem? (i := 200) (by rfl))
  change E.Page 2 (12,136) ≃ₗ[ℤ] (Fin 5 →₀ F2) at e12_136
  change ∀i : Fin 5, e12_136.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 12 136 i.val at he12_136
  have he12_136_0 : e12_136.symm (Finsupp.single 0 1) = I.interpretation.basis .sphere 12 136 0 := he12_136 0
  have he12_136_1 : e12_136.symm (Finsupp.single 1 1) = I.interpretation.basis .sphere 12 136 1 := he12_136 1
  have he12_136_2 : e12_136.symm (Finsupp.single 2 1) = I.interpretation.basis .sphere 12 136 2 := he12_136 2
  have he12_136_3 : e12_136.symm (Finsupp.single 3 1) = I.interpretation.basis .sphere 12 136 3 := he12_136 3
  have he12_136_4 : e12_136.symm (Finsupp.single 4 1) = I.interpretation.basis .sphere 12 136 4 := he12_136 4
  obtain ⟨e13_137,he13_137⟩ := I.basis ⟨.sphere, 13, 137, ["76,1,82,1", "9,1,251,1", "7,1,275,1", "0,5,367,1"]⟩ (by
    exact List.mem_of_getElem? (i := 208) (by rfl))
  change E.Page 2 (13,137) ≃ₗ[ℤ] (Fin 4 →₀ F2) at e13_137
  change ∀i : Fin 4, e13_137.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 13 137 i.val at he13_137
  have he13_137_0 : e13_137.symm (Finsupp.single 0 1) = I.interpretation.basis .sphere 13 137 0 := he13_137 0
  have he13_137_1 : e13_137.symm (Finsupp.single 1 1) = I.interpretation.basis .sphere 13 137 1 := he13_137 1
  have he13_137_2 : e13_137.symm (Finsupp.single 2 1) = I.interpretation.basis .sphere 13 137 2 := he13_137 2
  have he13_137_3 : e13_137.symm (Finsupp.single 3 1) = I.interpretation.basis .sphere 13 137 3 := he13_137 3
  obtain ⟨e15_138,he15_138⟩ := I.basis ⟨.sphere, 15, 138, ["438,1", "7,1,279,1", "0,2,418,1"]⟩ (by
    exact List.mem_of_getElem? (i := 222) (by rfl))
  change E.Page 2 (15,138) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e15_138
  change ∀i : Fin 3, e15_138.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 15 138 i.val at he15_138
  have he15_138_0 : e15_138.symm (Finsupp.single 0 1) = I.interpretation.basis .sphere 15 138 0 := he15_138 0
  have he15_138_1 : e15_138.symm (Finsupp.single 1 1) = I.interpretation.basis .sphere 15 138 1 := he15_138 1
  have he15_138_2 : e15_138.symm (Finsupp.single 2 1) = I.interpretation.basis .sphere 15 138 2 := he15_138 2
  obtain ⟨e13_136,he13_136⟩ := I.basis ⟨.sphere, 13, 136, ["418,1", "417,1", "0,2,386,1"]⟩ (by
    exact List.mem_of_getElem? (i := 207) (by rfl))
  change E.Page 2 (13,136) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e13_136
  change ∀i : Fin 3, e13_136.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 13 136 i.val at he13_136
  have he13_136_0 : e13_136.symm (Finsupp.single 0 1) = I.interpretation.basis .sphere 13 136 0 := he13_136 0
  have he13_136_1 : e13_136.symm (Finsupp.single 1 1) = I.interpretation.basis .sphere 13 136 1 := he13_136 1
  have he13_136_2 : e13_136.symm (Finsupp.single 2 1) = I.interpretation.basis .sphere 13 136 2 := he13_136 2
  obtain ⟨e14_137,he14_137⟩ := I.basis ⟨.sphere, 14, 137, ["23,1,181,1", "0,1,418,1", "0,3,386,1"]⟩ (by
    exact List.mem_of_getElem? (i := 215) (by rfl))
  change E.Page 2 (14,137) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e14_137
  change ∀i : Fin 3, e14_137.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 14 137 i.val at he14_137
  have he14_137_0 : e14_137.symm (Finsupp.single 0 1) = I.interpretation.basis .sphere 14 137 0 := he14_137 0
  have he14_137_1 : e14_137.symm (Finsupp.single 1 1) = I.interpretation.basis .sphere 14 137 1 := he14_137 1
  have he14_137_2 : e14_137.symm (Finsupp.single 2 1) = I.interpretation.basis .sphere 14 137 2 := he14_137 2
  have h171 : HasDifferential E 4 (6,131) (10,134) (I.interpretation.basis .sphere 6 131 0) (I.interpretation.basis .sphere 10 134 0 + I.interpretation.basis .sphere 10 134 3) := by
    have hrow := I.adamsStatements ⟨.sphere, .equation, 4, 6, 131, [0], 10, 134, [0, 3], "S0_AdamsE2_ss", 2492⟩ (by
      exact List.mem_of_getElem? (i := 171) (by rfl))
    dsimp only [AdamsStatement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 4 (6,131) (10,134) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 6 131 [0] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 10 134 [0, 3] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    simpa only [add_assoc] using h
  have h172 : HasDifferential E 4 (6,131) (10,134) (I.interpretation.basis .sphere 6 131 1) (I.interpretation.basis .sphere 10 134 0 + I.interpretation.basis .sphere 10 134 1 + I.interpretation.basis .sphere 10 134 3 + I.interpretation.basis .sphere 10 134 4) := by
    have hrow := I.adamsStatements ⟨.sphere, .equation, 4, 6, 131, [1], 10, 134, [0, 1, 3, 4], "S0_AdamsE2_ss", 2493⟩ (by
      exact List.mem_of_getElem? (i := 172) (by rfl))
    dsimp only [AdamsStatement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 4 (6,131) (10,134) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 6 131 [1] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 10 134 [0, 1, 3, 4] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    simpa only [add_assoc] using h
  have h201 : HasDifferential E 2 (8,133) (10,134) (I.interpretation.basis .sphere 8 133 1) (I.interpretation.basis .sphere 10 134 2 + I.interpretation.basis .sphere 10 134 4) := by
    have hrow := I.adamsStatements ⟨.sphere, .equation, 2, 8, 133, [1], 10, 134, [2, 4], "S0_AdamsE2_ss", 2630⟩ (by
      exact List.mem_of_getElem? (i := 201) (by rfl))
    dsimp only [AdamsStatement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 2 (8,133) (10,134) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 8 133 [1] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 10 134 [2, 4] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    simpa only [add_assoc] using h
  have h250 : HasDifferential E 5 (10,134) (15,138) (I.interpretation.basis .sphere 10 134 3) (I.interpretation.basis .sphere 15 138 1) := by
    have hrow := I.adamsStatements ⟨.sphere, .equation, 5, 10, 134, [3], 15, 138, [1], "S0_AdamsE2_ss", 2694⟩ (by
      exact List.mem_of_getElem? (i := 250) (by rfl))
    dsimp only [AdamsStatement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 5 (10,134) (15,138) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 10 134 [3] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 15 138 [1] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    simpa only [add_assoc] using h
  have h200 : HasDifferential E 3 (8,133) (11,135) (I.interpretation.basis .sphere 8 133 0) (I.interpretation.basis .sphere 11 135 0) := by
    have hrow := I.adamsStatements ⟨.sphere, .equation, 3, 8, 133, [0], 11, 135, [0], "S0_AdamsE2_ss", 2629⟩ (by
      exact List.mem_of_getElem? (i := 200) (by rfl))
    dsimp only [AdamsStatement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 3 (8,133) (11,135) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 8 133 [0] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 11 135 [0] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    simpa only [add_assoc] using h
  have h226 : HasDifferential E 3 (9,134) (12,136) (I.interpretation.basis .sphere 9 134 1) (I.interpretation.basis .sphere 12 136 0) := by
    have hrow := I.adamsStatements ⟨.sphere, .equation, 3, 9, 134, [1], 12, 136, [0], "S0_AdamsE2_ss", 2697⟩ (by
      exact List.mem_of_getElem? (i := 226) (by rfl))
    dsimp only [AdamsStatement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 3 (9,134) (12,136) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 9 134 [1] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 12 136 [0] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    simpa only [add_assoc] using h
  have h227 : HasDifferential E 2 (9,134) (11,135) (I.interpretation.basis .sphere 9 134 0) (I.interpretation.basis .sphere 11 135 3 + I.interpretation.basis .sphere 11 135 4) := by
    have hrow := I.adamsStatements ⟨.sphere, .equation, 2, 9, 134, [0], 11, 135, [3, 4], "S0_AdamsE2_ss", 2698⟩ (by
      exact List.mem_of_getElem? (i := 227) (by rfl))
    dsimp only [AdamsStatement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 2 (9,134) (11,135) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 9 134 [0] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 11 135 [3, 4] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    simpa only [add_assoc] using h
  have h228 : HasDifferential E 2 (9,134) (11,135) (I.interpretation.basis .sphere 9 134 4) (I.interpretation.basis .sphere 11 135 4) := by
    have hrow := I.adamsStatements ⟨.sphere, .equation, 2, 9, 134, [4], 11, 135, [4], "S0_AdamsE2_ss", 2699⟩ (by
      exact List.mem_of_getElem? (i := 228) (by rfl))
    dsimp only [AdamsStatement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 2 (9,134) (11,135) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 9 134 [4] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 11 135 [4] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    simpa only [add_assoc] using h
  have h253 : HasDifferential E 2 (10,135) (12,136) (I.interpretation.basis .sphere 10 135 1) (I.interpretation.basis .sphere 12 136 1 + I.interpretation.basis .sphere 12 136 2) := by
    have hrow := I.adamsStatements ⟨.sphere, .equation, 2, 10, 135, [1], 12, 136, [1, 2], "S0_AdamsE2_ss", 2785⟩ (by
      exact List.mem_of_getElem? (i := 253) (by rfl))
    dsimp only [AdamsStatement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 2 (10,135) (12,136) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 10 135 [1] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 12 136 [1, 2] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    simpa only [add_assoc] using h
  have h254 : HasDifferential E 2 (10,135) (12,136) (I.interpretation.basis .sphere 10 135 2) (I.interpretation.basis .sphere 12 136 3 + I.interpretation.basis .sphere 12 136 4) := by
    have hrow := I.adamsStatements ⟨.sphere, .equation, 2, 10, 135, [2], 12, 136, [3, 4], "S0_AdamsE2_ss", 2786⟩ (by
      exact List.mem_of_getElem? (i := 254) (by rfl))
    dsimp only [AdamsStatement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 2 (10,135) (12,136) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 10 135 [2] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 12 136 [3, 4] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    simpa only [add_assoc] using h
  have h255 : HasDifferential E 2 (10,135) (12,136) (I.interpretation.basis .sphere 10 135 4) (I.interpretation.basis .sphere 12 136 4) := by
    have hrow := I.adamsStatements ⟨.sphere, .equation, 2, 10, 135, [4], 12, 136, [4], "S0_AdamsE2_ss", 2787⟩ (by
      exact List.mem_of_getElem? (i := 255) (by rfl))
    dsimp only [AdamsStatement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 2 (10,135) (12,136) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 10 135 [4] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 12 136 [4] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    simpa only [add_assoc] using h
  have h277 : HasDifferential E 4 (11,135) (15,138) (I.interpretation.basis .sphere 11 135 1 + I.interpretation.basis .sphere 11 135 2) (I.interpretation.basis .sphere 15 138 0) := by
    have hrow := I.adamsStatements ⟨.sphere, .equation, 4, 11, 135, [1, 2], 15, 138, [0], "S0_AdamsE2_ss", 2781⟩ (by
      exact List.mem_of_getElem? (i := 277) (by rfl))
    dsimp only [AdamsStatement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 4 (11,135) (15,138) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 11 135 [1, 2] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 15 138 [0] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    simpa only [add_assoc] using h
  have h278 : HasDifferential E 2 (11,135) (13,136) (I.interpretation.basis .sphere 11 135 2) (I.interpretation.basis .sphere 13 136 2) := by
    have hrow := I.adamsStatements ⟨.sphere, .equation, 2, 11, 135, [2], 13, 136, [2], "S0_AdamsE2_ss", 2782⟩ (by
      exact List.mem_of_getElem? (i := 278) (by rfl))
    dsimp only [AdamsStatement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 2 (11,135) (13,136) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 11 135 [2] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 13 136 [2] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    simpa only [add_assoc] using h
  have h304 : HasDifferential E 2 (12,136) (14,137) (I.interpretation.basis .sphere 12 136 2) (I.interpretation.basis .sphere 14 137 2) := by
    have hrow := I.adamsStatements ⟨.sphere, .equation, 2, 12, 136, [2], 14, 137, [2], "S0_AdamsE2_ss", 2849⟩ (by
      exact List.mem_of_getElem? (i := 304) (by rfl))
    dsimp only [AdamsStatement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 2 (12,136) (14,137) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 12 136 [2] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 14 137 [2] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    simpa only [add_assoc] using h
  have h321 : HasDifferential E 2 (11,136) (13,137) (I.interpretation.basis .sphere 11 136 4) (I.interpretation.basis .sphere 13 137 3) := by
    have hrow := I.adamsStatements ⟨.sphere, .equation, 2, 11, 136, [4], 13, 137, [3], "S0_AdamsE2_ss", 2914⟩ (by
      exact List.mem_of_getElem? (i := 321) (by rfl))
    dsimp only [AdamsStatement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 2 (11,136) (13,137) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 11 136 [4] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 13 137 [3] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    simpa only [add_assoc] using h
  have h322 : HasDifferential E 3 (10,135) (13,137) (I.interpretation.basis .sphere 10 135 0) (I.interpretation.basis .sphere 13 137 0) := by
    have hrow := I.adamsStatements ⟨.sphere, .equation, 3, 10, 135, [0], 13, 137, [0], "S0_AdamsE2_ss", 2915⟩ (by
      exact List.mem_of_getElem? (i := 322) (by rfl))
    dsimp only [AdamsStatement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 3 (10,135) (13,137) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 10 135 [0] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 13 137 [0] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    simpa only [add_assoc] using h
  have h323 : ReachesPage E 1000 (13,137) (I.interpretation.basis .sphere 13 137 1) := by
    have hrow := I.adamsStatements ⟨.sphere, .reaches, 1000, 13, 137, [1], 13, 137, [], "S0_AdamsE2_ss", 2916⟩ (by
      exact List.mem_of_getElem? (i := 323) (by rfl))
    dsimp only [AdamsStatement] at hrow
    obtain ⟨a,ha,h⟩ := hrow
    have vx : Raw.coordinatesValid Raw.degrees .sphere 13 137 [1] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha
    rw [←ha] at h
    exact h
  have h324 : HasDifferential E 3 (13,137) (16,139) (I.interpretation.basis .sphere 13 137 2) (I.interpretation.basis .sphere 16 139 0) := by
    have hrow := I.adamsStatements ⟨.sphere, .equation, 3, 13, 137, [2], 16, 139, [0], "S0_AdamsE2_ss", 2917⟩ (by
      exact List.mem_of_getElem? (i := 324) (by rfl))
    dsimp only [AdamsStatement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 3 (13,137) (16,139) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 13 137 [2] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 16 139 [0] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    simpa only [add_assoc] using h
  have hrep2 {p : ℤ × ℤ} (x : E.Page 2 p) : RepresentsOnPage E 2 p x x := by
    exact represents_two_self _
  have hadd {r : ℤ} {p : ℤ × ℤ} {x y : E.Page 2 p} {a b : E.Page r p}
      (hx : RepresentsOnPage E r p x a) (hy : RepresentsOnPage E r p y b) :
      RepresentsOnPage E r p (x+y) (a+b) := by
    exact represents_add_tail (by assumption) (by assumption)
  have hsub {r : ℤ} {p : ℤ × ℤ} {x y : E.Page 2 p} {a b : E.Page r p}
      (hx : RepresentsOnPage E r p x a) (hy : RepresentsOnPage E r p y b) :
      RepresentsOnPage E r p (x-y) (a-b) := by
    exact represents_sub_tail (by assumption) (by assumption)
  have lift_e2 {r : ℤ} (hr : 2 ≤ r) {p : ℤ × ℤ} (x : E.Page r p) :
      ∃ a : E.Page 2 p, RepresentsOnPage E r p a x := by
    exact page_has_representative hr x
  have f2_expand {N : ℕ} (f : Fin N →₀ F2) :
      f = ∑ i : Fin N, if f i=0 then 0 else Finsupp.single i 1 := by
    exact FinitePageCalculus.f2_expand f
  have rep_zero {r : ℤ} {p : ℤ × ℤ} {x : E.Page r p}
      (h : RepresentsOnPage E r p 0 x) : x=0 :=
    represents_unique h (RepresentsOnPage.zero h.1)
  have rep_double {r : ℤ} {p : ℤ × ℤ} {x : E.Page 2 p} {a : E.Page r p}
      (hx : x+x=0) (ha : RepresentsOnPage E r p x a) : a+a=0 := by
    exact rep_zero (by simpa only [hx] using hadd ha ha)
  -- All four possible incoming d2 directions reach E3.
  have d2_13 : E.d 2 (13,137)=0 := by
    obtain ⟨_,x0,y0,hx0,hy0,_⟩ := h322
    obtain ⟨_,x2,y2,hx2,hy2,_⟩ := h324
    have h0 := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) (hrep2 _) ⟨y0,hy0⟩
    have h1 := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<1000) (hrep2 _) h323
    have h2 := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) (hrep2 _) ⟨x2,hx2⟩
    have h3 : E.d 2 (13,137) (I.interpretation.basis .sphere 13 137 3)=0 := by
      have hd := h321.eq_on_page_two.2
      change E.d 2 (11,136) _ = _ at hd
      rw [←hd]
      exact congrArg (fun f => f (I.interpretation.basis .sphere 11 136 4)) (E.d_comp_d 2 (11,136))
    have one (i : Fin 4) : E.d 2 (13,137) (e13_137.symm (Finsupp.single i 1))=0 := by
      rw [he13_137]
      fin_cases i
      · exact h0
      · exact h1
      · exact h2
      · exact h3
    have all (f : Fin 4 →₀ F2) : E.d 2 (13,137) (e13_137.symm f)=0 := by
      induction f using Finsupp.induction with
      | zero => simp
      | @single_add i a f hi ha ih =>
        rw [map_add,map_add,ih,add_zero]
        fin_cases a
        · simp
        · exact one i
    ext x
    simpa only [LinearEquiv.symm_apply_apply,ModuleCat.hom_zero,LinearMap.zero_apply] using all (e13_137 x)
  have hif {r : ℤ} {p : ℤ × ℤ} {x : E.Page 2 p} {a : E.Page r p}
      (c : F2) (h : RepresentsOnPage E r p x a) :
      RepresentsOnPage E r p (if c=0 then 0 else x) (if c=0 then 0 else a) := by
    split
    · exact RepresentsOnPage.zero h.1
    · exact h
  -- The complete d2 kernel in degree (12,136) consists of the d3 target
  -- basis0 and three d2 boundaries; consequently its entire d3 map is zero.
  have d3_12 : E.d 3 (12,136)=0 := by
    obtain ⟨_,in0,a0,hin0,ha0,hda0⟩ := h226
    have hd0 : E.d 3 (12,136) a0=0 :=
      IsPageBoundary.d_eq_zero (E:=E) (r:=3) (p:=(9,134)) ⟨in0,hda0⟩
    have rz12 : RepresentsOnPage E 3 (12,136)
        (I.interpretation.basis .sphere 12 136 1 + I.interpretation.basis .sphere 12 136 2) 0 :=
      differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) h253
    have rz34 : RepresentsOnPage E 3 (12,136)
        (I.interpretation.basis .sphere 12 136 3 + I.interpretation.basis .sphere 12 136 4) 0 :=
      differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) h254
    have rz4 : RepresentsOnPage E 3 (12,136) (I.interpretation.basis .sphere 12 136 4) 0 :=
      differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) h255
    have rz3 : RepresentsOnPage E 3 (12,136) (I.interpretation.basis .sphere 12 136 3) 0 := by
      simpa only [add_sub_cancel_right,sub_self] using hsub rz34 rz4
    have d0 := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) (hrep2 _) ⟨a0,ha0⟩
    have d12 := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) (hrep2 _) ⟨0,rz12⟩
    have d3 := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) (hrep2 _) ⟨0,rz3⟩
    have d4 := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) (hrep2 _) ⟨0,rz4⟩
    have d2 := h304.eq_on_page_two.2
    change E.d 2 (12,136) (I.interpretation.basis .sphere 12 136 2) = I.interpretation.basis .sphere 14 137 2 at d2
    have tn : I.interpretation.basis .sphere 14 137 2 ≠ 0 := by
      rw [←he14_137_2]
      intro h
      have hh := congrArg e14_137 h
      simp only [LinearEquiv.apply_symm_apply,map_zero] at hh
      have hh' := congrArg (fun f : Fin 3 →₀ F2 => f 2) hh
      norm_num at hh'
    have d1 : E.d 2 (12,136) (I.interpretation.basis .sphere 12 136 1) = -I.interpretation.basis .sphere 14 137 2 := by
      simpa only [map_add,d2,eq_neg_iff_add_eq_zero] using d12
    ext x
    obtain ⟨a,ha⟩ := lift_e2 (by decide : (2:ℤ)≤3) x
    have da := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) (hrep2 a) ⟨x,ha⟩
    let c : Fin 5 → F2 := e12_136 a
    have hcoef := congrArg e12_136.symm (f2_expand (e12_136 a))
    simp only [LinearEquiv.symm_apply_apply,map_sum,map_add,Fin.sum_univ_succ,apply_ite,map_zero] at hcoef
    change a = (if c 0=0 then 0 else e12_136.symm (Finsupp.single 0 1)) + ((if c 1=0 then 0 else e12_136.symm (Finsupp.single 1 1)) + ((if c 2=0 then 0 else e12_136.symm (Finsupp.single 2 1)) + ((if c 3=0 then 0 else e12_136.symm (Finsupp.single 3 1)) + ((if c 4=0 then 0 else e12_136.symm (Finsupp.single 4 1)) + 0)))) at hcoef
    simp only [he12_136_0,he12_136_1,he12_136_2,he12_136_3,he12_136_4,add_zero] at hcoef
    have hc : (c 1=0) ↔ (c 2=0) := by
      have hd := congrArg (E.d 2 (12,136)) hcoef
      simp only [map_add,apply_ite,map_zero] at hd
      rw [da,d0,d1,d2,d3,d4] at hd
      simp only [ite_self,zero_add,add_zero] at hd
      constructor
      · intro h1
        by_contra h2
        simp only [h1,h2,ite_true,ite_false,zero_add] at hd
        exact tn hd.symm
      · intro h2
        by_contra h1
        simp only [h1,h2,ite_true,ite_false,add_zero] at hd
        exact tn (neg_eq_zero.mp hd.symm)
    have hacomb : a = (if c 0=0 then 0 else I.interpretation.basis .sphere 12 136 0) +
        (if c 1=0 then 0 else I.interpretation.basis .sphere 12 136 1 + I.interpretation.basis .sphere 12 136 2) +
        (if c 3=0 then 0 else I.interpretation.basis .sphere 12 136 3) +
        (if c 4=0 then 0 else I.interpretation.basis .sphere 12 136 4) := by
      rw [hcoef]
      by_cases h1 : c 1=0
      · have h2 := hc.mp h1
        simp only [h1,h2,ite_true,zero_add,add_zero]
        abel
      · have h2 := mt hc.mpr h1
        simp only [h1,h2,ite_false]
        abel
    have hx : x=(if c 0=0 then 0 else a0) := by
      apply represents_unique ha
      rw [hacomb]
      simpa only [ite_self,add_zero] using hadd (hadd (hadd (hif (c 0) ha0) (hif (c 1) rz12)) (hif (c 3) rz3)) (hif (c 4) rz4)
    rw [hx]
    simp only [apply_ite,map_zero,hd0,ite_self,ModuleCat.hom_zero,LinearMap.zero_apply]
  obtain ⟨_,a4,t0,ha4,ht0,hda4⟩ := h277
  have hd4 : E.d 4 (11,135) a4=t0 := hda4
  -- Incoming d2 and d3 kill every E4 direction except basis1+basis2.
  have kernel_11 (x : E.Page 4 (11,135)) : x=0 ∨ x=a4 := by
    have rz0 : RepresentsOnPage E 4 (11,135) (I.interpretation.basis .sphere 11 135 0) 0 :=
      differential_target_later_zero (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<4) h200
    have rz34 : RepresentsOnPage E 4 (11,135)
        (I.interpretation.basis .sphere 11 135 3 + I.interpretation.basis .sphere 11 135 4) 0 :=
      differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4) h227
    have rz4 : RepresentsOnPage E 4 (11,135) (I.interpretation.basis .sphere 11 135 4) 0 :=
      differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4) h228
    have rz3 : RepresentsOnPage E 4 (11,135) (I.interpretation.basis .sphere 11 135 3) 0 := by
      simpa only [add_sub_cancel_right,sub_self] using hsub rz34 rz4
    have d0 := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4) (hrep2 _) ⟨0,rz0⟩
    have d12 := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4) (hrep2 _) ⟨a4,ha4⟩
    have d3 := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4) (hrep2 _) ⟨0,rz3⟩
    have d4 := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4) (hrep2 _) ⟨0,rz4⟩
    have d2 := h278.eq_on_page_two.2
    change E.d 2 (11,135) (I.interpretation.basis .sphere 11 135 2) = I.interpretation.basis .sphere 13 136 2 at d2
    have tn : I.interpretation.basis .sphere 13 136 2 ≠ 0 := by
      rw [←he13_136_2]
      intro h
      have hh := congrArg e13_136 h
      simp only [LinearEquiv.apply_symm_apply,map_zero] at hh
      have hh' := congrArg (fun f : Fin 3 →₀ F2 => f 2) hh
      norm_num at hh'
    have d1 : E.d 2 (11,135) (I.interpretation.basis .sphere 11 135 1) = -I.interpretation.basis .sphere 13 136 2 := by
      simpa only [map_add,d2,eq_neg_iff_add_eq_zero] using d12
    obtain ⟨a,ha⟩ := lift_e2 (by decide : (2:ℤ)≤4) x
    have da := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4) (hrep2 a) ⟨x,ha⟩
    let c : Fin 5 → F2 := e11_135 a
    have hcoef := congrArg e11_135.symm (f2_expand (e11_135 a))
    simp only [LinearEquiv.symm_apply_apply,map_sum,map_add,Fin.sum_univ_succ,apply_ite,map_zero] at hcoef
    change a = (if c 0=0 then 0 else e11_135.symm (Finsupp.single 0 1)) + ((if c 1=0 then 0 else e11_135.symm (Finsupp.single 1 1)) + ((if c 2=0 then 0 else e11_135.symm (Finsupp.single 2 1)) + ((if c 3=0 then 0 else e11_135.symm (Finsupp.single 3 1)) + ((if c 4=0 then 0 else e11_135.symm (Finsupp.single 4 1)) + 0)))) at hcoef
    simp only [he11_135_0,he11_135_1,he11_135_2,he11_135_3,he11_135_4,add_zero] at hcoef
    have hc : (c 1=0) ↔ (c 2=0) := by
      have hd := congrArg (E.d 2 (11,135)) hcoef
      simp only [map_add,apply_ite,map_zero] at hd
      rw [da,d0,d1,d2,d3,d4] at hd
      simp only [ite_self,zero_add,add_zero] at hd
      constructor
      · intro h1
        by_contra h2
        simp only [h1,h2,ite_true,ite_false,zero_add] at hd
        exact tn hd.symm
      · intro h2
        by_contra h1
        simp only [h1,h2,ite_true,ite_false,add_zero] at hd
        exact tn (neg_eq_zero.mp hd.symm)
    have hacomb : a = (if c 0=0 then 0 else I.interpretation.basis .sphere 11 135 0) +
        (if c 1=0 then 0 else I.interpretation.basis .sphere 11 135 1 + I.interpretation.basis .sphere 11 135 2) +
        (if c 3=0 then 0 else I.interpretation.basis .sphere 11 135 3) +
        (if c 4=0 then 0 else I.interpretation.basis .sphere 11 135 4) := by
      rw [hcoef]
      by_cases h1 : c 1=0
      · have h2 := hc.mp h1
        simp only [h1,h2,ite_true,zero_add,add_zero]
        abel
      · have h2 := mt hc.mpr h1
        simp only [h1,h2,ite_false]
        abel
    have hx : x=(if c 1=0 then 0 else a4) := by
      apply represents_unique ha
      rw [hacomb]
      simpa only [ite_self,add_zero,zero_add] using hadd (hadd (hadd (hif (c 0) rz0) (hif (c 1) ha4)) (hif (c 3) rz3)) (hif (c 4) rz4)
    by_cases h : c 1=0
    · exact Or.inl (by simpa only [h,ite_true] using hx)
    · exact Or.inr (by simpa only [h,ite_false] using hx)
  -- No d2 or d3 enters the d5 target degree, so distinct E2 labels
  -- that reach E4 remain distinct there.
  have nonzero4 {x : E.Page 2 (15,138)} (hx : x ≠ 0) {a : E.Page 4 (15,138)}
      (ha : RepresentsOnPage E 4 (15,138) x a) : a ≠ 0 := by
    obtain ⟨b,hb⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤4) ha
    have hn3 : b ≠ 0 := represents_next_nonzero_of_incoming_zero
      (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)≤2) (by exact d2_13) hb (hrep2 x) hx
    exact represents_next_nonzero_of_incoming_zero
      (by change (2:ℤ)≤3; omega) (by decide : (2:ℤ)≤3) (by exact d3_12) ha hb hn3
  obtain ⟨_,c5,t1,hc5,ht1,hdc5⟩ := h250
  have hd5 : E.d 5 (10,134) c5=t1 := hdc5
  -- The only possible d4 image is target basis0, independent of basis1.
  have t1n : t1 ≠ 0 := by
    obtain ⟨_,z,hz2,hz5⟩ := ht1
    let T := E.ssData (15,138)
    let i := Subobject.ofLE (T.Z 3) (T.Z 2) (T.Z_anti (by decide : (2:WithTop ℕ)≤3))
    let t14 := T.pageπ 2 (i z)
    have ht14 : RepresentsOnPage E 4 (15,138) (I.interpretation.basis .sphere 15 138 1) t14 := by
      refine ⟨by decide,i z,?_,rfl⟩
      change (i ≫ Subobject.ofLE (T.Z 2) (T.Z 0) _ ≫ T.pageπ 0) z = _
      dsimp only [i]
      rw [←Category.assoc,Subobject.ofLE_comp_ofLE]
      exact hz2
    have hn : t14 ≠ 0 := nonzero4 (by
      rw [←he15_138_1]
      intro h
      have hh := congrArg e15_138 h
      simp only [LinearEquiv.apply_symm_apply,map_zero] at hh
      have hh' := congrArg (fun f : Fin 3 →₀ F2 => f 1) hh
      norm_num at hh') ht14
    have hne : t14 ≠ t0 := by
      intro heq
      have hh := nonzero4 (x:=I.interpretation.basis .sphere 15 138 1 - I.interpretation.basis .sphere 15 138 0) (by
        rw [←he15_138_1,←he15_138_0]
        intro h
        have hh := congrArg e15_138 h
        simp only [map_sub,LinearEquiv.apply_symm_apply,map_zero] at hh
        have hh' := congrArg (fun f : Fin 3 →₀ F2 => f 1) hh
        norm_num at hh') (hsub ht14 ht0)
      exact hh (sub_eq_zero.mpr heq)
    intro hzero
    have hinc := (next_projection_zero_iff_incoming E 4
      (by change (2:ℤ)≤4; omega) (11,135) z).mp (hz5.trans hzero)
    change t14 ∈ LinearMap.range (E.d 4 (11,135)).hom at hinc
    obtain ⟨a,ha⟩ := hinc
    rcases kernel_11 a with h|h
    · apply hn
      simpa only [h,map_zero] using ha.symm
    · apply hne
      simpa only [h,hd4] using ha.symm
  have u_label : I.interpretation.sphere 10 134 U = I.interpretation.basis .sphere 10 134 4 := by
    have hc := I.monomials (⟨.sphere,10,134,["389,1","388,1","1,1,366,1","0,1,373,1","0,2,367,1"]⟩ : Raw.Degree) (by
      exact List.mem_of_getElem? (i := 181) (by rfl)) rfl
    obtain ⟨z,hz,he⟩ := hc (4 : Fin 5)
    have heq : U=z := by
      apply Subtype.ext
      rw [hz]
      change (generator ⟨0,by decide⟩ * generator ⟨0,by decide⟩) * generator ⟨367,by decide⟩ = projection (monomialOfString "0,2,367,1")
      have hs : "0,2,367,1" ≠ "" := by decide
      have hp : (("0,2,367,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [0,2,367,1] := by
        have split : "0,2,367,1".splitOn "," = ["0","2","367","1"] := by
          simp +decide [String.splitOn,String.splitOnAux]
        rw [split]
        simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
          String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
      simp only [monomialOfString,if_neg hs,hp]
      norm_num [polynomialOfPowers,RawData.generatorCount,generator,map_mul,pow_two]
    rw [heq]
    exact he
  let A := E.ssData (10,134)
  obtain ⟨z,hz,hzn⟩ := nonzero_permanent_of_survives1000 (D := D) V
    10 134 (by decide) (by norm_num) (by norm_num) _ (named_survive1000 I).1
  change (Subobject.ofLE (A.Z ⊤) (A.Z 0) (A.Z_anti le_top) ≫ A.pageπ 0) z = _ at hz
  change A.pageπ ⊤ z ≠ 0 at hzn
  let down (r : ℤ) := Subobject.ofLE (A.Z ⊤) (A.Z ↑(r-2).toNat) (A.Z_anti le_top)
  let val (r : ℤ) := down r ≫ A.pageπ ↑(r-2).toNat
  have rep (r : ℤ) (hr : 2≤r) (q : (Subobject.underlying.obj (A.Z ⊤) : ModuleCat.{v} ℤ)) :
      RepresentsOnPage E r (10,134) (val 2 q) (val r q) := by
    refine ⟨hr,down r q,?_,rfl⟩
    change (Subobject.ofLE _ _ _ ≫ A.pageπ 0) ((down r) q) = val 2 q
    dsimp only [val,down]
    rw [←CategoryTheory.comp_apply,←Category.assoc,Subobject.ofLE_comp_ofLE]
    rfl
  let u5 : E.Page 5 (10,134) := val 5 z
  have hu5 : RepresentsOnPage E 5 (10,134) (I.interpretation.basis .sphere 10 134 4) u5 := by
    have h := rep 5 (by decide) z
    change val 2 z = _ at hz
    rw [hz,u_label] at h
    exact h
  have hu0 : E.d 5 (10,134) u5=0 :=
    represents_d_zero_of_later (by change (2:ℤ)≤5; omega) (by decide : (5:ℤ)<6)
      (rep 5 (by decide) z) ⟨val 6 z,rep 6 (by decide) z⟩
  have r03 : RepresentsOnPage E 5 (10,134)
      (I.interpretation.basis .sphere 10 134 0 + I.interpretation.basis .sphere 10 134 3) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤4; omega) (by decide : (4:ℤ)<5) h171
  have r0134 : RepresentsOnPage E 5 (10,134)
      (I.interpretation.basis .sphere 10 134 0 + I.interpretation.basis .sphere 10 134 1 +
        I.interpretation.basis .sphere 10 134 3 + I.interpretation.basis .sphere 10 134 4) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤4; omega) (by decide : (4:ℤ)<5) h172
  have r24 : RepresentsOnPage E 5 (10,134)
      (I.interpretation.basis .sphere 10 134 2 + I.interpretation.basis .sphere 10 134 4) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<5) h201
  have ddouble (i : Fin 5) : I.interpretation.basis .sphere 10 134 i.val + I.interpretation.basis .sphere 10 134 i.val=0 := by
    rw [←he10_134 i]
    have hh : (Finsupp.single i (1:F2) : Fin 5 →₀ F2) + Finsupp.single i 1 = 0 := by
      rw [←Finsupp.single_add,show (1:F2)+1=0 from by decide,Finsupp.single_zero]
    have h := congrArg e10_134.symm hh
    simpa only [map_add,map_zero] using h
  have cdouble : c5+c5=0 := rep_double (ddouble 3) hc5
  have udouble : u5+u5=0 := rep_double (ddouble 4) hu5
  have cneg : -c5=c5 := by simpa only [add_sub_cancel_right,zero_sub] using (congrArg (fun t => t-c5) cdouble).symm
  have uneg : -u5=u5 := by simpa only [add_sub_cancel_right,zero_sub] using (congrArg (fun t => t-u5) udouble).symm
  have r0 : RepresentsOnPage E 5 (10,134) (I.interpretation.basis .sphere 10 134 0) c5 := by
    simpa only [add_sub_cancel_right,zero_sub,cneg] using hsub r03 hc5
  have r1 : RepresentsOnPage E 5 (10,134) (I.interpretation.basis .sphere 10 134 1) u5 := by
    have he : (I.interpretation.basis .sphere 10 134 0 + I.interpretation.basis .sphere 10 134 1 + I.interpretation.basis .sphere 10 134 3 + I.interpretation.basis .sphere 10 134 4) - (I.interpretation.basis .sphere 10 134 0 + I.interpretation.basis .sphere 10 134 3) - I.interpretation.basis .sphere 10 134 4 = I.interpretation.basis .sphere 10 134 1 := by abel
    simpa only [he,sub_self,zero_sub,uneg] using hsub (hsub r0134 r03) hu5
  have r2 : RepresentsOnPage E 5 (10,134) (I.interpretation.basis .sphere 10 134 2) u5 := by
    simpa only [add_sub_cancel_right,zero_sub,uneg] using hsub r24 hu5
  -- At E5 the complete five-element basis maps to [c,U,U,c,U].
  -- The nonzero differential of c leaves precisely zero and U in its kernel.
  have kernel5 (x : E.Page 5 (10,134)) (hx : E.d 5 (10,134) x=0) : x=0 ∨ x=u5 := by
    let vv : Fin 5 → E.Page 5 (10,134) := ![c5,u5,u5,c5,u5]
    have hv (i : Fin 5) : RepresentsOnPage E 5 (10,134) (e10_134.symm (Finsupp.single i 1)) (vv i) := by
      rw [he10_134]
      fin_cases i
      · exact r0
      · exact r1
      · exact r2
      · exact hc5
      · exact hu5
    obtain ⟨coef,hcoef⟩ := page_generated_from_representatives (by decide : (2:ℤ)≤5) e10_134 vv hv x
    simp only [Fin.sum_univ_succ] at hcoef
    change x = (if coef 0=0 then 0 else c5) + ((if coef 1=0 then 0 else u5) + ((if coef 2=0 then 0 else u5) + ((if coef 3=0 then 0 else c5) + ((if coef 4=0 then 0 else u5) + 0)))) at hcoef
    have hc : (coef 0=0) ↔ (coef 3=0) := by
      have hd := congrArg (E.d 5 (10,134)) hcoef
      simp only [map_add,apply_ite,map_zero] at hd
      rw [hx,hd5,hu0] at hd
      simp only [ite_self,zero_add,add_zero] at hd
      constructor
      · intro h0
        by_contra h3
        simp only [h0,h3,ite_true,ite_false,zero_add] at hd
        exact t1n hd.symm
      · intro h3
        by_contra h0
        simp only [h0,h3,ite_true,ite_false,add_zero] at hd
        exact t1n hd.symm
    have hform : x=(if coef 1=0 then 0 else u5) + (if coef 2=0 then 0 else u5) + (if coef 4=0 then 0 else u5) := by
      rw [hcoef]
      by_cases h0 : coef 0=0
      · have h3 := hc.mp h0
        simp only [h0,h3,ite_true,zero_add,add_zero]
        abel
      · have h3 := mt hc.mpr h0
        simp only [h0,h3,ite_false,add_zero]
        calc
          _ = (c5+c5) + ((if coef 1=0 then 0 else u5) + (if coef 2=0 then 0 else u5) + (if coef 4=0 then 0 else u5)) := by abel
          _ = _ := by rw [cdouble,zero_add]
    by_cases h1 : coef 1=0 <;> by_cases h2 : coef 2=0 <;> by_cases h4 : coef 4=0
    all_goals simp only [h1,h2,h4,ite_true,ite_false,zero_add,add_zero,udouble] at hform
    all_goals first | exact Or.inl hform | exact Or.inr hform
  refine ⟨z,hz,hzn,?_⟩
  intro y
  haveI : Epi (A.pageπ ⊤) := inferInstanceAs (Epi (cokernel.π _))
  obtain ⟨q,rfl⟩ := (ModuleCat.epi_iff_surjective (A.pageπ ⊤)).mp inferInstance y
  have hqzero : E.d 5 (10,134) (val 5 q)=0 :=
    represents_d_zero_of_later (by change (2:ℤ)≤5; omega) (by decide : (5:ℤ)<6)
      (rep 5 (by decide) q) ⟨val 6 q,rep 6 (by decide) q⟩
  rcases kernel5 (val 5 q) hqzero with hq|hq
  · left
    have h := A.infinity_projection_eq_of_page_projection_eq 3 q 0 (by
      change val 5 q = val 5 0
      rw [map_zero]
      exact hq)
    simpa only [map_zero] using h
  · right
    exact A.infinity_projection_eq_of_page_projection_eq 3 q z hq

private theorem theta_detection_step
    {D : AdamsComparison H M Syn}
    (i : Tridegree) (x : (D.family.sphere).E₂ i)
    (hframe : ∀ e : ((D.family.sphere).sequence.ssData i).eInfty,
      e=0 ∨ HasInfinityRepresentative D.family.sphere 2 i x e)
    (a : BiHom (i.2.1-i.1) i.2.2 (S_0_0 : Syn))
    (ha : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) i.1 a) :
    DetectsNonzero D.sphereConvergence i x a ∨
      FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) (i.1+1) a := by
  let F := towerFiltration (nuCoefficientUnit H.unit D.nu) (S_0_0 : Syn)
  have ham : a ∈ (ModuleCat.subobjectModule (syntheticHomotopy (S_0_0:Syn) (i.2.1-i.1,i.2.2)))
      (F.F i.1 (i.2.1-i.1,i.2.2)) := by
    simpa only [F,towerFiltration,OrderIso.apply_symm_apply,FiltrationAtLeast] using ha
  obtain ⟨a',ha'⟩ := ham
  let q := F.toAssociatedGraded i.1 (i.2.1-i.1,i.2.2) a'
  let e := (D.sphereConvergence.identification i).inv q
  have he : (D.sphereConvergence.identification i).hom e=q :=
    ConcreteCategory.congr_hom (D.sphereConvergence.identification i).inv_hom_id q
  by_cases he0 : e=0
  · right
    have hq : F.toAssociatedGraded i.1 (i.2.1-i.1,i.2.2) a'=0 := by
      rw [he0,map_zero] at he
      exact he.symm
    have hmem := (subobject_cokernel_π_eq_zero_iff
      (F.F (i.1+1) (i.2.1-i.1,i.2.2)) (F.F i.1 (i.2.1-i.1,i.2.2))
      (F.mono i.1 (i.2.1-i.1,i.2.2)) a').mp hq
    rw [ha'] at hmem
    simpa only [F,towerFiltration,OrderIso.apply_symm_apply,FiltrationAtLeast] using hmem
  · left
    have hr := (hframe e).resolve_left he0
    exact ⟨⟨e,hr,a',ha',he⟩,e,hr,he0⟩
/- The two complete frames and the intervening finite-page gap yield the
three branches, retaining an actual lambda preimage in the last branch. -/

private theorem theta_quotient_frame
    (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G) (s t : ℤ) (k : ℕ) (hst : t=s+124) (hsk : s-(k+2)≤4)
    (x : E2 H SphereSpectrum s t) (hx : ClassicalInfinityGenerated s t x) :
    ∃ x' : PageRepresentatives.permanentCycles H SphereSpectrum (s,t), x'.val=x ∧
      ∀ q : PageRepresentatives.PermanentQuotient H SphereSpectrum (1+(k:ℤ)) (s,t),
        q=0 ∨ q=NestedQuotient.projection _ _ x' := by
  classical
  let E := adamsTowerInternalSpectralSequence H.unit SphereSpectrum
  let P := E.ssData (s,t)
  have hB : P.B ⊤ = P.B (k:WithTop ℕ) := by
    have hin : ∀ r : ℤ, (k:ℤ)+2 ≤ r → E.d r ((s,t)-E.diffDeg r)=0 := by
      intro r hr
      change E.d r (s-r,t-(r-1))=0
      rw [show t-(r-1)=(s-r)+125 by omega]
      ext z
      exact no_outgoing_stem125_low I (s-r) (by omega) r (by omega) z
    have h := boundaries_top_eq_of_d_eq_zero E (k+2) (by change (2:ℤ)≤_; omega) (s,t) hin
    change P.B ⊤ = P.B (↑((k:ℤ)+2-2).toNat) at h
    simpa only [add_sub_cancel_right,Int.toNat_natCast] using h
  obtain ⟨z,hz,_,hall⟩ := hx
  change PageRepresentatives.cycleMap H SphereSpectrum ⊤ (s,t) z=x at hz
  let x' : PageRepresentatives.permanentCycles H SphereSpectrum (s,t) := ⟨x,⟨z,hz⟩⟩
  refine ⟨x',rfl,?_⟩
  have zero_of_infinity_zero (z' : (Subobject.underlying.obj (P.Z ⊤) : ModuleCat ℤ))
      (hzero : P.pageπ ⊤ z'=0) :
      PageRepresentatives.cycleMap H SphereSpectrum ⊤ (s,t) z' ∈
        PageRepresentatives.boundaries H SphereSpectrum (1+(k:ℤ)) (s,t) := by
    obtain ⟨b,hb⟩ := (cokernel_π_eq_zero_iff_mem_range
      (Subobject.ofLE (P.B ⊤) (P.Z ⊤) (P.B_le_Z ⊤)) z').mp hzero
    have hi : P.B ⊤ ≤ P.B (k:WithTop ℕ) := hB.le
    change ∃ q, PageRepresentatives.boundaryMap H SphereSpectrum
      (↑((1+(k:ℤ))-1).toNat) (s,t) q = _
    rw [show 1+(k:ℤ)-1=(k:ℤ) by omega,Int.toNat_natCast]
    refine ⟨(Subobject.ofLE _ _ hi) b,?_⟩
    rw [←hb]
    change (Subobject.ofLE _ _ hi ≫ PageRepresentatives.boundaryMap H SphereSpectrum (k:WithTop ℕ) (s,t)) b =
      (Subobject.ofLE _ _ (P.B_le_Z ⊤) ≫ PageRepresentatives.cycleMap H SphereSpectrum ⊤ (s,t)) b
    congr 1
    dsimp only [PageRepresentatives.boundaryMap,PageRepresentatives.cycleMap,P,E]
    rw [←Category.assoc,Subobject.ofLE_comp_ofLE,←Category.assoc,Subobject.ofLE_comp_ofLE]
  rintro ⟨y⟩
  obtain ⟨z',hz'⟩ := y.property
  rcases hall (P.pageπ ⊤ z') with h0|h1
  · left
    apply (NestedQuotient.projection_eq_zero y).mpr
    rw [←hz']
    exact zero_of_infinity_zero z' h0
  · right
    apply sub_eq_zero.mp
    change NestedQuotient.projection _ _ y - NestedQuotient.projection _ _ x'=0
    rw [←map_sub]
    apply (NestedQuotient.projection_eq_zero (y-x')).mpr
    change y.val-x ∈ _
    rw [←hz',←hz,←map_sub]
    exact zero_of_infinity_zero (z'-z) (by rw [map_sub,h1,sub_self])

private theorem theta_sphere_frame_family_map_data {X Y : Syn} (f : X ⟶ Y) (i : Tridegree) :
    familyPageMap D.family f 2 i = (D.family.functor.map f).toSSDataMorphism.pageMap i 0 := by
  classical
  let F := (D.family.functor.map f).toSSDataMorphism
  let PX := (D.family.functor.obj X).ssData i
  let PY := (D.family.functor.obj Y).ssData i
  let nX : WithTop ℕ := ↑(2-(D.family.functor.obj X).r₀).toNat
  let nY : WithTop ℕ := ↑(2-(D.family.functor.obj Y).r₀).toNat
  change (@eqToHom (ModuleCat ℤ) _ (PX.page 0) (PX.page nX) _ ≫
    (F.pageMap i nX ≫ @eqToHom (ModuleCat ℤ) _ (PY.page nX) (PY.page nY) _) ≫
    @eqToHom (ModuleCat ℤ) _ (PY.page nY) (PY.page 0) _) = F.pageMap i 0
  have hX : nX=0 := by dsimp only [nX]; rw [D.family.firstPage X]; rfl
  have hY : nY=0 := by dsimp only [nY]; rw [D.family.firstPage Y]; rfl
  have normalize (A B : WithTop ℕ → ModuleCat.{v} ℤ) (j : ∀ n, A n ⟶ B n)
      (n m : WithTop ℕ) (hn : n=0) (hm : m=0)
      (h1 : A 0=A n) (h2 : B n=B m) (h3 : B m=B 0) :
      eqToHom h1 ≫ (j n ≫ eqToHom h2) ≫ eqToHom h3 = j 0 := by
    subst n
    subst m
    simp only [eqToHom_refl,Category.id_comp,Category.comp_id]
  exact normalize PX.page PY.page (fun n => F.pageMap i n) nX nY hX hY _ _ _

private theorem theta_sphere_frame_map_infinity {X Y : Syn} (f : X ⟶ Y) (i : Tridegree)
    (y : (D.family.obj X).E₂ i) (e : ((D.family.obj X).sequence.ssData i).eInfty)
    (hy : HasInfinityRepresentative (D.family.obj X) 2 i y e) :
    HasInfinityRepresentative (D.family.obj Y) 2 i
      (familyPageMap D.family f 2 i y) ((D.family.functor.map f).eInftyMap i e) := by
  classical
  obtain ⟨hr,z,hz,he⟩ := hy
  change (Subobject.ofLE (((D.family.functor.obj X).ssData i).Z ⊤)
    (((D.family.functor.obj X).ssData i).Z 0) _ ≫ ((D.family.functor.obj X).ssData i).pageπ 0) z=y at hz
  let F := (D.family.functor.map f).toSSDataMorphism
  refine ⟨hr,F.cycleMap i ⊤ z,?_,?_⟩
  · rw [theta_sphere_frame_family_map_data]
    have h := F.cycleMap_ofLE_assoc i (show (0:WithTop ℕ)≤⊤ from le_top)
      (((D.family.obj Y).sequence.ssData i).pageπ 0)
    dsimp only [SyntheticAdamsFamily.obj] at h
    rw [←F.pageπ_pageMap] at h
    exact (congrArg (fun a => a z) h).symm.trans (by
      simpa only [ModuleCat.comp_apply,CategoryTheory.comp_apply] using congrArg (fun q => F.pageMap i 0 q) hz)
  · exact (congrArg (fun a => a z) (F.pageπ_pageMap i ⊤)).symm.trans (by
      change F.pageMap i ⊤ (((D.family.obj X).sequence.ssData i).pageπ ⊤ z)=_
      rw [he])

private theorem theta_sphere_frame
    (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G) (BHS : SyntheticComparisonTheorems D)
    (s t : ℤ) (k : ℕ) (hst : t=s+124) (hsk : s-(k+2)≤4)
    (x : E2 H SphereSpectrum s t) (hx : ClassicalInfinityGenerated s t x) :
    ∀ e : ((D.family.sphere).sequence.ssData (s,t,t-k)).eInfty,
      e=0 ∨ HasInfinityRepresentative D.family.sphere 2 (s,t,t-k) (D.sphereE2 s t k x) e := by
  classical
  classical
  obtain ⟨x',hx',hframe⟩ := theta_quotient_frame I s t k hst hsk x hx
  intro e
  let i : Tridegree := (s,t,t-k)
  let f := (D.family.functor.map D.nu.unitIso.hom).eInftyMap i
  let g := (D.family.functor.map D.nu.unitIso.inv).eInftyMap i
  have hfg : g ≫ f = 𝟙 _ := by
    dsimp only [f,g]
    rw [←SpectralSequenceMorphism.eInftyMap_comp,←Functor.map_comp,Iso.inv_hom_id,
      CategoryTheory.Functor.map_id,SpectralSequenceMorphism.eInftyMap_id]
  have hback : f (g e)=e := ConcreteCategory.congr_hom hfg e
  let nuE := BHS.eInfty.presentation.nuWindow SphereSpectrum (s,t) (t-k) (by omega)
  have heqcut : 1+t-(t-(k:ℤ))=1+(k:ℤ) := by omega
  have hfq : nuE (g e)=0 ∨ nuE (g e)=NestedQuotient.projection _ _ x' := by
    have hh : ∀ q : PageRepresentatives.PermanentQuotient H SphereSpectrum (1+t-(t-(k:ℤ))) (s,t),
        q=0 ∨ q=NestedQuotient.projection _ _ x' := by
      rw [heqcut]
      exact hframe
    exact hh (nuE (g e))
  rcases hfq with h0|h1
  · left
    have hg0 : g e=0 := nuE.injective (h0.trans (map_zero nuE).symm)
    rw [←hback,hg0,map_zero]
  · right
    have hr := (BHS.eInfty.labels.2 .sphere (s,t) k x' (g e)).mpr h1
    have hh := theta_sphere_frame_map_infinity D.nu.unitIso.hom i _ _ hr
    have hlabel : familyPageMap D.family D.nu.unitIso.hom 2 i
        (targetNuLabel D .sphere s t k x'.val) = D.sphereE2 s t k x := by
      rw [hx']
      dsimp only [targetNuLabel]
      rw [theta_sphere_frame_family_map_data,theta_sphere_frame_family_map_data]
      dsimp only [i] at *
      change ((D.family.functor.map (SyntheticCategory.biShift_zero.hom.app (D.nu.functor.obj SphereSpectrum))).toSSDataMorphism.pageMap (s,t,t-k) 0 ≫
        (D.family.functor.map D.nu.unitIso.hom).toSSDataMorphism.pageMap (s,t,t-k) 0) _ = _
      rw [←SSDataMorphism.pageMap_comp]
      have hp := D.comparisonCompatible.sphere_nu s t k x
      rw [theta_sphere_frame_family_map_data] at hp
      have hm : ((D.family.functor.map (SyntheticCategory.biShift_zero.hom.app (D.nu.functor.obj SphereSpectrum))).toSSDataMorphism.comp
          (D.family.functor.map D.nu.unitIso.hom).toSSDataMorphism) =
          (D.family.functor.map (SyntheticCategory.biShift_zero.hom.app (D.nu.functor.obj SphereSpectrum) ≫ D.nu.unitIso.hom)).toSSDataMorphism := by
        change (D.family.functor.map _ ≫ D.family.functor.map _).toSSDataMorphism = _
        rw [←CategoryTheory.Functor.map_comp]
      rw [hm]
      exact hp
    change HasInfinityRepresentative D.family.sphere 2 i _ (f (g e)) at hh
    rw [hback,hlabel] at hh
    exact hh

private theorem theta_three_cases_from_frames_permanentQuotient_zero_of_page_six_zero (s t b : ℤ) (hb : 5 ≤ b)
    (hpage : Subsingleton ((sequence D .sphere).Page 6 (s, t))) :
    Subsingleton (PageRepresentatives.PermanentQuotient H SphereSpectrum b (s, t)) := by
  classical
  set_option backward.isDefEq.respectTransparency false in
    let E := (sequence D .sphere).ssData (s, t)
    haveI : Subsingleton (E.page 4) := hpage
    have hcycles : PageRepresentatives.permanentCycles H SphereSpectrum (s, t) ≤
        PageRepresentatives.boundaries H SphereSpectrum 5 (s, t) := by
      rintro x ⟨z, hz⟩
      let zf := (Subobject.ofLE (E.Z ⊤) (E.Z 4) (E.Z_anti le_top)) z
      have hzero : E.pageπ 4 zf = 0 := Subsingleton.elim _ _
      obtain ⟨y, hy⟩ := (cokernel_π_eq_zero_iff_mem_range
        (Subobject.ofLE (E.B 4) (E.Z 4) (E.B_le_Z 4)) zf).mp hzero
      refine ⟨y, ?_⟩
      change PageRepresentatives.boundaryMap H SphereSpectrum 4 (s, t) y = x
      have hfactor : Subobject.ofLE (E.B 4) (E.Z 4) (E.B_le_Z 4) ≫
          PageRepresentatives.cycleMap H SphereSpectrum 4 (s, t) =
          PageRepresentatives.boundaryMap H SphereSpectrum 4 (s, t) := by
        dsimp only [PageRepresentatives.cycleMap, PageRepresentatives.boundaryMap, E, Computation.SphereAndCofiber.sequence, object]
        rw [← Category.assoc, Subobject.ofLE_comp_ofLE]
      rw [← hfactor, CategoryTheory.comp_apply]
      apply (congrArg (PageRepresentatives.cycleMap H SphereSpectrum 4 (s, t)) hy).trans
      exact (congrArg (fun f => f z)
        (PageRepresentatives.cycleMap_factor H SphereSpectrum (s, t) 4 ⊤ le_top)).trans hz
    have hall : ∀ x : PageRepresentatives.PermanentQuotient H SphereSpectrum b (s, t), x = 0 := by
      rintro ⟨x⟩
      change KIP126.Algebra.NestedQuotient.projection _ _ x = 0
      apply (KIP126.Algebra.NestedQuotient.projection_eq_zero x).mpr
      exact PageRepresentatives.boundaries_monotone H SphereSpectrum (s, t) hb (hcycles x.property)
    exact ⟨fun x y => (hall x).trans (hall y).symm⟩

private theorem theta_three_cases_from_frames
    (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G) (BHS : SyntheticComparisonTheorems D)
    (x10 : E2 H SphereSpectrum 10 134) (x13 : E2 H SphereSpectrum 13 137)
    (h10 : ClassicalInfinityGenerated 10 134 x10)
    (h13 : ClassicalInfinityGenerated 13 137 x13)
    (h11 : Subsingleton ((Computation.SphereAndCofiber.sequence D .sphere).Page 5 (11,135)))
    (h12 : Subsingleton ((Computation.SphereAndCofiber.sequence D .sphere).Page 4 (12,136)))
    (a : BiHom 124 128 (S_0_0 : Syn))
    (ha10 : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 10 a) :
    SphereDetected D 10 134 6 x10 a ∨ SphereDetected D 13 137 9 x13 a ∨
      ∃ b : BiHom 124 138 (S_0_0:Syn), lambdaMultiply 10 b=a := by
  classical
  have hgap : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 11 a →
      FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 13 a := by
    classical
    apply (D.sphereConvergence.filtrationAtLeast_iff_of_eInfty_isZero
      11 13 124 128 (by omega) ?_ a).mp
    intro j hj hj'
    have hpage : Subsingleton ((Computation.SphereAndCofiber.sequence D .sphere).Page 6 (j,124+j)) := by
      interval_cases j
      · exact adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum 5 6 11 135
          (by omega) (by omega) h11
      · exact adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum 4 6 12 136
          (by omega) (by omega) h12
    haveI : Subsingleton (PageRepresentatives.PermanentQuotient H SphereSpectrum
        (1+(124+j)-128) (j,124+j)) :=
      theta_three_cases_from_frames_permanentQuotient_zero_of_page_six_zero j (124+j) _ (by omega) hpage
    let e := BHS.eInfty.presentation.nuWindow SphereSpectrum (j,124+j) 128 (by omega)
    haveI : Subsingleton (((D.family.nu D.nu SphereSpectrum).sequence.ssData (j,124+j,128)).eInfty) := e.injective.subsingleton
    let hnu := ModuleCat.isZero_of_subsingleton
      (((D.family.nu D.nu SphereSpectrum).sequence.ssData (j,124+j,128)).eInfty)
    let f := (D.family.functor.map D.nu.unitIso.hom).eInftyMap (j,124+j,128)
    let g := (D.family.functor.map D.nu.unitIso.inv).eInftyMap (j,124+j,128)
    have hfg : g ≫ f = 𝟙 _ := by
      dsimp only [f,g]
      rw [←SpectralSequenceMorphism.eInftyMap_comp,←CategoryTheory.Functor.map_comp,Iso.inv_hom_id,
        CategoryTheory.Functor.map_id,SpectralSequenceMorphism.eInftyMap_id]
    apply (CategoryTheory.Limits.IsZero.iff_id_eq_zero _).mpr
    exact hfg.symm.trans (by rw [hnu.eq_of_src f 0,CategoryTheory.Limits.comp_zero])

  have hf10 := theta_sphere_frame I BHS 10 134 6 (by omega) (by omega) x10 h10

  classical
  rcases theta_detection_step (10,134,128) (D.sphereE2 10 134 6 x10) hf10 a ha10 with hdet|ha11
  · exact Or.inl hdet
  have ha13 := hgap ha11
  have hf13 := theta_sphere_frame I BHS 13 137 9 (by omega) (by omega) x13 h13
  rcases theta_detection_step (13,137,128) (D.sphereE2 13 137 9 x13) hf13 a ha13 with hdet|ha14
  · exact Or.inr (Or.inl hdet)
  right; right
  have hmap {X Y : Syn} (f : X ⟶ Y) {m w s : ℤ} (x : BiHom m w X)
      (hx : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) s x) :
      FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) s (x ≫ f) := by
    obtain ⟨z,hz⟩ := hx
    refine ⟨z ≫ adamsTowerInduced (nuCoefficientUnit H.unit D.nu) f s.toNat,?_⟩
    change (z ≫ adamsTowerInduced (nuCoefficientUnit H.unit D.nu) f s.toNat) ≫
      adamsTowerMap (nuCoefficientUnit H.unit D.nu) Y 0 s.toNat _ = x ≫ f
    change z ≫ adamsTowerMap (nuCoefficientUnit H.unit D.nu) X 0 s.toNat _ = x at hz
    rw [Category.assoc,adamsTowerInduced_map,←Category.assoc,hz]
    rfl
  have h := BHS.filtration_lambda .sphere 124 128 14 (by omega) (a ≫ D.nu.unitIso.inv)
  change FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 14 (a ≫ D.nu.unitIso.inv) ↔
    ∃ b : BiHom 124 138 (D.nu.functor.obj SphereSpectrum), lambdaMultiply 10 b=a ≫ D.nu.unitIso.inv at h
  obtain ⟨b,hb⟩ := h.mp (hmap D.nu.unitIso.inv a ha14)
  refine ⟨b ≫ D.nu.unitIso.hom,?_⟩
  simpa [lambdaMultiply,Category.assoc] using congrArg (fun q => q ≫ D.nu.unitIso.hom) hb

private theorem theta_square_detection_cases (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G)
    (BHS : SyntheticComparisonTheorems D) (V : SphereVanishingLine H)
    (SF : Derived.SphereFacts I.interpretation) :
    ClassicalInfinityGenerated 13 137 (I.interpretation.sphere 13 137 correction) ∧
      ∀ theta : BiHom 62 64 (S_0_0 : Syn),
        Theta5SquareNonzeroDetectionAt M D.toAdamsComparisonData L theta ∨
          SphereDetected D 13 137 9 (I.interpretation.sphere 13 137 correction)
            (sphereProduct theta theta) ∨
          ∃ a : BiHom 124 138 (S_0_0 : Syn), lambdaMultiply 10 a=sphereProduct theta theta := by
  /- BHS label agreement and the actual nu-unit map transport common infinity
  representatives to the synthetic sphere, including the zero case. -/
  /- Actual convergence gives either nonzero leading detection or membership
  in the next actual tower filtration. -/

  have classical_low_same_input (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G) (s : ℤ) (hs : s<10) :
      Subsingleton ((adamsTowerInternalSpectralSequence H.unit SphereSpectrum).ssData (s,s+124)).eInfty := by
    set_option backward.isDefEq.respectTransparency false in
    set_option maxRecDepth 10000 in
      let E := adamsTowerInternalSpectralSequence H.unit SphereSpectrum
      have collapse (r : ℤ) (hp : Subsingleton (E.Page r (s,s+124))) :
          Subsingleton ((E.ssData (s,s+124)).eInfty) := by
        let A := E.ssData (s,s+124)
        haveI : Epi (A.pageπ ⊤) := inferInstanceAs (Epi (CategoryTheory.Limits.cokernel.π _))
        refine ⟨fun x y => ?_⟩
        obtain ⟨x,rfl⟩ := (ModuleCat.epi_iff_surjective (A.pageπ ⊤)).mp inferInstance x
        obtain ⟨y,rfl⟩ := (ModuleCat.epi_iff_surjective (A.pageπ ⊤)).mp inferInstance y
        exact A.infinity_projection_eq_of_page_projection_eq ↑(r-E.r₀).toNat x y (hp.elim _ _)
      by_cases hneg : s < 0
      · exact collapse 2 (adamsTowerInternal_page_subsingleton_of_negative
          H.unit SphereSpectrum 2 s (s+124) hneg)
      have hs0 : 0 ≤ s := by omega
      by_cases hsmall : s ≤ 5
      · have hd : (⟨.sphere,s.toNat,(s+124).toNat,[]⟩ : KIP126.Computation.SphereAndCofiber.Raw.Degree) ∈ KIP126.Computation.SphereAndCofiber.Raw.degrees := by
          interval_cases s <;> simp [KIP126.Computation.SphereAndCofiber.Raw.degrees]
        obtain ⟨e,_⟩ := I.basis _ hd
        change KIP126.Computation.SphereAndCofiber.Page D .sphere s.toNat (s+124).toNat ≃ₗ[ℤ] (Fin 0 →₀ KIP126.Algebra.F2) at e
        have he : Subsingleton (KIP126.Computation.SphereAndCofiber.Page D .sphere s.toNat (s+124).toNat) := e.injective.subsingleton
        apply collapse 2
        simpa only [KIP126.Computation.SphereAndCofiber.Page,KIP126.Computation.SphereAndCofiber.sequence,KIP126.Computation.SphereAndCofiber.object,E,
        Int.toNat_of_nonneg hs0,
          Int.toNat_of_nonneg (by omega : 0 ≤ s+124)] using he
      have hfinite := stem124_finite_pages I
      change Subsingleton (E.Page 6 (6,130)) ∧ Subsingleton (E.Page 6 (7,131)) ∧
        Subsingleton (E.Page 3 (8,132)) ∧ Subsingleton (E.Page 4 (9,133)) at hfinite
      interval_cases s
      · exact collapse 6 hfinite.1
      · exact collapse 6 hfinite.2.1
      · exact collapse 3 hfinite.2.2.1
      · exact collapse 4 hfinite.2.2.2
  have theta_three_cases_same_input (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G)
      (BHS : SyntheticComparisonTheorems D) (V : SphereVanishingLine H)
      (SF : Derived.SphereFacts I.interpretation)
      (theta : BiHom 62 64 (S_0_0 : Syn)) :
      Theta5SquareNonzeroDetectionAt M D.toAdamsComparisonData L theta ∨
        SphereDetected D 13 137 9 (I.interpretation.sphere 13 137 KIP126.Computation.Near126.correction)
          (sphereProduct theta theta) ∨
        ∃ a : BiHom 124 138 (S_0_0 : Syn), lambdaMultiply 10 a=sphereProduct theta theta := by
    have h10 := stem124_af10_exhaustion I V
    rw [(KIP126.Computation.SphereAndCofiber.distinguished_expression_comparisons I).2.1] at h10
    exact theta_three_cases_from_frames I BHS (L.U M)
      (I.interpretation.sphere 13 137 KIP126.Computation.Near126.correction)
      h10 (stem124_af13_exhaustion I SF)
      SF.e5_stem124_af11
      SF.e4_stem124_af12
      (sphereProduct theta theta)
      (stem124_weight128_filtration_ten BHS I (classical_low_same_input I) (sphereProduct theta theta))
  exact ⟨stem124_af13_exhaustion I SF,theta_three_cases_same_input I BHS V SF⟩

end
end KIP126.Main.SectionSeven.DifferentialCriterion
