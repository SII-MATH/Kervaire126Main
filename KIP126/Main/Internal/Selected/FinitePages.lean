module
public import KIP126.Main.Conditions
public import KIP126.SSComputation.Table
import all KIP126.Main.Internal.PageCalculus
import all KIP126.Main.Internal.Selected.NormalizedTable

/-! Complete finite-page stem-124 calculations from Selected/ThetaData:33–741
at bbac1fc05843 (MIT), using the fixed actual table. -/
@[expose] section
namespace KIP126.Main.Internal.Selected
open CategoryTheory CategoryTheory.Limits KIP126.Core.Algebra
open KIP126.StableHomotopy KIP126.Core.SpectralSequence
open KIP126.Core.SpectralSequence.FinitePageCalculus
open KIP126.AdamsSynthetic.Standard (model)
open Normalized
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000

private theorem page_subsingleton_of_le (r t s u : ℤ) (hr : 2≤r) (hrt : r≤t)
    (hp : Subsingleton (Normalized.sphere.Page r (s,u))) :
    Subsingleton (Normalized.sphere.Page t (s,u)) := by
  have hall (a : Normalized.sphere.Page t (s,u)) : a=0 := by
    obtain ⟨x,hx⟩ := page_has_initial_representative (by omega) a
    obtain ⟨xr,hxr⟩ := KIP126.Main.Internal.reaches_before hr hrt ⟨a,hx⟩
    have hz : xr=0 := hp.elim _ _
    rw [hz] at hxr
    exact represents_later_zero hrt hxr hx
  exact ⟨fun a b => (hall a).trans (hall b).symm⟩

private theorem stem124_finite_pages_low124_d2_10  : (Normalized.sphere).d 2 (10,134) = 0 := by
  classical
  let E := Normalized.sphere
  have hrep2 {p : ℤ × ℤ} (x : E.Page 2 p) : RepresentsOnPage E 2 p x x := by
    exact represents_two_self _
  have h171 : HasDifferential E 4 (6,131) (10,134)
      (basis .sphere 6 131 0) (basis .sphere 10 134 0 + basis .sphere 10 134 3) := by
    have hrow := result ⟨.sphere,.equation,4,6,131,[0],10,134,[0, 3],"S0_AdamsE2_ss",2492⟩ (by
      exact List.mem_of_getElem? (i := 171) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 4 (6,131) (10,134) a b at h
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 6 131 [0] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 10 134 [0, 3] = true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [← ha,← hb] at h
    simpa only [add_assoc] using h
  have h172 : HasDifferential E 4 (6,131) (10,134)
      (basis .sphere 6 131 1) (basis .sphere 10 134 0 + basis .sphere 10 134 1 + basis .sphere 10 134 3 + basis .sphere 10 134 4) := by
    have hrow := result ⟨.sphere,.equation,4,6,131,[1],10,134,[0, 1, 3, 4],"S0_AdamsE2_ss",2493⟩ (by
      exact List.mem_of_getElem? (i := 172) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 4 (6,131) (10,134) a b at h
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 6 131 [1] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 10 134 [0, 1, 3, 4] = true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [← ha,← hb] at h
    simpa only [add_assoc] using h
  have h201 : HasDifferential E 2 (8,133) (10,134)
      (basis .sphere 8 133 1) (basis .sphere 10 134 2 + basis .sphere 10 134 4) := by
    have hrow := result ⟨.sphere,.equation,2,8,133,[1],10,134,[2, 4],"S0_AdamsE2_ss",2630⟩ (by
      exact List.mem_of_getElem? (i := 201) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 2 (8,133) (10,134) a b at h
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 8 133 [1] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 10 134 [2, 4] = true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [← ha,← hb] at h
    simpa only [add_assoc] using h
  have h250 : HasDifferential E 5 (10,134) (15,138)
      (basis .sphere 10 134 3) (basis .sphere 15 138 1) := by
    have hrow := result ⟨.sphere,.equation,5,10,134,[3],15,138,[1],"S0_AdamsE2_ss",2694⟩ (by
      exact List.mem_of_getElem? (i := 250) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 5 (10,134) (15,138) a b at h
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 10 134 [3] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 15 138 [1] = true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [← ha,← hb] at h
    simpa only [add_assoc] using h
  have h249 : ReachesPage E 1000 (10,134) (basis .sphere 10 134 4) := by
    have hrow := result ⟨.sphere,.reaches,1000,10,134,[4],10,134,[],"S0_AdamsE2_ss",2693⟩ (by
      exact List.mem_of_getElem? (i := 249) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,h⟩ := hrow
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 10 134 [4] = true := rfl
    simp only [decode,vx,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha
    rw [← ha] at h
    exact h
  have d03 := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4)
    (hrep2 _) (show ReachesPage E 4 (10,134) _ from ⟨h171.choose_spec.choose_spec.choose, h171.choose_spec.choose_spec.choose_spec.2.1⟩)
  have d0134 : E.d 2 (10,134) (basis .sphere 10 134 0 + basis .sphere 10 134 1 + basis .sphere 10 134 3 + basis .sphere 10 134 4) = 0 := by
    obtain ⟨_,xr,yr,hxr,hyr,_⟩ := h172
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4) (hrep2 _) ⟨yr,hyr⟩
  have d24 : E.d 2 (10,134) (basis .sphere 10 134 2 + basis .sphere 10 134 4) = 0 := by
    obtain ⟨_,hd⟩ := h201.eq_on_page_two
    change E.d 2 (8,133) (basis .sphere 8 133 1) = _ at hd
    rw [← hd]
    exact congrArg (fun f => f (basis .sphere 8 133 1)) (E.d_comp_d 2 (8,133))
  have d4 := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<1000) (hrep2 _) h249
  have d3 : E.d 2 (10,134) (basis .sphere 10 134 3) = 0 := by
    obtain ⟨_,xr,yr,hxr,hyr,_⟩ := h250
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<5) (hrep2 _) ⟨xr,hxr⟩
  have d0 : E.d 2 (10,134) (basis .sphere 10 134 0) = 0 := by simpa only [map_add,d3,add_zero] using d03
  have d1 : E.d 2 (10,134) (basis .sphere 10 134 1) = 0 := by simpa only [map_add,d0,d3,d4,zero_add,add_zero] using d0134
  have d2 : E.d 2 (10,134) (basis .sphere 10 134 2) = 0 := by simpa only [map_add,d4,add_zero] using d24
  obtain ⟨e,he⟩ := basis_correct ⟨.sphere,10,134,["389,1","388,1","1,1,366,1","0,1,373,1","0,2,367,1"]⟩ (by
    exact List.mem_of_getElem? (i := 181) (by rfl))
  change E.Page 2 (10,134) ≃ₗ[ℤ] (Fin 5 →₀ KIP126.Core.Algebra.F2) at e
  change ∀i : Fin 5, e.symm (Finsupp.single i 1) = basis .sphere 10 134 i.val at he
  have hone (i : Fin 5) : E.d 2 (10,134) (e.symm (Finsupp.single i 1)) = 0 := by
    rw [he]
    fin_cases i
    · exact d0
    · exact d1
    · exact d2
    · exact d3
    · exact d4
  have hall (f : Fin 5 →₀ KIP126.Core.Algebra.F2) : E.d 2 (10,134) (e.symm f) = 0 := by
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


private theorem stem124_finite_pages_low124_af9_four  :
    Subsingleton ((Normalized.sphere).Page 4 (9,133)) ∧
    (∀ y : (Normalized.sphere).Page 4 (12,135),
      RepresentsOnPage (Normalized.sphere) 4 (12,135) (basis .sphere 12 135 2) y → y ≠ 0) ∧
    ∀ x : (Normalized.sphere).Page 2 (9,133), (Normalized.sphere).d 2 (9,133) x = 0 ∨
      (Normalized.sphere).d 2 (9,133) x = basis .sphere 11 134 4 := by
  classical
  let E := Normalized.sphere
  have hrep2 {p : ℤ × ℤ} (x : E.Page 2 p) : RepresentsOnPage E 2 p x x := by
    exact represents_two_self _
  have hadd {r : ℤ} {p : ℤ × ℤ} {x y : E.Page 2 p} {xr yr : E.Page r p}
      (hx : RepresentsOnPage E r p x xr) (hy : RepresentsOnPage E r p y yr) :
      RepresentsOnPage E r p (x+y) (xr+yr) := by
    exact represents_add_tail (by assumption) (by assumption)
  have h221 : HasDifferential E 3 (9,133) (12,135)
      (basis .sphere 9 133 1 + basis .sphere 9 133 2) (basis .sphere 12 135 0) := by
    have hrow := result ⟨.sphere,.equation,3,9,133,[1, 2],12,135,[0],"S0_AdamsE2_ss",2626⟩ (by
      exact List.mem_of_getElem? (i := 221) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 3 (9,133) (12,135) a b at h
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 9 133 [1, 2] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 12 135 [0] = true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [← ha,← hb] at h
    simpa only [add_assoc] using h
  have h222 : HasDifferential E 3 (9,133) (12,135)
      (basis .sphere 9 133 0 + basis .sphere 9 133 2) (basis .sphere 12 135 1 + basis .sphere 12 135 2) := by
    have hrow := result ⟨.sphere,.equation,3,9,133,[0, 2],12,135,[1, 2],"S0_AdamsE2_ss",2627⟩ (by
      exact List.mem_of_getElem? (i := 222) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 3 (9,133) (12,135) a b at h
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 9 133 [0, 2] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 12 135 [1, 2] = true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [← ha,← hb] at h
    simpa only [add_assoc] using h
  have h223 : HasDifferential E 2 (9,133) (11,134)
      (basis .sphere 9 133 2) (basis .sphere 11 134 4) := by
    have hrow := result ⟨.sphere,.equation,2,9,133,[2],11,134,[4],"S0_AdamsE2_ss",2628⟩ (by
      exact List.mem_of_getElem? (i := 223) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 2 (9,133) (11,134) a b at h
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 9 133 [2] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 11 134 [4] = true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [← ha,← hb] at h
    simpa only [add_assoc] using h
  obtain ⟨e,he⟩ := basis_correct ⟨.sphere,9,133,["374,1", "373,1", "0,1,367,1"]⟩ (by
    exact List.mem_of_getElem? (i := 172) (by rfl))
  change E.Page 2 (9,133) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e
  change ∀ i : Fin 3, e.symm (Finsupp.single i 1) = basis .sphere 9 133 i.val at he
  obtain ⟨f,hf⟩ := basis_correct ⟨.sphere,11,134,["387,1", "386,1", "18,1,189,1", "0,1,69,1,80,1", "0,2,366,1"]⟩ (by
    exact List.mem_of_getElem? (i := 190) (by rfl))
  change E.Page 2 (11,134) ≃ₗ[ℤ] (Fin 5 →₀ F2) at f
  change ∀ i : Fin 5, f.symm (Finsupp.single i 1) = basis .sphere 11 134 i.val at hf
  obtain ⟨g,hg⟩ := basis_correct ⟨.sphere,12,135,["408,1", "0,1,386,1", "0,2,69,1,80,1"]⟩ (by
    exact List.mem_of_getElem? (i := 199) (by rfl))
  change E.Page 2 (12,135) ≃ₗ[ℤ] (Fin 3 →₀ F2) at g
  change ∀ i : Fin 3, g.symm (Finsupp.single i 1) = basis .sphere 12 135 i.val at hg
  have e0 : e.symm (Finsupp.single 0 1) = basis .sphere 9 133 0 := he 0
  have e1 : e.symm (Finsupp.single 1 1) = basis .sphere 9 133 1 := he 1
  have e2 : e.symm (Finsupp.single 2 1) = basis .sphere 9 133 2 := he 2
  have f4 : f.symm (Finsupp.single 4 1) = basis .sphere 11 134 4 := hf 4
  have g0 : g.symm (Finsupp.single 0 1) = basis .sphere 12 135 0 := hg 0
  have g1 : g.symm (Finsupp.single 1 1) = basis .sphere 12 135 1 := hg 1
  have g2 : g.symm (Finsupp.single 2 1) = basis .sphere 12 135 2 := hg 2
  have ht2 : basis .sphere 11 134 4 + basis .sphere 11 134 4 = 0 := by
    rw [← f4,← f.symm.map_add,← Finsupp.single_add,show (1:F2)+1=0 from rfl,Finsupp.single_zero,map_zero]
  have he22 : basis .sphere 9 133 2 + basis .sphere 9 133 2 = 0 := by
    rw [← e2,← e.symm.map_add,← Finsupp.single_add,show (1:F2)+1=0 from rfl,Finsupp.single_zero,map_zero]
  have htne : basis .sphere 11 134 4 ≠ 0 := by
    intro h
    have hh := congrArg (fun x => f x 4) h
    rw [← f4,LinearEquiv.apply_symm_apply] at hh
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
  obtain ⟨_,v,a,hv,ha,dv⟩ := h221
  obtain ⟨_,w,b,hw,hb,dw⟩ := h222
  have d2v := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) (hrep2 _) ⟨v,hv⟩
  have d2w := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) (hrep2 _) ⟨w,hw⟩
  have d22 : E.d 2 (9,133) (basis .sphere 9 133 2) = basis .sphere 11 134 4 := by
    obtain ⟨_,hd⟩ := h223.eq_on_page_two
    exact hd
  have d20 : E.d 2 (9,133) (basis .sphere 9 133 0) = basis .sphere 11 134 4 := by
    have hh := congrArg (fun z => z + basis .sphere 11 134 4) d2w
    simpa only [map_add,d22,add_assoc,ht2,add_zero,zero_add] using hh
  have d21 : E.d 2 (9,133) (basis .sphere 9 133 1) = basis .sphere 11 134 4 := by
    have hh := congrArg (fun z => z + basis .sphere 11 134 4) d2v
    simpa only [map_add,d22,add_assoc,ht2,add_zero,zero_add] using hh
  have hker2 (x : E.Page 2 (9,133)) (hx : E.d 2 (9,133) x = 0) :
      x = 0 ∨ x = basis .sphere 9 133 1 + basis .sphere 9 133 2 ∨
      x = basis .sphere 9 133 0 + basis .sphere 9 133 2 ∨
      x = (basis .sphere 9 133 1 + basis .sphere 9 133 2) +
        (basis .sphere 9 133 0 + basis .sphere 9 133 2) := by
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
        _ = (basis .sphere 9 133 0 + basis .sphere 9 133 1) +
          (basis .sphere 9 133 2 + basis .sphere 9 133 2) := by rw [he22,add_zero]
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
    rw [stem124_finite_pages_low124_d2_10] at hu
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
  have hr3 : RepresentsOnPage E 3 (12,135) (basis .sphere 12 135 2) (A.pageπ 1 z1) := by
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
  change E.d 2 (9,133) x = 0 ∨ E.d 2 (9,133) x = basis .sphere 11 134 4
  rcases stem124_finite_pages_f2_three (e x) with h|h|h|h|h|h|h|h
  all_goals have hh := congrArg e.symm h
  all_goals simp only [LinearEquiv.symm_apply_apply,map_zero,map_add,e0,e1,e2] at hh
  all_goals simp only [hh,map_zero,map_add,d20,d21,d22,ht2,zero_add]; tauto


private theorem stem124_finite_pages_s8_d2  :
    (Normalized.sphere).d 2 (8,132) (basis .sphere 8 132 0) =
      basis .sphere 10 133 2 := by
  classical
  let E := Normalized.sphere
  have hrow := result
    ⟨.sphere, .equation, 2, 8, 132, [0], 10, 133, [2], "S0_AdamsE2_ss", 2571⟩ (by
      exact List.mem_of_getElem? (i := 199) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x, hx, y, hy, h⟩ := hrow
  change decode .sphere 8 132 [0] = some x at hx
  change decode .sphere 10 133 [2] = some y at hy
  change HasDifferential E 2 (8,132) (10,133) x y at h
  have hx' : x = basis .sphere 8 132 0 := by
    have hv : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 8 132 [0] = true := by decide
    exact Option.some.inj (hx.symm.trans (by simp [decode, hv]))
  have hy' : y = basis .sphere 10 133 2 := by
    have hv : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 10 133 [2] = true := by decide
    exact Option.some.inj (hy.symm.trans (by simp [decode, hv]))
  have hd : E.d 2 (8,132) (basis .sphere 8 132 0) =
      basis .sphere 10 133 2 := by
    obtain ⟨_, hd⟩ := h.eq_on_page_two
    have hd' : E.d 2 (8,132) x = y := by exact hd
    rw [hx', hy'] at hd'
    exact hd'
  exact hd


private theorem stem124_finite_pages_s8_basis  : ∃ e : (Normalized.sphere).Page 2 (8,132) ≃ₗ[ℤ] (Fin 1 →₀ KIP126.Core.Algebra.F2), ∀i, e.symm (Finsupp.single i 1) = basis .sphere 8 132 i.val := by
  classical
  let E := Normalized.sphere
  obtain ⟨e, he⟩ := basis_correct ⟨.sphere, 8, 132, ["367,1"]⟩ (by
      exact List.mem_of_getElem? (i := 160) (by rfl))
  change E.Page 2 (8,132) ≃ₗ[ℤ] (Fin 1 →₀ KIP126.Core.Algebra.F2) at e
  change ∀ i : Fin 1, e.symm (Finsupp.single i 1) = basis .sphere 8 132 i.val at he
  exact ⟨e,he⟩


private theorem stem124_finite_pages_s10_basis  : ∃ f : (Normalized.sphere).Page 2 (10,133) ≃ₗ[ℤ] (Fin 3 →₀ KIP126.Core.Algebra.F2), ∀i, f.symm (Finsupp.single i 1) = basis .sphere 10 133 i.val := by
  classical
  let E := Normalized.sphere
  obtain ⟨f, hf⟩ := basis_correct ⟨.sphere, 10, 133, ["372,1", "69,1,80,1", "0,1,366,1"]⟩ (by
      exact List.mem_of_getElem? (i := 180) (by rfl))
  change E.Page 2 (10,133) ≃ₗ[ℤ] (Fin 3 →₀ KIP126.Core.Algebra.F2) at f
  change ∀ i : Fin 3, f.symm (Finsupp.single i 1) = basis .sphere 10 133 i.val at hf
  exact ⟨f,hf⟩


private theorem stem124_finite_pages_low124_af8_three  : Subsingleton ((Normalized.sphere).Page 3 (8,132)) := by
  classical
  let E := Normalized.sphere
  have hd := stem124_finite_pages_s8_d2
  obtain ⟨e, he⟩ := stem124_finite_pages_s8_basis
  obtain ⟨f,hf⟩ := stem124_finite_pages_s10_basis
  have hf2 : f.symm (Finsupp.single 2 1) = basis .sphere 10 133 2 := hf 2
  have he0 : e.symm (Finsupp.single 0 1) = basis .sphere 8 132 0 := he 0
  have hn : basis .sphere 10 133 2 ≠ 0 := by
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


private theorem stem124_finite_pages_low124_s7_four  :
    ∃ b : (Normalized.sphere).Page 4 (7,131),
      RepresentsOnPage (Normalized.sphere) 4 (7,131) (basis .sphere 7 131 1) b ∧
      (∀ a : (Normalized.sphere).Page 4 (7,131), a=0 ∨ a=b) ∧
      (Normalized.sphere).d 4 (7,131) = 0 := by
  classical
  let E := Normalized.sphere
  have h163 : HasDifferential E 2 (5,130) (7,131)
      (basis .sphere 5 130 0) (basis .sphere 7 131 2) := by
    have hrow := result ⟨.sphere,.equation,2,5,130,[0],7,131,[2],"S0_AdamsE2_ss",2435⟩ (by
      exact List.mem_of_getElem? (i := 163) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 2 (5,130) (7,131) a b at h
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 5 130 [0] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 7 131 [2] = true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [← ha,← hb] at h
    simpa only [add_assoc] using h
  have h182 : HasDifferential E 5 (7,131) (12,135)
      (basis .sphere 7 131 1) (basis .sphere 12 135 2) := by
    have hrow := result ⟨.sphere,.equation,5,7,131,[1],12,135,[2],"S0_AdamsE2_ss",2490⟩ (by
      exact List.mem_of_getElem? (i := 182) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 5 (7,131) (12,135) a b at h
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 7 131 [1] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 12 135 [2] = true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [← ha,← hb] at h
    simpa only [add_assoc] using h
  have h183 : HasDifferential E 3 (7,131) (10,133)
      (basis .sphere 7 131 0) (basis .sphere 10 133 0 + basis .sphere 10 133 1) := by
    have hrow := result ⟨.sphere,.equation,3,7,131,[0],10,133,[0, 1],"S0_AdamsE2_ss",2491⟩ (by
      exact List.mem_of_getElem? (i := 183) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 3 (7,131) (10,133) a b at h
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 7 131 [0] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 10 133 [0, 1] = true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [← ha,← hb] at h
    simpa only [add_assoc] using h
  obtain ⟨e,he⟩ := basis_correct ⟨.sphere,7,131,["353,1", "69,1,75,1", "0,1,339,1"]⟩ (by
    exact List.mem_of_getElem? (i := 148) (by rfl))
  change E.Page 2 (7,131) ≃ₗ[ℤ] (Fin 3 →₀ KIP126.Core.Algebra.F2) at e
  change ∀ i : Fin 3, e.symm (Finsupp.single i 1) = basis .sphere 7 131 i.val at he
  obtain ⟨f,hf⟩ := stem124_finite_pages_s8_basis
  obtain ⟨g,hg⟩ := stem124_finite_pages_s10_basis
  have g0 : g.symm (Finsupp.single 0 1) = basis .sphere 10 133 0 := hg 0
  have g1 : g.symm (Finsupp.single 1 1) = basis .sphere 10 133 1 := hg 1
  have g2 : g.symm (Finsupp.single 2 1) = basis .sphere 10 133 2 := hg 2
  obtain ⟨_,a,c,ha,hc,hd⟩ := h183
  obtain ⟨_,b5,z5,hb5,hz5,hd5⟩ := h182
  obtain ⟨b,hb⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤5) hb5
  have htzero : RepresentsOnPage E 3 (7,131) (basis .sphere 7 131 2) 0 :=
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
    · simp only [show (⟨0,by decide⟩ : KIP126.Core.Algebra.F2)=0 from rfl,Finsupp.single_zero,map_zero] at hu
      have hh := congrArg (fun q => g q 0) hu
      rw [← g0,← g1,map_add,LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change E.d 2 (8,132) (f.symm (Finsupp.single 0 1)) = _ at hu
      have f0 : f.symm (Finsupp.single 0 1) = basis .sphere 8 132 0 := hf 0
      have hs8 : E.d 2 (8,132) (basis .sphere 8 132 0) = basis .sphere 10 133 2 := stem124_finite_pages_s8_d2
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
  have hz3 : RepresentsOnPage E 3 (7,131) (basis .sphere 7 131 1)
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


private theorem stem124_finite_pages_low124_s7_six
    (h8 : Subsingleton ((Normalized.sphere).Page 4 (8,132)))
    (htarget : ∀ y : (Normalized.sphere).Page 4 (12,135),
      RepresentsOnPage (Normalized.sphere) 4 (12,135) (basis .sphere 12 135 2) y → y ≠ 0) :
    Subsingleton ((Normalized.sphere).Page 6 (7,131)) := by
  classical
  let E := Normalized.sphere
  obtain ⟨b4,hb4,frame4,hd4⟩ := stem124_finite_pages_low124_s7_four
  have h182 : HasDifferential E 5 (7,131) (12,135)
      (basis .sphere 7 131 1) (basis .sphere 12 135 2) := by
    have hrow := result ⟨.sphere,.equation,5,7,131,[1],12,135,[2],"S0_AdamsE2_ss",2490⟩ (by
      exact List.mem_of_getElem? (i := 182) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 5 (7,131) (12,135) a b at h
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 7 131 [1] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 12 135 [2] = true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
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
  have hz4 : RepresentsOnPage E 4 (7,131) (basis .sphere 7 131 1)
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


private theorem stem124_finite_pages_low124_af6_six
    (h74 : (Normalized.sphere).d 4 (7,131) = 0) : Subsingleton ((Normalized.sphere).Page 6 (6,130)) := by
  classical
  let E := Normalized.sphere
  have hrow := result ⟨.sphere,.equation,5,6,130,[0],11,134,[2],"S0_AdamsE2_ss",2434⟩ (by
    exact List.mem_of_getElem? (i := 170) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,h⟩ := hrow
  change HasDifferential E 5 (6,130) (11,134) x y at h
  have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 6 130 [0] = true := rfl
  have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 11 134 [2] = true := rfl
  simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [← hx,← hy] at h
  obtain ⟨_,x5,y5,hx5,hy5,hd5⟩ := h
  obtain ⟨e,he⟩ := basis_correct ⟨.sphere,6,130,["339,1"]⟩ (by
    exact List.mem_of_getElem? (i := 136) (by rfl))
  change E.Page 2 (6,130) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e
  change ∀ i : Fin 1, e.symm (Finsupp.single i 1) = basis .sphere 6 130 i.val at he
  obtain ⟨f,hf⟩ := basis_correct ⟨.sphere,11,134,["387,1", "386,1", "18,1,189,1", "0,1,69,1,80,1", "0,2,366,1"]⟩ (by
    exact List.mem_of_getElem? (i := 190) (by rfl))
  change E.Page 2 (11,134) ≃ₗ[ℤ] (Fin 5 →₀ F2) at f
  change ∀ i : Fin 5, f.symm (Finsupp.single i 1) = basis .sphere 11 134 i.val at hf
  have f2 : f.symm (Finsupp.single 2 1) = basis .sphere 11 134 2 := hf 2
  have f4 : f.symm (Finsupp.single 4 1) = basis .sphere 11 134 4 := hf 4
  have target3 (z3 : E.Page 3 (11,134))
      (h3 : RepresentsOnPage E 3 (11,134) (basis .sphere 11 134 2) z3) : z3 ≠ 0 := by
    intro hz3
    obtain ⟨_,z,hz,hzp⟩ := h3
    have hi := (next_projection_zero_iff_incoming E 2 (by change (2:ℤ)≤2; omega) (9,133) z).mp (hzp.trans hz3)
    change ∃ u, E.d 2 (9,133) u = (Subobject.ofLE _ _ ((E.ssData (11,134)).Z_anti bot_le) ≫ (E.ssData (11,134)).pageπ 0) z at hi
    obtain ⟨u,hu⟩ := hi
    have hlabel : E.d 2 (9,133) u = basis .sphere 11 134 2 := hu.trans hz
    rcases (stem124_finite_pages_low124_af9_four).2.2 u with hu0|hu4
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
    rw [(stem124_finite_pages_low124_af8_three).elim z 0,map_zero]
  have hy4ne := represents_next_nonzero_of_incoming_zero (by change (2:ℤ)≤3; omega)
    (by decide : (2:ℤ)≤3) hin3 hy4 hy3 (target3 y3 hy3)
  have hin4 : E.d 4 ((11,134)-E.diffDeg 4) = 0 := h74
  have hy5ne := represents_next_nonzero_of_incoming_zero (by change (2:ℤ)≤4; omega)
    (by decide : (2:ℤ)≤4) hin4 hy5 hy4 hy4ne
  have he0 : e.symm (Finsupp.single 0 1) = basis .sphere 6 130 0 := he 0
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
 :
    Subsingleton ((Normalized.sphere).Page 6 (6,130)) ∧
    Subsingleton ((Normalized.sphere).Page 6 (7,131)) ∧
    Subsingleton ((Normalized.sphere).Page 3 (8,132)) ∧
    Subsingleton ((Normalized.sphere).Page 4 (9,133)) := by
  classical
  classical
  obtain ⟨b,hb,hcases,h74⟩ := stem124_finite_pages_low124_s7_four
  have h8 := stem124_finite_pages_low124_af8_three
  have h9 := stem124_finite_pages_low124_af9_four
  have h8four := page_subsingleton_of_le 3 4 8 132
    (by omega) (by omega) h8
  exact ⟨stem124_finite_pages_low124_af6_six h74, stem124_finite_pages_low124_s7_six h8four h9.2.1, h8, h9.1⟩


end
end KIP126.Main.Internal.Selected
