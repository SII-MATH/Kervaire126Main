module
public import KIP126.Main.SectionSeven.AlphaOne
import all KIP126.Main.Internal.Selected.NormalizedFacts
import all KIP126.Main.Internal.PageCalculus
import all KIP126.Main.Internal.QuotientCalculus
import all KIP126.Main.Internal.AlphaOne.Quotients

/-! Full finite three-layer frames, AlphaOne/Existence.lean:58–873,
pinned bbac1fc05843 (MIT); same finite rows and complete bases. -/
@[expose] section
namespace KIP126.Main.Internal.AlphaOne
open CategoryTheory CategoryTheory.Limits KIP126.Core.Algebra
open KIP126.Core.SpectralSequence KIP126.Core.SpectralSequence.FinitePageCalculus
open KIP126.Main.Internal KIP126.Main.Internal.Selected
open KIP126.Computation.Table
open KIP126.AdamsSynthetic.Standard (model)
noncomputable section
universe v
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
private theorem alpha_all_finite_frames_d2_s14_t138_basis1  : HasDifferential (Normalized.sphere) 2 (14,138) (16,139)
    (Normalized.basis .sphere 14 138 1) (Normalized.basis .sphere 16 139 1 + Normalized.basis .sphere 16 139 2) := by
  classical
  have hrow := Normalized.result ⟨.sphere,.equation,2,14,138,[1],16,139,[1, 2],"S0_AdamsE2_ss",3072⟩ (by
    exact List.mem_of_getElem? (i := 366) (by rfl))
  dsimp only [Normalized.Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (Normalized.sphere) 2 (14,138) (16,139) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 14 138 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 16 139 [1, 2] = true := rfl
  simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem alpha_all_finite_frames_d2_s14_t138_basis0_add_basis1  : HasDifferential (Normalized.sphere) 2 (14,138) (16,139)
    (Normalized.basis .sphere 14 138 0 + Normalized.basis .sphere 14 138 1) (Normalized.basis .sphere 16 139 2) := by
  classical
  have hrow := Normalized.result ⟨.sphere,.equation,2,14,138,[0, 1],16,139,[2],"S0_AdamsE2_ss",3073⟩ (by
    exact List.mem_of_getElem? (i := 367) (by rfl))
  dsimp only [Normalized.Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (Normalized.sphere) 2 (14,138) (16,139) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 14 138 [0, 1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 16 139 [2] = true := rfl
  simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem alpha_all_finite_frames_d2_s12_t137_basis1  : HasDifferential (Normalized.sphere) 2 (12,137) (14,138)
    (Normalized.basis .sphere 12 137 1) (Normalized.basis .sphere 14 138 4) := by
  classical
  have hrow := Normalized.result ⟨.sphere,.equation,2,12,137,[1],14,138,[4],"S0_AdamsE2_ss",2921⟩ (by
    exact List.mem_of_getElem? (i := 308) (by rfl))
  dsimp only [Normalized.Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (Normalized.sphere) 2 (12,137) (14,138) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 12 137 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 14 138 [4] = true := rfl
  simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem alpha_all_finite_frames_d2_s12_t137_basis0  : HasDifferential (Normalized.sphere) 2 (12,137) (14,138)
    (Normalized.basis .sphere 12 137 0) (Normalized.basis .sphere 14 138 3) := by
  classical
  have hrow := Normalized.result ⟨.sphere,.equation,2,12,137,[0],14,138,[3],"S0_AdamsE2_ss",2922⟩ (by
    exact List.mem_of_getElem? (i := 309) (by rfl))
  dsimp only [Normalized.Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (Normalized.sphere) 2 (12,137) (14,138) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 12 137 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 14 138 [3] = true := rfl
  simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem alpha_all_finite_frames_d2_s15_t139_basis3  : HasDifferential (Normalized.sphere) 2 (15,139) (17,140)
    (Normalized.basis .sphere 15 139 3) (Normalized.basis .sphere 17 140 2 + Normalized.basis .sphere 17 140 3) := by
  classical
  have hrow := Normalized.result ⟨.sphere,.equation,2,15,139,[3],17,140,[2, 3],"S0_AdamsE2_ss",3141⟩ (by
    exact List.mem_of_getElem? (i := 382) (by rfl))
  dsimp only [Normalized.Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (Normalized.sphere) 2 (15,139) (17,140) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 15 139 [3] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 17 140 [2, 3] = true := rfl
  simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem alpha_all_finite_frames_d2_s15_t139_basis2_add_basis3  : HasDifferential (Normalized.sphere) 2 (15,139) (17,140)
    (Normalized.basis .sphere 15 139 2 + Normalized.basis .sphere 15 139 3) (Normalized.basis .sphere 17 140 3) := by
  classical
  have hrow := Normalized.result ⟨.sphere,.equation,2,15,139,[2, 3],17,140,[3],"S0_AdamsE2_ss",3142⟩ (by
    exact List.mem_of_getElem? (i := 383) (by rfl))
  dsimp only [Normalized.Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (Normalized.sphere) 2 (15,139) (17,140) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 15 139 [2, 3] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 17 140 [3] = true := rfl
  simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem alpha_all_finite_frames_d4_s11_t136_basis0  : HasDifferential (Normalized.sphere) 4 (11,136) (15,139)
    (Normalized.basis .sphere 11 136 0) (Normalized.basis .sphere 15 139 0) := by
  classical
  have hrow := Normalized.result ⟨.sphere,.equation,4,11,136,[0],15,139,[0],"S0_AdamsE2_ss",2853⟩ (by
    exact List.mem_of_getElem? (i := 282) (by rfl))
  dsimp only [Normalized.Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (Normalized.sphere) 4 (11,136) (15,139) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 11 136 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 15 139 [0] = true := rfl
  simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem alpha_all_finite_frames_d2_s11_t136_basis4  : HasDifferential (Normalized.sphere) 2 (11,136) (13,137)
    (Normalized.basis .sphere 11 136 4) (Normalized.basis .sphere 13 137 3) := by
  classical
  have hrow := Normalized.result ⟨.sphere,.equation,2,11,136,[4],13,137,[3],"S0_AdamsE2_ss",2914⟩ (by
    exact List.mem_of_getElem? (i := 321) (by rfl))
  dsimp only [Normalized.Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (Normalized.sphere) 2 (11,136) (13,137) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 11 136 [4] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 13 137 [3] = true := rfl
  simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  exact h

private theorem alpha_all_finite_frames_d3_s10_t135_basis0  : HasDifferential (Normalized.sphere) 3 (10,135) (13,137)
    (Normalized.basis .sphere 10 135 0) (Normalized.basis .sphere 13 137 0) := by
  classical
  have hrow := Normalized.result ⟨.sphere,.equation,3,10,135,[0],13,137,[0],"S0_AdamsE2_ss",2915⟩ (by
    exact List.mem_of_getElem? (i := 322) (by rfl))
  dsimp only [Normalized.Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (Normalized.sphere) 3 (10,135) (13,137) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 135 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 13 137 [0] = true := rfl
  simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  exact h

private theorem alpha_all_finite_frames_boundary_of_zero_representative
    {r : ℤ} {p : ℤ×ℤ} {x : Normalized.sphere.Page 2 p}
    (hx : RepresentsOnPage (Normalized.sphere) r p x 0) :
    x ∈ boundaries (r-1) p := by
  classical
  let E := Normalized.sphere
  let P := E.ssData p
  obtain ⟨hr,z,hz,hzero⟩ := hx
  change (Subobject.ofLE (P.Z ↑(r-2).toNat) (P.Z 0) _ ≫ P.pageπ 0) z=x at hz
  change P.pageπ ↑(r-2).toNat z=0 at hzero
  obtain ⟨y,hy⟩ := (cokernel_π_eq_zero_iff_mem_range
    (Subobject.ofLE (P.B ↑(r-2).toNat) (P.Z ↑(r-2).toNat) (P.B_le_Z _)) z).mp hzero
  have hrindex : r-1-1=r-2 := by omega
  change ∃ y, boundaryMap ↑(r-1-1).toNat p y=x
  rw [hrindex]
  refine ⟨y,?_⟩
  have hf : Subobject.ofLE (P.B ↑(r-2).toNat) (P.Z ↑(r-2).toNat) (P.B_le_Z _) ≫
      cycleMap ↑(r-2).toNat p = boundaryMap ↑(r-2).toNat p := by
    dsimp only [boundaryMap,boundaryMapFor,cycleMap,cycleMapFor,P,E]
    rw [←Category.assoc,Subobject.ofLE_comp_ofLE]
  rw [←hf,CategoryTheory.comp_apply,hy]
  exact hz


private theorem alpha_all_finite_frames_cycle_differential_zero
    {r c : ℤ} {p : ℤ×ℤ} {x : Normalized.sphere.Page 2 p}
    {a : (Normalized.sphere).Page r p}
    (hr : 2≤r) (hc : r≤c)
    (hx : x∈cycles c p)
    (ha : RepresentsOnPage (Normalized.sphere) r p x a) :
    (Normalized.sphere).d r p a=0 := by
  classical
  obtain ⟨y,hy⟩ := (cycles_reaches c p (by omega) x).mp hx
  exact represents_d_zero_of_later hr (by omega : r<c+1) ha ⟨y,hy⟩


private theorem alpha_all_finite_frames_cycle_quotient_frame_of_boundary
    {c b : ℤ} {p : ℤ×ℤ} (v : Normalized.sphere.Page 2 (p.1,p.2))
    (hv : v∈cycles c p)
    (h : ∀ z, z∈cycles c p → z∈boundaries b p ∨ z-v∈boundaries b p) :
    ∀ q : CycleQuotient c b p,
      q=0 ∨ q=KIP126.Literature.subquotientClass _ _ ⟨v,hv⟩ := by
  classical
  rintro ⟨z⟩
  rcases h z.val z.property with hz|hz
  · exact Or.inl ((subquotientClass_eq_zero_iff _ _ z).mpr hz)
  · right
    apply sub_eq_zero.mp
    change KIP126.Literature.subquotientClass _ _ z-KIP126.Literature.subquotientClass _ _ ⟨v,hv⟩=0
    rw [←map_sub]
    exact (subquotientClass_eq_zero_iff _ _ (z-⟨v,hv⟩)).mpr hz


private theorem alpha_all_finite_frames_rep_two (p : ℤ×ℤ) (x : (Normalized.sphere).Page 2 p) :
    RepresentsOnPage (Normalized.sphere) 2 p x x := by
  classical
  let E := Normalized.sphere
  haveI : Epi ((E.ssData p).pageπ 0) := inferInstanceAs (Epi (cokernel.π _))
  obtain ⟨z,rfl⟩ := (ModuleCat.epi_iff_surjective ((E.ssData p).pageπ 0)).mp inferInstance x
  exact ⟨by decide,z,by simp only [Subobject.ofLE_refl,Category.id_comp]; rfl,rfl⟩


private theorem alpha_all_finite_frames_alpha_finite_frame_14
    (hc : (Normalized.basis .sphere 14 138 2)∈cycles 4 (14,138)) :
    ∀ q : CycleQuotient 4 8 (14,138),
      q=0 ∨ q=KIP126.Literature.subquotientClass _ _ ⟨(Normalized.basis .sphere 14 138 2),hc⟩ := by
  classical
  let E := Normalized.sphere
  have h366 : HasDifferential E 2 (14,138) (16,139)
      (Normalized.basis .sphere 14 138 1) (Normalized.basis .sphere 16 139 1 + Normalized.basis .sphere 16 139 2) := alpha_all_finite_frames_d2_s14_t138_basis1
  have h367 : HasDifferential E 2 (14,138) (16,139)
      (Normalized.basis .sphere 14 138 0 + Normalized.basis .sphere 14 138 1) (Normalized.basis .sphere 16 139 2) := alpha_all_finite_frames_d2_s14_t138_basis0_add_basis1
  have h308 : HasDifferential E 2 (12,137) (14,138)
      (Normalized.basis .sphere 12 137 1) (Normalized.basis .sphere 14 138 4) := alpha_all_finite_frames_d2_s12_t137_basis1
  have h309 : HasDifferential E 2 (12,137) (14,138)
      (Normalized.basis .sphere 12 137 0) (Normalized.basis .sphere 14 138 3) := alpha_all_finite_frames_d2_s12_t137_basis0
  obtain ⟨e,he⟩ := Normalized.basis_correct ⟨.sphere,14,138,["440,1", "439,1", "23,1,190,1", "1,1,418,1", "1,1,417,1"]⟩ (by
    exact List.mem_of_getElem? (i := 216) (by rfl))
  change E.Page 2 (14,138) ≃ₗ[ℤ] (Fin 5 →₀ F2) at e
  change ∀ i : Fin 5, e.symm (Finsupp.single i 1) = Normalized.basis .sphere 14 138 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 5) 1) = Normalized.basis .sphere 14 138 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 5) 1) = Normalized.basis .sphere 14 138 1 := he 1
  have he2 : e.symm (Finsupp.single (2:Fin 5) 1) = Normalized.basis .sphere 14 138 2 := he 2
  have he3 : e.symm (Finsupp.single (3:Fin 5) 1) = Normalized.basis .sphere 14 138 3 := he 3
  have he4 : e.symm (Finsupp.single (4:Fin 5) 1) = Normalized.basis .sphere 14 138 4 := he 4
  obtain ⟨f,hf⟩ := Normalized.basis_correct ⟨.sphere,16,139,["1,1,424,1", "0,1,438,1", "0,3,418,1"]⟩ (by
    exact List.mem_of_getElem? (i := 230) (by rfl))
  change E.Page 2 (16,139) ≃ₗ[ℤ] (Fin 3 →₀ F2) at f
  change ∀ i : Fin 3, f.symm (Finsupp.single i 1) = Normalized.basis .sphere 16 139 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 3) 1) = Normalized.basis .sphere 16 139 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 3) 1) = Normalized.basis .sphere 16 139 1 := hf 1
  have hf2 : f.symm (Finsupp.single (2:Fin 3) 1) = Normalized.basis .sphere 16 139 2 := hf 2
  let B := boundaries 8 (14,138)
  have b3 : Normalized.basis .sphere 14 138 3∈B := by
    exact alpha_all_finite_frames_boundary_of_zero_representative (r:=9) (p:=(14,138))
      (differential_target_later_zero (E:=E) (by change (2:ℤ)≤2;omega) (by decide) h309)
  have hd3 : E.d 2 (14,138) (Normalized.basis .sphere 14 138 3)=0 :=
    alpha_all_finite_frames_cycle_differential_zero (r:=2) (c:=4) (p:=(14,138)) (by decide) (by decide)
      (boundaries_le_cycles (14,138) 8 4 b3) (alpha_all_finite_frames_rep_two (14,138) _)
  have b4 : Normalized.basis .sphere 14 138 4∈B := by
    exact alpha_all_finite_frames_boundary_of_zero_representative (r:=9) (p:=(14,138))
      (differential_target_later_zero (E:=E) (by change (2:ℤ)≤2;omega) (by decide) h308)
  have hd4 : E.d 2 (14,138) (Normalized.basis .sphere 14 138 4)=0 :=
    alpha_all_finite_frames_cycle_differential_zero (r:=2) (c:=4) (p:=(14,138)) (by decide) (by decide)
      (boundaries_le_cycles (14,138) 8 4 b4) (alpha_all_finite_frames_rep_two (14,138) _)
  have hd2 : E.d 2 (14,138) (Normalized.basis .sphere 14 138 2)=0 :=
    alpha_all_finite_frames_cycle_differential_zero (r:=2) (c:=4) (p:=(14,138)) (by decide) (by decide) hc (alpha_all_finite_frames_rep_two (14,138) _)
  have hd1 : E.d 2 (14,138) (Normalized.basis .sphere 14 138 1)=Normalized.basis .sphere 16 139 1+Normalized.basis .sphere 16 139 2 := h366.eq_on_page_two.2
  have hd0 : E.d 2 (14,138) (Normalized.basis .sphere 14 138 0)=-Normalized.basis .sphere 16 139 1 := by
    have hh := h367.eq_on_page_two.2
    change E.d 2 (14,138) (Normalized.basis .sphere 14 138 0+Normalized.basis .sphere 14 138 1)=Normalized.basis .sphere 16 139 2 at hh
    rw [map_add,hd1] at hh
    have haux : ((show E.Page 2 (16,139) from E.d 2 (14,138) (Normalized.basis .sphere 14 138 0))+Normalized.basis .sphere 16 139 1)+Normalized.basis .sphere 16 139 2=0+Normalized.basis .sphere 16 139 2 := by
      simpa only [add_assoc,zero_add] using hh
    exact eq_neg_of_add_eq_zero_left (add_right_cancel haux)
  apply alpha_all_finite_frames_cycle_quotient_frame_of_boundary _ hc
  intro x hx
  have hd : E.d 2 (14,138) x=0 := alpha_all_finite_frames_cycle_differential_zero (r:=2) (c:=4) (p:=(14,138)) (by decide) (by decide) hx (alpha_all_finite_frames_rep_two (14,138) x)
  have heq : e x=Finsupp.single 0 (e x 0) + Finsupp.single 1 (e x 1) + Finsupp.single 2 (e x 2) + Finsupp.single 3 (e x 3) + Finsupp.single 4 (e x 4) := by
    ext i
    fin_cases i <;> simp
  have hxe : x=e.symm (Finsupp.single 0 (e x 0) + Finsupp.single 1 (e x 1) + Finsupp.single 2 (e x 2) + Finsupp.single 3 (e x 3) + Finsupp.single 4 (e x 4)) := by rw [←heq,LinearEquiv.symm_apply_apply]
  generalize hc0 : e x 0=c0 at hxe
  generalize hc1 : e x 1=c1 at hxe
  generalize hc2 : e x 2=c2 at hxe
  generalize hc3 : e x 3=c3 at hxe
  generalize hc4 : e x 4=c4 at hxe
  fin_cases c0 <;> fin_cases c1 <;> fin_cases c2 <;> fin_cases c3 <;> fin_cases c4
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
    simp only [Finsupp.single_zero,map_zero,add_zero] at hxe
    left
    rw [hxe]
    exact B.zero_mem
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
    simp only [Finsupp.single_zero,he4,add_zero,zero_add] at hxe
    left
    rw [hxe]
    exact b4
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
    simp only [Finsupp.single_zero,he3,add_zero,zero_add] at hxe
    left
    rw [hxe]
    exact b3
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,he3,he4,add_zero,zero_add] at hxe
    left
    rw [hxe]
    exact B.add_mem b3 b4
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
    simp only [Finsupp.single_zero,he2,add_zero,zero_add] at hxe
    right
    rw [hxe]
    have hcanc : ((Normalized.basis .sphere 14 138 2)-(Normalized.basis .sphere 14 138 2) : E.Page 2 (14,138))=0 := by abel
    rw [hcanc]
    exact B.zero_mem
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,he2,he4,add_zero,zero_add] at hxe
    right
    rw [hxe]
    have hcanc : ((Normalized.basis .sphere 14 138 2 + Normalized.basis .sphere 14 138 4)-(Normalized.basis .sphere 14 138 2) : E.Page 2 (14,138))=Normalized.basis .sphere 14 138 4 := by abel
    rw [hcanc]
    exact b4
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,he2,he3,add_zero,zero_add] at hxe
    right
    rw [hxe]
    have hcanc : ((Normalized.basis .sphere 14 138 2 + Normalized.basis .sphere 14 138 3)-(Normalized.basis .sphere 14 138 2) : E.Page 2 (14,138))=Normalized.basis .sphere 14 138 3 := by abel
    rw [hcanc]
    exact b3
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,he2,he3,he4,add_zero,zero_add] at hxe
    right
    rw [hxe]
    have hcanc : ((Normalized.basis .sphere 14 138 2 + Normalized.basis .sphere 14 138 3 + Normalized.basis .sphere 14 138 4)-(Normalized.basis .sphere 14 138 2) : E.Page 2 (14,138))=Normalized.basis .sphere 14 138 3 + Normalized.basis .sphere 14 138 4 := by abel
    rw [hcanc]
    exact B.add_mem b3 b4
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
    simp only [Finsupp.single_zero,he1,add_zero,zero_add] at hxe
    exfalso
    rw [hxe] at hd
    simp only [hd1] at hd
    have hh := congrArg (fun z=>f z 2) hd
    norm_num [map_add,map_neg,map_zero,←hf0,←hf1,←hf2,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.neg_apply,Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,he1,he4,add_zero,zero_add] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd1,hd4,add_zero] at hd
    have hh := congrArg (fun z=>f z 2) hd
    norm_num [map_add,map_neg,map_zero,←hf0,←hf1,←hf2,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.neg_apply,Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,he1,he3,add_zero,zero_add] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd1,hd3,add_zero] at hd
    have hh := congrArg (fun z=>f z 2) hd
    norm_num [map_add,map_neg,map_zero,←hf0,←hf1,←hf2,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.neg_apply,Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,he1,he3,he4,add_zero,zero_add] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd1,hd3,hd4,add_zero] at hd
    have hh := congrArg (fun z=>f z 2) hd
    norm_num [map_add,map_neg,map_zero,←hf0,←hf1,←hf2,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.neg_apply,Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,he1,he2,add_zero,zero_add] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd1,hd2,add_zero] at hd
    have hh := congrArg (fun z=>f z 2) hd
    norm_num [map_add,map_neg,map_zero,←hf0,←hf1,←hf2,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.neg_apply,Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,he1,he2,he4,add_zero,zero_add] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd1,hd2,hd4,add_zero] at hd
    have hh := congrArg (fun z=>f z 2) hd
    norm_num [map_add,map_neg,map_zero,←hf0,←hf1,←hf2,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.neg_apply,Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,he1,he2,he3,add_zero,zero_add] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd1,hd2,hd3,add_zero] at hd
    have hh := congrArg (fun z=>f z 2) hd
    norm_num [map_add,map_neg,map_zero,←hf0,←hf1,←hf2,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.neg_apply,Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,he1,he2,he3,he4,zero_add] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd1,hd2,hd3,hd4,add_zero] at hd
    have hh := congrArg (fun z=>f z 2) hd
    norm_num [map_add,map_neg,map_zero,←hf0,←hf1,←hf2,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.neg_apply,Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
    simp only [Finsupp.single_zero,he0,add_zero] at hxe
    exfalso
    rw [hxe] at hd
    simp only [hd0] at hd
    have hh := congrArg (fun z=>f z 1) hd
    norm_num [map_add,map_neg,map_zero,←hf0,←hf1,←hf2,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.neg_apply,Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,he0,he4,add_zero] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd0,hd4,add_zero] at hd
    have hh := congrArg (fun z=>f z 1) hd
    norm_num [map_add,map_neg,map_zero,←hf0,←hf1,←hf2,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.neg_apply,Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,he0,he3,add_zero] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd0,hd3,add_zero] at hd
    have hh := congrArg (fun z=>f z 1) hd
    norm_num [map_add,map_neg,map_zero,←hf0,←hf1,←hf2,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.neg_apply,Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,he0,he3,he4,add_zero] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd0,hd3,hd4,add_zero] at hd
    have hh := congrArg (fun z=>f z 1) hd
    norm_num [map_add,map_neg,map_zero,←hf0,←hf1,←hf2,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.neg_apply,Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,he0,he2,add_zero] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd0,hd2,add_zero] at hd
    have hh := congrArg (fun z=>f z 1) hd
    norm_num [map_add,map_neg,map_zero,←hf0,←hf1,←hf2,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.neg_apply,Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,he0,he2,he4,add_zero] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd0,hd2,hd4,add_zero] at hd
    have hh := congrArg (fun z=>f z 1) hd
    norm_num [map_add,map_neg,map_zero,←hf0,←hf1,←hf2,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.neg_apply,Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,he0,he2,he3,add_zero] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd0,hd2,hd3,add_zero] at hd
    have hh := congrArg (fun z=>f z 1) hd
    norm_num [map_add,map_neg,map_zero,←hf0,←hf1,←hf2,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.neg_apply,Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,he0,he2,he3,he4,add_zero] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd0,hd2,hd3,hd4,add_zero] at hd
    have hh := congrArg (fun z=>f z 1) hd
    norm_num [map_add,map_neg,map_zero,←hf0,←hf1,←hf2,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.neg_apply,Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,he0,he1,add_zero] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd0,hd1] at hd
    have hh := congrArg (fun z=>f z 2) hd
    norm_num [map_add,map_neg,map_zero,←hf0,←hf1,←hf2,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.neg_apply,Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,he0,he1,he4,add_zero] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd0,hd1,hd4,add_zero] at hd
    have hh := congrArg (fun z=>f z 2) hd
    norm_num [map_add,map_neg,map_zero,←hf0,←hf1,←hf2,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.neg_apply,Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,he0,he1,he3,add_zero] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd0,hd1,hd3,add_zero] at hd
    have hh := congrArg (fun z=>f z 2) hd
    norm_num [map_add,map_neg,map_zero,←hf0,←hf1,←hf2,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.neg_apply,Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,he0,he1,he3,he4,add_zero] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd0,hd1,hd3,hd4,add_zero] at hd
    have hh := congrArg (fun z=>f z 2) hd
    norm_num [map_add,map_neg,map_zero,←hf0,←hf1,←hf2,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.neg_apply,Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,he0,he1,he2,add_zero] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd0,hd1,hd2,add_zero] at hd
    have hh := congrArg (fun z=>f z 2) hd
    norm_num [map_add,map_neg,map_zero,←hf0,←hf1,←hf2,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.neg_apply,Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,he0,he1,he2,he4,add_zero] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd0,hd1,hd2,hd4,add_zero] at hd
    have hh := congrArg (fun z=>f z 2) hd
    norm_num [map_add,map_neg,map_zero,←hf0,←hf1,←hf2,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.neg_apply,Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,he0,he1,he2,he3,add_zero] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd0,hd1,hd2,hd3,add_zero] at hd
    have hh := congrArg (fun z=>f z 2) hd
    norm_num [map_add,map_neg,map_zero,←hf0,←hf1,←hf2,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.neg_apply,Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
    simp only [map_add,he0,he1,he2,he3,he4] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd0,hd1,hd2,hd3,hd4,add_zero] at hd
    have hh := congrArg (fun z=>f z 2) hd
    norm_num [map_add,map_neg,map_zero,←hf0,←hf1,←hf2,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.neg_apply,Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff] at hh


private theorem alpha_all_finite_frames_alpha_finite_frame_15
    (hc : (Normalized.basis .sphere 15 139 1 + Normalized.basis .sphere 15 139 3)∈cycles 3 (15,139)) :
    ∀ q : CycleQuotient 3 9 (15,139),
      q=0 ∨ q=KIP126.Literature.subquotientClass _ _ ⟨(Normalized.basis .sphere 15 139 1 + Normalized.basis .sphere 15 139 3),hc⟩ := by
  classical
  let E := Normalized.sphere
  have h382 : HasDifferential E 2 (15,139) (17,140)
      (Normalized.basis .sphere 15 139 3) (Normalized.basis .sphere 17 140 2 + Normalized.basis .sphere 17 140 3) := alpha_all_finite_frames_d2_s15_t139_basis3
  have h383 : HasDifferential E 2 (15,139) (17,140)
      (Normalized.basis .sphere 15 139 2 + Normalized.basis .sphere 15 139 3) (Normalized.basis .sphere 17 140 3) := alpha_all_finite_frames_d2_s15_t139_basis2_add_basis3
  have h282 : HasDifferential E 4 (11,136) (15,139)
      (Normalized.basis .sphere 11 136 0) (Normalized.basis .sphere 15 139 0) := alpha_all_finite_frames_d4_s11_t136_basis0
  obtain ⟨e,he⟩ := Normalized.basis_correct ⟨.sphere,15,139,["448,1", "3,2,287,1", "0,1,440,1", "0,1,439,1"]⟩ (by
    exact List.mem_of_getElem? (i := 223) (by rfl))
  change E.Page 2 (15,139) ≃ₗ[ℤ] (Fin 4 →₀ F2) at e
  change ∀ i : Fin 4, e.symm (Finsupp.single i 1) = Normalized.basis .sphere 15 139 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 4) 1) = Normalized.basis .sphere 15 139 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 4) 1) = Normalized.basis .sphere 15 139 1 := he 1
  have he2 : e.symm (Finsupp.single (2:Fin 4) 1) = Normalized.basis .sphere 15 139 2 := he 2
  have he3 : e.symm (Finsupp.single (3:Fin 4) 1) = Normalized.basis .sphere 15 139 3 := he 3
  obtain ⟨f,hf⟩ := Normalized.basis_correct ⟨.sphere,17,140,["8,1,280,1", "3,1,359,1", "0,2,438,1", "0,4,418,1"]⟩ (by
    exact List.mem_of_getElem? (i := 238) (by rfl))
  change E.Page 2 (17,140) ≃ₗ[ℤ] (Fin 4 →₀ F2) at f
  change ∀ i : Fin 4, f.symm (Finsupp.single i 1) = Normalized.basis .sphere 17 140 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 4) 1) = Normalized.basis .sphere 17 140 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 4) 1) = Normalized.basis .sphere 17 140 1 := hf 1
  have hf2 : f.symm (Finsupp.single (2:Fin 4) 1) = Normalized.basis .sphere 17 140 2 := hf 2
  have hf3 : f.symm (Finsupp.single (3:Fin 4) 1) = Normalized.basis .sphere 17 140 3 := hf 3
  let B := boundaries 9 (15,139)
  have b0 : Normalized.basis .sphere 15 139 0∈B := by
    exact alpha_all_finite_frames_boundary_of_zero_representative (r:=10) (p:=(15,139))
      (differential_target_later_zero (E:=E) (by change (2:ℤ)≤4;omega) (by decide) h282)
  have hd0 : E.d 2 (15,139) (Normalized.basis .sphere 15 139 0)=0 :=
    alpha_all_finite_frames_cycle_differential_zero (r:=2) (c:=3) (p:=(15,139)) (by decide) (by decide)
      (boundaries_le_cycles (15,139) 9 3 b0) (alpha_all_finite_frames_rep_two (15,139) _)
  have hd3 : E.d 2 (15,139) (Normalized.basis .sphere 15 139 3)=Normalized.basis .sphere 17 140 2+Normalized.basis .sphere 17 140 3 := h382.eq_on_page_two.2
  have hd1 : E.d 2 (15,139) (Normalized.basis .sphere 15 139 1)=-(Normalized.basis .sphere 17 140 2+Normalized.basis .sphere 17 140 3) := by
    have hh : E.d 2 (15,139) (Normalized.basis .sphere 15 139 1 + Normalized.basis .sphere 15 139 3)=0 :=
      alpha_all_finite_frames_cycle_differential_zero (r:=2) (c:=3) (p:=(15,139)) (by decide) (by decide) hc (alpha_all_finite_frames_rep_two (15,139) _)
    rw [map_add,hd3] at hh
    exact eq_neg_of_add_eq_zero_left hh
  have hd2 : E.d 2 (15,139) (Normalized.basis .sphere 15 139 2)=-Normalized.basis .sphere 17 140 2 := by
    have hh := h383.eq_on_page_two.2
    change E.d 2 (15,139) (Normalized.basis .sphere 15 139 2+Normalized.basis .sphere 15 139 3)=Normalized.basis .sphere 17 140 3 at hh
    rw [map_add,hd3] at hh
    have haux : ((show E.Page 2 (17,140) from E.d 2 (15,139) (Normalized.basis .sphere 15 139 2))+Normalized.basis .sphere 17 140 2)+Normalized.basis .sphere 17 140 3=0+Normalized.basis .sphere 17 140 3 := by
      simpa only [add_assoc,zero_add] using hh
    exact eq_neg_of_add_eq_zero_left (add_right_cancel haux)
  apply alpha_all_finite_frames_cycle_quotient_frame_of_boundary _ hc
  intro x hx
  have hd : E.d 2 (15,139) x=0 := alpha_all_finite_frames_cycle_differential_zero (r:=2) (c:=3) (p:=(15,139)) (by decide) (by decide) hx (alpha_all_finite_frames_rep_two (15,139) x)
  have heq : e x=Finsupp.single 0 (e x 0) + Finsupp.single 1 (e x 1) + Finsupp.single 2 (e x 2) + Finsupp.single 3 (e x 3) := by
    ext i
    fin_cases i <;> simp
  have hxe : x=e.symm (Finsupp.single 0 (e x 0) + Finsupp.single 1 (e x 1) + Finsupp.single 2 (e x 2) + Finsupp.single 3 (e x 3)) := by rw [←heq,LinearEquiv.symm_apply_apply]
  generalize hc0 : e x 0=c0 at hxe
  generalize hc1 : e x 1=c1 at hxe
  generalize hc2 : e x 2=c2 at hxe
  generalize hc3 : e x 3=c3 at hxe
  fin_cases c0 <;> fin_cases c1 <;> fin_cases c2 <;> fin_cases c3
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2)) at hxe
    simp only [Finsupp.single_zero,map_zero,add_zero] at hxe
    left
    rw [hxe]
    exact B.zero_mem
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2)) at hxe
    simp only [Finsupp.single_zero,he3,add_zero,zero_add] at hxe
    exfalso
    rw [hxe] at hd
    simp only [hd3] at hd
    have hh := congrArg (fun z=>f z 3) hd
    norm_num [map_add,map_neg,map_zero,←hf0,←hf1,←hf2,←hf3,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.neg_apply,Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2)) at hxe
    simp only [Finsupp.single_zero,he2,add_zero,zero_add] at hxe
    exfalso
    rw [hxe] at hd
    simp only [hd2] at hd
    have hh := congrArg (fun z=>f z 2) hd
    norm_num [map_add,map_neg,map_zero,←hf0,←hf1,←hf2,←hf3,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.neg_apply,Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,he2,he3,add_zero,zero_add] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd2,hd3] at hd
    have hh := congrArg (fun z=>f z 3) hd
    norm_num [map_add,map_neg,map_zero,←hf0,←hf1,←hf2,←hf3,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.neg_apply,Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2)) at hxe
    simp only [Finsupp.single_zero,he1,add_zero,zero_add] at hxe
    exfalso
    rw [hxe] at hd
    simp only [hd1] at hd
    have hh := congrArg (fun z=>f z 3) hd
    norm_num [map_add,map_neg,map_zero,←hf0,←hf1,←hf2,←hf3,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.neg_apply,Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,he1,he3,add_zero,zero_add] at hxe
    right
    rw [hxe]
    have hcanc : ((Normalized.basis .sphere 15 139 1 + Normalized.basis .sphere 15 139 3)-(Normalized.basis .sphere 15 139 1 + Normalized.basis .sphere 15 139 3) : E.Page 2 (15,139))=0 := by abel
    rw [hcanc]
    exact B.zero_mem
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,he1,he2,add_zero,zero_add] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd1,hd2] at hd
    have hh := congrArg (fun z=>f z 3) hd
    norm_num [map_add,map_neg,map_zero,←hf0,←hf1,←hf2,←hf3,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.neg_apply,Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,he1,he2,he3,zero_add] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd1,hd2,hd3] at hd
    have hh := congrArg (fun z=>f z 2) hd
    norm_num [map_add,map_neg,map_zero,←hf0,←hf1,←hf2,←hf3,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.neg_apply,Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2)) at hxe
    simp only [Finsupp.single_zero,he0,add_zero] at hxe
    left
    rw [hxe]
    exact b0
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,he0,he3,add_zero] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd0,hd3,zero_add] at hd
    have hh := congrArg (fun z=>f z 3) hd
    norm_num [map_add,map_neg,map_zero,←hf0,←hf1,←hf2,←hf3,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.neg_apply,Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,he0,he2,add_zero] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd0,hd2,zero_add] at hd
    have hh := congrArg (fun z=>f z 2) hd
    norm_num [map_add,map_neg,map_zero,←hf0,←hf1,←hf2,←hf3,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.neg_apply,Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,he0,he2,he3,add_zero] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd0,hd2,hd3,zero_add] at hd
    have hh := congrArg (fun z=>f z 3) hd
    norm_num [map_add,map_neg,map_zero,←hf0,←hf1,←hf2,←hf3,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.neg_apply,Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,he0,he1,add_zero] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd0,hd1,zero_add] at hd
    have hh := congrArg (fun z=>f z 3) hd
    norm_num [map_add,map_neg,map_zero,←hf0,←hf1,←hf2,←hf3,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.neg_apply,Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,he0,he1,he3,add_zero] at hxe
    right
    rw [hxe]
    have hcanc : ((Normalized.basis .sphere 15 139 0 + Normalized.basis .sphere 15 139 1 + Normalized.basis .sphere 15 139 3)-(Normalized.basis .sphere 15 139 1 + Normalized.basis .sphere 15 139 3) : E.Page 2 (15,139))=Normalized.basis .sphere 15 139 0 := by abel
    rw [hcanc]
    exact b0
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,he0,he1,he2,add_zero] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd0,hd1,hd2,zero_add] at hd
    have hh := congrArg (fun z=>f z 3) hd
    norm_num [map_add,map_neg,map_zero,←hf0,←hf1,←hf2,←hf3,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.neg_apply,Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2)) at hxe
    simp only [map_add,he0,he1,he2,he3] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd0,hd1,hd2,hd3,zero_add] at hd
    have hh := congrArg (fun z=>f z 2) hd
    norm_num [map_add,map_neg,map_zero,←hf0,←hf1,←hf2,←hf3,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.neg_apply,Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff] at hh


private theorem alpha_all_finite_frames_alpha_finite_frame_13   :
    ∃ c : cycles 5 (13,137), c.val=Normalized.basis .sphere 13 137 1 ∧
      ∀ q : CycleQuotient 5 7 (13,137),
        q=0 ∨ q=KIP126.Literature.subquotientClass _ _ c := by
  classical
  let E := Normalized.sphere
  let A := E.ssData (13,137)
  obtain ⟨z,hz,hzn⟩ := Normalized.correction_permanent
  change (Subobject.ofLE (A.Z ⊤) (A.Z 0) (A.Z_anti le_top) ≫ A.pageπ 0) z = _ at hz
  change A.pageπ ⊤ z ≠ 0 at hzn
  have h321 : HasDifferential E 2 (11,136) (13,137)
      (Normalized.basis .sphere 11 136 4) (Normalized.basis .sphere 13 137 3) := alpha_all_finite_frames_d2_s11_t136_basis4
  have h322 : HasDifferential E 3 (10,135) (13,137)
      (Normalized.basis .sphere 10 135 0) (Normalized.basis .sphere 13 137 0) := alpha_all_finite_frames_d3_s10_t135_basis0
  obtain ⟨_,incoming,a,hincoming,ha,hda⟩ := h322
  have hd2 := Normalized.d3_h4_x109
  change HasNonzeroDifferential E 3 (13,137) (16,139)
    (Normalized.basis .sphere 13 137 2) _ at hd2
  obtain ⟨_,c,t,hc,ht,hdc,htn⟩ := hd2
  have hdc' : E.d 3 (13,137) c = t := hdc
  have hda' : E.d 3 (10,135) incoming = a := hda
  let down (r : ℤ) := Subobject.ofLE (A.Z ⊤) (A.Z ↑(r-2).toNat) (A.Z_anti le_top)
  let val (r : ℤ) := down r ≫ A.pageπ ↑(r-2).toNat
  have rep (r : ℤ) (hr : 2 ≤ r) (q : (Subobject.underlying.obj (A.Z ⊤) : ModuleCat ℤ)) :
      RepresentsOnPage E r (13,137) (val 2 q) (val r q) := by
    refine ⟨hr, down r q, ?_, rfl⟩
    change (Subobject.ofLE _ _ _ ≫ A.pageπ 0) ((down r) q) = val 2 q
    dsimp only [val, down]
    rw [← CategoryTheory.comp_apply, ← Category.assoc, Subobject.ofLE_comp_ofLE]
    rfl
  let b : E.Page 3 (13,137) := val 3 z
  have hb : RepresentsOnPage E 3 (13,137) (Normalized.basis .sphere 13 137 1) b := by
    have h := rep 3 (by decide) z
    change val 2 z = _ at hz
    rw [hz] at h
    exact h
  have hthree : RepresentsOnPage E 3 (13,137) (Normalized.basis .sphere 13 137 3) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) h321
  obtain ⟨e,he⟩ := Normalized.basis_correct ⟨.sphere,13,137,["76,1,82,1", "9,1,251,1", "7,1,275,1", "0,5,367,1"]⟩ (by
    exact List.mem_of_getElem? (i := 208) (by rfl))
  change E.Page 2 (13,137) ≃ₗ[ℤ] (Fin 4 →₀ F2) at e
  change ∀i : Fin 4, e.symm (Finsupp.single i 1) = Normalized.basis .sphere 13 137 i.val at he
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

  let v := Normalized.basis .sphere 13 137 1
  have hvc : v∈cycles 5 (13,137) := by
    apply (cycles_reaches 5 (13,137) (by decide) v).mpr
    refine ⟨val 6 z,?_⟩
    have hh := rep 6 (by decide) z
    change val 2 z=_ at hz
    rw [hz] at hh
    exact hh
  refine ⟨⟨v,hvc⟩,rfl,?_⟩
  apply alpha_all_finite_frames_cycle_quotient_frame_of_boundary (p:=(13,137)) (c:=5) (b:=7) v hvc
  let B := boundaries 7 (13,137)
  have b0 : Normalized.basis .sphere 13 137 0∈B := by
    apply alpha_all_finite_frames_boundary_of_zero_representative (r:=8) (p:=(13,137))
    exact differential_target_later_zero (E:=E) (r:=3) (t:=8) (p:=(10,135)) (q:=(13,137)) (by change (2:ℤ)≤3;omega) (by decide)
      ⟨rfl,incoming,a,hincoming,ha,hda⟩
  have lift_boundary {y : E.Page 2 (13,137)} (hy : RepresentsOnPage E 3 (13,137) y 0) : y∈B := by
    exact boundaries_monotone (13,137) (by decide : (2:ℤ)≤7)
      (alpha_all_finite_frames_boundary_of_zero_representative (r:=3) (p:=(13,137)) hy)
  intro x hx
  obtain ⟨xr,hxr⟩ := (cycles_reaches 2 (13,137) (by decide) x).mp
    (cycles_antitone (13,137) (by decide : (2:ℤ)≤5) hx)
  have hxzero : E.d 3 (13,137) xr=0 :=
    alpha_all_finite_frames_cycle_differential_zero (r:=3) (c:=5) (p:=(13,137)) (by decide) (by decide) hx hxr
  rcases hkernel xr hxzero with hq|hq|hq|hq
  · left
    rw [hq] at hxr
    exact lift_boundary hxr
  · left
    have hh := represents_sub_tail hxr ha
    rw [hq,sub_self] at hh
    have hm := B.add_mem (lift_boundary hh) b0
    simpa only [sub_add_cancel] using hm
  · right
    have hh := represents_sub_tail hxr hb
    rw [hq,sub_self] at hh
    exact lift_boundary hh
  · right
    have hh := represents_sub_tail (represents_sub_tail hxr hb) ha
    rw [hq,add_sub_cancel_right,sub_self] at hh
    have hm := B.add_mem (lift_boundary hh) b0
    simpa only [sub_add_cancel] using hm


private theorem alpha_all_finite_frames

    (h14 : Normalized.basis .sphere 14 138 2∈cycles 4 (14,138))
    (h15 : Normalized.basis .sphere 15 139 1+Normalized.basis .sphere 15 139 3∈cycles 3 (15,139)) :
    (∃ c : cycles 5 (13,137), c.val=Normalized.basis .sphere 13 137 1 ∧
      ∀ q : CycleQuotient 5 7 (13,137), q=0 ∨ q=KIP126.Literature.subquotientClass _ _ c) ∧
    (∀ q : CycleQuotient 4 8 (14,138), q=0 ∨
      q=KIP126.Literature.subquotientClass _ _ ⟨Normalized.basis .sphere 14 138 2,h14⟩) ∧
    (∀ q : CycleQuotient 3 9 (15,139), q=0 ∨
      q=KIP126.Literature.subquotientClass _ _ ⟨Normalized.basis .sphere 15 139 1+Normalized.basis .sphere 15 139 3,h15⟩) := by
  classical
  exact ⟨alpha_all_finite_frames_alpha_finite_frame_13  ,alpha_all_finite_frames_alpha_finite_frame_14  h14,alpha_all_finite_frames_alpha_finite_frame_15  h15⟩


end
end KIP126.Main.Internal.AlphaOne
end
