module

public import KIP126.Def.AdamsSynthetic.SectionSeven.AlphaOne
public import KIP126.Def.SpectralSequence.Basic.Category.Proofs
public import KIP126.Def.SpectralSequence.FinitePageCalculus.Proofs
public import KIP126.Def.Synthetic.Detection.Vanishing.Proofs
public import KIP126.Def.Synthetic.Sphere.Homotopy.Proofs
public import KIP126.Main.Literature.AdamsSynthetic.Theorems
public import KIP126.Main.Computation.LinCoordinates.Model.BasisCatalogue.FiniteCertificates
public import KIP126.Main.Computation.SphereAndCofiber.Consequences


import all Init.Data.String.Search
import all Init.Data.String.Slice

import all Init.Data.String.Legacy

@[expose] public section


/-! Filtration and representative calculations for Proposition 7.8 and
Lemma 7.14 (`lem:x_123_9`). The complete bases, products and differential
calculations refer to the same standard sphere as the literature hypotheses.
These lemmas derive the required homotopy relations from those inputs. -/
namespace KIP126.Main.SectionSeven
open KIP126.SpectralSequence.FinitePageCalculus
open CategoryTheory
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.SpectralSequence
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.AdamsSynthetic.SectionSeven
open KIP126.Literature.AdamsSynthetic
noncomputable section

-- Preserve the outer local attribute preceding this section in AlphaOne.
attribute [local irreducible] KIP126.LinE2.homogeneousPart

section AlphaOneExistenceProof
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.SpectralSequence
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.AdamsSynthetic.SectionSeven
open KIP126.Algebra
universe u v w
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local irreducible] adamsTowerSSData adamsTowerInternalD
variable {C : Type u} [StableHomotopyCategory.{u,v} C] [HasFunctorialCofiber (C:=C)]
    {Syn : Type w} [SyntheticCategory.{w,v} Syn] [HasFunctorialCofiber (C:=Syn)]
    {H : Mod2EilenbergMacLane (C:=C)} {M : MilnorCooperations H} {D : AdamsComparison H M Syn}

open KIP126.Literature.AdamsSynthetic
open CategoryTheory.Pretriangulated KIP126.LinE2 KIP126.Algebra
open KIP126.Computation.SphereAndCofiber KIP126.Computation.Near126
open PageRepresentatives
private theorem alpha_all_finite_frames_d2_s14_t138_basis1 (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (14,138) (16,139)
    (I.interpretation.basis .sphere 14 138 1) (I.interpretation.basis .sphere 16 139 1 + I.interpretation.basis .sphere 16 139 2) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,14,138,[1],16,139,[1, 2],"S0_AdamsE2_ss",3072⟩ (by
    exact List.mem_of_getElem? (i := 366) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (14,138) (16,139) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 14 138 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 16 139 [1, 2] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem alpha_all_finite_frames_d2_s14_t138_basis0_add_basis1 (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (14,138) (16,139)
    (I.interpretation.basis .sphere 14 138 0 + I.interpretation.basis .sphere 14 138 1) (I.interpretation.basis .sphere 16 139 2) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,14,138,[0, 1],16,139,[2],"S0_AdamsE2_ss",3073⟩ (by
    exact List.mem_of_getElem? (i := 367) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (14,138) (16,139) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 14 138 [0, 1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 16 139 [2] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem alpha_all_finite_frames_d2_s12_t137_basis1 (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (12,137) (14,138)
    (I.interpretation.basis .sphere 12 137 1) (I.interpretation.basis .sphere 14 138 4) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,12,137,[1],14,138,[4],"S0_AdamsE2_ss",2921⟩ (by
    exact List.mem_of_getElem? (i := 308) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (12,137) (14,138) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 12 137 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 14 138 [4] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem alpha_all_finite_frames_d2_s12_t137_basis0 (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (12,137) (14,138)
    (I.interpretation.basis .sphere 12 137 0) (I.interpretation.basis .sphere 14 138 3) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,12,137,[0],14,138,[3],"S0_AdamsE2_ss",2922⟩ (by
    exact List.mem_of_getElem? (i := 309) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (12,137) (14,138) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 12 137 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 14 138 [3] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem alpha_all_finite_frames_d2_s15_t139_basis3 (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (15,139) (17,140)
    (I.interpretation.basis .sphere 15 139 3) (I.interpretation.basis .sphere 17 140 2 + I.interpretation.basis .sphere 17 140 3) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,15,139,[3],17,140,[2, 3],"S0_AdamsE2_ss",3141⟩ (by
    exact List.mem_of_getElem? (i := 382) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (15,139) (17,140) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 15 139 [3] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 17 140 [2, 3] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem alpha_all_finite_frames_d2_s15_t139_basis2_add_basis3 (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (15,139) (17,140)
    (I.interpretation.basis .sphere 15 139 2 + I.interpretation.basis .sphere 15 139 3) (I.interpretation.basis .sphere 17 140 3) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,15,139,[2, 3],17,140,[3],"S0_AdamsE2_ss",3142⟩ (by
    exact List.mem_of_getElem? (i := 383) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (15,139) (17,140) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 15 139 [2, 3] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 17 140 [3] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem alpha_all_finite_frames_d4_s11_t136_basis0 (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 4 (11,136) (15,139)
    (I.interpretation.basis .sphere 11 136 0) (I.interpretation.basis .sphere 15 139 0) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,4,11,136,[0],15,139,[0],"S0_AdamsE2_ss",2853⟩ (by
    exact List.mem_of_getElem? (i := 282) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 4 (11,136) (15,139) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 11 136 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 15 139 [0] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem alpha_all_finite_frames_d2_s11_t136_basis4 (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (11,136) (13,137)
    (I.interpretation.basis .sphere 11 136 4) (I.interpretation.basis .sphere 13 137 3) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,11,136,[4],13,137,[3],"S0_AdamsE2_ss",2914⟩ (by
    exact List.mem_of_getElem? (i := 321) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (11,136) (13,137) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 11 136 [4] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 13 137 [3] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  exact h

private theorem alpha_all_finite_frames_d3_s10_t135_basis0 (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 3 (10,135) (13,137)
    (I.interpretation.basis .sphere 10 135 0) (I.interpretation.basis .sphere 13 137 0) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,3,10,135,[0],13,137,[0],"S0_AdamsE2_ss",2915⟩ (by
    exact List.mem_of_getElem? (i := 322) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (10,135) (13,137) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 135 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 13 137 [0] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  exact h

private theorem alpha_all_finite_frames_boundary_of_zero_representative {H : Mod2EilenbergMacLane (C:=C)}
    {r : ℤ} {p : ℤ×ℤ} {x : E2 H SphereSpectrum p.1 p.2}
    (hx : RepresentsOnPage (adamsTowerInternalSpectralSequence H.unit SphereSpectrum) r p x 0) :
    x ∈ boundaries H SphereSpectrum (r-1) p := by
  classical
  let E := adamsTowerInternalSpectralSequence H.unit SphereSpectrum
  let P := E.ssData p
  obtain ⟨hr,z,hz,hzero⟩ := hx
  change (Subobject.ofLE (P.Z ↑(r-2).toNat) (P.Z 0) _ ≫ P.pageπ 0) z=x at hz
  change P.pageπ ↑(r-2).toNat z=0 at hzero
  obtain ⟨y,hy⟩ := (cokernel_π_eq_zero_iff_mem_range
    (Subobject.ofLE (P.B ↑(r-2).toNat) (P.Z ↑(r-2).toNat) (P.B_le_Z _)) z).mp hzero
  have hrindex : r-1-1=r-2 := by omega
  change ∃ y, boundaryMap H SphereSpectrum ↑(r-1-1).toNat p y=x
  rw [hrindex]
  refine ⟨y,?_⟩
  have hf : Subobject.ofLE (P.B ↑(r-2).toNat) (P.Z ↑(r-2).toNat) (P.B_le_Z _) ≫
      cycleMap H SphereSpectrum ↑(r-2).toNat p = boundaryMap H SphereSpectrum ↑(r-2).toNat p := by
    dsimp only [boundaryMap,cycleMap,P,E]
    rw [←Category.assoc,Subobject.ofLE_comp_ofLE]
  rw [←hf,CategoryTheory.comp_apply,hy]
  exact hz


private theorem alpha_all_finite_frames_cycle_differential_zero {H : Mod2EilenbergMacLane (C:=C)}
    {r c : ℤ} {p : ℤ×ℤ} {x : E2 H SphereSpectrum p.1 p.2}
    {a : (adamsTowerInternalSpectralSequence H.unit SphereSpectrum).Page r p}
    (hr : 2≤r) (hc : r≤c)
    (hx : x∈cycles H SphereSpectrum c p)
    (ha : RepresentsOnPage (adamsTowerInternalSpectralSequence H.unit SphereSpectrum) r p x a) :
    (adamsTowerInternalSpectralSequence H.unit SphereSpectrum).d r p a=0 := by
  classical
  obtain ⟨y,hy⟩ := (isCycle_iff_represents H SphereSpectrum (c+1) (by omega) p x).mp
    ⟨by omega,by simpa using hx⟩
  exact represents_d_zero_of_later hr (by omega : r<c+1) ha ⟨y,hy⟩


private theorem alpha_all_finite_frames_cycle_quotient_frame_of_boundary {H : Mod2EilenbergMacLane (C:=C)}
    {c b : ℤ} {p : ℤ×ℤ} (v : E2 H SphereSpectrum p.1 p.2)
    (hv : v∈cycles H SphereSpectrum c p)
    (h : ∀ z, z∈cycles H SphereSpectrum c p → z∈boundaries H SphereSpectrum b p ∨ z-v∈boundaries H SphereSpectrum b p) :
    ∀ q : CycleQuotient H SphereSpectrum c b p,
      q=0 ∨ q=NestedQuotient.projection _ _ ⟨v,hv⟩ := by
  classical
  rintro ⟨z⟩
  rcases h z.val z.property with hz|hz
  · exact Or.inl ((NestedQuotient.projection_eq_zero z).mpr hz)
  · right
    apply sub_eq_zero.mp
    change NestedQuotient.projection _ _ z-NestedQuotient.projection _ _ ⟨v,hv⟩=0
    rw [←map_sub]
    exact (NestedQuotient.projection_eq_zero (z-⟨v,hv⟩)).mpr hz


private theorem alpha_all_finite_frames_rep_two {H : Mod2EilenbergMacLane (C:=C)} (p : ℤ×ℤ) (x : (adamsTowerInternalSpectralSequence H.unit SphereSpectrum).Page 2 p) :
    RepresentsOnPage (adamsTowerInternalSpectralSequence H.unit SphereSpectrum) 2 p x x := by
  classical
  let E := adamsTowerInternalSpectralSequence H.unit SphereSpectrum
  haveI : Epi ((E.ssData p).pageπ 0) := inferInstanceAs (Epi (cokernel.π _))
  obtain ⟨z,rfl⟩ := (ModuleCat.epi_iff_surjective ((E.ssData p).pageπ 0)).mp inferInstance x
  exact ⟨by decide,z,by simp only [Subobject.ofLE_refl,Category.id_comp]; rfl,rfl⟩


set_option maxHeartbeats 800000 in
private theorem alpha_all_finite_frames_alpha_finite_frame_14 {D : AdamsComparison H M Syn} (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G)
    (hc : (I.interpretation.basis .sphere 14 138 2)∈cycles H SphereSpectrum 4 (14,138)) :
    ∀ q : CycleQuotient H SphereSpectrum 4 8 (14,138),
      q=0 ∨ q=NestedQuotient.projection _ _ ⟨(I.interpretation.basis .sphere 14 138 2),hc⟩ := by
  classical
  let E := sequence D .sphere
  have h366 : HasDifferential E 2 (14,138) (16,139)
      (I.interpretation.basis .sphere 14 138 1) (I.interpretation.basis .sphere 16 139 1 + I.interpretation.basis .sphere 16 139 2) := alpha_all_finite_frames_d2_s14_t138_basis1 I
  have h367 : HasDifferential E 2 (14,138) (16,139)
      (I.interpretation.basis .sphere 14 138 0 + I.interpretation.basis .sphere 14 138 1) (I.interpretation.basis .sphere 16 139 2) := alpha_all_finite_frames_d2_s14_t138_basis0_add_basis1 I
  have h308 : HasDifferential E 2 (12,137) (14,138)
      (I.interpretation.basis .sphere 12 137 1) (I.interpretation.basis .sphere 14 138 4) := alpha_all_finite_frames_d2_s12_t137_basis1 I
  have h309 : HasDifferential E 2 (12,137) (14,138)
      (I.interpretation.basis .sphere 12 137 0) (I.interpretation.basis .sphere 14 138 3) := alpha_all_finite_frames_d2_s12_t137_basis0 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,14,138,["440,1", "439,1", "23,1,190,1", "1,1,418,1", "1,1,417,1"]⟩ (by
    exact List.mem_of_getElem? (i := 216) (by rfl))
  change E.Page 2 (14,138) ≃ₗ[ℤ] (Fin 5 →₀ F2) at e
  change ∀ i : Fin 5, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 14 138 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 5) 1) = I.interpretation.basis .sphere 14 138 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 5) 1) = I.interpretation.basis .sphere 14 138 1 := he 1
  have he2 : e.symm (Finsupp.single (2:Fin 5) 1) = I.interpretation.basis .sphere 14 138 2 := he 2
  have he3 : e.symm (Finsupp.single (3:Fin 5) 1) = I.interpretation.basis .sphere 14 138 3 := he 3
  have he4 : e.symm (Finsupp.single (4:Fin 5) 1) = I.interpretation.basis .sphere 14 138 4 := he 4
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,16,139,["1,1,424,1", "0,1,438,1", "0,3,418,1"]⟩ (by
    exact List.mem_of_getElem? (i := 230) (by rfl))
  change E.Page 2 (16,139) ≃ₗ[ℤ] (Fin 3 →₀ F2) at f
  change ∀ i : Fin 3, f.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 16 139 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 3) 1) = I.interpretation.basis .sphere 16 139 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 3) 1) = I.interpretation.basis .sphere 16 139 1 := hf 1
  have hf2 : f.symm (Finsupp.single (2:Fin 3) 1) = I.interpretation.basis .sphere 16 139 2 := hf 2
  let B := boundaries H SphereSpectrum 8 (14,138)
  have b3 : I.interpretation.basis .sphere 14 138 3∈B := by
    exact alpha_all_finite_frames_boundary_of_zero_representative (H:=H) (r:=9) (p:=(14,138))
      (differential_target_later_zero (E:=E) (by change (2:ℤ)≤2;omega) (by decide) h309)
  have hd3 : E.d 2 (14,138) (I.interpretation.basis .sphere 14 138 3)=0 :=
    alpha_all_finite_frames_cycle_differential_zero (H:=H) (r:=2) (c:=4) (p:=(14,138)) (by decide) (by decide)
      (boundaries_le_cycles H SphereSpectrum (14,138) 8 4 b3) (alpha_all_finite_frames_rep_two (14,138) _)
  have b4 : I.interpretation.basis .sphere 14 138 4∈B := by
    exact alpha_all_finite_frames_boundary_of_zero_representative (H:=H) (r:=9) (p:=(14,138))
      (differential_target_later_zero (E:=E) (by change (2:ℤ)≤2;omega) (by decide) h308)
  have hd4 : E.d 2 (14,138) (I.interpretation.basis .sphere 14 138 4)=0 :=
    alpha_all_finite_frames_cycle_differential_zero (H:=H) (r:=2) (c:=4) (p:=(14,138)) (by decide) (by decide)
      (boundaries_le_cycles H SphereSpectrum (14,138) 8 4 b4) (alpha_all_finite_frames_rep_two (14,138) _)
  have hd2 : E.d 2 (14,138) (I.interpretation.basis .sphere 14 138 2)=0 :=
    alpha_all_finite_frames_cycle_differential_zero (H:=H) (r:=2) (c:=4) (p:=(14,138)) (by decide) (by decide) hc (alpha_all_finite_frames_rep_two (14,138) _)
  have hd1 : E.d 2 (14,138) (I.interpretation.basis .sphere 14 138 1)=I.interpretation.basis .sphere 16 139 1+I.interpretation.basis .sphere 16 139 2 := h366.eq_on_page_two.2
  have hd0 : E.d 2 (14,138) (I.interpretation.basis .sphere 14 138 0)=-I.interpretation.basis .sphere 16 139 1 := by
    have hh := h367.eq_on_page_two.2
    change E.d 2 (14,138) (I.interpretation.basis .sphere 14 138 0+I.interpretation.basis .sphere 14 138 1)=I.interpretation.basis .sphere 16 139 2 at hh
    rw [map_add,hd1] at hh
    have haux : ((show E.Page 2 (16,139) from E.d 2 (14,138) (I.interpretation.basis .sphere 14 138 0))+I.interpretation.basis .sphere 16 139 1)+I.interpretation.basis .sphere 16 139 2=0+I.interpretation.basis .sphere 16 139 2 := by
      simpa only [add_assoc,zero_add] using hh
    exact eq_neg_of_add_eq_zero_left (add_right_cancel haux)
  apply alpha_all_finite_frames_cycle_quotient_frame_of_boundary _ hc
  intro x hx
  have hd : E.d 2 (14,138) x=0 := alpha_all_finite_frames_cycle_differential_zero (H:=H) (r:=2) (c:=4) (p:=(14,138)) (by decide) (by decide) hx (alpha_all_finite_frames_rep_two (14,138) x)
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
    have hcanc : ((I.interpretation.basis .sphere 14 138 2)-(I.interpretation.basis .sphere 14 138 2) : E.Page 2 (14,138))=0 := by abel
    rw [hcanc]
    exact B.zero_mem
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,he2,he4,add_zero,zero_add] at hxe
    right
    rw [hxe]
    have hcanc : ((I.interpretation.basis .sphere 14 138 2 + I.interpretation.basis .sphere 14 138 4)-(I.interpretation.basis .sphere 14 138 2) : E.Page 2 (14,138))=I.interpretation.basis .sphere 14 138 4 := by abel
    rw [hcanc]
    exact b4
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,he2,he3,add_zero,zero_add] at hxe
    right
    rw [hxe]
    have hcanc : ((I.interpretation.basis .sphere 14 138 2 + I.interpretation.basis .sphere 14 138 3)-(I.interpretation.basis .sphere 14 138 2) : E.Page 2 (14,138))=I.interpretation.basis .sphere 14 138 3 := by abel
    rw [hcanc]
    exact b3
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,he2,he3,he4,add_zero,zero_add] at hxe
    right
    rw [hxe]
    have hcanc : ((I.interpretation.basis .sphere 14 138 2 + I.interpretation.basis .sphere 14 138 3 + I.interpretation.basis .sphere 14 138 4)-(I.interpretation.basis .sphere 14 138 2) : E.Page 2 (14,138))=I.interpretation.basis .sphere 14 138 3 + I.interpretation.basis .sphere 14 138 4 := by abel
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


private theorem alpha_all_finite_frames_alpha_finite_frame_15 {D : AdamsComparison H M Syn} (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G)
    (hc : (I.interpretation.basis .sphere 15 139 1 + I.interpretation.basis .sphere 15 139 3)∈cycles H SphereSpectrum 3 (15,139)) :
    ∀ q : CycleQuotient H SphereSpectrum 3 9 (15,139),
      q=0 ∨ q=NestedQuotient.projection _ _ ⟨(I.interpretation.basis .sphere 15 139 1 + I.interpretation.basis .sphere 15 139 3),hc⟩ := by
  classical
  let E := sequence D .sphere
  have h382 : HasDifferential E 2 (15,139) (17,140)
      (I.interpretation.basis .sphere 15 139 3) (I.interpretation.basis .sphere 17 140 2 + I.interpretation.basis .sphere 17 140 3) := alpha_all_finite_frames_d2_s15_t139_basis3 I
  have h383 : HasDifferential E 2 (15,139) (17,140)
      (I.interpretation.basis .sphere 15 139 2 + I.interpretation.basis .sphere 15 139 3) (I.interpretation.basis .sphere 17 140 3) := alpha_all_finite_frames_d2_s15_t139_basis2_add_basis3 I
  have h282 : HasDifferential E 4 (11,136) (15,139)
      (I.interpretation.basis .sphere 11 136 0) (I.interpretation.basis .sphere 15 139 0) := alpha_all_finite_frames_d4_s11_t136_basis0 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,15,139,["448,1", "3,2,287,1", "0,1,440,1", "0,1,439,1"]⟩ (by
    exact List.mem_of_getElem? (i := 223) (by rfl))
  change E.Page 2 (15,139) ≃ₗ[ℤ] (Fin 4 →₀ F2) at e
  change ∀ i : Fin 4, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 15 139 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 4) 1) = I.interpretation.basis .sphere 15 139 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 4) 1) = I.interpretation.basis .sphere 15 139 1 := he 1
  have he2 : e.symm (Finsupp.single (2:Fin 4) 1) = I.interpretation.basis .sphere 15 139 2 := he 2
  have he3 : e.symm (Finsupp.single (3:Fin 4) 1) = I.interpretation.basis .sphere 15 139 3 := he 3
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,17,140,["8,1,280,1", "3,1,359,1", "0,2,438,1", "0,4,418,1"]⟩ (by
    exact List.mem_of_getElem? (i := 238) (by rfl))
  change E.Page 2 (17,140) ≃ₗ[ℤ] (Fin 4 →₀ F2) at f
  change ∀ i : Fin 4, f.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 17 140 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 4) 1) = I.interpretation.basis .sphere 17 140 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 4) 1) = I.interpretation.basis .sphere 17 140 1 := hf 1
  have hf2 : f.symm (Finsupp.single (2:Fin 4) 1) = I.interpretation.basis .sphere 17 140 2 := hf 2
  have hf3 : f.symm (Finsupp.single (3:Fin 4) 1) = I.interpretation.basis .sphere 17 140 3 := hf 3
  let B := boundaries H SphereSpectrum 9 (15,139)
  have b0 : I.interpretation.basis .sphere 15 139 0∈B := by
    exact alpha_all_finite_frames_boundary_of_zero_representative (H:=H) (r:=10) (p:=(15,139))
      (differential_target_later_zero (E:=E) (by change (2:ℤ)≤4;omega) (by decide) h282)
  have hd0 : E.d 2 (15,139) (I.interpretation.basis .sphere 15 139 0)=0 :=
    alpha_all_finite_frames_cycle_differential_zero (H:=H) (r:=2) (c:=3) (p:=(15,139)) (by decide) (by decide)
      (boundaries_le_cycles H SphereSpectrum (15,139) 9 3 b0) (alpha_all_finite_frames_rep_two (15,139) _)
  have hd3 : E.d 2 (15,139) (I.interpretation.basis .sphere 15 139 3)=I.interpretation.basis .sphere 17 140 2+I.interpretation.basis .sphere 17 140 3 := h382.eq_on_page_two.2
  have hd1 : E.d 2 (15,139) (I.interpretation.basis .sphere 15 139 1)=-(I.interpretation.basis .sphere 17 140 2+I.interpretation.basis .sphere 17 140 3) := by
    have hh : E.d 2 (15,139) (I.interpretation.basis .sphere 15 139 1 + I.interpretation.basis .sphere 15 139 3)=0 :=
      alpha_all_finite_frames_cycle_differential_zero (H:=H) (r:=2) (c:=3) (p:=(15,139)) (by decide) (by decide) hc (alpha_all_finite_frames_rep_two (15,139) _)
    rw [map_add,hd3] at hh
    exact eq_neg_of_add_eq_zero_left hh
  have hd2 : E.d 2 (15,139) (I.interpretation.basis .sphere 15 139 2)=-I.interpretation.basis .sphere 17 140 2 := by
    have hh := h383.eq_on_page_two.2
    change E.d 2 (15,139) (I.interpretation.basis .sphere 15 139 2+I.interpretation.basis .sphere 15 139 3)=I.interpretation.basis .sphere 17 140 3 at hh
    rw [map_add,hd3] at hh
    have haux : ((show E.Page 2 (17,140) from E.d 2 (15,139) (I.interpretation.basis .sphere 15 139 2))+I.interpretation.basis .sphere 17 140 2)+I.interpretation.basis .sphere 17 140 3=0+I.interpretation.basis .sphere 17 140 3 := by
      simpa only [add_assoc,zero_add] using hh
    exact eq_neg_of_add_eq_zero_left (add_right_cancel haux)
  apply alpha_all_finite_frames_cycle_quotient_frame_of_boundary _ hc
  intro x hx
  have hd : E.d 2 (15,139) x=0 := alpha_all_finite_frames_cycle_differential_zero (H:=H) (r:=2) (c:=3) (p:=(15,139)) (by decide) (by decide) hx (alpha_all_finite_frames_rep_two (15,139) x)
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
    have hcanc : ((I.interpretation.basis .sphere 15 139 1 + I.interpretation.basis .sphere 15 139 3)-(I.interpretation.basis .sphere 15 139 1 + I.interpretation.basis .sphere 15 139 3) : E.Page 2 (15,139))=0 := by abel
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
    have hcanc : ((I.interpretation.basis .sphere 15 139 0 + I.interpretation.basis .sphere 15 139 1 + I.interpretation.basis .sphere 15 139 3)-(I.interpretation.basis .sphere 15 139 1 + I.interpretation.basis .sphere 15 139 3) : E.Page 2 (15,139))=I.interpretation.basis .sphere 15 139 0 := by abel
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


private theorem alpha_all_finite_frames_alpha_finite_frame_13 {D : AdamsComparison H M Syn} (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G) (facts : Derived.SphereFacts I.interpretation) :
    ∃ c : cycles H SphereSpectrum 5 (13,137), c.val=I.interpretation.sphere 13 137 correction ∧
      ∀ q : CycleQuotient H SphereSpectrum 5 7 (13,137),
        q=0 ∨ q=NestedQuotient.projection _ _ c := by
  classical
  have af13_labels (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G) :
      I.interpretation.sphere 13 137 correction = I.interpretation.basis .sphere 13 137 1 ∧
      I.interpretation.sphere 13 137 (mulAt (atom .h4) (atom .x_109_12)) = I.interpretation.basis .sphere 13 137 2 := by
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
  let E := sequence D .sphere
  let A := E.ssData (13,137)
  obtain ⟨hl1,hl2⟩ := af13_labels I
  obtain ⟨z,hz,hzn⟩ := facts.correction_permanent
  change (Subobject.ofLE (A.Z ⊤) (A.Z 0) (A.Z_anti le_top) ≫ A.pageπ 0) z = _ at hz
  change A.pageπ ⊤ z ≠ 0 at hzn
  have h321 : HasDifferential E 2 (11,136) (13,137)
      (I.interpretation.basis .sphere 11 136 4) (I.interpretation.basis .sphere 13 137 3) := alpha_all_finite_frames_d2_s11_t136_basis4 I
  have h322 : HasDifferential E 3 (10,135) (13,137)
      (I.interpretation.basis .sphere 10 135 0) (I.interpretation.basis .sphere 13 137 0) := alpha_all_finite_frames_d3_s10_t135_basis0 I
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

  let v := I.interpretation.basis .sphere 13 137 1
  have hvc : v∈cycles H SphereSpectrum 5 (13,137) := by
    apply permanentCycles_le_cycles H SphereSpectrum (13,137) 5
    change ∃ q, cycleMap H SphereSpectrum ⊤ (13,137) q=v
    exact ⟨z,hz.trans hl1⟩
  refine ⟨⟨v,hvc⟩,hl1.symm,?_⟩
  apply alpha_all_finite_frames_cycle_quotient_frame_of_boundary (H:=H) (p:=(13,137)) (c:=5) (b:=7) v hvc
  let B := boundaries H SphereSpectrum 7 (13,137)
  have b0 : I.interpretation.basis .sphere 13 137 0∈B := by
    apply alpha_all_finite_frames_boundary_of_zero_representative (H:=H) (r:=8) (p:=(13,137))
    exact differential_target_later_zero (E:=E) (r:=3) (t:=8) (p:=(10,135)) (q:=(13,137)) (by change (2:ℤ)≤3;omega) (by decide)
      ⟨rfl,incoming,a,hincoming,ha,hda⟩
  have lift_boundary {y : E.Page 2 (13,137)} (hy : RepresentsOnPage E 3 (13,137) y 0) : y∈B := by
    exact boundaries_monotone H SphereSpectrum (13,137) (by decide : (2:ℤ)≤7)
      (alpha_all_finite_frames_boundary_of_zero_representative (H:=H) (r:=3) (p:=(13,137)) hy)
  intro x hx
  obtain ⟨xr,hxr⟩ := (isCycle_iff_represents H SphereSpectrum 3 (by decide) (13,137) x).mp
    ⟨by decide,cycles_antitone H SphereSpectrum (13,137) (by decide : (2:ℤ)≤5) hx⟩
  have hxzero : E.d 3 (13,137) xr=0 :=
    alpha_all_finite_frames_cycle_differential_zero (H:=H) (r:=3) (c:=5) (p:=(13,137)) (by decide) (by decide) hx hxr
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
    {L : SphereAdamsClasses H} {G : KIP126.Literature.AdamsSynthetic.TmfDetectionClasses H}
    (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G) (facts : Derived.SphereFacts I.interpretation)
    (h14 : I.interpretation.basis .sphere 14 138 2∈cycles H SphereSpectrum 4 (14,138))
    (h15 : I.interpretation.basis .sphere 15 139 1+I.interpretation.basis .sphere 15 139 3∈cycles H SphereSpectrum 3 (15,139)) :
    (∃ c : cycles H SphereSpectrum 5 (13,137), c.val=I.interpretation.sphere 13 137 correction ∧
      ∀ q : CycleQuotient H SphereSpectrum 5 7 (13,137), q=0 ∨ q=NestedQuotient.projection _ _ c) ∧
    (∀ q : CycleQuotient H SphereSpectrum 4 8 (14,138), q=0 ∨
      q=NestedQuotient.projection _ _ ⟨I.interpretation.basis .sphere 14 138 2,h14⟩) ∧
    (∀ q : CycleQuotient H SphereSpectrum 3 9 (15,139), q=0 ∨
      q=NestedQuotient.projection _ _ ⟨I.interpretation.basis .sphere 15 139 1+I.interpretation.basis .sphere 15 139 3,h15⟩) := by
  classical
  exact ⟨alpha_all_finite_frames_alpha_finite_frame_13 I facts,alpha_all_finite_frames_alpha_finite_frame_14 I h14,alpha_all_finite_frames_alpha_finite_frame_15 I h15⟩

private theorem alpha_exists_from_finite_frames_family_map_data {D : AdamsComparison H M Syn} {X Y : Syn} (f : X ⟶ Y) (r : ℤ) (i : Tridegree) :
    familyPageMap D.family f r i = (D.family.functor.map f).toSSDataMorphism.pageMap i (↑(r-2).toNat) := by
  classical
  let F := (D.family.functor.map f).toSSDataMorphism
  let PX := (D.family.functor.obj X).ssData i
  let PY := (D.family.functor.obj Y).ssData i
  let nX : WithTop ℕ := ↑(r-(D.family.functor.obj X).r₀).toNat
  let nY : WithTop ℕ := ↑(r-(D.family.functor.obj Y).r₀).toNat
  change (@eqToHom (ModuleCat.{v} ℤ) _ (PX.page (↑(r-2).toNat)) (PX.page nX) _ ≫
    (F.pageMap i nX ≫ @eqToHom (ModuleCat.{v} ℤ) _ (PY.page nX) (PY.page nY) _) ≫
    @eqToHom (ModuleCat.{v} ℤ) _ (PY.page nY) (PY.page (↑(r-2).toNat)) _) = F.pageMap i (↑(r-2).toNat)
  have hX : nX=↑(r-2).toNat := by dsimp only [nX]; rw [D.family.firstPage X]
  have hY : nY=↑(r-2).toNat := by dsimp only [nY]; rw [D.family.firstPage Y]
  have normalize (A B : WithTop ℕ → ModuleCat.{v} ℤ) (j : ∀ n, A n ⟶ B n)
      (n m n0 : WithTop ℕ) (hn : n=n0) (hm : m=n0)
      (h1 : A n0=A n) (h2 : B n=B m) (h3 : B m=B n0) :
      eqToHom h1 ≫ (j n ≫ eqToHom h2) ≫ eqToHom h3 = j n0 := by
    subst n
    subst m
    simp only [eqToHom_refl,Category.id_comp,Category.comp_id]
  exact normalize PX.page PY.page (fun n => F.pageMap i n) nX nY (↑(r-2).toNat) hX hY _ _ _


private theorem alpha_exists_from_finite_frames_family_page_comp {D : AdamsComparison H M Syn} {X Y Z : Syn} (f : X ⟶ Y) (g : Y ⟶ Z) (r : ℤ) (i : Tridegree) :
    familyPageMap D.family f r i ≫ familyPageMap D.family g r i = familyPageMap D.family (f ≫ g) r i := by
  classical
  rw [alpha_exists_from_finite_frames_family_map_data,alpha_exists_from_finite_frames_family_map_data,alpha_exists_from_finite_frames_family_map_data,Functor.map_comp]
  exact (SSDataMorphism.pageMap_comp _ _ _ _).symm


private theorem alpha_exists_from_finite_frames_family_infinity_representative_map {D : AdamsComparison H M Syn}
    {X Y : Syn} (f : X ⟶ Y) (i : Tridegree)
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
  · rw [alpha_exists_from_finite_frames_family_map_data]
    have h := F.cycleMap_ofLE_assoc i (show (0:WithTop ℕ)≤⊤ from le_top)
      (((D.family.obj Y).sequence.ssData i).pageπ 0)
    dsimp only [SyntheticAdamsFamily.obj] at h
    rw [←F.pageπ_pageMap] at h
    exact (congrArg (fun a => a z) h).symm.trans (by
      simpa only [ModuleCat.comp_apply,CategoryTheory.comp_apply] using congrArg (fun q => F.pageMap i 0 q) hz)
  · exact (congrArg (fun a => a z) (F.pageπ_pageMap i ⊤)).symm.trans (by
      change F.pageMap i ⊤ (((D.family.obj X).sequence.ssData i).pageπ ⊤ z)=_
      rw [he])


private theorem alpha_exists_from_finite_frames_sphere_quotient_label_to_nu {D : AdamsComparison H M Syn} (q k : ℕ) (s t : ℤ)
    (x : E2 H SphereSpectrum s t) :
    familyPageMap D.family (XModLambdaN.map D.nu.unitIso.inv q) 2 (s,t,t-k)
      (D.quotientLabel q s t k x) = finiteTargetLabel D .sphere q s t k x := by
  classical
  let nx : (D.family.obj ((SyntheticCategory.biShift (0,0)).obj
      (D.nu.functor.obj SphereSpectrum))).E₂ (s,t,t-k) := by
    simpa only [ClassicalObject.obj,add_zero] using D.nuE2 .sphere 0 s t k x
  let f := XModLambdaN.map D.nu.unitIso.inv q
  have hbase : familyPageMap D.family D.nu.unitIso.inv 2 (s,t,t-k) (D.sphereE2 s t k x)=
      targetNuLabel D .sphere s t k x := by
    have hc : familyPageMap D.family
        (SyntheticCategory.biShift_zero.hom.app _ ≫ D.nu.unitIso.hom) 2 (s,t,t-k) nx =
        D.sphereE2 s t k x := by
      convert D.comparisonCompatible.sphere_nu s t k x using 1; simp [nx,ClassicalObject.obj]
    calc
      _ = familyPageMap D.family D.nu.unitIso.inv 2 (s,t,t-k)
          (familyPageMap D.family (SyntheticCategory.biShift_zero.hom.app _ ≫ D.nu.unitIso.hom) 2 (s,t,t-k)
            nx) := congrArg (fun y => familyPageMap D.family D.nu.unitIso.inv 2 (s,t,t-k) y) hc.symm
      _ = familyPageMap D.family ((SyntheticCategory.biShift_zero.hom.app _ ≫ D.nu.unitIso.hom) ≫ D.nu.unitIso.inv)
          2 (s,t,t-k) nx :=
        ConcreteCategory.congr_hom (alpha_exists_from_finite_frames_family_page_comp (D:=D) (SyntheticCategory.biShift_zero.hom.app _ ≫ D.nu.unitIso.hom) D.nu.unitIso.inv 2 (s,t,t-k)) nx
      _ = targetNuLabel D .sphere s t k x := by
        simp only [Category.assoc,Iso.hom_inv_id,Category.comp_id]
        dsimp only [targetNuLabel]
        congr 1
  have hlabel : familyPageMap D.family f 2 (s,t,t-k) (D.quotientLabel q s t k x)=
      finiteTargetLabel D .sphere q s t k x := by
    calc
      _ = familyPageMap D.family (XModLambdaN.incl (S_0_0 : Syn) q ≫ XModLambdaN.map D.nu.unitIso.inv q)
          2 (s,t,t-k) (D.sphereE2 s t k x) :=
        ConcreteCategory.congr_hom (alpha_exists_from_finite_frames_family_page_comp (D:=D) (XModLambdaN.incl (S_0_0 : Syn) q) (XModLambdaN.map D.nu.unitIso.inv q) 2 (s,t,t-k)) (D.sphereE2 s t k x)
      _ = familyPageMap D.family (D.nu.unitIso.inv ≫ XModLambdaN.incl (D.nu.functor.obj SphereSpectrum) q)
          2 (s,t,t-k) (D.sphereE2 s t k x) := by rw [XModLambdaN.incl_naturality]; rfl
      _ = familyPageMap D.family (XModLambdaN.incl (D.nu.functor.obj SphereSpectrum) q) 2 (s,t,t-k)
          (familyPageMap D.family D.nu.unitIso.inv 2 (s,t,t-k) (D.sphereE2 s t k x)) :=
        (ConcreteCategory.congr_hom (alpha_exists_from_finite_frames_family_page_comp (D:=D) D.nu.unitIso.inv (XModLambdaN.incl (D.nu.functor.obj SphereSpectrum) q) 2 (s,t,t-k)) (D.sphereE2 s t k x)).symm
      _ = finiteTargetLabel D .sphere q s t k x := congrArg
        (fun y => familyPageMap D.family (XModLambdaN.incl (D.nu.functor.obj SphereSpectrum) q) 2 (s,t,t-k) y) hbase
  exact hlabel


private theorem alpha_exists_from_finite_frames_detection_exists_of_infinity {D : AdamsComparison H M Syn}
    {X : Syn} (c : TowerConvergence (nuCoefficientUnit H.unit D.nu) D.family X)
    (i : Tridegree) (x : (D.family.obj X).E₂ i)
    (e : ((D.family.obj X).sequence.ssData i).eInfty)
    (hx : HasInfinityRepresentative (D.family.obj X) 2 i x e) (hne : e≠0) :
    ∃ a : BiHom (i.2.1-i.1) i.2.2 X, DetectsNonzero c i x a := by
  classical
  let F := towerFiltration (nuCoefficientUnit H.unit D.nu) X
  haveI : Epi (F.toAssociatedGraded i.1 (i.2.1-i.1,i.2.2)) := inferInstanceAs (Epi (cokernel.π _))
  obtain ⟨a,ha⟩ := (ModuleCat.epi_iff_surjective (F.toAssociatedGraded i.1 (i.2.1-i.1,i.2.2))).mp
    inferInstance ((c.identification i).hom e)
  exact ⟨(F.F i.1 (i.2.1-i.1,i.2.2)).arrow a,⟨e,hx,a,rfl,ha.symm⟩,e,hx,hne⟩


private theorem alpha_exists_from_finite_frames_finite_sphere_detection_exists {D : AdamsComparison H M Syn}
    (BHS : EInftyComparison D) (q : ℕ) (hq : 0<q) (s t : ℤ)
    (x : E2 H SphereSpectrum s t)
    (hx : x∈PageRepresentatives.cycles H SphereSpectrum q (s,t)) (hne : x≠0) :
    ∃ a : BiHom (t-s) (t-0) (XModLambdaN (S_0_0 : Syn) q), FiniteDetected D q hq s t 0 x a := by
  classical
  let P := BHS.presentation.finiteWindow SphereSpectrum q hq (s,t) (t-0)
    (by constructor <;> omega)
  let y : PageRepresentatives.cycles H SphereSpectrum ((q:ℤ)-t+(t-0)) (s,t) :=
    ⟨x,by simpa only [sub_zero,sub_add_cancel] using hx⟩
  let e := P.symm (NestedQuotient.projection _ _ y)
  have he : HasInfinityRepresentative (D.family.nuQuotient D.nu SphereSpectrum q) 2 (s,t,t-0)
      (finiteTargetLabel D .sphere q s t 0 x) e := by
    apply (BHS.labels.1 .sphere q hq (s,t) 0 hq y e).mpr
    exact P.apply_symm_apply _
  have en : e≠0 := by
    intro hz
    have hp := congrArg P hz
    change P (P.symm _)=P 0 at hp
    rw [P.apply_symm_apply,map_zero] at hp
    have hm := (NestedQuotient.projection_eq_zero y).mp hp
    have hb : (1:ℤ)+t-(t-0)=1 := by omega
    change x∈PageRepresentatives.boundaries H SphereSpectrum (1+t-(t-0)) (s,t) at hm
    rw [hb,PageRepresentatives.boundaries_one,Submodule.mem_bot] at hm
    exact hne hm
  let f := XModLambdaN.map D.nu.unitIso.hom q
  let g := XModLambdaN.map D.nu.unitIso.inv q
  have hgf : g≫f=𝟙 _ := by
    dsimp only [f,g]
    rw [←D.quotientFunctoriality.map_comp,Iso.inv_hom_id,D.quotientFunctoriality.map_id]
  have hfg : f≫g=𝟙 _ := by
    dsimp only [f,g]
    rw [←D.quotientFunctoriality.map_comp,Iso.hom_inv_id,D.quotientFunctoriality.map_id]
  let e' := (D.family.functor.map f).eInftyMap (s,t,t-0) e
  have hel : familyPageMap D.family f 2 (s,t,t-0) (finiteTargetLabel D .sphere q s t 0 x)=D.quotientLabel q s t 0 x := by
    rw [←alpha_exists_from_finite_frames_sphere_quotient_label_to_nu (D:=D) q 0 s t x]
    calc
      _ = familyPageMap D.family (g≫f) 2 (s,t,t-0) (D.quotientLabel q s t 0 x) :=
        ConcreteCategory.congr_hom (alpha_exists_from_finite_frames_family_page_comp (D:=D) g f 2 (s,t,t-0)) _
      _ = D.quotientLabel q s t 0 x := by
        rw [hgf,alpha_exists_from_finite_frames_family_map_data,CategoryTheory.Functor.map_id]
        exact ConcreteCategory.congr_hom (SSDataMorphism.pageMap_id
          (D.family.functor.obj (XModLambdaN (S_0_0 : Syn) q)).ssData (s,t,t-0) ↑(2-2:ℤ).toNat) _
  have he' : HasInfinityRepresentative (D.family.quotient (S_0_0 : Syn) q) 2 (s,t,t-0)
      (D.quotientLabel q s t 0 x) e' := by
    have hh := alpha_exists_from_finite_frames_family_infinity_representative_map f (s,t,t-0) _ _ he
    rw [hel] at hh
    exact hh
  have en' : e'≠0 := by
    intro hz
    apply en
    have hh := congrArg (fun a=>(D.family.functor.map g).eInftyMap (s,t,t-0) a) hz
    change ((D.family.functor.map f).eInftyMap (s,t,t-0) ≫ (D.family.functor.map g).eInftyMap (s,t,t-0)) e=_ at hh
    rw [←SpectralSequenceMorphism.eInftyMap_comp,←Functor.map_comp,hfg,
      CategoryTheory.Functor.map_id,SpectralSequenceMorphism.eInftyMap_id] at hh
    simpa only [ConcreteCategory.id_apply,map_zero] using hh
  exact alpha_exists_from_finite_frames_detection_exists_of_infinity (D:=D) (D.quotientConvergence q hq) (s,t,t-0) _ e' he' en'


private theorem alpha_exists_from_finite_frames_detected_map {D : AdamsComparison H M Syn}
    (X Y : SyntheticObject) (f : X.obj D.nu D.hopfAndDetector ⟶ Y.obj D.nu D.hopfAndDetector)
    (i : Tridegree) (x : (D.family.obj (X.obj D.nu D.hopfAndDetector)).E₂ i)
    (a : BiHom (i.2.1-i.1) i.2.2 (X.obj D.nu D.hopfAndDetector))
    (ha : Detects (D.convergence X) i x a) :
    Detects (D.convergence Y) i (familyPageMap D.family f 2 i x) (a≫f) := by
  classical
  obtain ⟨c,hca,hce⟩ := D.comparisonCompatible.convergence_natural X Y f
  obtain ⟨e,he,a',ha',hgr⟩ := ha
  let F := towerFiltration (nuCoefficientUnit H.unit D.nu) (X.obj D.nu D.hopfAndDetector)
  let G := towerFiltration (nuCoefficientUnit H.unit D.nu) (Y.obj D.nu D.hopfAndDetector)
  let m := (i.2.1-i.1,i.2.2)
  let k := (c.filtration_compat i.1 m).choose
  have hk : k≫(G.F i.1 m).arrow=(F.F i.1 m).arrow≫syntheticHomotopyMap f m := by
    have hh := (c.filtration_compat i.1 m).choose_spec
    change k≫(G.F i.1 m).arrow=(F.F i.1 m).arrow≫c.aMap m at hh
    rw [hca] at hh
    exact hh
  have hc : c.eMap i ≫ ((D.convergence Y).identification i).hom =
      ((D.convergence X).identification i).hom ≫ Filtration.inducedAssocGradedMap c.aMap c.filtration_compat i.1 m := by
    have hh := c.iso_compat i
    simpa only [KIP126.SpectralSequence.Filtration.transportGraded_self,Category.comp_id,TowerConvergence.toSynthetic,SyntheticAdamsConvergence.toConvergence] using hh
  have hq : F.toAssociatedGraded i.1 m ≫
      Filtration.inducedAssocGradedMap c.aMap c.filtration_compat i.1 m =
      k≫G.toAssociatedGraded i.1 m := by
    exact cokernel.π_desc _ _ _
  refine ⟨(D.family.functor.map f).eInftyMap i e,alpha_exists_from_finite_frames_family_infinity_representative_map f i x e he,k a',?_,?_⟩
  · have hh := ConcreteCategory.congr_hom hk a'
    change (G.F i.1 m).arrow (k a')=((F.F i.1 m).arrow a')≫f at hh
    change (F.F i.1 m).arrow a'=a at ha'
    rw [ha'] at hh
    exact hh
  · have hh := ConcreteCategory.congr_hom hc e
    rw [hce] at hh
    change ((D.convergence Y).identification i).hom ((D.family.functor.map f).eInftyMap i e)=_
    calc
      _ = (Filtration.inducedAssocGradedMap c.aMap c.filtration_compat i.1 m)
          (((D.convergence X).identification i).hom e) := hh
      _ = (Filtration.inducedAssocGradedMap c.aMap c.filtration_compat i.1 m)
          (F.toAssociatedGraded i.1 m a') := by rw [hgr]
      _ = G.toAssociatedGraded i.1 m (k a') := ConcreteCategory.congr_hom hq a'


private theorem alpha_exists_from_finite_frames_finite_sphere_infinity_nonzero {D : AdamsComparison H M Syn}
    (BHS : EInftyComparison D) (q : ℕ) (hq : 0<q) (s t : ℤ)
    (x : E2 H SphereSpectrum s t)
    (hx : x∈PageRepresentatives.cycles H SphereSpectrum q (s,t)) (hne : x≠0)
    (e : ((D.family.quotient (S_0_0 : Syn) q).sequence.ssData (s,t,t-0)).eInfty)
    (he : HasInfinityRepresentative (D.family.quotient (S_0_0 : Syn) q) 2 (s,t,t-0)
      (D.quotientLabel q s t 0 x) e) : e≠0 := by
  classical
  let g := XModLambdaN.map D.nu.unitIso.inv q
  have hh := alpha_exists_from_finite_frames_family_infinity_representative_map g (s,t,t-0) _ _ he
  have hl := alpha_exists_from_finite_frames_sphere_quotient_label_to_nu (D:=D) q 0 s t x
  change familyPageMap D.family g 2 (s,t,t-0) (D.quotientLabel q s t 0 x)=_ at hl
  rw [hl] at hh
  let y : PageRepresentatives.cycles H SphereSpectrum ((q:ℤ)-t+(t-0)) (s,t) :=
    ⟨x,by simpa only [sub_zero,sub_add_cancel] using hx⟩
  have hp := (BHS.labels.1 .sphere q hq (s,t) 0 hq y _).mp hh
  intro he0
  rw [he0,map_zero,map_zero] at hp
  have hm := (NestedQuotient.projection_eq_zero y).mp hp.symm
  have hb : (1:ℤ)+t-(t-0)=1 := by omega
  change x∈PageRepresentatives.boundaries H SphereSpectrum (1+t-(t-0)) (s,t) at hm
  rw [hb,PageRepresentatives.boundaries_one,Submodule.mem_bot] at hm
  exact hne hm


private theorem alpha_exists_from_finite_frames_finite_sphere_detected_rho {D : AdamsComparison H M Syn}
    (BHS : EInftyComparison D) (i j : ℕ) (hi : 0 < i) (hj : 0 < j) (hij : i ≤ j) (s t : ℤ)
    (x : E2 H SphereSpectrum s t)
    (hx : x∈PageRepresentatives.cycles H SphereSpectrum i (s,t)) (hne : x≠0)
    (a : BiHom (t-s) (t-0) (XModLambdaN (S_0_0 : Syn) j))
    (ha : FiniteDetected D j hj s t 0 x a) :
    FiniteDetected D i hi s t 0 x (a≫(D.quotientTower S_0_0).rho i j hij) := by
  classical
  let rho := (D.quotientTower S_0_0).rho i j hij
  have hl : familyPageMap D.family rho 2 (s,t,t-0) (D.quotientLabel j s t 0 x)=D.quotientLabel i s t 0 x := by
    change familyPageMap D.family rho 2 (s,t,t-0)
      (familyPageMap D.family (XModLambdaN.incl (S_0_0 : Syn) j) 2 (s,t,t-0) (D.sphereE2 s t 0 x))=_
    calc
      _ = familyPageMap D.family (XModLambdaN.incl (S_0_0 : Syn) j≫rho) 2 (s,t,t-0) (D.sphereE2 s t 0 x) :=
        ConcreteCategory.congr_hom (alpha_exists_from_finite_frames_family_page_comp (D:=D) (XModLambdaN.incl (S_0_0 : Syn) j) rho 2 (s,t,t-0)) _
      _ = D.quotientLabel i s t 0 x := by
        dsimp only [rho]
        rw [FiniteLambdaQuotientTower.rho_quotient]
        rfl
  have hd := alpha_exists_from_finite_frames_detected_map (D:=D) (.quotient j .sphere) (.quotient i .sphere) rho (s,t,t-0) _ a ha.1
  have hd' : Detects (D.quotientConvergence i hi) (s,t,t-0)
      (D.quotientLabel i s t 0 x) (a≫rho) := hl ▸ hd
  refine ⟨hd',?_⟩
  obtain ⟨e,he,_⟩ := hd'
  exact ⟨e,he,alpha_exists_from_finite_frames_finite_sphere_infinity_nonzero BHS i hi s t x hx hne e he⟩


private theorem alpha_exists_from_finite_frames_alpha_one_detected_pair {D : AdamsComparison H M Syn}
    (BHS : EInftyComparison D) (V : E2 H SphereSpectrum 9 132)
    (hV : SurvivesTo (adamsTowerInternalSpectralSequence H.unit SphereSpectrum) 12 (9,132) V) :
    ∃ a : BiHom 123 132 (XModLambdaN (S_0_0 : Syn) 11),
      FiniteDetected D 11 (by decide) 9 132 0 V a ∧
      FiniteDetected D 9 (by decide) 9 132 0 V (a≫(D.quotientTower S_0_0).rho 9 11 (by decide)) := by
  classical
  obtain ⟨v,hv,hvn⟩ := hV
  have hc : V∈PageRepresentatives.cycles H SphereSpectrum 11 (9,132) :=
    ((PageRepresentatives.isCycle_iff_represents H SphereSpectrum 12 (by decide) (9,132) V).mpr ⟨v,hv⟩).2
  have hn : V≠0 := by
    intro h0
    rw [h0] at hv
    obtain ⟨_,z,hz,hzv⟩ := hv
    let P := (adamsTowerInternalSpectralSequence H.unit SphereSpectrum).ssData (9,132)
    have hm := (subobject_cokernel_π_eq_zero_iff (P.B 0) (P.Z 0) (P.B_le_Z 0)
      ((Subobject.ofLE (P.Z 10) (P.Z 0) (P.Z_anti (by decide))) z)).mp hz
    apply hvn
    rw [←hzv]
    apply (subobject_cokernel_π_eq_zero_iff (P.B 10) (P.Z 10) (P.B_le_Z 10) z).mpr
    change (Subobject.ofLE (P.Z 10) (P.Z 0) _ ≫ (P.Z 0).arrow) z ∈ _ at hm
    rw [Subobject.ofLE_arrow] at hm
    exact (ModuleCat.subobjectModule P.V).monotone (P.B_mono (by decide : (0:WithTop ℕ)≤10)) hm
  obtain ⟨a,ha⟩ := alpha_exists_from_finite_frames_finite_sphere_detection_exists BHS 11 (by decide) 9 132 V hc hn
  refine ⟨a,ha,?_⟩
  apply alpha_exists_from_finite_frames_finite_sphere_detected_rho BHS 9 11 (by decide) (by decide) (by decide) 9 132 V _ hn a ha
  exact PageRepresentatives.cycles_antitone H SphereSpectrum (9,132) (by decide : (9:ℤ)≤11) hc


private theorem alpha_exists_from_finite_frames_finite_detection_peel {D : AdamsComparison H M Syn}
    (q : ℕ) (hq : 0<q) (i : Tridegree)
    (x : (D.family.quotient (S_0_0 : Syn) q).E₂ i)
    (hframe : ∀ e : ((D.family.quotient (S_0_0 : Syn) q).sequence.ssData i).eInfty,
      e=0 ∨ HasInfinityRepresentative (D.family.quotient (S_0_0 : Syn) q) 2 i x e)
    (c : BiHom (i.2.1-i.1) i.2.2 (XModLambdaN (S_0_0 : Syn) q))
    (hc : Detects (D.quotientConvergence q hq) i x c)
    (a : BiHom (i.2.1-i.1) i.2.2 (XModLambdaN (S_0_0 : Syn) q))
    (ha : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) i.1 a) :
    ∃ b : Bool, FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) (i.1+1)
      (a-(if b then c else 0)) := by
  classical
  let F := towerFiltration (nuCoefficientUnit H.unit D.nu) (XModLambdaN (S_0_0 : Syn) q)
  have ham : a ∈ (ModuleCat.subobjectModule
      (syntheticHomotopy (XModLambdaN (S_0_0 : Syn) q) (i.2.1-i.1,i.2.2)))
      (F.F i.1 (i.2.1-i.1,i.2.2)) := by
    simpa only [F,towerFiltration,OrderIso.apply_symm_apply,FiltrationAtLeast] using ha
  obtain ⟨a',ha'⟩ := ham
  let gr := F.toAssociatedGraded i.1 (i.2.1-i.1,i.2.2) a'
  let e := ((D.quotientConvergence q hq).identification i).inv gr
  have he : ((D.quotientConvergence q hq).identification i).hom e=gr :=
    ConcreteCategory.congr_hom ((D.quotientConvergence q hq).identification i).inv_hom_id gr
  rcases hframe e with he0|hex
  · refine ⟨false,?_⟩
    simp only [Bool.false_eq_true,↓reduceIte,sub_zero]
    have hzero : Detects (D.quotientConvergence q hq) i 0 a := by
      refine ⟨0,HasInfinityRepresentative.zero _ 2 (by decide) i,a',ha',?_⟩
      rw [he0] at he
      exact he
    exact detects_zero_filtration (D.quotientConvergence q hq) i hzero
  · refine ⟨true,?_⟩
    simp only [↓reduceIte]
    have hax : Detects (D.quotientConvergence q hq) i x a := ⟨e,hex,a',ha',he⟩
    exact detects_sub_filtration (D.quotientConvergence q hq) i hax hc


private theorem alpha_exists_from_finite_frames_sphere_lift_finite_detection {D : AdamsComparison H M Syn}
    (q : ℕ) (hq : 0<q) (k : ℕ) (s t : ℤ)
    (x : E2 H SphereSpectrum s t) (c : BiHom (t-s) t (S_0_0 : Syn))
    (hc : D.sphereFirstQuotient s t (quotientClass 1 c)=x) :
    Detects (D.quotientConvergence q hq) (s,t,t-k) (D.quotientLabel q s t k x)
      (lambdaMultiply k (quotientClass q c)) := by
  classical
  have h := D.comparisonCompatible.homotopy_lambda s t k c
  rw [hc] at h
  have hh := alpha_exists_from_finite_frames_detected_map (D:=D) .sphere (.quotient q .sphere)
    (XModLambdaN.incl (S_0_0 : Syn) q) (s,t,t-k) _ (lambdaMultiply k c) h
  change Detects (D.quotientConvergence q hq) (s,t,t-k) (D.quotientLabel q s t k x)
    (lambdaMultiply k c≫XModLambdaN.incl (S_0_0 : Syn) q) at hh
  have hcomm : lambdaMultiply k c≫XModLambdaN.incl (S_0_0 : Syn) q =
      lambdaMultiply k (quotientClass q c) := by
    simp only [lambdaMultiply,quotientClass,Category.assoc]
  rw [hcomm] at hh
  exact hh


private theorem alpha_exists_from_finite_frames_sphere_quotient_high_filtration_zero {D : AdamsComparison H M Syn} (BHS : EInftyComparison D)
    (q : ℕ) (hq : 0<q) (m w : ℤ) (N : ℕ) (hN : (q:ℤ)≤m+N-w)
    (z : BiHom m w (XModLambdaN (S_0_0 : Syn) q))
    (hz : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) N z) : z=0 := by
  classical
  let O : SyntheticObject := .quotient q .sphere
  have hsep : ∀ z : BiHom m w (O.obj D.nu D.hopfAndDetector),
      (∀ j : ℕ, FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) j z) → z=0 :=
    D.homotopySeparated O m w
  refine (D.convergence O).eq_zero_of_eInfty_isZero_ge N m w hsep ?_ z hz
  intro j hj
  let i : Tridegree := (j,m+j,w)
  let f := XModLambdaN.map D.nu.unitIso.hom q
  let g := XModLambdaN.map D.nu.unitIso.inv q
  have hgf : g≫f=𝟙 _ := by
    dsimp only [f,g]
    rw [←D.quotientFunctoriality.map_comp,Iso.inv_hom_id,D.quotientFunctoriality.map_id]
  let P := BHS.presentation.finite SphereSpectrum q hq ((j:ℤ),m+j) w
  have hh : ¬(0≤m+j-w ∧ m+j-w<q) := by omega
  haveI : Subsingleton (PageRepresentatives.finiteEInftyModel H SphereSpectrum q ((j:ℤ),m+j) w) := by
    dsimp only [PageRepresentatives.finiteEInftyModel]
    rw [if_neg hh]
    infer_instance
  apply ModuleCat.isZero_iff_subsingleton.mpr
  apply subsingleton_of_forall_eq 0
  intro e
  have he : (D.family.functor.map g).eInftyMap i e=0 :=
    P.injective (Subsingleton.elim _ _)
  have h := congrArg (fun a=>(D.family.functor.map f).eInftyMap i a) he
  change ((D.family.functor.map g).eInftyMap i ≫ (D.family.functor.map f).eInftyMap i) e=_ at h
  rw [←SpectralSequenceMorphism.eInftyMap_comp,←Functor.map_comp,hgf,
    CategoryTheory.Functor.map_id,SpectralSequenceMorphism.eInftyMap_id] at h
  simpa only [ConcreteCategory.id_apply,map_zero] using h


private theorem alpha_exists_from_finite_frames_finite_sphere_frame {D : AdamsComparison H M Syn}
    (BHS : EInftyComparison D) (q k : ℕ) (hq : 0<q) (hkq : k<q) (s t : ℤ)
    (c : PageRepresentatives.cycles H SphereSpectrum ((q:ℤ)-t+(t-k)) (s,t))
    (hframe : ∀ y : PageRepresentatives.CycleQuotient H SphereSpectrum
        ((q:ℤ)-t+(t-k)) (1+t-(t-k)) (s,t),
      y=0 ∨ y=NestedQuotient.projection _ _ c) :
    ∀ e : ((D.family.quotient (S_0_0 : Syn) q).sequence.ssData (s,t,t-k)).eInfty,
      e=0 ∨ HasInfinityRepresentative (D.family.quotient (S_0_0 : Syn) q) 2 (s,t,t-k)
        (D.quotientLabel q s t k c.val) e := by
  classical
  intro e
  let P := BHS.presentation.finiteWindow SphereSpectrum q hq (s,t) (t-k)
    (by constructor <;> omega)
  let f := XModLambdaN.map D.nu.unitIso.hom q
  let g := XModLambdaN.map D.nu.unitIso.inv q
  have hgf : g≫f=𝟙 _ := by
    dsimp only [f,g]
    rw [←D.quotientFunctoriality.map_comp,Iso.inv_hom_id,D.quotientFunctoriality.map_id]
  have heq : (D.family.functor.map f).eInftyMap (s,t,t-k)
      ((D.family.functor.map g).eInftyMap (s,t,t-k) e)=e := by
    change ((D.family.functor.map g).eInftyMap (s,t,t-k) ≫
      (D.family.functor.map f).eInftyMap (s,t,t-k)) e=e
    rw [←SpectralSequenceMorphism.eInftyMap_comp,←Functor.map_comp,hgf,
      CategoryTheory.Functor.map_id,SpectralSequenceMorphism.eInftyMap_id]
    rfl
  rcases hframe (P ((D.family.functor.map g).eInftyMap (s,t,t-k) e)) with hz|hz
  · left
    have hzero : (D.family.functor.map g).eInftyMap (s,t,t-k) e=0 :=
      P.injective (hz.trans (map_zero P).symm)
    rw [hzero,map_zero] at heq
    exact heq.symm
  · right
    have hn := (BHS.labels.1 .sphere q hq (s,t) k hkq c _).mpr hz
    have hl : familyPageMap D.family f 2 (s,t,t-k)
        (finiteTargetLabel D .sphere q s t k c.val)=D.quotientLabel q s t k c.val := by
      rw [←alpha_exists_from_finite_frames_sphere_quotient_label_to_nu (D:=D) q k s t c.val]
      calc
        _ = familyPageMap D.family (g≫f) 2 (s,t,t-k) (D.quotientLabel q s t k c.val) :=
          ConcreteCategory.congr_hom (alpha_exists_from_finite_frames_family_page_comp (D:=D) g f 2 (s,t,t-k)) _
        _ = D.quotientLabel q s t k c.val := by
          rw [hgf,alpha_exists_from_finite_frames_family_map_data,CategoryTheory.Functor.map_id]
          exact ConcreteCategory.congr_hom (SSDataMorphism.pageMap_id
            (D.family.functor.obj (XModLambdaN (S_0_0 : Syn) q)).ssData
            (s,t,t-k) ↑(2-2:ℤ).toNat) _
    have h := alpha_exists_from_finite_frames_family_infinity_representative_map f (s,t,t-k) _ _ hn
    rw [hl,heq] at h
    exact h


private theorem alpha_exists_from_finite_frames_filtration_postcompose {D : AdamsComparison H M Syn} {X Y : Syn} (f : X⟶Y) (s m w : ℤ)
    (a : BiHom m w X) (ha : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) s a) :
    FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) s (a≫f) := by
  classical
  obtain ⟨b,hb⟩ := ha
  refine ⟨b≫adamsTowerInduced (nuCoefficientUnit H.unit D.nu) f s.toNat,?_⟩
  change (b≫adamsTowerInduced (nuCoefficientUnit H.unit D.nu) f s.toNat)≫
    adamsTowerMap (nuCoefficientUnit H.unit D.nu) Y 0 s.toNat _=a≫f
  change b≫adamsTowerMap (nuCoefficientUnit H.unit D.nu) X 0 s.toNat _=a at hb
  rw [Category.assoc,adamsTowerInduced_map,←Category.assoc,hb]
  rfl


private theorem alpha_exists_from_finite_frames_alpha_three_layer_restriction {D : AdamsComparison H M Syn}
    {L : SphereAdamsClasses H} {G : KIP126.Literature.AdamsSynthetic.TmfDetectionClasses H}
    (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G) (BHS : EInftyComparison D) (facts : Derived.SphereFacts I.interpretation)
    (h14 : I.interpretation.basis .sphere 14 138 2∈PageRepresentatives.cycles H SphereSpectrum 4 (14,138))
    (h15 : I.interpretation.basis .sphere 15 139 1+I.interpretation.basis .sphere 15 139 3∈PageRepresentatives.cycles H SphereSpectrum 3 (15,139))
    (c13 : BiHom 124 137 (S_0_0 : Syn))
    (hc13 : D.sphereFirstQuotient 13 137 (quotientClass 1 c13)=I.interpretation.sphere 13 137 correction)
    (c14 : BiHom 124 138 (S_0_0 : Syn))
    (hc14 : D.sphereFirstQuotient 14 138 (quotientClass 1 c14)=I.interpretation.basis .sphere 14 138 2)
    (c15 : BiHom 124 139 (S_0_0 : Syn))
    (hc15 : D.sphereFirstQuotient 15 139 (quotientClass 1 c15)=I.interpretation.basis .sphere 15 139 1+I.interpretation.basis .sphere 15 139 3)
    (z : BiHom 124 131 (XModLambdaN (S_0_0 : Syn) 11))
    (hz : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 13 z) :
    ∃ b13 b14 b15 : Bool,
      z≫(D.quotientTower S_0_0).rho 9 11 (by decide) =
      (if b13 then (show BiHom 124 131 (XModLambdaN (S_0_0 : Syn) 9) from lambdaMultiply 6 (quotientClass 9 c13)) else 0)+
      (if b14 then (show BiHom 124 131 (XModLambdaN (S_0_0 : Syn) 9) from lambdaMultiply 7 (quotientClass 9 c14)) else 0)+
      (if b15 then (show BiHom 124 131 (XModLambdaN (S_0_0 : Syn) 9) from lambdaMultiply 8 (quotientClass 9 c15)) else 0) := by
  classical
  obtain ⟨frame13,frame14a,frame15a⟩ := alpha_all_finite_frames I facts h14 h15
  obtain ⟨x13,hx13,frame13⟩ := frame13
  have frame13' := alpha_exists_from_finite_frames_finite_sphere_frame (D:=D) BHS 11 6 (by decide) (by decide) 13 137 x13 frame13
  rw [hx13] at frame13'
  have frame14 := alpha_exists_from_finite_frames_finite_sphere_frame (D:=D) BHS 11 7 (by decide) (by decide) 14 138
    ⟨I.interpretation.basis .sphere 14 138 2,h14⟩ frame14a
  have frame15 := alpha_exists_from_finite_frames_finite_sphere_frame (D:=D) BHS 11 8 (by decide) (by decide) 15 139
    ⟨I.interpretation.basis .sphere 15 139 1+I.interpretation.basis .sphere 15 139 3,h15⟩
    frame15a
  let v13 : BiHom 124 131 (XModLambdaN (S_0_0 : Syn) 11) := lambdaMultiply 6 (quotientClass 11 c13)
  let v14 : BiHom 124 131 (XModLambdaN (S_0_0 : Syn) 11) := lambdaMultiply 7 (quotientClass 11 c14)
  let v15 : BiHom 124 131 (XModLambdaN (S_0_0 : Syn) 11) := lambdaMultiply 8 (quotientClass 11 c15)
  obtain ⟨b13,hb13⟩ := alpha_exists_from_finite_frames_finite_detection_peel (D:=D) 11 (by decide) (13,137,131) _ frame13' v13
    (alpha_exists_from_finite_frames_sphere_lift_finite_detection (D:=D) 11 (by decide) 6 13 137 _ c13 hc13) z hz
  obtain ⟨b14,hb14⟩ := alpha_exists_from_finite_frames_finite_detection_peel (D:=D) 11 (by decide) (14,138,131) _ frame14 v14
    (alpha_exists_from_finite_frames_sphere_lift_finite_detection (D:=D) 11 (by decide) 7 14 138 _ c14 hc14) _ hb13
  obtain ⟨b15,hb15⟩ := alpha_exists_from_finite_frames_finite_detection_peel (D:=D) 11 (by decide) (15,139,131) _ frame15 v15
    (alpha_exists_from_finite_frames_sphere_lift_finite_detection (D:=D) 11 (by decide) 8 15 139 _ c15 hc15) _ hb14
  let rho := (D.quotientTower S_0_0).rho 9 11 (by decide)
  have hzero : (((z-(if b13 then v13 else 0))-(if b14 then v14 else 0))-(if b15 then v15 else 0))≫rho=0 := by
    apply alpha_exists_from_finite_frames_sphere_quotient_high_filtration_zero (D:=D) BHS 9 (by decide) 124 131 16 (by decide)
    exact alpha_exists_from_finite_frames_filtration_postcompose (D:=D) rho 16 124 131 _ hb15
  have hc (n : ℕ) (w : ℤ) (c : BiHom 124 w (S_0_0 : Syn)) :
      lambdaMultiply n (quotientClass 11 c)≫rho=lambdaMultiply n (quotientClass 9 c) := by
    simp only [lambdaMultiply,quotientClass,Category.assoc,rho,
      FiniteLambdaQuotientTower.rho_quotient]
  refine ⟨b13,b14,b15,?_⟩
  simp only [Preadditive.sub_comp,ite_comp,zero_comp,v13,v14,v15,hc] at hzero
  rw [sub_sub,sub_sub] at hzero
  simpa only [add_assoc] using (sub_eq_zero.mp hzero)


private theorem alpha_exists_from_finite_frames_detects_infinity_equal {D : AdamsComparison H M Syn}
    (X : SyntheticObject) (i : Tridegree)
    (a : BiHom (i.2.1-i.1) i.2.2 (X.obj D.nu D.hopfAndDetector))
    (x y : (D.family.obj (X.obj D.nu D.hopfAndDetector)).E₂ i)
    (ha : Detects (D.convergence X) i x a)
    (hb : Detects (D.convergence X) i y a) :
    ∃ e, HasInfinityRepresentative (D.family.obj (X.obj D.nu D.hopfAndDetector)) 2 i x e ∧
      HasInfinityRepresentative (D.family.obj (X.obj D.nu D.hopfAndDetector)) 2 i y e := by
  classical
  obtain ⟨e,he,a',ha',hga⟩ := ha
  obtain ⟨f,hf,b',hb',hgb⟩ := hb
  have hab : a'=b' := (ModuleCat.mono_iff_injective _).mp inferInstance (ha'.trans hb'.symm)
  have hef : e=f := (ModuleCat.mono_iff_injective _).mp inferInstance (by rw [hga,hgb,hab])
  exact ⟨e,he,hef.symm ▸ hf⟩


private theorem alpha_exists_from_finite_frames_sphere_zero_weight_label {D : AdamsComparison H M Syn}
    (BHS : EInftyComparison D) (x : E2 H SphereSpectrum 10 134)
    (a : BiHom (134-10) (134-0) (S_0_0 : Syn))
    (ha : Detects D.sphereConvergence (10,134,134-0) (D.sphereE2 10 134 0 x) a) :
    D.sphereFirstQuotient 10 134 (quotientClass 1 a)=x := by
  classical
  let y := D.sphereFirstQuotient 10 134 (quotientClass 1 a)
  have hd := alpha_exists_from_finite_frames_detected_map (D:=D) .sphere (.quotient 1 .sphere)
    (XModLambdaN.incl (S_0_0 : Syn) 1) (10,134,134-0) _ a ha
  have hd' := D.comparisonCompatible.first_quotient 10 134 y
  have hy : (D.sphereFirstQuotient 10 134).symm y=quotientClass 1 a := by
    exact (D.sphereFirstQuotient 10 134).symm_apply_apply _
  rw [hy] at hd'
  obtain ⟨e,he,hf⟩ := alpha_exists_from_finite_frames_detects_infinity_equal (.quotient 1 .sphere) (10,134,134-0)
    (quotientClass 1 a) _ _ hd hd'
  change HasInfinityRepresentative (D.family.quotient (S_0_0 : Syn) 1) 2 (10,134,134-0)
    (D.quotientLabel 1 10 134 0 x) e at he
  change HasInfinityRepresentative (D.family.quotient (S_0_0 : Syn) 1) 2 (10,134,134-0)
    (D.quotientLabel 1 10 134 0 y) e at hf
  let g := XModLambdaN.map D.nu.unitIso.inv 1
  have he' := alpha_exists_from_finite_frames_family_infinity_representative_map g (10,134,134-0) _ _ he
  have hf' := alpha_exists_from_finite_frames_family_infinity_representative_map g (10,134,134-0) _ _ hf
  have hlx := alpha_exists_from_finite_frames_sphere_quotient_label_to_nu (D:=D) 1 0 10 134 x
  have hly := alpha_exists_from_finite_frames_sphere_quotient_label_to_nu (D:=D) 1 0 10 134 y
  change familyPageMap D.family g 2 (10,134,134-0) (D.quotientLabel 1 10 134 0 x)=_ at hlx
  change familyPageMap D.family g 2 (10,134,134-0) (D.quotientLabel 1 10 134 0 y)=_ at hly
  rw [hlx] at he'
  rw [hly] at hf'
  let xx : PageRepresentatives.cycles H SphereSpectrum (1-134+(134-0)) (10,134) :=
    ⟨x,by simp only [sub_zero,sub_add_cancel,PageRepresentatives.cycles_one,Submodule.mem_top]⟩
  let yy : PageRepresentatives.cycles H SphereSpectrum (1-134+(134-0)) (10,134) :=
    ⟨y,by simp only [sub_zero,sub_add_cancel,PageRepresentatives.cycles_one,Submodule.mem_top]⟩
  have hxq := (BHS.labels.1 .sphere 1 (by decide) (10,134) 0 (by decide) xx _).mp he'
  have hyq := (BHS.labels.1 .sphere 1 (by decide) (10,134) 0 (by decide) yy _).mp hf'
  have heq := hxq.symm.trans hyq
  change NestedQuotient.projection _ (PageRepresentatives.boundaries H SphereSpectrum 1 (10,134)) xx =
    NestedQuotient.projection _ (PageRepresentatives.boundaries H SphereSpectrum 1 (10,134)) yy at heq
  have hz : NestedQuotient.projection _ (PageRepresentatives.boundaries H SphereSpectrum 1 (10,134)) (xx-yy)=0 := by rw [map_sub,heq,sub_self]
  have hm := (NestedQuotient.projection_eq_zero (xx-yy)).mp hz
  change x-y∈PageRepresentatives.boundaries H SphereSpectrum 1 (10,134) at hm
  have ht : 1+134-(134-0)=1 := by omega
  change x-y∈PageRepresentatives.boundaries H SphereSpectrum 1 (10,134) at hm
  rw [PageRepresentatives.boundaries_one,Submodule.mem_bot] at hm
  exact (sub_eq_zero.mp hm).symm


private theorem alpha_exists_from_finite_frames_finite_boundary_detects_sub_filtration {D : AdamsComparison H M Syn}
    (BHS : EInftyComparison D)
    (x y : E2 H SphereSpectrum 10 134)
    (hx : x∈PageRepresentatives.cycles H SphereSpectrum 8 (10,134))
    (hy : y∈PageRepresentatives.cycles H SphereSpectrum 8 (10,134))
    (hxy : x-y∈PageRepresentatives.boundaries H SphereSpectrum 4 (10,134))
    (a b : BiHom 124 131 (XModLambdaN (S_0_0 : Syn) 11))
    (ha : Detects (D.quotientConvergence 11 (by decide)) (10,134,131)
      (D.quotientLabel 11 10 134 3 x) a)
    (hb : Detects (D.quotientConvergence 11 (by decide)) (10,134,131)
      (D.quotientLabel 11 10 134 3 y) b) :
    FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 11 (a-b) := by
  classical
  obtain ⟨e,he,a',ha',hga⟩ := ha
  obtain ⟨f,hf,b',hb',hgb⟩ := hb
  let g := XModLambdaN.map D.nu.unitIso.inv 11
  have he' := alpha_exists_from_finite_frames_family_infinity_representative_map g (10,134,131) _ _ he
  have hf' := alpha_exists_from_finite_frames_family_infinity_representative_map g (10,134,131) _ _ hf
  have hlx := alpha_exists_from_finite_frames_sphere_quotient_label_to_nu (D:=D) 11 3 10 134 x
  have hly := alpha_exists_from_finite_frames_sphere_quotient_label_to_nu (D:=D) 11 3 10 134 y
  change familyPageMap D.family g 2 (10,134,131) (D.quotientLabel 11 10 134 3 x)=_ at hlx
  change familyPageMap D.family g 2 (10,134,131) (D.quotientLabel 11 10 134 3 y)=_ at hly
  rw [hlx] at he'
  rw [hly] at hf'
  let xx : PageRepresentatives.cycles H SphereSpectrum (11-134+(134-3)) (10,134) := ⟨x,hx⟩
  let yy : PageRepresentatives.cycles H SphereSpectrum (11-134+(134-3)) (10,134) := ⟨y,hy⟩
  have hxq := (BHS.labels.1 .sphere 11 (by decide) (10,134) 3 (by decide) xx _).mp he'
  have hyq := (BHS.labels.1 .sphere 11 (by decide) (10,134) 3 (by decide) yy _).mp hf'
  have hz : NestedQuotient.projection _ (PageRepresentatives.boundaries H SphereSpectrum 4 (10,134)) (xx-yy)=0 :=
    (NestedQuotient.projection_eq_zero (xx-yy)).mpr hxy
  rw [map_sub] at hz
  have heq := sub_eq_zero.mp hz
  have hge : (D.family.functor.map g).eInftyMap (10,134,131) e=
      (D.family.functor.map g).eInftyMap (10,134,131) f := by
    apply (BHS.presentation.finiteWindow SphereSpectrum 11 (by decide) (10,134) 131 (by decide)).injective
    change BHS.presentation.finiteWindow SphereSpectrum 11 (by decide) (10,134) 131 (by decide)
      ((D.family.functor.map g).eInftyMap (10,134,131) e) =
      NestedQuotient.projection _ (PageRepresentatives.boundaries H SphereSpectrum 4 (10,134)) xx at hxq
    change BHS.presentation.finiteWindow SphereSpectrum 11 (by decide) (10,134) 131 (by decide)
      ((D.family.functor.map g).eInftyMap (10,134,131) f) =
      NestedQuotient.projection _ (PageRepresentatives.boundaries H SphereSpectrum 4 (10,134)) yy at hyq
    exact hxq.trans (heq.trans hyq.symm)
  let h := (D.family.functor.map (XModLambdaN.map D.nu.unitIso.hom 11)).eInftyMap (10,134,131)
  have hgh : (D.family.functor.map g).eInftyMap (10,134,131) ≫ h=𝟙 _ := by
    dsimp only [g,h]
    rw [←SpectralSequenceMorphism.eInftyMap_comp,←Functor.map_comp,
      ←D.quotientFunctoriality.map_comp,D.nu.unitIso.inv_hom_id,
      D.quotientFunctoriality.map_id,CategoryTheory.Functor.map_id,SpectralSequenceMorphism.eInftyMap_id]
  have hef : e=f := by
    have he0 := ConcreteCategory.congr_hom hgh e
    have hf0 := ConcreteCategory.congr_hom hgh f
    change h ((D.family.functor.map g).eInftyMap (10,134,131) e)=e at he0
    change h ((D.family.functor.map g).eInftyMap (10,134,131) f)=f at hf0
    exact he0.symm.trans ((congrArg h hge).trans hf0)
  apply detects_sub_filtration (D.quotientConvergence 11 (by decide)) (10,134,131)
    (show Detects _ _ (D.quotientLabel 11 10 134 3 x) a from ⟨e,he,a',ha',hga⟩)
  exact ⟨e,he,b',hb',hef ▸ hgb⟩


private def alpha_exists_from_finite_frames_shiftSwap (a b : ℤ × ℤ) (A : Syn) :
    (SyntheticCategory.biShift b).obj ((SyntheticCategory.biShift a).obj A) ≅
    (SyntheticCategory.biShift a).obj ((SyntheticCategory.biShift b).obj A) :=
  (biShiftAddIso a b (a+b) rfl).app A ≪≫
    ((biShiftAddIso b a (a+b) (add_comm _ _)).app A).symm


omit [HasFunctorialCofiber (C := Syn)] in
private theorem alpha_exists_from_finite_frames_shiftSwap_add (coh : BiShiftCoherence Syn)
    (a b c : ℤ × ℤ) (A : Syn) :
    (alpha_exists_from_finite_frames_shiftSwap a (b+c) A).hom ≫
      (SyntheticCategory.biShift a).map ((biShiftAddIso b c (b+c) rfl).inv.app A) =
    (biShiftAddIso b c (b+c) rfl).inv.app ((SyntheticCategory.biShift a).obj A) ≫
      (SyntheticCategory.biShift c).map (alpha_exists_from_finite_frames_shiftSwap a b A).hom ≫
      (alpha_exists_from_finite_frames_shiftSwap a c ((SyntheticCategory.biShift b).obj A)).hom := by
  classical
  let habc : (a+b)+c=a+(b+c) := add_assoc a b c
  let hbac : b+(a+c)=a+(b+c) := by abel
  have h₁ := coh.associativity a b c (a+b) (b+c) (a+(b+c)) rfl rfl habc rfl A
  have h₂ := coh.associativity b a c (a+b) (a+c) (a+(b+c))
    (add_comm _ _) rfl habc hbac A
  have h₃ := coh.associativity b c a (b+c) (a+c) (a+(b+c))
    rfl (add_comm _ _) (add_comm _ _) hbac A
  simp only [alpha_exists_from_finite_frames_shiftSwap,Iso.trans_hom,Iso.symm_hom,Iso.app_hom,Iso.app_inv]
  rw [Functor.map_comp]
  apply (cancel_epi ((biShiftAddIso b c (b+c) rfl).hom.app
    ((SyntheticCategory.biShift a).obj A))).mp
  simp only [Category.assoc,Iso.hom_inv_id_app_assoc]
  rw [← Category.assoc,← h₁]
  simp only [Category.assoc]
  apply (cancel_epi ((SyntheticCategory.biShift c).map
    ((biShiftAddIso a b (a+b) rfl).hom.app A))).mpr
  -- Cancel the common left factor introduced by the first associativity square.
  apply (cancel_epi ((SyntheticCategory.biShift c).map
    ((biShiftAddIso b a (a+b) (add_comm _ _)).hom.app A))).mp
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app,CategoryTheory.Functor.map_id,Category.id_comp]
  rw [← Category.assoc,h₂]
  simp only [Category.assoc]
  apply (cancel_epi ((biShiftAddIso a c (a+c) rfl).hom.app
    ((SyntheticCategory.biShift b).obj A))).mpr
  apply (cancel_epi ((biShiftAddIso c a (a+c) (add_comm _ _)).hom.app
    ((SyntheticCategory.biShift b).obj A))).mp
  rw [← Category.assoc,← Category.assoc,← h₃]
  simp only [Category.assoc,
    Iso.hom_inv_id_app]
  erw [CategoryTheory.Category.id_comp,←Functor.map_comp,Iso.hom_inv_id_app,CategoryTheory.Functor.map_id]
  rfl


omit [HasFunctorialCofiber (C := Syn)] in
private theorem alpha_exists_from_finite_frames_shiftSwap_add_eq (coh : BiShiftCoherence Syn)
    (a b c d : ℤ × ℤ) (h : b+c=d) (A : Syn) :
    (alpha_exists_from_finite_frames_shiftSwap a d A).hom ≫
      (SyntheticCategory.biShift a).map ((biShiftAddIso b c d h).inv.app A) =
    (biShiftAddIso b c d h).inv.app ((SyntheticCategory.biShift a).obj A) ≫
      (SyntheticCategory.biShift c).map (alpha_exists_from_finite_frames_shiftSwap a b A).hom ≫
      (alpha_exists_from_finite_frames_shiftSwap a c ((SyntheticCategory.biShift b).obj A)).hom := by
  classical
  subst d
  exact alpha_exists_from_finite_frames_shiftSwap_add coh a b c A


omit [HasFunctorialCofiber (C := Syn)] in
private theorem alpha_exists_from_finite_frames_shiftSwap_natural (a b : ℤ × ℤ) {A B : Syn} (f : A ⟶ B) :
    (SyntheticCategory.biShift b).map ((SyntheticCategory.biShift a).map f) ≫
      (alpha_exists_from_finite_frames_shiftSwap a b B).hom =
    (alpha_exists_from_finite_frames_shiftSwap a b A).hom ≫
      (SyntheticCategory.biShift a).map ((SyntheticCategory.biShift b).map f) := by
  classical
  exact ((biShiftAddIso a b (a+b) rfl) ≪≫
    (biShiftAddIso b a (a+b) (add_comm _ _)).symm).hom.naturality f


omit [HasFunctorialCofiber (C := Syn)] in
private theorem alpha_exists_from_finite_frames_shiftSwap_hom_eq (a b d : ℤ × ℤ)
    (hab : a+b=d) (hba : b+a=d) (A : Syn) :
    (alpha_exists_from_finite_frames_shiftSwap a b A).hom =
      (biShiftAddIso a b d hab).hom.app A ≫ (biShiftAddIso b a d hba).inv.app A := by
  classical
  subst d
  rfl


omit [HasFunctorialCofiber (C := Syn)] in
private theorem alpha_exists_from_finite_frames_lambda_pow_shift (coh : BiShiftCoherence Syn)
    (n : ℕ) (a : ℤ × ℤ) (A : Syn) :
    lambdaPow n ((SyntheticCategory.biShift a).obj A) =
      (alpha_exists_from_finite_frames_shiftSwap a (KIP126.Synthetic.Context.lambdaDegree n) A).hom ≫
        (SyntheticCategory.biShift a).map (lambdaPow n A) := by
  classical
  induction n generalizing A with
  | zero =>
    change SyntheticCategory.biShift_zero.hom.app ((SyntheticCategory.biShift a).obj A) =
      (alpha_exists_from_finite_frames_shiftSwap a 0 A).hom ≫
        (SyntheticCategory.biShift a).map (SyntheticCategory.biShift_zero.hom.app A)
    have h : SyntheticCategory.biShift_zero.hom.app ((SyntheticCategory.biShift a).obj A) =
        (biShiftAddIso a 0 a (add_zero a)).hom.app A ≫
          (biShiftAddIso 0 a a (zero_add a)).inv.app A ≫
            (SyntheticCategory.biShift a).map (SyntheticCategory.biShift_zero.hom.app A) := by
      rw [←coh.left_unit a A,Iso.inv_hom_id_app,Category.comp_id]
      exact (coh.right_unit a A).symm
    rw [alpha_exists_from_finite_frames_shiftSwap_hom_eq a 0 a (add_zero a) (zero_add a),Category.assoc]
    exact h
  | succ n ih =>
    have h1 : lambdaPow 1 ((SyntheticCategory.biShift a).obj A) =
        (alpha_exists_from_finite_frames_shiftSwap a (KIP126.Synthetic.Context.lambdaDegree 1) A).hom ≫
          (SyntheticCategory.biShift a).map (lambdaPow 1 A) := by
      rw [lambdaPow_one coh,lambdaPow_one coh]
      change SyntheticCategory.lam.app ((SyntheticCategory.biShift a).obj A) =
        (alpha_exists_from_finite_frames_shiftSwap a (0,-1) A).hom ≫ (SyntheticCategory.biShift a).map (SyntheticCategory.lam.app A)
      rw [alpha_exists_from_finite_frames_shiftSwap_hom_eq a (0,-1) (a+(0,-1)) rfl (add_comm _ _),Category.assoc]
      exact coh.lambda_comm a A
    have hn := alpha_exists_from_finite_frames_shiftSwap_natural a (KIP126.Synthetic.Context.lambdaDegree n) (lambdaPow 1 A)
    have hh := alpha_exists_from_finite_frames_shiftSwap_add_eq coh a (KIP126.Synthetic.Context.lambdaDegree 1) (KIP126.Synthetic.Context.lambdaDegree n)
      (KIP126.Synthetic.Context.lambdaDegree (n+1)) (by ext <;> simp [KIP126.Synthetic.Context.lambdaDegree]) A
    change (alpha_exists_from_finite_frames_shiftSwap a (KIP126.Synthetic.Context.lambdaDegree (n+1)) A).hom ≫
        (SyntheticCategory.biShift a).map ((lambdaShiftAddIso 1 n (n+1) (by omega)).inv.app A) =
      (lambdaShiftAddIso 1 n (n+1) (by omega)).inv.app ((SyntheticCategory.biShift a).obj A) ≫
        (SyntheticCategory.biShift (KIP126.Synthetic.Context.lambdaDegree n)).map (alpha_exists_from_finite_frames_shiftSwap a (KIP126.Synthetic.Context.lambdaDegree 1) A).hom ≫
        (alpha_exists_from_finite_frames_shiftSwap a (KIP126.Synthetic.Context.lambdaDegree n) ((SyntheticCategory.biShift (KIP126.Synthetic.Context.lambdaDegree 1)).obj A)).hom at hh
    rw [lambdaPow_add coh 1 n (n+1) (by omega) ((SyntheticCategory.biShift a).obj A),
      lambdaPow_add coh 1 n (n+1) (by omega) A,h1,ih]
    simp only [Functor.map_comp,Category.assoc]
    rw [reassoc_of% hn]
    rw [reassoc_of% hh]
    rfl


omit [HasFunctorialCofiber (C := Syn)] in
private theorem alpha_exists_from_finite_frames_shift_assoc_inv (coh : BiShiftCoherence Syn)
    (a b c ab bc total : ℤ × ℤ) (hab : a+b=ab) (hbc : b+c=bc)
    (habc : ab+c=total) (habc' : a+bc=total) (A : Syn) :
    (biShiftAddIso ab c total habc).inv.app A ≫
      (SyntheticCategory.biShift c).map ((biShiftAddIso a b ab hab).inv.app A) =
    (biShiftAddIso a bc total habc').inv.app A ≫
      (biShiftAddIso b c bc hbc).inv.app ((SyntheticCategory.biShift a).obj A) := by
  classical
  have he : ((SyntheticCategory.biShift c).mapIso ((biShiftAddIso a b ab hab).app A) ≪≫
      (biShiftAddIso ab c total habc).app A) =
    ((biShiftAddIso b c bc hbc).app ((SyntheticCategory.biShift a).obj A) ≪≫
      (biShiftAddIso a bc total habc').app A) :=
    Iso.ext (coh.associativity a b c ab bc total hab hbc habc habc' A)
  have hi := congrArg Iso.inv he
  exact hi


private theorem alpha_exists_from_finite_frames_sphere_action_lambda_three (D : AdamsComparison H M Syn)
    (η : BiHom 1 2 (S_0_0 : Syn))
    (a : BiHom 123 132 (XModLambdaN (S_0_0 : Syn) 11)) :
    sphereAction (lambdaMultiply 3 η) a = lambdaMultiply 3 (sphereAction η a) := by
  classical
  let S := (S_0_0 : Syn)
  have h₁ := alpha_exists_from_finite_frames_shift_assoc_inv D.shiftCoherence (1,2) (123,132) (0,-3)
    (124,134) (123,129) (124,131) (by decide) (by decide) (by decide) (by decide) S
  have h₂ := alpha_exists_from_finite_frames_shift_assoc_inv D.shiftCoherence (1,2) (0,-3) (123,132)
    (1,-1) (123,129) (124,131) (by decide) (by decide) (by decide) (by decide) S
  simp only [biShiftAddIso,Iso.trans_inv,eqToIso.inv,
    eqToHom_refl,Category.id_comp] at h₁ h₂
  have hp :
    (SyntheticCategory.biShift_comp (124,134) (0,-3)).inv.app S ≫
      lambdaPow 3 (Smn 124 134) ≫
      (SyntheticCategory.biShift_comp (1,2) (123,132)).inv.app S =
    (SyntheticCategory.biShift_comp (1,-1) (123,132)).inv.app S ≫
      (SyntheticCategory.biShift (123,132)).map
        ((SyntheticCategory.biShift_comp (1,2) (0,-3)).inv.app S) ≫
      (SyntheticCategory.biShift (123,132)).map (lambdaPow 3 (Smn 1 2)) := by
    rw [←lambdaPow_naturality]
    change (SyntheticCategory.biShift_comp (124,134) (0,-3)).inv.app S ≫
      (SyntheticCategory.biShift (0,-3)).map ((SyntheticCategory.biShift_comp (1,2) (123,132)).inv.app S) ≫
      lambdaPow 3 ((SyntheticCategory.biShift (123,132)).obj (Smn 1 2)) = _
    rw [alpha_exists_from_finite_frames_lambda_pow_shift D.shiftCoherence 3 (123,132) (Smn 1 2)]
    dsimp only [alpha_exists_from_finite_frames_shiftSwap,KIP126.Synthetic.Context.lambdaDegree]
    simp only [Iso.trans_hom,Iso.trans_inv,Iso.symm_hom,Iso.app_hom,Iso.app_inv,biShiftAddIso,eqToIso.hom,eqToIso.inv,eqToHom_refl,
      Category.comp_id,Category.id_comp]
    simp only [Category.assoc]
    erw [←Category.assoc ((SyntheticCategory.biShift_comp (124,134) (0,-3)).inv.app S)]
    erw [h₁]
    simp only [Category.assoc,Smn,S,Nat.cast_ofNat,Iso.inv_hom_id_app_assoc]
    simpa only [Category.assoc,Smn,S,Nat.cast_ofNat] using
      (congrArg (fun z => z ≫ (SyntheticCategory.biShift (123,132)).map (lambdaPow 3 (Smn 1 2))) h₂.symm)
  unfold sphereAction lambdaMultiply
  simp only [eqToHom_refl,Category.id_comp,Functor.map_comp,Category.assoc]
  simpa only [Category.assoc,S,Smn,Int.reduceAdd,Int.reduceSub,Nat.cast_ofNat] using
    (congrArg (fun z => z ≫ (SyntheticCategory.biShift (123,132)).map η ≫ a) hp).symm


private theorem alpha_exists_from_finite_frames_boundary_of_zero_representative {H : Mod2EilenbergMacLane (C:=C)}
    {r : ℤ} {p : ℤ×ℤ} {x : E2 H SphereSpectrum p.1 p.2}
    (hx : RepresentsOnPage (adamsTowerInternalSpectralSequence H.unit SphereSpectrum) r p x 0) :
    x ∈ boundaries H SphereSpectrum (r-1) p := by
  classical
  let E := adamsTowerInternalSpectralSequence H.unit SphereSpectrum
  let P := E.ssData p
  obtain ⟨hr,z,hz,hzero⟩ := hx
  change (Subobject.ofLE (P.Z ↑(r-2).toNat) (P.Z 0) _ ≫ P.pageπ 0) z=x at hz
  change P.pageπ ↑(r-2).toNat z=0 at hzero
  obtain ⟨y,hy⟩ := (cokernel_π_eq_zero_iff_mem_range
    (Subobject.ofLE (P.B ↑(r-2).toNat) (P.Z ↑(r-2).toNat) (P.B_le_Z _)) z).mp hzero
  have hrindex : r-1-1=r-2 := by omega
  change ∃ y, boundaryMap H SphereSpectrum ↑(r-1-1).toNat p y=x
  rw [hrindex]
  refine ⟨y,?_⟩
  have hf : Subobject.ofLE (P.B ↑(r-2).toNat) (P.Z ↑(r-2).toNat) (P.B_le_Z _) ≫
      cycleMap H SphereSpectrum ↑(r-2).toNat p = boundaryMap H SphereSpectrum ↑(r-2).toNat p := by
    dsimp only [boundaryMap,cycleMap,P,E]
    rw [←Category.assoc,Subobject.ofLE_comp_ofLE]
  rw [←hf,CategoryTheory.comp_apply,hy]
  exact hz


private theorem alpha_exists_from_finite_frames_cycle_quotient_zero_of_page {H : Mod2EilenbergMacLane (C:=C)}
    (r c b : ℤ) (p : ℤ×ℤ) (hr : 2≤r) (hc : r≤c+1) (hb : r-1≤b)
    (hz : Subsingleton ((adamsTowerInternalSpectralSequence H.unit SphereSpectrum).Page r p)) :
    Subsingleton (CycleQuotient H SphereSpectrum c b p) := by
  classical
  have hall (x : cycles H SphereSpectrum c p) : NestedQuotient.projection _ (boundaries H SphereSpectrum b p) x=0 := by
    obtain ⟨x',hx'⟩ := (isCycle_iff_represents H SphereSpectrum (c+1) (by omega) p x.val).mp ⟨by omega,by simp⟩
    obtain ⟨xr,hxr⟩ := represents_before hr hc hx'
    rw [hz.elim xr 0] at hxr
    exact (NestedQuotient.projection_eq_zero x).mpr
      (boundaries_monotone H SphereSpectrum p hb (alpha_exists_from_finite_frames_boundary_of_zero_representative hxr))
  have hz' (x : CycleQuotient H SphereSpectrum c b p) : x=0 := by
    obtain ⟨x⟩ := x
    exact hall x
  exact ⟨fun x y=>(hz' x).trans (hz' y).symm⟩


private theorem alpha_exists_from_finite_frames_alpha_error_filtration_gap {D : AdamsComparison H M Syn}
    (BHS : SyntheticComparisonTheorems D)
    (h11 : Subsingleton ((adamsTowerInternalSpectralSequence H.unit SphereSpectrum).Page 5 (11,135)))
    (h12 : Subsingleton ((adamsTowerInternalSpectralSequence H.unit SphereSpectrum).Page 4 (12,136)))
    (a : BiHom 124 131 (XModLambdaN (S_0_0 : Syn) 11)) :
    FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 11 a ↔
      FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 13 a := by
  classical
  apply (D.quotientConvergence 11 (by decide)).filtrationAtLeast_iff_of_eInfty_isZero
    11 13 124 131 (by decide)
  intro j hj hj'
  haveI : Subsingleton (PageRepresentatives.CycleQuotient H SphereSpectrum
      (11-(124+j)+131) (1+(124+j)-131) (j,124+j)) := by
    rw [show (11:ℤ)-(124+j)+131=18-j by omega,
      show (1:ℤ)+(124+j)-131=j-6 by omega,add_comm 124 j]
    have hjcases : j=11 ∨ j=12 := by omega
    rcases hjcases with rfl|rfl
    · exact alpha_exists_from_finite_frames_cycle_quotient_zero_of_page 5 7 5 (11,135) (by decide) (by decide) (by decide) h11
    · exact alpha_exists_from_finite_frames_cycle_quotient_zero_of_page 4 6 6 (12,136) (by decide) (by decide) (by decide) h12
  let e := BHS.eInfty.presentation.finiteWindow SphereSpectrum 11 (by decide) (j,124+j) 131
    (by constructor <;> omega)
  haveI : Subsingleton (((D.family.nuQuotient D.nu SphereSpectrum 11).sequence.ssData (j,124+j,131)).eInfty) :=
    e.injective.subsingleton
  let hn := ModuleCat.isZero_of_subsingleton
    (((D.family.nuQuotient D.nu SphereSpectrum 11).sequence.ssData (j,124+j,131)).eInfty)
  let f := (D.family.functor.map (XModLambdaN.map D.nu.unitIso.hom 11)).eInftyMap (j,124+j,131)
  let g := (D.family.functor.map (XModLambdaN.map D.nu.unitIso.inv 11)).eInftyMap (j,124+j,131)
  have hfg : g ≫ f=𝟙 _ := by
    dsimp only [f,g]
    rw [←SpectralSequenceMorphism.eInftyMap_comp,←Functor.map_comp,
      ←D.quotientFunctoriality.map_comp,D.nu.unitIso.inv_hom_id,
      D.quotientFunctoriality.map_id,CategoryTheory.Functor.map_id,SpectralSequenceMorphism.eInftyMap_id]
  apply (CategoryTheory.Limits.IsZero.iff_id_eq_zero _).mpr
  exact hfg.symm.trans (by rw [hn.eq_of_src f 0,CategoryTheory.Limits.comp_zero])


private theorem alpha_exists_from_finite_frames_alpha_error_filtration_thirteen {D : AdamsComparison H M Syn}
    (BHS : SyntheticComparisonTheorems D) (algebra : AdamsAlgebraStructures D) (compatibility : AlgebraDetectionCompatibility D algebra)
    (η : BiHom 1 2 (S_0_0 : Syn)) (hη : EtaChoice M D.toAdamsComparisonData η)
    (U : E2 H SphereSpectrum 10 134) (V : E2 H SphereSpectrum 9 132)
    (source : E2 H SphereSpectrum 8 133)
    (hU : U∈PageRepresentatives.cycles H SphereSpectrum 8 (10,134))
    (hd : HasDifferential (adamsTowerInternalSpectralSequence H.unit SphereSpectrum)
      2 (8,133) (10,134) source (Sphere.Internal.product H M (s:=1) (t:=2) (s':=9) (t':=132) (Sphere.Internal.hi H M 1) V + U))
    (h11 : Subsingleton ((adamsTowerInternalSpectralSequence H.unit SphereSpectrum).Page 5 (11,135)))
    (h12 : Subsingleton ((adamsTowerInternalSpectralSequence H.unit SphereSpectrum).Page 4 (12,136)))
    (a : BiHom 123 132 (XModLambdaN (S_0_0 : Syn) 11))
    (ha : FiniteDetected D 11 (by decide) 9 132 0 V a)
    (u : BiHom 124 134 (S_0_0 : Syn)) (hu : SphereDetected D 10 134 0 U u) :
    FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 13
      ((show BiHom 124 131 (XModLambdaN (S_0_0 : Syn) 11) from lambdaMultiply 3 (sphereAction η a))-
        (show BiHom 124 131 (XModLambdaN (S_0_0 : Syn) 11) from lambdaMultiply 3 (quotientClass 11 u))) := by
  classical
  have hlabel := alpha_exists_from_finite_frames_sphere_zero_weight_label BHS.eInfty U u hu.1
  have he := D.comparisonCompatible.homotopy_lambda 1 2 3 η
  change D.sphereFirstQuotient 1 2 (quotientClass 1 η)=Sphere.Internal.hi H M 1 at hη
  rw [hη] at he
  have hp : Detects (D.quotientConvergence 11 (by decide)) (10,134,131)
      (D.quotientLabel 11 10 134 3 (Sphere.Internal.product H M (s:=1) (t:=2) (s':=9) (t':=132) (Sphere.Internal.hi H M 1) V))
      (sphereAction (lambdaMultiply 3 η) a) :=
    compatibility.finite_action 11 (by decide) 1 2 9 132 3 0
      (Sphere.Internal.hi H M 1) V (lambdaMultiply 3 η) a he ha.1
  rw [alpha_exists_from_finite_frames_sphere_action_lambda_three D η a] at hp
  have hu3 := D.comparisonCompatible.homotopy_lambda 10 134 3 u
  rw [hlabel] at hu3
  have huq := alpha_exists_from_finite_frames_detected_map (D:=D) .sphere (.quotient 11 .sphere)
    (XModLambdaN.incl (S_0_0 : Syn) 11) (10,134,131) _ (lambdaMultiply 3 u) hu3
  have hcomm : lambdaMultiply 3 u≫XModLambdaN.incl (S_0_0 : Syn) 11 =
      lambdaMultiply 3 (quotientClass 11 u) := by
    simp only [lambdaMultiply,quotientClass,Category.assoc]
  change Detects (D.quotientConvergence 11 (by decide)) (10,134,131)
    (D.quotientLabel 11 10 134 3 U) (lambdaMultiply 3 u≫XModLambdaN.incl (S_0_0 : Syn) 11) at huq
  rw [hcomm] at huq
  have hU2 : U+U=0 := by
    apply (MilnorCohomology.comparison H M 10 134).symm.injective
    rw [map_add,map_zero,←two_smul KIP126.Algebra.F2,
      show (2:KIP126.Algebra.F2)=0 from rfl,zero_smul]
  have hneg : -U=U := by
    apply neg_eq_iff_add_eq_zero.mpr
    exact hU2
  have hd0 := differential_target_later_zero (show (adamsTowerInternalSpectralSequence H.unit SphereSpectrum).r₀≤2 from le_rfl)
    (show (2:ℤ)<3 from by decide) hd
  have hbound := alpha_exists_from_finite_frames_boundary_of_zero_representative (H:=H) (r:=3) (p:=(10,134)) hd0
  have hbound4 : Sphere.Internal.product H M (s:=1) (t:=2) (s':=9) (t':=132) (Sphere.Internal.hi H M 1) V-U∈
      PageRepresentatives.boundaries H SphereSpectrum 4 (10,134) := by
    rw [sub_eq_add_neg,hneg]
    exact PageRepresentatives.boundaries_monotone H SphereSpectrum (10,134) (by decide : (2:ℤ)≤4) hbound
  have hprod : Sphere.Internal.product H M (s:=1) (t:=2) (s':=9) (t':=132) (Sphere.Internal.hi H M 1) V∈
      PageRepresentatives.cycles H SphereSpectrum 8 (10,134) := by
    have hb := PageRepresentatives.boundaries_le_cycles H SphereSpectrum (10,134) 4 8 hbound4
    have hh := (PageRepresentatives.cycles H SphereSpectrum 8 (10,134)).add_mem hb hU
    simpa only [sub_add_cancel] using hh
  apply (alpha_exists_from_finite_frames_alpha_error_filtration_gap BHS h11 h12 _).mp
  exact alpha_exists_from_finite_frames_finite_boundary_detects_sub_filtration BHS.eInfty _ U hprod hU hbound4 _ _ hp huq


private theorem alpha_exists_from_finite_frames_lambda_six_one (D : AdamsComparison H M Syn)
    (c : BiHom 124 138 (S_0_0 : Syn)) :
    lambdaMultiply 6 (lambdaMultiply 1 c) = lambdaMultiply 7 c := by
  classical
  have ha := alpha_exists_from_finite_frames_shift_assoc_inv D.shiftCoherence (124,138) (0,-1) (0,-6)
    (124,137) (0,-7) (124,131) (by decide) (by decide) (by decide) (by decide) (S_0_0 : Syn)
  simp only [biShiftAddIso, Iso.trans_inv, eqToIso.inv, eqToHom_refl, Category.id_comp] at ha
  unfold lambdaMultiply
  simp only [eqToHom_refl, Category.id_comp, Nat.cast_ofNat, Int.reduceSub]
  erw [← reassoc_of% (lambdaPow_naturality 6
    ((SyntheticCategory.biShift_comp (124,138) (0,-1)).inv.app (S_0_0 : Syn)))]
  erw [← reassoc_of% (lambdaPow_naturality 6 (lambdaPow 1 (Smn 124 138)))]
  erw [← Category.assoc, ha]
  erw [lambdaPow_add D.shiftCoherence 1 6 7 (by decide) (Smn 124 138)]
  simp only [lambdaShiftAddIso, biShiftAddIso, KIP126.Synthetic.Context.lambdaDegree,
    Iso.trans_inv, eqToIso.inv, eqToHom_refl,
    Category.id_comp, Category.assoc]
  rfl


private theorem alpha_exists_from_finite_frames_lambda_six_two (D : AdamsComparison H M Syn)
    (c : BiHom 124 139 (S_0_0 : Syn)) :
    lambdaMultiply 6 (lambdaMultiply 2 c) = lambdaMultiply 8 c := by
  classical
  have ha := alpha_exists_from_finite_frames_shift_assoc_inv D.shiftCoherence (124,139) (0,-2) (0,-6)
    (124,137) (0,-8) (124,131) (by decide) (by decide) (by decide) (by decide) (S_0_0 : Syn)
  simp only [biShiftAddIso, Iso.trans_inv, eqToIso.inv, eqToHom_refl, Category.id_comp] at ha
  unfold lambdaMultiply
  simp only [eqToHom_refl, Category.id_comp, Nat.cast_ofNat, Int.reduceSub]
  erw [← reassoc_of% (lambdaPow_naturality 6
    ((SyntheticCategory.biShift_comp (124,139) (0,-2)).inv.app (S_0_0 : Syn)))]
  erw [← reassoc_of% (lambdaPow_naturality 6 (lambdaPow 2 (Smn 124 139)))]
  erw [← Category.assoc, ha]
  erw [lambdaPow_add D.shiftCoherence 2 6 8 (by decide) (Smn 124 139)]
  simp only [lambdaShiftAddIso, biShiftAddIso, KIP126.Synthetic.Context.lambdaDegree,
    Iso.trans_inv, eqToIso.inv, eqToHom_refl,
    Category.id_comp, Category.assoc]
  rfl


private theorem alpha_exists_from_finite_frames_lambda_one_one (D : AdamsComparison H M Syn)
    (c : BiHom 125 141 (S_0_0 : Syn)) :
    lambdaMultiply 1 (lambdaMultiply 1 c) = lambdaMultiply 2 c := by
  classical
  have ha := alpha_exists_from_finite_frames_shift_assoc_inv D.shiftCoherence (125,141) (0,-1) (0,-1)
    (125,140) (0,-2) (125,139) (by decide) (by decide) (by decide) (by decide) (S_0_0 : Syn)
  simp only [biShiftAddIso, Iso.trans_inv, eqToIso.inv, eqToHom_refl, Category.id_comp] at ha
  unfold lambdaMultiply
  simp only [eqToHom_refl, Category.id_comp, Nat.cast_ofNat, Int.reduceSub]
  erw [← reassoc_of% (lambdaPow_naturality 1
    ((SyntheticCategory.biShift_comp (125,141) (0,-1)).inv.app (S_0_0 : Syn)))]
  erw [← reassoc_of% (lambdaPow_naturality 1 (lambdaPow 1 (Smn 125 141)))]
  erw [← Category.assoc, ha]
  erw [lambdaPow_add D.shiftCoherence 1 1 2 (by decide) (Smn 125 141)]
  simp only [lambdaShiftAddIso, biShiftAddIso, KIP126.Synthetic.Context.lambdaDegree,
    Iso.trans_inv, eqToIso.inv, eqToHom_refl,
    Category.id_comp, Category.assoc]
  rfl


private theorem alpha_exists_from_finite_frames_sphere_action_right_one (D : AdamsComparison H M Syn)
    (η : BiHom 1 2 (S_0_0 : Syn))
    (c : BiHom 124 138 (S_0_0 : Syn)) :
    sphereAction η (lambdaMultiply 1 c) = lambdaMultiply 1 (sphereAction η c) := by
  classical
  have ha := alpha_exists_from_finite_frames_shift_assoc_inv D.shiftCoherence (1,2) (124,138) (0,-1)
    (125,140) (124,137) (125,139) (by decide) (by decide) (by decide) (by decide) (S_0_0 : Syn)
  simp only [biShiftAddIso, Iso.trans_inv, eqToIso.inv, eqToHom_refl, Category.id_comp] at ha
  unfold sphereAction lambdaMultiply
  simp only [eqToHom_refl, Category.id_comp, Int.reduceAdd]
  erw [← reassoc_of% (lambdaPow_naturality 1
    ((SyntheticCategory.biShift_comp (1,2) (124,138)).inv.app (S_0_0 : Syn)))]
  erw [← reassoc_of% (lambdaPow_naturality 1
    ((SyntheticCategory.biShift (124,138)).map η))]
  erw [reassoc_of% ha]
  erw [← reassoc_of% ((SyntheticCategory.biShift_comp (124,138) (0,-1)).inv.naturality η)]
  rfl


private theorem alpha_exists_from_finite_frames_sphere_action_right_two (D : AdamsComparison H M Syn)
    (η : BiHom 1 2 (S_0_0 : Syn))
    (c : BiHom 124 139 (S_0_0 : Syn)) :
    sphereAction η (lambdaMultiply 2 c) = lambdaMultiply 2 (sphereAction η c) := by
  classical
  have ha := alpha_exists_from_finite_frames_shift_assoc_inv D.shiftCoherence (1,2) (124,139) (0,-2)
    (125,141) (124,137) (125,139) (by decide) (by decide) (by decide) (by decide) (S_0_0 : Syn)
  simp only [biShiftAddIso, Iso.trans_inv, eqToIso.inv, eqToHom_refl, Category.id_comp] at ha
  unfold sphereAction lambdaMultiply
  simp only [eqToHom_refl, Category.id_comp, Nat.cast_ofNat,
    Int.reduceSub, Int.reduceAdd]
  erw [← reassoc_of% (lambdaPow_naturality 2
    ((SyntheticCategory.biShift_comp (1,2) (124,139)).inv.app (S_0_0 : Syn)))]
  erw [← reassoc_of% (lambdaPow_naturality 2
    ((SyntheticCategory.biShift (124,139)).map η))]
  erw [reassoc_of% ha]
  erw [← reassoc_of% ((SyntheticCategory.biShift_comp (124,139) (0,-2)).inv.naturality η)]
  rfl


private theorem alpha_exists_from_finite_frames_sphere_action_right_two_as_ones (D : AdamsComparison H M Syn)
    (η : BiHom 1 2 (S_0_0 : Syn)) (c : BiHom 124 139 (S_0_0 : Syn)) :
    sphereAction η (lambdaMultiply 2 c) = lambdaMultiply 1 (lambdaMultiply 1 (sphereAction η c)) := by
  classical
  exact (alpha_exists_from_finite_frames_sphere_action_right_two D η c).trans (alpha_exists_from_finite_frames_lambda_one_one D (sphereAction η c)).symm


private theorem alpha_exists_from_finite_frames_lambda_one_division_of_quotient_zero
    {X : Syn} (m w : ℤ) (z : BiHom m (w-1) X) (hz : quotientClass 1 z=0) :
    ∃ b : BiHom m w X, lambdaMultiply 1 b=z := by
  classical
  obtain ⟨a,ha⟩ := (vanishesModLambda_iff_factors 1 z).mp hz
  let F := SyntheticCategory.biShift (Syn:=Syn) (0,-1)
  let e : F.obj (Smn m w : Syn) ≅ Smn m (w-1) :=
    (SyntheticCategory.biShift_comp (m,w) (0,-1)).app S_0_0 ≪≫
      eqToIso (by congr 1; simp [sub_eq_add_neg])
  let b := (SyntheticCategory.biShift_fullyFaithful (Syn:=Syn) (0,-1)).preimage (e.hom≫a)
  have hb : F.map b=e.hom≫a :=
    (SyntheticCategory.biShift_fullyFaithful (Syn:=Syn) (0,-1)).map_preimage _
  refine ⟨b,?_⟩
  have he : lambdaMultiply 1 b=e.inv≫lambdaPow 1 (Smn m w)≫b := by
    unfold lambdaMultiply
    change eqToHom (by congr 1; simp) ≫ (SyntheticCategory.biShift_comp (m,w) (0,-1)).inv.app S_0_0 ≫
      lambdaPow 1 (Smn m w) ≫ b =
      (eqToHom (by congr 1; simp) ≫ (SyntheticCategory.biShift_comp (m,w) (0,-1)).inv.app S_0_0) ≫
      lambdaPow 1 (Smn m w) ≫ b
    exact (Category.assoc _ _ _).symm
  rw [he]
  rw [←lambdaPow_naturality 1 b]
  change e.inv≫F.map b≫lambdaPow 1 X=z
  rw [hb]
  simp only [Category.assoc,e.inv_hom_id_assoc]
  exact ha


private theorem alpha_exists_from_finite_frames_sphere_zero_weight_label_14_139 {D : AdamsComparison H M Syn}
    (BHS : EInftyComparison D) (x : E2 H SphereSpectrum 14 139)
    (a : BiHom (139-14) (139-0) (S_0_0 : Syn))
    (ha : Detects D.sphereConvergence (14,139,139-0) (D.sphereE2 14 139 0 x) a) :
    D.sphereFirstQuotient 14 139 (quotientClass 1 a)=x := by
  classical
  let y := D.sphereFirstQuotient 14 139 (quotientClass 1 a)
  have hd := alpha_exists_from_finite_frames_detected_map (D:=D) .sphere (.quotient 1 .sphere)
    (XModLambdaN.incl (S_0_0 : Syn) 1) (14,139,139-0) _ a ha
  have hd' := D.comparisonCompatible.first_quotient 14 139 y
  have hy : (D.sphereFirstQuotient 14 139).symm y=quotientClass 1 a := by
    exact (D.sphereFirstQuotient 14 139).symm_apply_apply _
  rw [hy] at hd'
  obtain ⟨e,he,hf⟩ := alpha_exists_from_finite_frames_detects_infinity_equal (.quotient 1 .sphere) (14,139,139-0)
    (quotientClass 1 a) _ _ hd hd'
  change HasInfinityRepresentative (D.family.quotient (S_0_0 : Syn) 1) 2 (14,139,139-0)
    (D.quotientLabel 1 14 139 0 x) e at he
  change HasInfinityRepresentative (D.family.quotient (S_0_0 : Syn) 1) 2 (14,139,139-0)
    (D.quotientLabel 1 14 139 0 y) e at hf
  let g := XModLambdaN.map D.nu.unitIso.inv 1
  have he' := alpha_exists_from_finite_frames_family_infinity_representative_map g (14,139,139-0) _ _ he
  have hf' := alpha_exists_from_finite_frames_family_infinity_representative_map g (14,139,139-0) _ _ hf
  have hlx := alpha_exists_from_finite_frames_sphere_quotient_label_to_nu (D:=D) 1 0 14 139 x
  have hly := alpha_exists_from_finite_frames_sphere_quotient_label_to_nu (D:=D) 1 0 14 139 y
  change familyPageMap D.family g 2 (14,139,139-0) (D.quotientLabel 1 14 139 0 x)=_ at hlx
  change familyPageMap D.family g 2 (14,139,139-0) (D.quotientLabel 1 14 139 0 y)=_ at hly
  rw [hlx] at he'
  rw [hly] at hf'
  let xx : PageRepresentatives.cycles H SphereSpectrum (1-139+(139-0)) (14,139) :=
    ⟨x,by simp only [sub_zero,sub_add_cancel,PageRepresentatives.cycles_one,Submodule.mem_top]⟩
  let yy : PageRepresentatives.cycles H SphereSpectrum (1-139+(139-0)) (14,139) :=
    ⟨y,by simp only [sub_zero,sub_add_cancel,PageRepresentatives.cycles_one,Submodule.mem_top]⟩
  have hxq := (BHS.labels.1 .sphere 1 (by decide) (14,139) 0 (by decide) xx _).mp he'
  have hyq := (BHS.labels.1 .sphere 1 (by decide) (14,139) 0 (by decide) yy _).mp hf'
  have heq := hxq.symm.trans hyq
  change NestedQuotient.projection _ (PageRepresentatives.boundaries H SphereSpectrum 1 (14,139)) xx =
    NestedQuotient.projection _ (PageRepresentatives.boundaries H SphereSpectrum 1 (14,139)) yy at heq
  have hz : NestedQuotient.projection _ (PageRepresentatives.boundaries H SphereSpectrum 1 (14,139)) (xx-yy)=0 := by rw [map_sub,heq,sub_self]
  have hm := (NestedQuotient.projection_eq_zero (xx-yy)).mp hz
  change x-y∈PageRepresentatives.boundaries H SphereSpectrum 1 (14,139) at hm
  have ht : 1+139-(139-0)=1 := by omega
  change x-y∈PageRepresentatives.boundaries H SphereSpectrum 1 (14,139) at hm
  rw [PageRepresentatives.boundaries_one,Submodule.mem_bot] at hm
  exact (sub_eq_zero.mp hm).symm


private theorem alpha_exists_from_finite_frames_eta_correction_lambda_divisible {D : AdamsComparison H M Syn}
    (BHS : EInftyComparison D)
    (η : BiHom 1 2 (S_0_0 : Syn)) (c : BiHom 124 137 (S_0_0 : Syn))
    (x : E2 H SphereSpectrum 13 137)
    (hη : D.sphereFirstQuotient 1 2 (quotientClass 1 η)=Sphere.Internal.hi H M 1)
    (hc : D.sphereFirstQuotient 13 137 (quotientClass 1 c)=x)
    (hp : Sphere.Internal.product H M (s:=1) (t:=2) (s':=13) (t':=137) (Sphere.Internal.hi H M 1) x=0) :
    ∃ b : BiHom 125 140 (S_0_0 : Syn), lambdaMultiply 1 b=sphereAction η c := by
  classical
  have hη0 : lambdaMultiply 0 η=η := by
    have hc := D.shiftCoherence.right_unit (1,2) (S_0_0 : Syn)
    have he : (SyntheticCategory.biShift_comp (1,2) (0,0)).hom.app (S_0_0 : Syn)=
        SyntheticCategory.biShift_zero.hom.app (Smn 1 2 : Syn) := by
      change (biShiftAddIso (1,2) (0,0) (1,2) (by decide)).hom.app _=_ at hc
      simpa only [biShiftAddIso,Iso.trans_hom,NatTrans.comp_app,eqToIso.hom,
        eqToHom_app,eqToHom_refl,Category.comp_id,Smn] using hc
    dsimp only [lambdaMultiply,lambdaPow]
    simp only [eqToHom_refl,Category.id_comp]
    rw [←he]
    change (SyntheticCategory.biShift_comp (1,2) (0,0)).inv.app (S_0_0 : Syn) ≫
      (SyntheticCategory.biShift_comp (1,2) (0,0)).hom.app (S_0_0 : Syn) ≫ η=η
    rw [←Category.assoc,Iso.inv_hom_id_app,Category.id_comp]
  have hc0 : lambdaMultiply 0 c=c := by
    have hc := D.shiftCoherence.right_unit (124,137) (S_0_0 : Syn)
    have he : (SyntheticCategory.biShift_comp (124,137) (0,0)).hom.app (S_0_0 : Syn)=
        SyntheticCategory.biShift_zero.hom.app (Smn 124 137 : Syn) := by
      change (biShiftAddIso (124,137) (0,0) (124,137) (by decide)).hom.app _=_ at hc
      simpa only [biShiftAddIso,Iso.trans_hom,NatTrans.comp_app,eqToIso.hom,
        eqToHom_app,eqToHom_refl,Category.comp_id,Smn] using hc
    dsimp only [lambdaMultiply,lambdaPow]
    simp only [eqToHom_refl,Category.id_comp]
    rw [←he]
    change (SyntheticCategory.biShift_comp (124,137) (0,0)).inv.app (S_0_0 : Syn) ≫
      (SyntheticCategory.biShift_comp (124,137) (0,0)).hom.app (S_0_0 : Syn) ≫ c=c
    rw [←Category.assoc,Iso.inv_hom_id_app,Category.id_comp]
  have hηd := D.comparisonCompatible.homotopy_lambda 1 2 0 η
  rw [hη0,hη] at hηd
  have hcd := D.comparisonCompatible.homotopy_lambda 13 137 0 c
  rw [hc0,hc] at hcd
  have hd := D.multiplicationCompatible 1 2 13 137 0 0 (Sphere.Internal.hi H M 1) x η c hηd hcd
  change Detects D.sphereConvergence (14,139,139-0)
    (D.sphereE2 14 139 0 (Sphere.Internal.product H M (s:=1) (t:=2) (s':=13) (t':=137) (Sphere.Internal.hi H M 1) x))
    (sphereAction η c) at hd
  rw [hp] at hd
  have hfirst := alpha_exists_from_finite_frames_sphere_zero_weight_label_14_139 BHS 0 (sphereAction η c) hd
  have hzero : quotientClass 1 (sphereAction η c)=0 := by
    apply (D.sphereFirstQuotient 14 139).injective
    exact hfirst.trans (map_zero (D.sphereFirstQuotient 14 139)).symm
  exact alpha_exists_from_finite_frames_lambda_one_division_of_quotient_zero 125 140 (sphereAction η c) hzero


private theorem alpha_exists_from_finite_frames_sphere_first_label_transport {D : AdamsComparison H M Syn} (s t : ℤ)
    (x : E2 H SphereSpectrum s t) :
    D.sphereFirstQuotient s t
      (firstLabel D .sphere s t x ≫ XModLambdaN.map
        (SyntheticCategory.biShift_zero.hom.app (D.nu.functor.obj SphereSpectrum) ≫ D.nu.unitIso.hom) 1)=x := by
  classical
  let e : nuZero D .sphere ≅ (S_0_0 : Syn) :=
    SyntheticCategory.biShift_zero.app _ ≪≫ D.nu.unitIso
  let q := (D.quotientFunctoriality.functor 1).mapIso e
  let c : BiHom (t-s) t (XModLambdaN (nuZero D .sphere) 1) ≃+ E2 H SphereSpectrum s t :=
    Eq.mp (congrArg (fun z : ℤ => BiHom (t-s) z (XModLambdaN (nuZero D .sphere) 1) ≃+
      E2 H SphereSpectrum s t) (Int.add_zero t)) (D.firstQuotient SphereSpectrum 0 s t)
  change c ((firstLabel D .sphere s t x ≫ q.hom) ≫ q.inv)=x
  rw [Category.assoc,q.hom_inv_id]
  erw [Category.comp_id]
  have cast_symm (w₁ w₂ : ℤ) (h : w₁=w₂)
      (E : BiHom (t-s) w₁ (XModLambdaN (nuZero D .sphere) 1) ≃+ E2 H SphereSpectrum s t)
      (x : E2 H SphereSpectrum s t) :
      Eq.mp (congrArg (fun z => BiHom (t-s) z (XModLambdaN (nuZero D .sphere) 1)) h) (E.symm x) =
        (Eq.mp (congrArg (fun z : ℤ => BiHom (t-s) z (XModLambdaN (nuZero D .sphere) 1) ≃+
          E2 H SphereSpectrum s t) h) E).symm x := by
    subst w₂
    rfl
  have hx : firstLabel D .sphere s t x=c.symm x := by
    dsimp only [firstLabel,c,ClassicalObject.obj,nuZero]
    exact cast_symm (t+0) t (Int.add_zero t) (D.firstQuotient SphereSpectrum 0 s t) x
  rw [hx,c.apply_symm_apply]


private theorem alpha_exists_from_finite_frames_sphere_permanent_first_quotient_lift {D : AdamsComparison H M Syn}
    (synthetic : SyntheticComparisonTheorems D) (s t : ℤ) (x : E2 H SphereSpectrum s t)
    (hx : IsPermanentCycle (adamsTowerInternalSpectralSequence H.unit SphereSpectrum) (s,t) x) :
    ∃ a : BiHom (t-s) t (S_0_0 : Syn), D.sphereFirstQuotient s t (quotientClass 1 a)=x := by
  classical
  have hp : x∈PageRepresentatives.permanentCycles H SphereSpectrum (s,t) := by
    exact hx
  obtain ⟨a,ha⟩ := (synthetic.permanent_lift .sphere s t x).mp hp
  let e := SyntheticCategory.biShift_zero.hom.app (D.nu.functor.obj SphereSpectrum) ≫ D.nu.unitIso.hom
  refine ⟨a≫e,?_⟩
  have hc : quotientClass 1 (a≫e)=quotientClass 1 a≫XModLambdaN.map e 1 := by
    unfold quotientClass
    simp only [Category.assoc]
    exact congrArg (fun h => a≫h) (XModLambdaN.incl_naturality e 1)
  rw [hc,ha]
  exact alpha_exists_from_finite_frames_sphere_first_label_transport s t x


private theorem alpha_exists_from_finite_frames_alpha_h0_rho_zero {D : AdamsComparison H M Syn}
    (hzero : ∀ a : BiHom 123 130 (XModLambdaN (S_0_0 : Syn) 9),
      FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 16 a → a=0)
    (h0 : BiHom 0 1 (S_0_0 : Syn))
    (a : BiHom 123 132 (XModLambdaN (S_0_0 : Syn) 11))
    (ha : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 17
      (lambdaMultiply 3 (sphereAction h0 a))) :
    lambdaMultiply 3 (sphereAction h0 (a≫(D.quotientTower S_0_0).rho 9 11 (by decide)))=0 := by
  classical
  apply hzero
  have h := alpha_exists_from_finite_frames_filtration_postcompose (D:=D) ((D.quotientTower S_0_0).rho 9 11 (by decide))
    17 123 130 (lambdaMultiply 3 (sphereAction h0 a)) ha
  have h16 : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 16
      (lambdaMultiply 3 (sphereAction h0 a)≫(D.quotientTower S_0_0).rho 9 11 (by decide)) :=
    towerFiltrationSubmodule_antitone _ _ _ (by decide : (16:ℤ)≤17) h
  simpa only [lambdaMultiply,sphereAction,Category.assoc] using h16


private theorem alpha_exists_from_finite_frames_alpha_correction_sum (D : AdamsComparison H M Syn)
    (η : BiHom 1 2 (S_0_0 : Syn))
    (c13 : BiHom 124 137 (S_0_0 : Syn))
    (c14 : BiHom 124 138 (S_0_0 : Syn))
    (c15 : BiHom 124 139 (S_0_0 : Syn))
    (b : BiHom 125 140 (S_0_0 : Syn)) (hb : lambdaMultiply 1 b=sphereAction η c13)
    (b13 b14 b15 : Bool) :
    ∃ (a2 : BiHom 124 137 (XModLambdaN (S_0_0 : Syn) 9))
      (a3 : BiHom 125 140 (XModLambdaN (S_0_0 : Syn) 9)),
      (if b13 then (show BiHom 124 131 (XModLambdaN (S_0_0 : Syn) 9) from lambdaMultiply 6 (quotientClass 9 c13)) else 0)+
      (if b14 then (show BiHom 124 131 (XModLambdaN (S_0_0 : Syn) 9) from lambdaMultiply 7 (quotientClass 9 c14)) else 0)+
      (if b15 then (show BiHom 124 131 (XModLambdaN (S_0_0 : Syn) 9) from lambdaMultiply 8 (quotientClass 9 c15)) else 0)=lambdaMultiply 6 a2 ∧
      sphereAction η a2=lambdaMultiply 1 a3 := by
  classical
  have lam_add {m w : ℤ} {X : Syn} (n : ℕ) (a b : BiHom m w X) :
      lambdaMultiply n (a+b)=lambdaMultiply n a+lambdaMultiply n b := by
    simp only [lambdaMultiply,Preadditive.comp_add]
  have lam_if {m w : ℤ} {X : Syn} (n : ℕ) (a : BiHom m w X) (b : Bool) :
      lambdaMultiply n (if b then a else 0)=(if b then lambdaMultiply n a else 0) := by
    cases b <;> simp only [Bool.false_eq_true,↓reduceIte,lambdaMultiply,comp_zero]
  have act_add {m w : ℤ} {X : Syn} (a b : BiHom m w X) :
      sphereAction η (a+b)=sphereAction η a+sphereAction η b := by
    simp only [sphereAction,Preadditive.comp_add]
  have act_if {m w : ℤ} {X : Syn} (a : BiHom m w X) (b : Bool) :
      sphereAction η (if b then a else 0)=(if b then sphereAction η a else 0) := by
    cases b <;> simp only [Bool.false_eq_true,↓reduceIte,sphereAction,comp_zero]
  let c : BiHom 124 137 (S_0_0 : Syn) := (if b13 then c13 else 0)+
    (if b14 then (show BiHom 124 137 (S_0_0 : Syn) from lambdaMultiply 1 c14) else 0)+
    (if b15 then (show BiHom 124 137 (S_0_0 : Syn) from lambdaMultiply 2 c15) else 0)
  let d : BiHom 125 140 (S_0_0 : Syn) := (if b13 then b else 0)+
    (if b14 then (show BiHom 125 140 (S_0_0 : Syn) from sphereAction η c14) else 0)+
    (if b15 then (show BiHom 125 140 (S_0_0 : Syn) from lambdaMultiply 1 (sphereAction η c15)) else 0)
  have hlam : lambdaMultiply 6 c=
      (if b13 then (show BiHom 124 131 (S_0_0 : Syn) from lambdaMultiply 6 c13) else 0)+
      (if b14 then (show BiHom 124 131 (S_0_0 : Syn) from lambdaMultiply 7 c14) else 0)+
      (if b15 then (show BiHom 124 131 (S_0_0 : Syn) from lambdaMultiply 8 c15) else 0) := by
    dsimp only [c]
    rw [lam_add,lam_add,lam_if,lam_if,lam_if,alpha_exists_from_finite_frames_lambda_six_one D,alpha_exists_from_finite_frames_lambda_six_two D]
  have heta : sphereAction η c=lambdaMultiply 1 d := by
    dsimp only [c,d]
    rw [act_add,act_add,act_if,act_if,act_if,lam_add,lam_add,lam_if,lam_if,lam_if,
      hb,alpha_exists_from_finite_frames_sphere_action_right_one D,alpha_exists_from_finite_frames_sphere_action_right_two_as_ones D]
  refine ⟨quotientClass 9 c,quotientClass 9 d,?_,?_⟩
  · have hh := congrArg (fun a=>a≫XModLambdaN.incl (S_0_0 : Syn) 9) hlam
    simp only [Preadditive.add_comp,ite_comp,zero_comp] at hh
    simpa only [lambdaMultiply,quotientClass,Category.assoc] using hh.symm
  · have hh := congrArg (fun a=>a≫XModLambdaN.incl (S_0_0 : Syn) 9) heta
    simpa only [lambdaMultiply,sphereAction,quotientClass,Category.assoc] using hh


private theorem alpha_one_correction_equations {D : AdamsComparison H M Syn}
    {L : SphereAdamsClasses H} {G : KIP126.Literature.AdamsSynthetic.TmfDetectionClasses H}
    (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G) (facts : Derived.SphereFacts I.interpretation) :
    I.interpretation.sphere 10 134 U∈PageRepresentatives.cycles H SphereSpectrum 8 (10,134) ∧
    HasDifferential (sequence D .sphere) 2 (8,133) (10,134)
      (I.interpretation.sphere 8 133 (atom .x_125_8))
      (Sphere.Internal.product H M (s:=1) (t:=2) (s':=9) (t':=132) (Sphere.Internal.hi H M 1)
        (I.interpretation.sphere 9 132 V)+I.interpretation.sphere 10 134 U) ∧
    Sphere.Internal.product H M (s:=1) (t:=2) (s':=13) (t':=137) (Sphere.Internal.hi H M 1)
      (I.interpretation.sphere 13 137 correction)=0 := by
  classical
  constructor
  · apply PageRepresentatives.permanentCycles_le_cycles H SphereSpectrum (10,134) 8
    obtain ⟨z,hz,_⟩ := facts.u_permanent
    exact ⟨z,hz⟩
  constructor
  · have h := (facts.d2_x_125_8).toHasDifferential
    have hp := I.products ⟨1,2,9,132⟩ (by simp [Raw.products]) dataH1 V
    dsimp only at hp
    change HasDifferential (sequence D .sphere) 2 (8,133) (10,134)
      (I.interpretation.sphere 8 133 (atom .x_125_8))
      (I.interpretation.sphere 10 134 (mulAt dataH1 V+U)) at h
    rw [map_add,hp,I.distinguishedClasses.h1] at h
    exact h
  · have hp := I.products ⟨1,2,13,137⟩ (by simp [Raw.products]) dataH1 correction
    dsimp only at hp
    rw [I.distinguishedClasses.h1] at hp
    exact hp.symm.trans facts.h1_correction_zero


private theorem alpha_exists_from_finite_frames
    {L : SphereAdamsClasses H} {G : KIP126.Literature.AdamsSynthetic.TmfDetectionClasses H}
    (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G) (BHS : SyntheticComparisonTheorems D) (facts : Derived.SphereFacts I.interpretation)
    (algebra : AdamsAlgebraStructures D) (compatibility : AlgebraDetectionCompatibility D algebra)
    (η : BiHom 1 2 (S_0_0 : Syn)) (hη : EtaChoice M D.toAdamsComparisonData η)
    (h0 : BiHom 0 1 (S_0_0 : Syn))
    (h0filtration : ∀ (a : BiHom 123 132 (XModLambdaN (S_0_0 : Syn) 11)),
      FiniteDetected D 11 (by decide) 9 132 0 (I.interpretation.sphere 9 132 V) a →
      FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 17 (lambdaMultiply 3 (sphereAction h0 a)))
    (h0zero : ∀ a : BiHom 123 130 (XModLambdaN (S_0_0 : Syn) 9),
      FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 16 a → a=0)
    (hp14 : IsPermanentCycle (sequence D .sphere) (14,138) (I.interpretation.basis .sphere 14 138 2))
    (hp15 : IsPermanentCycle (sequence D .sphere) (15,139)
      (I.interpretation.basis .sphere 15 139 1+I.interpretation.basis .sphere 15 139 3)) :
    ∃ a : BiHom 123 132 (XModLambdaN (S_0_0 : Syn) 11),
      AlphaOneProperties D η h0 (I.interpretation.sphere 10 134 U) (I.interpretation.sphere 9 132 V) a := by
  classical
  obtain ⟨a,ha11,ha9⟩ := alpha_exists_from_finite_frames_alpha_one_detected_pair BHS.eInfty _ facts.v_to_e12
  obtain ⟨hU,hd,hprod⟩ := alpha_one_correction_equations I facts
  have hpc : IsPermanentCycle (sequence D .sphere) (13,137) (I.interpretation.sphere 13 137 correction) := by
    obtain ⟨z,hz,_⟩ := facts.correction_permanent
    exact ⟨z,hz⟩
  obtain ⟨c13,hc13⟩ := alpha_exists_from_finite_frames_sphere_permanent_first_quotient_lift BHS 13 137 _ hpc
  obtain ⟨c14,hc14⟩ := alpha_exists_from_finite_frames_sphere_permanent_first_quotient_lift BHS 14 138 _ hp14
  obtain ⟨c15,hc15⟩ := alpha_exists_from_finite_frames_sphere_permanent_first_quotient_lift BHS 15 139 _ hp15
  obtain ⟨b,hb⟩ := alpha_exists_from_finite_frames_eta_correction_lambda_divisible BHS.eInfty η c13 _ hη hc13 hprod
  have h14 : I.interpretation.basis .sphere 14 138 2∈PageRepresentatives.cycles H SphereSpectrum 4 (14,138) :=
    PageRepresentatives.permanentCycles_le_cycles H SphereSpectrum (14,138) 4 hp14
  have h15 : I.interpretation.basis .sphere 15 139 1+I.interpretation.basis .sphere 15 139 3∈PageRepresentatives.cycles H SphereSpectrum 3 (15,139) :=
    PageRepresentatives.permanentCycles_le_cycles H SphereSpectrum (15,139) 3 hp15
  refine ⟨a,ha11,ha9,?_,?_⟩
  · intro u hu
    have herr := alpha_exists_from_finite_frames_alpha_error_filtration_thirteen BHS algebra compatibility η hη _ _ _ hU hd
      facts.e5_stem124_af11 facts.e4_stem124_af12 a ha11 u hu
    obtain ⟨b13,b14,b15,hbits⟩ := alpha_exists_from_finite_frames_alpha_three_layer_restriction I BHS.eInfty facts h14 h15
      c13 hc13 c14 hc14 c15 hc15 _ herr
    obtain ⟨a2,a3,hs,heta⟩ := alpha_exists_from_finite_frames_alpha_correction_sum (D:=D) η c13 c14 c15 b hb b13 b14 b15
    refine ⟨a2,a3,?_,heta⟩
    have he := hbits.trans hs
    have hrho :
        ((show BiHom 124 131 (XModLambdaN (S_0_0 : Syn) 11) from lambdaMultiply 3 (sphereAction η a))-
          (show BiHom 124 131 (XModLambdaN (S_0_0 : Syn) 11) from lambdaMultiply 3 (quotientClass 11 u)))≫
            (D.quotientTower S_0_0).rho 9 11 (by decide) =
        (show BiHom 124 131 (XModLambdaN (S_0_0 : Syn) 9) from lambdaMultiply 3
          (sphereAction η (a≫(D.quotientTower S_0_0).rho 9 11 (by decide))))-
          (show BiHom 124 131 (XModLambdaN (S_0_0 : Syn) 9) from lambdaMultiply 3 (quotientClass 9 u)) := by
      simp only [Preadditive.sub_comp,lambdaMultiply,sphereAction,quotientClass,Category.assoc,
        FiniteLambdaQuotientTower.rho_quotient]
    rw [hrho] at he
    exact sub_eq_iff_eq_add'.mp he
  · exact alpha_exists_from_finite_frames_alpha_h0_rho_zero h0zero h0 a (h0filtration a ha11)

end

end AlphaOneExistenceProof

end
end KIP126.Main.SectionSeven
