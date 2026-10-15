module

public import KIP126.Computation.LinCoordinates.Certificates.SphereAndCofiber.Bounds
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Legacy

/-! Finite-page survival of the named U, P, Q and correction classes. -/

@[expose] public section

namespace KIP126.Computation.SphereAndCofiber
open CategoryTheory.Limits KIP126.Algebra
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
open KIP126.SpectralSequence.FinitePageCalculus
open KIP126.LinE2.RelationCertificates
open CategoryTheory
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology KIP126.Classical.Adams
open KIP126.SpectralSequence KIP126.Synthetic.Context KIP126.AdamsSynthetic
open KIP126.LinE2 KIP126.Computation.Near126
attribute [local irreducible] KIP126.LinE2.homogeneousPart adamsTowerSSData adamsTowerInternalD
universe u v w
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H}

variable {D : AdamsComparison H M Syn} {L : SphereAdamsClasses H} {G : KIP126.Literature.AdamsSynthetic.TmfDetectionClasses H}
section

private theorem u_survives1000_h157 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 3 (4,130) (7,132) (I.interpretation.basis .sphere 4 130 0) (I.interpretation.basis .sphere 7 132 0) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere, .equation, 3, 4, 130, [0], 7, 132, [0], "S0_AdamsE2_ss", 2437⟩ (by
    exact List.mem_of_getElem? (i := 157) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (4,130) (7,132) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 4 130 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 7 132 [0] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem u_survives1000_h163 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (5,130) (7,131) (I.interpretation.basis .sphere 5 130 0) (I.interpretation.basis .sphere 7 131 2) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere, .equation, 2, 5, 130, [0], 7, 131, [2], "S0_AdamsE2_ss", 2435⟩ (by
    exact List.mem_of_getElem? (i := 163) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (5,130) (7,131) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 5 130 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 7 131 [2] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem u_survives1000_h171 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 4 (6,131) (10,134) (I.interpretation.basis .sphere 6 131 0) (I.interpretation.basis .sphere 10 134 0 + I.interpretation.basis .sphere 10 134 3) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere, .equation, 4, 6, 131, [0], 10, 134, [0, 3], "S0_AdamsE2_ss", 2492⟩ (by
    exact List.mem_of_getElem? (i := 171) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 4 (6,131) (10,134) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 6 131 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 10 134 [0, 3] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem u_survives1000_h172 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 4 (6,131) (10,134) (I.interpretation.basis .sphere 6 131 1) (I.interpretation.basis .sphere 10 134 0 + I.interpretation.basis .sphere 10 134 1 + I.interpretation.basis .sphere 10 134 3 + I.interpretation.basis .sphere 10 134 4) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere, .equation, 4, 6, 131, [1], 10, 134, [0, 1, 3, 4], "S0_AdamsE2_ss", 2493⟩ (by
    exact List.mem_of_getElem? (i := 172) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 4 (6,131) (10,134) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 6 131 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 10 134 [0, 1, 3, 4] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem u_survives1000_h200 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 3 (8,133) (11,135) (I.interpretation.basis .sphere 8 133 0) (I.interpretation.basis .sphere 11 135 0) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere, .equation, 3, 8, 133, [0], 11, 135, [0], "S0_AdamsE2_ss", 2629⟩ (by
    exact List.mem_of_getElem? (i := 200) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (8,133) (11,135) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 133 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 11 135 [0] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem u_survives1000_h201 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (8,133) (10,134) (I.interpretation.basis .sphere 8 133 1) (I.interpretation.basis .sphere 10 134 2 + I.interpretation.basis .sphere 10 134 4) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere, .equation, 2, 8, 133, [1], 10, 134, [2, 4], "S0_AdamsE2_ss", 2630⟩ (by
    exact List.mem_of_getElem? (i := 201) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (8,133) (10,134) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 133 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 10 134 [2, 4] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem u_survives1000_h249 (I : AdamsComputationTheorems D L G) : ReachesPage (sequence D .sphere) 1000 (10,134) (I.interpretation.basis .sphere 10 134 4) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere, .reaches, 1000, 10, 134, [4], 10, 134, [], "S0_AdamsE2_ss", 2693⟩ (by
    exact List.mem_of_getElem? (i := 249) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨a,ha,h⟩ := hrow
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 134 [4] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha
  rw [←ha] at h
  exact h

private theorem u_survives1000
    {C : Type u} [StableHomotopyCategory.{u,v} C] [HasFunctorialCofiber (C:=C)]
    {Syn : Type w} [SyntheticCategory.{w,v} Syn] [HasFunctorialCofiber (C:=Syn)]
    {H : Mod2EilenbergMacLane (C:=C)} {M : MilnorCooperations H} {D : AdamsComparison H M Syn}
    {L : SphereAdamsClasses H} {G : KIP126.Literature.AdamsSynthetic.TmfDetectionClasses H} (I : AdamsComputationTheorems D L G) :
    SurvivesTo (sequence D .sphere) 1000 (10,134) (I.interpretation.basis .sphere 10 134 4) := by
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
  obtain ⟨e8_133,he8_133⟩ := I.basis ⟨.sphere, 8, 133, ["376,1", "375,1"]⟩ (by
    exact List.mem_of_getElem? (i := 161) (by rfl))
  change E.Page 2 (8,133) ≃ₗ[ℤ] (Fin 2 →₀ F2) at e8_133
  change ∀i : Fin 2, e8_133.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 8 133 i.val at he8_133
  have he8_133_0 : e8_133.symm (Finsupp.single 0 1) = I.interpretation.basis .sphere 8 133 0 := he8_133 0
  have he8_133_1 : e8_133.symm (Finsupp.single 1 1) = I.interpretation.basis .sphere 8 133 1 := he8_133 1
  obtain ⟨e7_132,he7_132⟩ := I.basis ⟨.sphere, 7, 132, ["0,2,340,1"]⟩ (by
    exact List.mem_of_getElem? (i := 149) (by rfl))
  change E.Page 2 (7,132) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e7_132
  change ∀i : Fin 1, e7_132.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 7 132 i.val at he7_132
  have he7_132_0 : e7_132.symm (Finsupp.single 0 1) = I.interpretation.basis .sphere 7 132 0 := he7_132 0
  obtain ⟨e6_131,he6_131⟩ := I.basis ⟨.sphere, 6, 131, ["69,1,76,1", "0,1,340,1"]⟩ (by
    exact List.mem_of_getElem? (i := 137) (by rfl))
  change E.Page 2 (6,131) ≃ₗ[ℤ] (Fin 2 →₀ F2) at e6_131
  change ∀i : Fin 2, e6_131.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 6 131 i.val at he6_131
  have he6_131_0 : e6_131.symm (Finsupp.single 0 1) = I.interpretation.basis .sphere 6 131 0 := he6_131 0
  have he6_131_1 : e6_131.symm (Finsupp.single 1 1) = I.interpretation.basis .sphere 6 131 1 := he6_131 1
  obtain ⟨e5_130,he5_130⟩ := I.basis ⟨.sphere, 5, 130, ["340,1"]⟩ (by
    exact List.mem_of_getElem? (i := 126) (by rfl))
  change E.Page 2 (5,130) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e5_130
  change ∀i : Fin 1, e5_130.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 5 130 i.val at he5_130
  have he5_130_0 : e5_130.symm (Finsupp.single 0 1) = I.interpretation.basis .sphere 5 130 0 := he5_130 0
  obtain ⟨e7_131,he7_131⟩ := I.basis ⟨.sphere, 7, 131, ["353,1", "69,1,75,1", "0,1,339,1"]⟩ (by
    exact List.mem_of_getElem? (i := 148) (by rfl))
  change E.Page 2 (7,131) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e7_131
  change ∀i : Fin 3, e7_131.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 7 131 i.val at he7_131
  have he7_131_0 : e7_131.symm (Finsupp.single 0 1) = I.interpretation.basis .sphere 7 131 0 := he7_131 0
  have he7_131_1 : e7_131.symm (Finsupp.single 1 1) = I.interpretation.basis .sphere 7 131 1 := he7_131 1
  have he7_131_2 : e7_131.symm (Finsupp.single 2 1) = I.interpretation.basis .sphere 7 131 2 := he7_131 2
  have h157 : HasDifferential E 3 (4,130) (7,132) (I.interpretation.basis .sphere 4 130 0) (I.interpretation.basis .sphere 7 132 0) := u_survives1000_h157 I
  have h163 : HasDifferential E 2 (5,130) (7,131) (I.interpretation.basis .sphere 5 130 0) (I.interpretation.basis .sphere 7 131 2) := u_survives1000_h163 I
  have h171 : HasDifferential E 4 (6,131) (10,134) (I.interpretation.basis .sphere 6 131 0) (I.interpretation.basis .sphere 10 134 0 + I.interpretation.basis .sphere 10 134 3) := u_survives1000_h171 I
  have h172 : HasDifferential E 4 (6,131) (10,134) (I.interpretation.basis .sphere 6 131 1) (I.interpretation.basis .sphere 10 134 0 + I.interpretation.basis .sphere 10 134 1 + I.interpretation.basis .sphere 10 134 3 + I.interpretation.basis .sphere 10 134 4) := u_survives1000_h172 I
  have h200 : HasDifferential E 3 (8,133) (11,135) (I.interpretation.basis .sphere 8 133 0) (I.interpretation.basis .sphere 11 135 0) := u_survives1000_h200 I
  have h201 : HasDifferential E 2 (8,133) (10,134) (I.interpretation.basis .sphere 8 133 1) (I.interpretation.basis .sphere 10 134 2 + I.interpretation.basis .sphere 10 134 4) := u_survives1000_h201 I
  have h249 : ReachesPage E 1000 (10,134) (I.interpretation.basis .sphere 10 134 4) := u_survives1000_h249 I
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
  have generated_one {r : ℤ} (hr : 2≤r) {p : ℤ×ℤ}
      (e : E.Page 2 p ≃ₗ[ℤ] (Fin 1 →₀ F2)) (a : E.Page r p)
      (ha : RepresentsOnPage E r p (e.symm (Finsupp.single 0 1)) a)
      (x : E.Page r p) : x=0 ∨ x=a := by
    exact FinitePageCalculus.generated_one hr e a ha x
  have generated_two {r : ℤ} (hr : 2≤r) {p : ℤ×ℤ}
      (e : E.Page 2 p ≃ₗ[ℤ] (Fin 2 →₀ F2)) (a b : E.Page r p)
      (ha : RepresentsOnPage E r p (e.symm (Finsupp.single 0 1)) a)
      (hb : RepresentsOnPage E r p (e.symm (Finsupp.single 1 1)) b)
      (x : E.Page r p) : x=0 ∨ x=a ∨ x=b ∨ x=a+b := by
    exact FinitePageCalculus.generated_two hr e a b ha hb x
  have incoming2 (x : E.Page 2 (8,133)) : E.d 2 (8,133) x=0 ∨
      E.d 2 (8,133) x=I.interpretation.basis .sphere 10 134 2+I.interpretation.basis .sphere 10 134 4 := by
    obtain ⟨_,a,b,ha,hb,hd⟩ := h200
    have d0 := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) (hrep2 _) ⟨a,ha⟩
    have d1 := h201.eq_on_page_two.2
    change E.d 2 (8,133) (I.interpretation.basis .sphere 8 133 1)=_ at d1
    have h := generated_two (by decide : (2:ℤ)≤2) e8_133 _ _
      (by rw [he8_133_0]; exact hrep2 _) (by rw [he8_133_1]; exact hrep2 _) x
    rcases h with h|h|h|h
    · exact Or.inl (by rw [h,map_zero])
    · exact Or.inl (by rw [h,d0])
    · exact Or.inr (by rw [h,d1])
    · exact Or.inr (by rw [h,map_add,d0,d1,zero_add])
  have incoming3 : E.d 3 (7,132)=0 := by
    obtain ⟨_,a,b,ha,hb,hd⟩ := h157
    have hd0 : E.d 3 (7,132) b=0 := IsPageBoundary.d_eq_zero (E:=E) (r:=3) (p:=(4,130)) ⟨a,hd⟩
    ext x
    rcases generated_one (by decide : (2:ℤ)≤3) e7_132 b (by rw [he7_132_0]; exact hb) x with h|h
    · simp only [h,map_zero,ModuleCat.hom_zero]
    · simp only [h,hd0,ModuleCat.hom_zero,LinearMap.zero_apply]
  obtain ⟨_,a4,y4,ha4,hy4,hda4⟩ := h171
  obtain ⟨_,b4,z4,hb4,hz4,hdb4⟩ := h172
  have incoming4 (x : E.Page 4 (6,131)) : E.d 4 (6,131) x=0 ∨ E.d 4 (6,131) x=y4 ∨
      E.d 4 (6,131) x=z4 ∨ E.d 4 (6,131) x=y4+z4 := by
    have da : E.d 4 (6,131) a4=y4 := hda4
    have db : E.d 4 (6,131) b4=z4 := hdb4
    rcases generated_two (by decide : (2:ℤ)≤4) e6_131 a4 b4
      (by rw [he6_131_0]; exact ha4) (by rw [he6_131_1]; exact hb4) x with h|h|h|h
    · exact Or.inl (by rw [h,map_zero])
    · exact Or.inr (Or.inl (by rw [h,da]))
    · exact Or.inr (Or.inr (Or.inl (by rw [h,db])))
    · exact Or.inr (Or.inr (Or.inr (by rw [h,map_add,da,db])))
  have source5 : Subsingleton (E.Page 3 (5,130)) := by
    have hd := h163.eq_on_page_two.2
    change E.d 2 (5,130) (I.interpretation.basis .sphere 5 130 0)=I.interpretation.basis .sphere 7 131 2 at hd
    have hn : I.interpretation.basis .sphere 7 131 2 ≠ 0 := by
      rw [←he7_131_2]
      intro h
      have hh := congrArg (fun x => e7_131 x 2) h
      simp at hh
    have ker (x : E.Page 2 (5,130)) (hx : E.d 2 (5,130) x=0) : x=0 := by
      rcases generated_one (by decide : (2:ℤ)≤2) e5_130 _ (by rw [he5_130_0]; exact hrep2 _) x with h|h
      · exact h
      · exact (hn (by simpa only [h,hd] using hx)).elim
    have hinj : Function.Injective (E.d 2 (5,130)) := (injective_iff_map_eq_zero _).mpr ker
    let S := E.pageShortComplex 2 ((5,130)-E.diffDeg 2)
    have hs : Function.Injective S.g := hinj
    have hsex : S.Exact := S.moduleCat_exact_iff.mpr (by
      intro z hz
      have hz0 : z=0 := hs (hz.trans (map_zero _).symm)
      exact ⟨0,by simp [hz0]⟩)
    have hzero := (S.exact_iff_isZero_homology).mp hsex
    exact ModuleCat.subsingleton_of_isZero ((pageHomologyIso E 2 (5,130)
      (by change (2:ℤ)≤2; omega)).isZero_iff.mpr hzero)
  have incoming_late (r : ℤ) (hr : 5≤r) : E.d r ((10,134)-E.diffDeg r)=0 := by
    have hz : Subsingleton (E.Page r (10-r,135-r)) := by
      by_cases heq : r=5
      · subst r
        exact adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum 3 5 5 130 (by omega) (by omega) source5
      have hq : 10-r≤4 := by omega
      by_cases hneg : 10-r<0
      · exact adamsTowerInternal_page_subsingleton_of_negative H.unit SphereSpectrum r (10-r) (135-r) hneg
      have hd : (⟨.sphere,(10-r).toNat,(135-r).toNat,[]⟩ : Raw.Degree) ∈ Raw.degrees := by
        have hq0 : 0≤10-r := by omega
        have hrlo : 6≤r := by omega
        have hrhi : r≤10 := by omega
        interval_cases r <;> simp [Raw.degrees]
      obtain ⟨e,_⟩ := I.basis _ hd
      change Page D .sphere (10-r).toNat (135-r).toNat ≃ₗ[ℤ] (Fin 0 →₀ F2) at e
      have he : Subsingleton (Page D .sphere (10-r).toNat (135-r).toNat) := e.injective.subsingleton
      apply adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum 2 r (10-r) (135-r) (by omega) (by omega)
      simpa only [KIP126.Computation.SphereAndCofiber.Page,KIP126.Computation.SphereAndCofiber.sequence,KIP126.Computation.SphereAndCofiber.object,ClassicalObject.obj,
        Int.toNat_of_nonneg (by omega : 0≤10-r),Int.toNat_of_nonneg (by omega : 0≤135-r)] using he
    have hp : (10,134)-E.diffDeg r=(10-r,135-r) := by
      change (10-r,134-(r-1))=(10-r,135-r)
      congr 1; omega
    rw [hp]
    ext x
    change E.d r (10-r,135-r) x=0
    rw [hz.elim x 0,map_zero]
  let ell (x : E.Page 2 (10,134)) : F2 := e10_134 x 1 + e10_134 x 2 + e10_134 x 4
  have ell0 : ell 0=0 := by simp [ell]
  have elladd (x y : E.Page 2 (10,134)) : ell (x+y)=ell x+ell y := by
    dsimp only [ell]
    simp only [map_add,Finsupp.add_apply]
    abel
  have ellsub (x y : E.Page 2 (10,134)) : ell (x-y)=ell x-ell y := by
    dsimp only [ell]
    simp only [map_sub,Finsupp.sub_apply]
    abel
  have ellB (i : Fin 5) : ell (I.interpretation.basis .sphere 10 134 i.val) =
      (Finsupp.single i (1:F2) : Fin 5 →₀ F2) 1 +
      (Finsupp.single i (1:F2) : Fin 5 →₀ F2) 2 +
      (Finsupp.single i (1:F2) : Fin 5 →₀ F2) 4 := by
    rw [←he10_134 i]
    simp only [ell,LinearEquiv.apply_symm_apply]
  have ellB0 : ell (I.interpretation.basis .sphere 10 134 0)=0 := by simpa using ellB 0
  have ellB1 : ell (I.interpretation.basis .sphere 10 134 1)=1 := by simpa using ellB 1
  have ellB2 : ell (I.interpretation.basis .sphere 10 134 2)=1 := by simpa using ellB 2
  have ellB3 : ell (I.interpretation.basis .sphere 10 134 3)=0 := by simpa using ellB 3
  have ellB4 : ell (I.interpretation.basis .sphere 10 134 4)=1 := by simpa using ellB 4
  have ell_incoming2 (x : E.Page 2 (8,133)) : ell (E.d 2 (8,133) x)=0 := by
    rcases incoming2 x with h|h
    · rw [h,ell0]
    · rw [h,elladd,ellB2,ellB4]
      decide
  have nonzero3 {x : E.Page 2 (10,134)} (hx : ell x=1) {a : E.Page 3 (10,134)}
      (ha : RepresentsOnPage E 3 (10,134) x a) : a ≠ 0 := by
    obtain ⟨_,z,hz2,hz3⟩ := ha
    intro hzero
    obtain ⟨b,hb⟩ := (next_projection_zero_iff_incoming E 2
      (by change (2:ℤ)≤2; omega) (8,133) z).mp (hz3.trans hzero)
    have he : E.d 2 (8,133) b=x := hb.trans hz2
    have hh := ell_incoming2 b
    rw [he,hx] at hh
    exact one_ne_zero hh
  have nonzero4 {x : E.Page 2 (10,134)} (hx : ell x=1) {a : E.Page 4 (10,134)}
      (ha : RepresentsOnPage E 4 (10,134) x a) : a ≠ 0 := by
    obtain ⟨b,hb⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤4) ha
    exact represents_next_nonzero_of_incoming_zero_at
      (by change (2:ℤ)≤3; omega) (by decide : (2:ℤ)≤3) (by exact incoming3) ha hb (nonzero3 hx hb)
  have nonzero5 {a : E.Page 5 (10,134)}
      (ha : RepresentsOnPage E 5 (10,134) (I.interpretation.basis .sphere 10 134 4) a) : a ≠ 0 := by
    obtain ⟨_,z,hz2,hz5⟩ := ha
    let A := E.ssData (10,134)
    let i := Subobject.ofLE (A.Z 3) (A.Z 2) (A.Z_anti (by decide : (2:WithTop ℕ)≤3))
    let u4 := A.pageπ 2 (i z)
    have hu4 : RepresentsOnPage E 4 (10,134) (I.interpretation.basis .sphere 10 134 4) u4 := by
      refine ⟨by decide,i z,?_,rfl⟩
      change (i ≫ Subobject.ofLE (A.Z 2) (A.Z 0) _ ≫ A.pageπ 0) z = _
      dsimp only [i]
      rw [←Category.assoc,Subobject.ofLE_comp_ofLE]
      exact hz2
    have un : u4≠0 := nonzero4 ellB4 hu4
    have uy : u4≠y4 := by
      intro h
      have hn := nonzero4 (by rw [ellsub,ellB4,elladd,ellB0,ellB3]; simp) (hsub hu4 hy4)
      exact hn (sub_eq_zero.mpr h)
    have uz : u4≠z4 := by
      intro h
      have hn := nonzero4 (by
        rw [ellsub,ellB4,elladd,elladd,elladd,ellB0,ellB1,ellB3,ellB4]
        decide) (hsub hu4 hz4)
      exact hn (sub_eq_zero.mpr h)
    have uyz : u4≠y4+z4 := by
      intro h
      have hn := nonzero4 (by
        rw [ellsub,ellB4,elladd,elladd,elladd,elladd,elladd,ellB0,ellB1,ellB3,ellB4]
        decide) (hsub hu4 (hadd hy4 hz4))
      exact hn (sub_eq_zero.mpr h)
    intro hzero
    obtain ⟨b,hb⟩ := (next_projection_zero_iff_incoming E 4
      (by change (2:ℤ)≤4; omega) (6,131) z).mp (hz5.trans hzero)
    change E.d 4 (6,131) b=u4 at hb
    rcases incoming4 b with h|h|h|h
    · exact un (hb.symm.trans h)
    · exact uy (hb.symm.trans h)
    · exact uz (hb.symm.trans h)
    · exact uyz (hb.symm.trans h)
  obtain ⟨a,ha⟩ := h249
  refine ⟨a,ha,?_⟩
  obtain ⟨_,z,hz2,hza⟩ := ha
  let A := E.ssData (10,134)
  let i := Subobject.ofLE (A.Z 998) (A.Z 3) (A.Z_anti (by decide : (3:WithTop ℕ)≤998))
  have rep5 : RepresentsOnPage E 5 (10,134) (I.interpretation.basis .sphere 10 134 4) (A.pageπ 3 (i z)) := by
    refine ⟨by decide,i z,?_,rfl⟩
    change (i ≫ Subobject.ofLE (A.Z 3) (A.Z 0) _ ≫ A.pageπ 0) z = _
    dsimp only [i]
    rw [←Category.assoc,Subobject.ofLE_comp_ofLE]
    exact hz2
  have hB : A.B ⊤=A.B 3 := boundaries_top_eq_of_d_eq_zero E 5 (by change (2:ℤ)≤5; omega) (10,134) incoming_late
  intro ha0
  have hb := (subobject_cokernel_π_eq_zero_iff (A.B 998) (A.Z 998) (A.B_le_Z _) z).mp (hza.trans ha0)
  have hb' := (ModuleCat.subobjectModule A.V).monotone (A.B_mono (show (998:WithTop ℕ)≤⊤ from le_top)) hb
  rw [hB] at hb'
  apply nonzero5 rep5
  apply (subobject_cokernel_π_eq_zero_iff (A.B 3) (A.Z 3) (A.B_le_Z _) (i z)).mpr
  change (i ≫ (A.Z 3).arrow) z ∈ _
  dsimp only [i]
  rwa [Subobject.ofLE_arrow]

private theorem p_survives1000_h198 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 3 (8,131) (11,133) (I.interpretation.basis .sphere 8 131 0) (I.interpretation.basis .sphere 11 133 0 + I.interpretation.basis .sphere 11 133 1) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere, .equation, 3, 8, 131, [0], 11, 133, [0, 1], "S0_AdamsE2_ss", 2488⟩ (by
    exact List.mem_of_getElem? (i := 198) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (8,131) (11,133) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 131 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 11 133 [0, 1] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem p_survives1000_h199 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (8,132) (10,133) (I.interpretation.basis .sphere 8 132 0) (I.interpretation.basis .sphere 10 133 2) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere, .equation, 2, 8, 132, [0], 10, 133, [2], "S0_AdamsE2_ss", 2571⟩ (by
    exact List.mem_of_getElem? (i := 199) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (8,132) (10,133) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 132 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 10 133 [2] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem p_survives1000_h219 (I : AdamsComputationTheorems D L G) : ReachesPage (sequence D .sphere) 12 (9,132) (I.interpretation.basis .sphere 9 132 0 + I.interpretation.basis .sphere 9 132 1) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere, .reaches, 12, 9, 132, [0, 1], 9, 132, [], "S0_AdamsE2_ss", 2569⟩ (by
    exact List.mem_of_getElem? (i := 219) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨a,ha,h⟩ := hrow
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 132 [0, 1] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha
  rw [←ha] at h
  exact h

private theorem p_survives1000_h220 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 3 (9,132) (12,134) (I.interpretation.basis .sphere 9 132 1) (I.interpretation.basis .sphere 12 134 1 + I.interpretation.basis .sphere 12 134 2) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere, .equation, 3, 9, 132, [1], 12, 134, [1, 2], "S0_AdamsE2_ss", 2570⟩ (by
    exact List.mem_of_getElem? (i := 220) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (9,132) (12,134) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 132 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 134 [1, 2] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem p_survives1000_h245 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (10,133) (12,134) (I.interpretation.basis .sphere 10 133 1) (I.interpretation.basis .sphere 12 134 2) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere, .equation, 2, 10, 133, [1], 12, 134, [2], "S0_AdamsE2_ss", 2625⟩ (by
    exact List.mem_of_getElem? (i := 245) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (10,133) (12,134) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 133 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 134 [2] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem p_survives1000_h268 (I : AdamsComputationTheorems D L G) : ReachesPage (sequence D .sphere) 1000 (11,133) (I.interpretation.basis .sphere 11 133 1) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere, .reaches, 1000, 11, 133, [1], 11, 133, [], "S0_AdamsE2_ss", 2622⟩ (by
    exact List.mem_of_getElem? (i := 268) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨a,ha,h⟩ := hrow
  have vx : Raw.coordinatesValid Raw.degrees .sphere 11 133 [1] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha
  rw [←ha] at h
  exact h

private theorem p_survives1000_h295 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 3 (9,132) (12,134) (I.interpretation.basis .sphere 9 132 0) (I.interpretation.basis .sphere 12 134 1) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere, .equation, 3, 9, 132, [0], 12, 134, [1], "S0_AdamsE2_ss", 2683⟩ (by
    exact List.mem_of_getElem? (i := 295) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (9,132) (12,134) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 132 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 134 [1] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem p_survives1000_h296 (I : AdamsComputationTheorems D L G) : ReachesPage (sequence D .sphere) 1000 (12,134) (I.interpretation.basis .sphere 12 134 0) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere, .reaches, 1000, 12, 134, [0], 12, 134, [], "S0_AdamsE2_ss", 2684⟩ (by
    exact List.mem_of_getElem? (i := 296) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨a,ha,h⟩ := hrow
  have vx : Raw.coordinatesValid Raw.degrees .sphere 12 134 [0] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha
  rw [←ha] at h
  exact h

set_option maxHeartbeats 800000 in
private theorem p_survives1000
    {C : Type u} [StableHomotopyCategory.{u,v} C] [HasFunctorialCofiber (C:=C)]
    {Syn : Type w} [SyntheticCategory.{w,v} Syn] [HasFunctorialCofiber (C:=Syn)]
    {H : Mod2EilenbergMacLane (C:=C)} {M : MilnorCooperations H} {D : AdamsComparison H M Syn}
    {L : SphereAdamsClasses H} {G : KIP126.Literature.AdamsSynthetic.TmfDetectionClasses H} (I : AdamsComputationTheorems D L G) :
    SurvivesTo (sequence D .sphere) 1000 (11,133) (I.interpretation.basis .sphere 11 133 1) := by
  classical
  let E := sequence D .sphere
  obtain ⟨e11_133,he11_133⟩ := I.basis ⟨.sphere, 11, 133, ["371,1", "69,1,79,1"]⟩ (by
    exact List.mem_of_getElem? (i := 189) (by rfl))
  change E.Page 2 (11,133) ≃ₗ[ℤ] (Fin 2 →₀ F2) at e11_133
  change ∀i : Fin 2, e11_133.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 11 133 i.val at he11_133
  have he11_133_0 : e11_133.symm (Finsupp.single 0 1) = I.interpretation.basis .sphere 11 133 0 := he11_133 0
  have he11_133_1 : e11_133.symm (Finsupp.single 1 1) = I.interpretation.basis .sphere 11 133 1 := he11_133 1
  obtain ⟨e12_134,he12_134⟩ := I.basis ⟨.sphere, 12, 134, ["18,1,188,1", "0,1,371,1", "0,1,69,1,79,1"]⟩ (by
    exact List.mem_of_getElem? (i := 198) (by rfl))
  change E.Page 2 (12,134) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e12_134
  change ∀i : Fin 3, e12_134.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 12 134 i.val at he12_134
  have he12_134_0 : e12_134.symm (Finsupp.single 0 1) = I.interpretation.basis .sphere 12 134 0 := he12_134 0
  have he12_134_1 : e12_134.symm (Finsupp.single 1 1) = I.interpretation.basis .sphere 12 134 1 := he12_134 1
  have he12_134_2 : e12_134.symm (Finsupp.single 2 1) = I.interpretation.basis .sphere 12 134 2 := he12_134 2
  obtain ⟨e10_133,he10_133⟩ := I.basis ⟨.sphere, 10, 133, ["372,1", "69,1,80,1", "0,1,366,1"]⟩ (by
    exact List.mem_of_getElem? (i := 180) (by rfl))
  change E.Page 2 (10,133) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e10_133
  change ∀i : Fin 3, e10_133.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 10 133 i.val at he10_133
  have he10_133_0 : e10_133.symm (Finsupp.single 0 1) = I.interpretation.basis .sphere 10 133 0 := he10_133 0
  have he10_133_1 : e10_133.symm (Finsupp.single 1 1) = I.interpretation.basis .sphere 10 133 1 := he10_133 1
  have he10_133_2 : e10_133.symm (Finsupp.single 2 1) = I.interpretation.basis .sphere 10 133 2 := he10_133 2
  obtain ⟨e9_132,he9_132⟩ := I.basis ⟨.sphere, 9, 132, ["366,1", "0,1,352,1"]⟩ (by
    exact List.mem_of_getElem? (i := 171) (by rfl))
  change E.Page 2 (9,132) ≃ₗ[ℤ] (Fin 2 →₀ F2) at e9_132
  change ∀i : Fin 2, e9_132.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 9 132 i.val at he9_132
  have he9_132_0 : e9_132.symm (Finsupp.single 0 1) = I.interpretation.basis .sphere 9 132 0 := he9_132 0
  have he9_132_1 : e9_132.symm (Finsupp.single 1 1) = I.interpretation.basis .sphere 9 132 1 := he9_132 1
  obtain ⟨e8_131,he8_131⟩ := I.basis ⟨.sphere, 8, 131, ["352,1"]⟩ (by
    exact List.mem_of_getElem? (i := 159) (by rfl))
  change E.Page 2 (8,131) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e8_131
  change ∀i : Fin 1, e8_131.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 8 131 i.val at he8_131
  have he8_131_0 : e8_131.symm (Finsupp.single 0 1) = I.interpretation.basis .sphere 8 131 0 := he8_131 0
  have h198 : HasDifferential E 3 (8,131) (11,133) (I.interpretation.basis .sphere 8 131 0) (I.interpretation.basis .sphere 11 133 0 + I.interpretation.basis .sphere 11 133 1) := p_survives1000_h198 I
  have h199 : HasDifferential E 2 (8,132) (10,133) (I.interpretation.basis .sphere 8 132 0) (I.interpretation.basis .sphere 10 133 2) := p_survives1000_h199 I
  have h219 : ReachesPage E 12 (9,132) (I.interpretation.basis .sphere 9 132 0 + I.interpretation.basis .sphere 9 132 1) := p_survives1000_h219 I
  have h220 : HasDifferential E 3 (9,132) (12,134) (I.interpretation.basis .sphere 9 132 1) (I.interpretation.basis .sphere 12 134 1 + I.interpretation.basis .sphere 12 134 2) := p_survives1000_h220 I
  have h245 : HasDifferential E 2 (10,133) (12,134) (I.interpretation.basis .sphere 10 133 1) (I.interpretation.basis .sphere 12 134 2) := p_survives1000_h245 I
  have h268 : ReachesPage E 1000 (11,133) (I.interpretation.basis .sphere 11 133 1) := p_survives1000_h268 I
  have h295 : HasDifferential E 3 (9,132) (12,134) (I.interpretation.basis .sphere 9 132 0) (I.interpretation.basis .sphere 12 134 1) := p_survives1000_h295 I
  have h296 : ReachesPage E 1000 (12,134) (I.interpretation.basis .sphere 12 134 0) := p_survives1000_h296 I
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
  have generated_one {r : ℤ} (hr : 2≤r) {p : ℤ×ℤ}
      (e : E.Page 2 p ≃ₗ[ℤ] (Fin 1 →₀ F2)) (a : E.Page r p)
      (ha : RepresentsOnPage E r p (e.symm (Finsupp.single 0 1)) a)
      (x : E.Page r p) : x=0 ∨ x=a := by
    exact FinitePageCalculus.generated_one hr e a ha x
  have generated_two {r : ℤ} (hr : 2≤r) {p : ℤ×ℤ}
      (e : E.Page 2 p ≃ₗ[ℤ] (Fin 2 →₀ F2)) (a b : E.Page r p)
      (ha : RepresentsOnPage E r p (e.symm (Finsupp.single 0 1)) a)
      (hb : RepresentsOnPage E r p (e.symm (Finsupp.single 1 1)) b)
      (x : E.Page r p) : x=0 ∨ x=a ∨ x=b ∨ x=a+b := by
    exact FinitePageCalculus.generated_two hr e a b ha hb x
  have low123 (r q : ℤ) (hr : 2≤r) (hq : q≤7) : Subsingleton (E.Page r (q,q+123)) := by
    by_cases hneg : q<0
    · exact adamsTowerInternal_page_subsingleton_of_negative H.unit SphereSpectrum r q (q+123) hneg
    have hq0 : 0≤q := by omega
    have hd : (⟨.sphere,q.toNat,(q+123).toNat,[]⟩ : Raw.Degree) ∈ Raw.degrees := by
      interval_cases q <;> simp [Raw.degrees]
    obtain ⟨e,_⟩ := I.basis _ hd
    change KIP126.Computation.SphereAndCofiber.Page D .sphere q.toNat (q+123).toNat ≃ₗ[ℤ] (Fin 0 →₀ F2) at e
    have he : Subsingleton (KIP126.Computation.SphereAndCofiber.Page D .sphere q.toNat (q+123).toNat) := e.injective.subsingleton
    apply adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum 2 r q (q+123) (by omega) hr
    simpa only [KIP126.Computation.SphereAndCofiber.Page,KIP126.Computation.SphereAndCofiber.sequence,KIP126.Computation.SphereAndCofiber.object,ClassicalObject.obj,
      Int.toNat_of_nonneg hq0,Int.toNat_of_nonneg (by omega : 0≤q+123)] using he
  obtain ⟨_,a30,t30,ha30,ht30,hda30⟩ := h295
  obtain ⟨_,a31,t31,ha31,ht31,hda31⟩ := h220
  have d2_9 : E.d 2 (9,132)=0 := by
    have d0 := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) (hrep2 _) ⟨a30,ha30⟩
    have d1 := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) (hrep2 _) ⟨a31,ha31⟩
    ext x
    rcases generated_two (by decide : (2:ℤ)≤2) e9_132 _ _
      (by rw [he9_132_0];exact hrep2 _) (by rw [he9_132_1];exact hrep2 _) x with h|h|h|h
    all_goals simp only [h,map_add,map_zero,d0,d1,zero_add,ModuleCat.hom_zero,LinearMap.zero_apply]
  obtain ⟨_,a3,t3,ha3,ht3,hda3⟩ := h198
  have incoming3 (x : E.Page 3 (8,131)) : E.d 3 (8,131) x=0 ∨ E.d 3 (8,131) x=t3 := by
    have hd : E.d 3 (8,131) a3=t3 := hda3
    rcases generated_one (by decide : (2:ℤ)≤3) e8_131 a3 (by rw [he8_131_0];exact ha3) x with h|h
    · exact Or.inl (by rw [h,map_zero])
    · exact Or.inr (by rw [h,hd])
  have nonzero3 {x : E.Page 2 (11,133)} (hx : x≠0) {a : E.Page 3 (11,133)}
      (ha : RepresentsOnPage E 3 (11,133) x a) : a≠0 :=
    represents_next_nonzero_of_incoming_zero_at (by change (2:ℤ)≤2;omega) (by decide : (2:ℤ)≤2)
      (by exact d2_9) ha (hrep2 x) hx
  have nonzero4 {a : E.Page 4 (11,133)}
      (ha : RepresentsOnPage E 4 (11,133) (I.interpretation.basis .sphere 11 133 1) a) : a≠0 := by
    obtain ⟨_,z,hz2,hz4⟩ := ha
    let A := E.ssData (11,133)
    let i := Subobject.ofLE (A.Z 2) (A.Z 1) (A.Z_anti (by decide : (1:WithTop ℕ)≤2))
    let p3 := A.pageπ 1 (i z)
    have hp3 : RepresentsOnPage E 3 (11,133) (I.interpretation.basis .sphere 11 133 1) p3 := by
      refine ⟨by decide,i z,?_,rfl⟩
      change (i ≫ Subobject.ofLE (A.Z 1) (A.Z 0) _ ≫ A.pageπ 0) z = _
      dsimp only [i]
      rw [←Category.assoc,Subobject.ofLE_comp_ofLE]
      exact hz2
    have pn : p3≠0 := nonzero3 (by
      rw [←he11_133_1]
      intro h
      have hh := congrArg (fun x => e11_133 x 1) h
      simp at hh) hp3
    have pt : p3≠t3 := by
      intro h
      have hn := nonzero3 (by
        rw [←he11_133_0,←he11_133_1]
        intro h
        have hh := congrArg (fun x => e11_133 x 0) h
        simp only [map_add,map_sub,LinearEquiv.apply_symm_apply,map_zero,Finsupp.add_apply,Finsupp.sub_apply] at hh
        norm_num at hh) (hsub hp3 ht3)
      exact hn (sub_eq_zero.mpr h)
    intro hzero
    obtain ⟨b,hb⟩ := (next_projection_zero_iff_incoming E 3
      (by change (2:ℤ)≤3;omega) (8,131) z).mp (hz4.trans hzero)
    change E.d 3 (8,131) b=p3 at hb
    rcases incoming3 b with h|h
    · exact pn (hb.symm.trans h)
    · exact pt (hb.symm.trans h)
  have incoming_late (r : ℤ) (hr : 4≤r) : E.d r ((11,133)-E.diffDeg r)=0 := by
    have hp : (11,133)-E.diffDeg r=(11-r,(11-r)+123) := by
      change (11-r,133-(r-1))=(11-r,(11-r)+123)
      congr 1; omega
    rw [hp]
    have hz := low123 r (11-r) (by omega) (by omega)
    ext x
    change E.d r _ x=0
    rw [hz.elim x 0,map_zero]
  obtain ⟨a,ha⟩ := h268
  refine ⟨a,ha,?_⟩
  obtain ⟨_,z,hz2,hza⟩ := ha
  let A := E.ssData (11,133)
  let i := Subobject.ofLE (A.Z 998) (A.Z 2) (A.Z_anti (by decide : (2:WithTop ℕ)≤998))
  have rep4 : RepresentsOnPage E 4 (11,133) (I.interpretation.basis .sphere 11 133 1) (A.pageπ 2 (i z)) := by
    refine ⟨by decide,i z,?_,rfl⟩
    change (i ≫ Subobject.ofLE (A.Z 2) (A.Z 0) _ ≫ A.pageπ 0) z = _
    dsimp only [i]
    rw [←Category.assoc,Subobject.ofLE_comp_ofLE]
    exact hz2
  have hB : A.B ⊤=A.B 2 := boundaries_top_eq_of_d_eq_zero E 4 (by change (2:ℤ)≤4;omega) (11,133) incoming_late
  intro ha0
  have hb := (subobject_cokernel_π_eq_zero_iff (A.B 998) (A.Z 998) (A.B_le_Z _) z).mp (hza.trans ha0)
  have hb' := (ModuleCat.subobjectModule A.V).monotone (A.B_mono (show (998:WithTop ℕ)≤⊤ from le_top)) hb
  rw [hB] at hb'
  apply nonzero4 rep4
  apply (subobject_cokernel_π_eq_zero_iff (A.B 2) (A.Z 2) (A.B_le_Z _) (i z)).mpr
  change (i ≫ (A.Z 2).arrow) z ∈ _
  dsimp only [i]
  rwa [Subobject.ofLE_arrow]

private theorem q_survives1000_h198 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 3 (8,131) (11,133) (I.interpretation.basis .sphere 8 131 0) (I.interpretation.basis .sphere 11 133 0 + I.interpretation.basis .sphere 11 133 1) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere, .equation, 3, 8, 131, [0], 11, 133, [0, 1], "S0_AdamsE2_ss", 2488⟩ (by
    exact List.mem_of_getElem? (i := 198) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (8,131) (11,133) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 131 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 11 133 [0, 1] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem q_survives1000_h199 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (8,132) (10,133) (I.interpretation.basis .sphere 8 132 0) (I.interpretation.basis .sphere 10 133 2) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere, .equation, 2, 8, 132, [0], 10, 133, [2], "S0_AdamsE2_ss", 2571⟩ (by
    exact List.mem_of_getElem? (i := 199) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (8,132) (10,133) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 132 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 10 133 [2] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem q_survives1000_h220 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 3 (9,132) (12,134) (I.interpretation.basis .sphere 9 132 1) (I.interpretation.basis .sphere 12 134 1 + I.interpretation.basis .sphere 12 134 2) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere, .equation, 3, 9, 132, [1], 12, 134, [1, 2], "S0_AdamsE2_ss", 2570⟩ (by
    exact List.mem_of_getElem? (i := 220) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (9,132) (12,134) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 132 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 134 [1, 2] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem q_survives1000_h245 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (10,133) (12,134) (I.interpretation.basis .sphere 10 133 1) (I.interpretation.basis .sphere 12 134 2) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere, .equation, 2, 10, 133, [1], 12, 134, [2], "S0_AdamsE2_ss", 2625⟩ (by
    exact List.mem_of_getElem? (i := 245) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (10,133) (12,134) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 133 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 134 [2] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem q_survives1000_h295 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 3 (9,132) (12,134) (I.interpretation.basis .sphere 9 132 0) (I.interpretation.basis .sphere 12 134 1) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere, .equation, 3, 9, 132, [0], 12, 134, [1], "S0_AdamsE2_ss", 2683⟩ (by
    exact List.mem_of_getElem? (i := 295) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (9,132) (12,134) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 132 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 134 [1] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem q_survives1000_h296 (I : AdamsComputationTheorems D L G) : ReachesPage (sequence D .sphere) 1000 (12,134) (I.interpretation.basis .sphere 12 134 0) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere, .reaches, 1000, 12, 134, [0], 12, 134, [], "S0_AdamsE2_ss", 2684⟩ (by
    exact List.mem_of_getElem? (i := 296) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨a,ha,h⟩ := hrow
  have vx : Raw.coordinatesValid Raw.degrees .sphere 12 134 [0] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha
  rw [←ha] at h
  exact h

private theorem q_survives1000_h294 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (10,133) (12,134) (I.interpretation.basis .sphere 10 133 0) (I.interpretation.basis .sphere 12 134 2) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere, .equation, 2, 10, 133, [0], 12, 134, [2], "S0_AdamsE2_ss", 2682⟩ (by
    exact List.mem_of_getElem? (i := 294) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (10,133) (12,134) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 133 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 134 [2] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem q_survives1000_nonzero4
    {C : Type u} [StableHomotopyCategory.{u,v} C] [HasFunctorialCofiber (C:=C)]
    {Syn : Type w} [SyntheticCategory.{w,v} Syn] [HasFunctorialCofiber (C:=Syn)]
    {H : Mod2EilenbergMacLane (C:=C)} {M : MilnorCooperations H} {D : AdamsComparison H M Syn}
    {L : SphereAdamsClasses H} {G : KIP126.Literature.AdamsSynthetic.TmfDetectionClasses H}     (I : AdamsComputationTheorems D L G) {a : (sequence D .sphere).Page 4 (12,134)}
      (ha : RepresentsOnPage (sequence D .sphere) 4 (12,134) (I.interpretation.basis .sphere 12 134 0) a) : a≠0  := by
  classical
  let E := sequence D .sphere
  obtain ⟨e12_134,he12_134⟩ := I.basis ⟨.sphere, 12, 134, ["18,1,188,1", "0,1,371,1", "0,1,69,1,79,1"]⟩ (by
    exact List.mem_of_getElem? (i := 198) (by rfl))
  change E.Page 2 (12,134) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e12_134
  change ∀i : Fin 3, e12_134.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 12 134 i.val at he12_134
  have he12_134_0 : e12_134.symm (Finsupp.single 0 1) = I.interpretation.basis .sphere 12 134 0 := he12_134 0
  have he12_134_1 : e12_134.symm (Finsupp.single 1 1) = I.interpretation.basis .sphere 12 134 1 := he12_134 1
  have he12_134_2 : e12_134.symm (Finsupp.single 2 1) = I.interpretation.basis .sphere 12 134 2 := he12_134 2
  obtain ⟨e10_133,he10_133⟩ := I.basis ⟨.sphere, 10, 133, ["372,1", "69,1,80,1", "0,1,366,1"]⟩ (by
    exact List.mem_of_getElem? (i := 180) (by rfl))
  change E.Page 2 (10,133) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e10_133
  change ∀i : Fin 3, e10_133.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 10 133 i.val at he10_133
  obtain ⟨e9_132,he9_132⟩ := I.basis ⟨.sphere, 9, 132, ["366,1", "0,1,352,1"]⟩ (by
    exact List.mem_of_getElem? (i := 171) (by rfl))
  change E.Page 2 (9,132) ≃ₗ[ℤ] (Fin 2 →₀ F2) at e9_132
  change ∀i : Fin 2, e9_132.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 9 132 i.val at he9_132
  have he9_132_0 : e9_132.symm (Finsupp.single 0 1) = I.interpretation.basis .sphere 9 132 0 := he9_132 0
  have he9_132_1 : e9_132.symm (Finsupp.single 1 1) = I.interpretation.basis .sphere 9 132 1 := he9_132 1
  have h199 : HasDifferential E 2 (8,132) (10,133) (I.interpretation.basis .sphere 8 132 0) (I.interpretation.basis .sphere 10 133 2) := q_survives1000_h199 I
  have h220 : HasDifferential E 3 (9,132) (12,134) (I.interpretation.basis .sphere 9 132 1) (I.interpretation.basis .sphere 12 134 1 + I.interpretation.basis .sphere 12 134 2) := q_survives1000_h220 I
  have h245 : HasDifferential E 2 (10,133) (12,134) (I.interpretation.basis .sphere 10 133 1) (I.interpretation.basis .sphere 12 134 2) := q_survives1000_h245 I
  have h295 : HasDifferential E 3 (9,132) (12,134) (I.interpretation.basis .sphere 9 132 0) (I.interpretation.basis .sphere 12 134 1) := q_survives1000_h295 I
  have hadd {r : ℤ} {p : ℤ × ℤ} {x y : E.Page 2 p} {a b : E.Page r p}
      (hx : RepresentsOnPage E r p x a) (hy : RepresentsOnPage E r p y b) :
      RepresentsOnPage E r p (x+y) (a+b) := by
    exact represents_add_tail (by assumption) (by assumption)
  have hsub {r : ℤ} {p : ℤ × ℤ} {x y : E.Page 2 p} {a b : E.Page r p}
      (hx : RepresentsOnPage E r p x a) (hy : RepresentsOnPage E r p y b) :
      RepresentsOnPage E r p (x-y) (a-b) := by
    exact represents_sub_tail (by assumption) (by assumption)
  have generated_two {r : ℤ} (hr : 2≤r) {p : ℤ×ℤ}
      (e : E.Page 2 p ≃ₗ[ℤ] (Fin 2 →₀ F2)) (a b : E.Page r p)
      (ha : RepresentsOnPage E r p (e.symm (Finsupp.single 0 1)) a)
      (hb : RepresentsOnPage E r p (e.symm (Finsupp.single 1 1)) b)
      (x : E.Page r p) : x=0 ∨ x=a ∨ x=b ∨ x=a+b := by
    exact FinitePageCalculus.generated_two hr e a b ha hb x
  have h294 : HasDifferential E 2 (10,133) (12,134) (I.interpretation.basis .sphere 10 133 0) (I.interpretation.basis .sphere 12 134 2) := q_survives1000_h294 I
  obtain ⟨_,a30,t30,ha30,ht30,hda30⟩ := h295
  obtain ⟨_,a31,t31,ha31,ht31,hda31⟩ := h220
  let ell (x : E.Page 2 (12,134)) : F2 := e12_134 x 0
  have ell0 : ell 0=0 := by simp [ell]
  have elladd (x y : E.Page 2 (12,134)) : ell (x+y)=ell x+ell y := by simp [ell]
  have ellsub (x y : E.Page 2 (12,134)) : ell (x-y)=ell x-ell y := by simp [ell]
  have ellB0 : ell (I.interpretation.basis .sphere 12 134 0)=1 := by
    rw [←he12_134_0]
    simp [ell]
  have ellB1 : ell (I.interpretation.basis .sphere 12 134 1)=0 := by
    rw [←he12_134_1]
    simp [ell]
  have ellB2 : ell (I.interpretation.basis .sphere 12 134 2)=0 := by
    rw [←he12_134_2]
    simp [ell]
  have ell_incoming2 (x : E.Page 2 (10,133)) : ell (E.d 2 (10,133) x)=0 := by
    have d0 := h294.eq_on_page_two.2
    have d1 := h245.eq_on_page_two.2
    change E.d 2 (10,133) (I.interpretation.basis .sphere 10 133 0)=I.interpretation.basis .sphere 12 134 2 at d0
    change E.d 2 (10,133) (I.interpretation.basis .sphere 10 133 1)=I.interpretation.basis .sphere 12 134 2 at d1
    have d2 : E.d 2 (10,133) (I.interpretation.basis .sphere 10 133 2)=0 := by
      have hd := h199.eq_on_page_two.2
      change E.d 2 (8,132) _ = _ at hd
      rw [←hd]
      exact congrArg (fun f => f (I.interpretation.basis .sphere 8 132 0)) (E.d_comp_d 2 (8,132))
    have one (i : Fin 3) : ell (E.d 2 (10,133) (e10_133.symm (Finsupp.single i 1)))=0 := by
      rw [he10_133]
      fin_cases i
      · rw [d0,ellB2]
      · rw [d1,ellB2]
      · rw [d2,ell0]
    have all (f : Fin 3 →₀ F2) : ell (E.d 2 (10,133) (e10_133.symm f))=0 := by
      induction f using Finsupp.induction with
      | zero => simp only [map_zero,ell0]
      | @single_add i a f hi ha ih =>
        rw [map_add,map_add,elladd,ih,add_zero]
        fin_cases a
        · simp only [Fin.mk_zero,Finsupp.single_zero,map_zero,ell0]
        · exact one i
    simpa only [LinearEquiv.symm_apply_apply] using all (e10_133 x)
  have nonzero3 {x : E.Page 2 (12,134)} (hx : ell x=1) {a : E.Page 3 (12,134)}
      (ha : RepresentsOnPage E 3 (12,134) x a) : a≠0 := by
    obtain ⟨_,z,hz2,hz3⟩ := ha
    intro ha0
    obtain ⟨b,hb⟩ := (next_projection_zero_iff_incoming E 2
      (by change (2:ℤ)≤2;omega) (10,133) z).mp (hz3.trans ha0)
    have he : E.d 2 (10,133) b=x := hb.trans hz2
    have hh := ell_incoming2 b
    rw [he,hx] at hh
    exact one_ne_zero hh

  obtain ⟨_,z,hz2,hz4⟩ := ha
  let A := E.ssData (12,134)
  let i := Subobject.ofLE (A.Z 2) (A.Z 1) (A.Z_anti (by decide : (1:WithTop ℕ)≤2))
  let q3 := A.pageπ 1 (i z)
  have hq3 : RepresentsOnPage E 3 (12,134) (I.interpretation.basis .sphere 12 134 0) q3 := by
    refine ⟨by decide,i z,?_,rfl⟩
    change (i ≫ Subobject.ofLE (A.Z 1) (A.Z 0) _ ≫ A.pageπ 0) z = _
    dsimp only [i]
    rw [←Category.assoc,Subobject.ofLE_comp_ofLE]
    exact hz2
  have avoid {x : E.Page 2 (12,134)} {t : E.Page 3 (12,134)}
      (hx : ell x=0) (ht : RepresentsOnPage E 3 (12,134) x t) : q3≠t := by
    intro h
    have hn := nonzero3 (by rw [ellsub,ellB0,hx,sub_zero]) (hsub hq3 ht)
    exact hn (sub_eq_zero.mpr h)
  have qn : q3≠0 := nonzero3 ellB0 hq3
  have q0 : q3≠t30 := avoid ellB1 ht30
  have q1 : q3≠t31 := avoid (by rw [elladd,ellB1,ellB2,add_zero]) ht31
  have q01 : q3≠t30+t31 := avoid (by simp only [elladd,ellB1,ellB2,add_zero]) (hadd ht30 ht31)
  intro ha0
  obtain ⟨b,hb⟩ := (next_projection_zero_iff_incoming E 3
    (by change (2:ℤ)≤3;omega) (9,132) z).mp (hz4.trans ha0)
  change E.d 3 (9,132) b=q3 at hb
  have d0 : E.d 3 (9,132) a30=t30 := hda30
  have d1 : E.d 3 (9,132) a31=t31 := hda31
  rcases generated_two (by decide : (2:ℤ)≤3) e9_132 a30 a31
    (by rw [he9_132_0];exact ha30) (by rw [he9_132_1];exact ha31) b with h|h|h|h
  · apply qn
    simpa only [h,map_zero] using hb.symm
  · apply q0
    simpa only [h,d0] using hb.symm
  · apply q1
    simpa only [h,d1] using hb.symm
  · apply q01
    simpa only [h,map_add,d0,d1] using hb.symm

private theorem q_survives1000_source8
    {C : Type u} [StableHomotopyCategory.{u,v} C] [HasFunctorialCofiber (C:=C)]
    {Syn : Type w} [SyntheticCategory.{w,v} Syn] [HasFunctorialCofiber (C:=Syn)]
    {H : Mod2EilenbergMacLane (C:=C)} {M : MilnorCooperations H} {D : AdamsComparison H M Syn}
    {L : SphereAdamsClasses H} {G : KIP126.Literature.AdamsSynthetic.TmfDetectionClasses H}     (I : AdamsComputationTheorems D L G) : Subsingleton ((sequence D .sphere).Page 4 (8,131))  := by
  classical
  let E := sequence D .sphere
  obtain ⟨e11_133,he11_133⟩ := I.basis ⟨.sphere, 11, 133, ["371,1", "69,1,79,1"]⟩ (by
    exact List.mem_of_getElem? (i := 189) (by rfl))
  change E.Page 2 (11,133) ≃ₗ[ℤ] (Fin 2 →₀ F2) at e11_133
  change ∀i : Fin 2, e11_133.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 11 133 i.val at he11_133
  have he11_133_0 : e11_133.symm (Finsupp.single 0 1) = I.interpretation.basis .sphere 11 133 0 := he11_133 0
  have he11_133_1 : e11_133.symm (Finsupp.single 1 1) = I.interpretation.basis .sphere 11 133 1 := he11_133 1
  obtain ⟨e9_132,he9_132⟩ := I.basis ⟨.sphere, 9, 132, ["366,1", "0,1,352,1"]⟩ (by
    exact List.mem_of_getElem? (i := 171) (by rfl))
  change E.Page 2 (9,132) ≃ₗ[ℤ] (Fin 2 →₀ F2) at e9_132
  change ∀i : Fin 2, e9_132.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 9 132 i.val at he9_132
  have he9_132_0 : e9_132.symm (Finsupp.single 0 1) = I.interpretation.basis .sphere 9 132 0 := he9_132 0
  have he9_132_1 : e9_132.symm (Finsupp.single 1 1) = I.interpretation.basis .sphere 9 132 1 := he9_132 1
  obtain ⟨e8_131,he8_131⟩ := I.basis ⟨.sphere, 8, 131, ["352,1"]⟩ (by
    exact List.mem_of_getElem? (i := 159) (by rfl))
  change E.Page 2 (8,131) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e8_131
  change ∀i : Fin 1, e8_131.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 8 131 i.val at he8_131
  have he8_131_0 : e8_131.symm (Finsupp.single 0 1) = I.interpretation.basis .sphere 8 131 0 := he8_131 0
  have h198 : HasDifferential E 3 (8,131) (11,133) (I.interpretation.basis .sphere 8 131 0) (I.interpretation.basis .sphere 11 133 0 + I.interpretation.basis .sphere 11 133 1) := q_survives1000_h198 I
  have h220 : HasDifferential E 3 (9,132) (12,134) (I.interpretation.basis .sphere 9 132 1) (I.interpretation.basis .sphere 12 134 1 + I.interpretation.basis .sphere 12 134 2) := q_survives1000_h220 I
  have h295 : HasDifferential E 3 (9,132) (12,134) (I.interpretation.basis .sphere 9 132 0) (I.interpretation.basis .sphere 12 134 1) := q_survives1000_h295 I
  have hrep2 {p : ℤ × ℤ} (x : E.Page 2 p) : RepresentsOnPage E 2 p x x := by
    exact represents_two_self _
  have generated_one {r : ℤ} (hr : 2≤r) {p : ℤ×ℤ}
      (e : E.Page 2 p ≃ₗ[ℤ] (Fin 1 →₀ F2)) (a : E.Page r p)
      (ha : RepresentsOnPage E r p (e.symm (Finsupp.single 0 1)) a)
      (x : E.Page r p) : x=0 ∨ x=a := by
    exact FinitePageCalculus.generated_one hr e a ha x
  have generated_two {r : ℤ} (hr : 2≤r) {p : ℤ×ℤ}
      (e : E.Page 2 p ≃ₗ[ℤ] (Fin 2 →₀ F2)) (a b : E.Page r p)
      (ha : RepresentsOnPage E r p (e.symm (Finsupp.single 0 1)) a)
      (hb : RepresentsOnPage E r p (e.symm (Finsupp.single 1 1)) b)
      (x : E.Page r p) : x=0 ∨ x=a ∨ x=b ∨ x=a+b := by
    exact FinitePageCalculus.generated_two hr e a b ha hb x
  obtain ⟨_,a30,t30,ha30,ht30,hda30⟩ := h295
  obtain ⟨_,a31,t31,ha31,ht31,hda31⟩ := h220
  have d2_9 : E.d 2 (9,132)=0 := by
    have d0 := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) (hrep2 _) ⟨a30,ha30⟩
    have d1 := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) (hrep2 _) ⟨a31,ha31⟩
    ext x
    rcases generated_two (by decide : (2:ℤ)≤2) e9_132 _ _
      (by rw [he9_132_0];exact hrep2 _) (by rw [he9_132_1];exact hrep2 _) x with h|h|h|h
    all_goals simp only [h,map_add,map_zero,d0,d1,zero_add,ModuleCat.hom_zero,LinearMap.zero_apply]
  obtain ⟨_,a3,t3,ha3,ht3,hda3⟩ := h198
  have p_nonzero3 {x : E.Page 2 (11,133)} (hx : x≠0) {a : E.Page 3 (11,133)}
      (ha : RepresentsOnPage E 3 (11,133) x a) : a≠0 :=
    represents_next_nonzero_of_incoming_zero_at (by change (2:ℤ)≤2;omega) (by decide : (2:ℤ)≤2)
      (by exact d2_9) ha (hrep2 x) hx

  have tn : t3≠0 := p_nonzero3 (by
    rw [←he11_133_0,←he11_133_1]
    intro h
    have hh := congrArg (fun x => e11_133 x 0) h
    simp only [map_add,LinearEquiv.apply_symm_apply,map_zero,Finsupp.add_apply] at hh
    norm_num at hh) ht3
  have hd : E.d 3 (8,131) a3=t3 := hda3
  have ker (x : E.Page 3 (8,131)) (hx : E.d 3 (8,131) x=0) : x=0 := by
    rcases generated_one (by decide : (2:ℤ)≤3) e8_131 a3 (by rw [he8_131_0];exact ha3) x with h|h
    · exact h
    · exact (tn (by simpa only [h,hd] using hx)).elim
  have hinj : Function.Injective (E.d 3 (8,131)) := (injective_iff_map_eq_zero _).mpr ker
  let S := E.pageShortComplex 3 ((8,131)-E.diffDeg 3)
  have hs : Function.Injective S.g := hinj
  have hsex : S.Exact := S.moduleCat_exact_iff.mpr (by
    intro z hz
    have hz0 : z=0 := hs (hz.trans (map_zero _).symm)
    exact ⟨0,by simp [hz0]⟩)
  have hzero := (S.exact_iff_isZero_homology).mp hsex
  exact ModuleCat.subsingleton_of_isZero ((pageHomologyIso E 3 (8,131)
    (by change (2:ℤ)≤3;omega)).isZero_iff.mpr hzero)

private theorem q_survives1000
    {C : Type u} [StableHomotopyCategory.{u,v} C] [HasFunctorialCofiber (C:=C)]
    {Syn : Type w} [SyntheticCategory.{w,v} Syn] [HasFunctorialCofiber (C:=Syn)]
    {H : Mod2EilenbergMacLane (C:=C)} {M : MilnorCooperations H} {D : AdamsComparison H M Syn}
    {L : SphereAdamsClasses H} {G : KIP126.Literature.AdamsSynthetic.TmfDetectionClasses H} (I : AdamsComputationTheorems D L G) :
    SurvivesTo (sequence D .sphere) 1000 (12,134) (I.interpretation.basis .sphere 12 134 0) := by
  classical
  let E := sequence D .sphere
  have h296 : ReachesPage E 1000 (12,134) (I.interpretation.basis .sphere 12 134 0) := q_survives1000_h296 I
  have low123 (r q : ℤ) (hr : 2≤r) (hq : q≤7) : Subsingleton (E.Page r (q,q+123)) := by
    by_cases hneg : q<0
    · exact adamsTowerInternal_page_subsingleton_of_negative H.unit SphereSpectrum r q (q+123) hneg
    have hq0 : 0≤q := by omega
    have hd : (⟨.sphere,q.toNat,(q+123).toNat,[]⟩ : Raw.Degree) ∈ Raw.degrees := by
      interval_cases q <;> simp [Raw.degrees]
    obtain ⟨e,_⟩ := I.basis _ hd
    change KIP126.Computation.SphereAndCofiber.Page D .sphere q.toNat (q+123).toNat ≃ₗ[ℤ] (Fin 0 →₀ F2) at e
    have he : Subsingleton (KIP126.Computation.SphereAndCofiber.Page D .sphere q.toNat (q+123).toNat) := e.injective.subsingleton
    apply adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum 2 r q (q+123) (by omega) hr
    simpa only [KIP126.Computation.SphereAndCofiber.Page,KIP126.Computation.SphereAndCofiber.sequence,KIP126.Computation.SphereAndCofiber.object,ClassicalObject.obj,
      Int.toNat_of_nonneg hq0,Int.toNat_of_nonneg (by omega : 0≤q+123)] using he
  have source8 : Subsingleton (E.Page 4 (8,131))  := q_survives1000_source8 I
  have nonzero4 {a : E.Page 4 (12,134)}
      (ha : RepresentsOnPage E 4 (12,134) (I.interpretation.basis .sphere 12 134 0) a) : a≠0  := q_survives1000_nonzero4 I ha
  have incoming_late (r : ℤ) (hr : 4≤r) : E.d r ((12,134)-E.diffDeg r)=0 := by
    have hp : (12,134)-E.diffDeg r=(12-r,(12-r)+123) := by
      change (12-r,134-(r-1))=(12-r,(12-r)+123)
      congr 1; omega
    rw [hp]
    have hz : Subsingleton (E.Page r (12-r,(12-r)+123)) := by
      by_cases he : r=4
      · subst r
        exact source8
      exact low123 r (12-r) (by omega) (by omega)
    ext x
    change E.d r _ x=0
    rw [hz.elim x 0,map_zero]
  obtain ⟨a,ha⟩ := h296
  refine ⟨a,ha,?_⟩
  obtain ⟨_,z,hz2,hza⟩ := ha
  let A := E.ssData (12,134)
  let i := Subobject.ofLE (A.Z 998) (A.Z 2) (A.Z_anti (by decide : (2:WithTop ℕ)≤998))
  have rep4 : RepresentsOnPage E 4 (12,134) (I.interpretation.basis .sphere 12 134 0) (A.pageπ 2 (i z)) := by
    refine ⟨by decide,i z,?_,rfl⟩
    change (i ≫ Subobject.ofLE (A.Z 2) (A.Z 0) _ ≫ A.pageπ 0) z = _
    dsimp only [i]
    rw [←Category.assoc,Subobject.ofLE_comp_ofLE]
    exact hz2
  have hB : A.B ⊤=A.B 2 := boundaries_top_eq_of_d_eq_zero E 4 (by change (2:ℤ)≤4;omega) (12,134) incoming_late
  intro ha0
  have hb := (subobject_cokernel_π_eq_zero_iff (A.B 998) (A.Z 998) (A.B_le_Z _) z).mp (hza.trans ha0)
  have hb' := (ModuleCat.subobjectModule A.V).monotone (A.B_mono (show (998:WithTop ℕ)≤⊤ from le_top)) hb
  rw [hB] at hb'
  apply nonzero4 rep4
  apply (subobject_cokernel_π_eq_zero_iff (A.B 2) (A.Z 2) (A.B_le_Z _) (i z)).mpr
  change (i ≫ (A.Z 2).arrow) z ∈ _
  dsimp only [i]
  rwa [Subobject.ofLE_arrow]

private theorem named_survival_labels
    {C : Type u} [StableHomotopyCategory.{u,v} C] [HasFunctorialCofiber (C:=C)]
    {Syn : Type w} [SyntheticCategory.{w,v} Syn] [HasFunctorialCofiber (C:=Syn)]
    {H : Mod2EilenbergMacLane (C:=C)} {M : MilnorCooperations H} {D : AdamsComparison H M Syn}
    {L : SphereAdamsClasses H} {G : KIP126.Literature.AdamsSynthetic.TmfDetectionClasses H} (I : AdamsComputationTheorems D L G) :
    I.interpretation.sphere 10 134 U = I.interpretation.basis .sphere 10 134 4 ∧
    I.interpretation.sphere 11 133 P = I.interpretation.basis .sphere 11 133 1 ∧
    I.interpretation.sphere 12 134 Q = I.interpretation.basis .sphere 12 134 0 := by
  classical
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
  have p_label : I.interpretation.sphere 11 133 P = I.interpretation.basis .sphere 11 133 1 := by
    have hc := I.monomials (⟨.sphere,11,133,["371,1","69,1,79,1"]⟩ : Raw.Degree) (by
      exact List.mem_of_getElem? (i := 189) (by rfl)) rfl
    obtain ⟨z,hz,he⟩ := hc (1 : Fin 2)
    have heq : P=z := by
      apply Subtype.ext
      rw [hz]
      change generator ⟨69,by decide⟩ * generator ⟨79,by decide⟩ = projection (monomialOfString "69,1,79,1")
      have hs : "69,1,79,1" ≠ "" := by decide
      have hp : (("69,1,79,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [69,1,79,1] := by
        have split : "69,1,79,1".splitOn "," = ["69","1","79","1"] := by
          simp +decide [String.splitOn,String.splitOnAux]
        rw [split]
        simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
          String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
      simp only [monomialOfString,if_neg hs,hp]
      norm_num [polynomialOfPowers,RawData.generatorCount,generator,map_mul,pow_two]
    rw [heq]
    exact he
  have q_label : I.interpretation.sphere 12 134 Q = I.interpretation.basis .sphere 12 134 0 := by
    have hc := I.monomials (⟨.sphere,12,134,["18,1,188,1","0,1,371,1","0,1,69,1,79,1"]⟩ : Raw.Degree) (by
      exact List.mem_of_getElem? (i := 198) (by rfl)) rfl
    obtain ⟨z,hz,he⟩ := hc (0 : Fin 3)
    have heq : Q=z := by
      apply Subtype.ext
      rw [hz]
      change generator ⟨18,by decide⟩ * generator ⟨188,by decide⟩ = projection (monomialOfString "18,1,188,1")
      have hs : "18,1,188,1" ≠ "" := by decide
      have hp : (("18,1,188,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [18,1,188,1] := by
        have split : "18,1,188,1".splitOn "," = ["18","1","188","1"] := by
          simp +decide [String.splitOn,String.splitOnAux]
        rw [split]
        simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
          String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
      simp only [monomialOfString,if_neg hs,hp]
      norm_num [polynomialOfPowers,RawData.generatorCount,generator,map_mul,pow_two]
    rw [heq]
    exact he
  exact ⟨u_label,p_label,q_label⟩

private theorem named_upq_survives1000 (I : AdamsComputationTheorems D L G) :
    Derived.Survival I.interpretation 1000 U ∧
    Derived.Survival I.interpretation 1000 P ∧ Derived.Survival I.interpretation 1000 Q := by
  classical

  obtain ⟨hu,hp,hq⟩ := named_survival_labels I
  constructor
  · change SurvivesTo (sequence D .sphere) 1000 (10,134) _
    rw [hu]
    exact u_survives1000 I
  constructor
  · change SurvivesTo (sequence D .sphere) 1000 (11,133) _
    rw [hp]
    exact p_survives1000 I
  · change SurvivesTo (sequence D .sphere) 1000 (12,134) _
    rw [hq]
    exact q_survives1000 I

private theorem correction_source8_four_h200 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 3 (8,133) (11,135)
    (I.interpretation.basis .sphere 8 133 0) (I.interpretation.basis .sphere 11 135 0) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,3,8,133,[0],11,135,[0],"S0_AdamsE2_ss",2629⟩ (by
    exact List.mem_of_getElem? (i := 200) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (8,133) (11,135) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 133 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 11 135 [0] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem correction_source8_four_h201 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (8,133) (10,134)
    (I.interpretation.basis .sphere 8 133 1) (I.interpretation.basis .sphere 10 134 2 + I.interpretation.basis .sphere 10 134 4) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,8,133,[1],10,134,[2, 4],"S0_AdamsE2_ss",2630⟩ (by
    exact List.mem_of_getElem? (i := 201) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (8,133) (10,134) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 133 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 10 134 [2, 4] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem correction_source8_four_h226 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 3 (9,134) (12,136)
    (I.interpretation.basis .sphere 9 134 1) (I.interpretation.basis .sphere 12 136 0) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,3,9,134,[1],12,136,[0],"S0_AdamsE2_ss",2697⟩ (by
    exact List.mem_of_getElem? (i := 226) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (9,134) (12,136) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 134 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 136 [0] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem correction_source8_four_h227 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (9,134) (11,135)
    (I.interpretation.basis .sphere 9 134 0) (I.interpretation.basis .sphere 11 135 3 + I.interpretation.basis .sphere 11 135 4) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,9,134,[0],11,135,[3, 4],"S0_AdamsE2_ss",2698⟩ (by
    exact List.mem_of_getElem? (i := 227) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (9,134) (11,135) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 134 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 11 135 [3, 4] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem correction_source8_four_h228 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (9,134) (11,135)
    (I.interpretation.basis .sphere 9 134 4) (I.interpretation.basis .sphere 11 135 4) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,9,134,[4],11,135,[4],"S0_AdamsE2_ss",2699⟩ (by
    exact List.mem_of_getElem? (i := 228) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (9,134) (11,135) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 134 [4] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 11 135 [4] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem correction_source8_four_h224 (I : AdamsComputationTheorems D L G) : ReachesPage (sequence D .sphere) 1000 (9,134) (I.interpretation.basis .sphere 9 134 2) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.reaches,1000,9,134,[2],9,134,[],"S0_AdamsE2_ss",2695⟩ (by
    exact List.mem_of_getElem? (i := 224) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,hd⟩ := hrow
  change ReachesPage (sequence D .sphere) 1000 (9,134) x at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 134 [2] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
  rw [←hx] at hd
  simpa only [add_assoc] using hd

private theorem correction_source8_four_h225 (I : AdamsComputationTheorems D L G) : ReachesPage (sequence D .sphere) 7 (9,134) (I.interpretation.basis .sphere 9 134 3) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.reaches,7,9,134,[3],9,134,[],"S0_AdamsE2_ss",2696⟩ (by
    exact List.mem_of_getElem? (i := 225) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,hd⟩ := hrow
  change ReachesPage (sequence D .sphere) 7 (9,134) x at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 134 [3] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
  rw [←hx] at hd
  simpa only [add_assoc] using hd

private theorem correction_source8_four (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 4 (8,133)) := by
  classical
  let E := sequence D .sphere
  have h200 : HasDifferential E 3 (8,133) (11,135)
      (I.interpretation.basis .sphere 8 133 0) (I.interpretation.basis .sphere 11 135 0) := correction_source8_four_h200 I
  have h201 : HasDifferential E 2 (8,133) (10,134)
      (I.interpretation.basis .sphere 8 133 1) (I.interpretation.basis .sphere 10 134 2 + I.interpretation.basis .sphere 10 134 4) := correction_source8_four_h201 I
  have h226 : HasDifferential E 3 (9,134) (12,136)
      (I.interpretation.basis .sphere 9 134 1) (I.interpretation.basis .sphere 12 136 0) := correction_source8_four_h226 I
  have h227 : HasDifferential E 2 (9,134) (11,135)
      (I.interpretation.basis .sphere 9 134 0) (I.interpretation.basis .sphere 11 135 3 + I.interpretation.basis .sphere 11 135 4) := correction_source8_four_h227 I
  have h228 : HasDifferential E 2 (9,134) (11,135)
      (I.interpretation.basis .sphere 9 134 4) (I.interpretation.basis .sphere 11 135 4) := correction_source8_four_h228 I
  have h224 : ReachesPage E 1000 (9,134) (I.interpretation.basis .sphere 9 134 2) := correction_source8_four_h224 I
  have h225 : ReachesPage E 7 (9,134) (I.interpretation.basis .sphere 9 134 3) := correction_source8_four_h225 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,8,133,["376,1", "375,1"]⟩ (by
    exact List.mem_of_getElem? (i := 161) (by rfl))
  change E.Page 2 (8,133) ≃ₗ[ℤ] (Fin 2 →₀ F2) at e
  change ∀ i : Fin 2, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 8 133 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 2) 1) = I.interpretation.basis .sphere 8 133 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 2) 1) = I.interpretation.basis .sphere 8 133 1 := he 1
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,9,134,["391,1", "390,1", "69,1,82,1", "18,1,190,1", "0,1,375,1"]⟩ (by
    exact List.mem_of_getElem? (i := 173) (by rfl))
  change E.Page 2 (9,134) ≃ₗ[ℤ] (Fin 5 →₀ F2) at f
  change ∀ i : Fin 5, f.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 9 134 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 5) 1) = I.interpretation.basis .sphere 9 134 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 5) 1) = I.interpretation.basis .sphere 9 134 1 := hf 1
  have hf2 : f.symm (Finsupp.single (2:Fin 5) 1) = I.interpretation.basis .sphere 9 134 2 := hf 2
  have hf3 : f.symm (Finsupp.single (3:Fin 5) 1) = I.interpretation.basis .sphere 9 134 3 := hf 3
  have hf4 : f.symm (Finsupp.single (4:Fin 5) 1) = I.interpretation.basis .sphere 9 134 4 := hf 4
  obtain ⟨g,hg⟩ := I.basis ⟨.sphere,11,135,["411,1", "410,1", "409,1", "0,1,389,1", "0,3,367,1"]⟩ (by
    exact List.mem_of_getElem? (i := 191) (by rfl))
  change E.Page 2 (11,135) ≃ₗ[ℤ] (Fin 5 →₀ F2) at g
  change ∀ i : Fin 5, g.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 11 135 i.val at hg
  have hg0 : g.symm (Finsupp.single (0:Fin 5) 1) = I.interpretation.basis .sphere 11 135 0 := hg 0
  have hg1 : g.symm (Finsupp.single (1:Fin 5) 1) = I.interpretation.basis .sphere 11 135 1 := hg 1
  have hg2 : g.symm (Finsupp.single (2:Fin 5) 1) = I.interpretation.basis .sphere 11 135 2 := hg 2
  have hg3 : g.symm (Finsupp.single (3:Fin 5) 1) = I.interpretation.basis .sphere 11 135 3 := hg 3
  have hg4 : g.symm (Finsupp.single (4:Fin 5) 1) = I.interpretation.basis .sphere 11 135 4 := hg 4
  obtain ⟨k,hk⟩ := I.basis ⟨.sphere,10,134,["389,1", "388,1", "1,1,366,1", "0,1,373,1", "0,2,367,1"]⟩ (by
    exact List.mem_of_getElem? (i := 181) (by rfl))
  change E.Page 2 (10,134) ≃ₗ[ℤ] (Fin 5 →₀ F2) at k
  change ∀ i : Fin 5, k.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 10 134 i.val at hk
  have hk0 : k.symm (Finsupp.single (0:Fin 5) 1) = I.interpretation.basis .sphere 10 134 0 := hk 0
  have hk1 : k.symm (Finsupp.single (1:Fin 5) 1) = I.interpretation.basis .sphere 10 134 1 := hk 1
  have hk2 : k.symm (Finsupp.single (2:Fin 5) 1) = I.interpretation.basis .sphere 10 134 2 := hk 2
  have hk3 : k.symm (Finsupp.single (3:Fin 5) 1) = I.interpretation.basis .sphere 10 134 3 := hk 3
  have hk4 : k.symm (Finsupp.single (4:Fin 5) 1) = I.interpretation.basis .sphere 10 134 4 := hk 4
  have dz {p : ℤ×ℤ} {x : E.Page 2 p} {r : ℤ} (hr : 3≤r)
      (hx : ReachesPage E r p x) : E.d 2 p x=0 := by
    obtain ⟨a,ha⟩ := hx
    obtain ⟨b,hb⟩ := represents_before (by decide : (2:ℤ)≤2) (by omega : (2:ℤ)≤r) ha
    rw [←hb.eq_on_page_two] at hb
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by omega) hb ⟨a,ha⟩
  have hd0 : E.d 2 (9,134) (I.interpretation.basis .sphere 9 134 0) =
      I.interpretation.basis .sphere 11 135 3 + I.interpretation.basis .sphere 11 135 4 := h227.eq_on_page_two.2
  have hd1 : E.d 2 (9,134) (I.interpretation.basis .sphere 9 134 1) = 0 := by
    obtain ⟨_,x,y,hx,_,_⟩ := h226
    exact dz (by decide) ⟨x,hx⟩
  have hd2 : E.d 2 (9,134) (I.interpretation.basis .sphere 9 134 2) = 0 := dz (by decide) h224
  have hd3 : E.d 2 (9,134) (I.interpretation.basis .sphere 9 134 3) = 0 := dz (by decide) h225
  have hd4 : E.d 2 (9,134) (I.interpretation.basis .sphere 9 134 4) =
      I.interpretation.basis .sphere 11 135 4 := h228.eq_on_page_two.2
  have incoming_zero (x : E.Page 2 (9,134)) : g (E.d 2 (9,134) x) 0=0 := by
    have hall (a : Fin 5 →₀ F2) : g (E.d 2 (9,134) (f.symm a)) 0=0 := by
      induction a using Finsupp.induction with
      | zero => simp
      | @single_add i c a hi hci ih =>
        rw [map_add,map_add,map_add,Finsupp.add_apply,ih,add_zero]
        fin_cases c
        · simp
        · change g (E.d 2 (9,134) (f.symm (Finsupp.single i 1))) 0=0
          fin_cases i
          · change g (E.d 2 (9,134) (f.symm (Finsupp.single 0 1))) 0=0
            simp only [hf0,hd0,map_add,←hg3,←hg4,LinearEquiv.apply_symm_apply,Finsupp.add_apply]
            norm_num [Finsupp.single_apply,Fin.ext_iff]
          · change g (E.d 2 (9,134) (f.symm (Finsupp.single 1 1))) 0=0
            simp only [hf1,hd1,map_zero,Finsupp.zero_apply]
          · change g (E.d 2 (9,134) (f.symm (Finsupp.single 2 1))) 0=0
            simp only [hf2,hd2,map_zero,Finsupp.zero_apply]
          · change g (E.d 2 (9,134) (f.symm (Finsupp.single 3 1))) 0=0
            simp only [hf3,hd3,map_zero,Finsupp.zero_apply]
          · change g (E.d 2 (9,134) (f.symm (Finsupp.single 4 1))) 0=0
            simp only [hf4,hd4,←hg4,LinearEquiv.apply_symm_apply]
            norm_num [Finsupp.single_apply,Fin.ext_iff]
    simpa only [LinearEquiv.symm_apply_apply] using hall (f x)
  obtain ⟨_,a,b,ha,hb,hd⟩ := h200
  have hd' : E.d 3 (8,133) a=b := hd
  have hbne : b≠0 := by
    intro hb0
    obtain ⟨_,z,hx,hz⟩ := hb
    have hh := (next_projection_zero_iff_incoming E 2 (by change (2:ℤ)≤2; omega) (9,134) z).mp (hz.trans hb0)
    change (Subobject.ofLE _ _ ((E.ssData (11,135)).Z_anti bot_le) ≫
      (E.ssData (11,135)).pageπ 0) z ∈ LinearMap.range (E.d 2 (9,134)).hom at hh
    change (Subobject.ofLE _ _ ((E.ssData (11,135)).Z_anti bot_le) ≫
      (E.ssData (11,135)).pageπ 0) z=I.interpretation.basis .sphere 11 135 0 at hx
    rw [hx] at hh
    obtain ⟨u,hu⟩ := hh
    have hzero := incoming_zero u
    rw [hu,←hg0,LinearEquiv.apply_symm_apply] at hzero
    norm_num [Finsupp.single_apply] at hzero
  have hn : E.d 2 (8,133) (e.symm (Finsupp.single 1 1)) ≠ 0 := by
    rw [he1]
    have hh : E.d 2 (8,133) (I.interpretation.basis .sphere 8 133 1) =
      I.interpretation.basis .sphere 10 134 2 + I.interpretation.basis .sphere 10 134 4 := h201.eq_on_page_two.2
    rw [hh]
    intro hz
    have hz' := congrArg (fun x=>k x 2) hz
    simp only [map_add,map_zero,←hk2,←hk4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hz'
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hz'
  have frame : ∀ q : E.Page 3 (8,133), q=0 ∨ q=a :=
    frame_after_second (by change (2:ℤ)≤2; omega) (by decide) e (he0.symm ▸ ha) hn
  have ker (q : E.Page 3 (8,133)) (hq : E.d 3 (8,133) q=0) : q=0 := by
    rcases frame q with hh|hh
    · exact hh
    · exact (hbne (by simpa only [hh,hd'] using hq)).elim
  let S := E.pageShortComplex 3 ((8,133)-E.diffDeg 3)
  have hs : S.Exact := S.moduleCat_exact_iff.mpr (by
    intro x hx
    exact ⟨0,by rw [ker x hx,map_zero]⟩)
  exact ModuleCat.subsingleton_of_isZero ((pageHomologyIso E 3 (8,133)
    (by change (2:ℤ)≤3; omega)).isZero_iff.mpr ((S.exact_iff_isZero_homology).mp hs))

private theorem correction_source9_d4_zero_h226 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 3 (9,134) (12,136)
    (I.interpretation.basis .sphere 9 134 1) (I.interpretation.basis .sphere 12 136 0) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,3,9,134,[1],12,136,[0],"S0_AdamsE2_ss",2697⟩ (by
    exact List.mem_of_getElem? (i := 226) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (9,134) (12,136) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 134 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 136 [0] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem correction_source9_d4_zero_h227 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (9,134) (11,135)
    (I.interpretation.basis .sphere 9 134 0) (I.interpretation.basis .sphere 11 135 3 + I.interpretation.basis .sphere 11 135 4) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,9,134,[0],11,135,[3, 4],"S0_AdamsE2_ss",2698⟩ (by
    exact List.mem_of_getElem? (i := 227) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (9,134) (11,135) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 134 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 11 135 [3, 4] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem correction_source9_d4_zero_h228 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (9,134) (11,135)
    (I.interpretation.basis .sphere 9 134 4) (I.interpretation.basis .sphere 11 135 4) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,9,134,[4],11,135,[4],"S0_AdamsE2_ss",2699⟩ (by
    exact List.mem_of_getElem? (i := 228) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (9,134) (11,135) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 134 [4] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 11 135 [4] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem correction_source9_d4_zero_h251 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (8,134) (10,135)
    (I.interpretation.basis .sphere 8 134 1) (I.interpretation.basis .sphere 10 135 3) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,8,134,[1],10,135,[3],"S0_AdamsE2_ss",2783⟩ (by
    exact List.mem_of_getElem? (i := 251) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (8,134) (10,135) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 134 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 10 135 [3] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem correction_source9_d4_zero_h252 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 3 (10,135) (13,137)
    (I.interpretation.basis .sphere 10 135 0) (I.interpretation.basis .sphere 13 137 0) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,3,10,135,[0],13,137,[0],"S0_AdamsE2_ss",2784⟩ (by
    exact List.mem_of_getElem? (i := 252) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (10,135) (13,137) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 135 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 13 137 [0] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem correction_source9_d4_zero_h253 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (10,135) (12,136)
    (I.interpretation.basis .sphere 10 135 1) (I.interpretation.basis .sphere 12 136 1 + I.interpretation.basis .sphere 12 136 2) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,10,135,[1],12,136,[1, 2],"S0_AdamsE2_ss",2785⟩ (by
    exact List.mem_of_getElem? (i := 253) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (10,135) (12,136) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 135 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 136 [1, 2] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem correction_source9_d4_zero_h254 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (10,135) (12,136)
    (I.interpretation.basis .sphere 10 135 2) (I.interpretation.basis .sphere 12 136 3 + I.interpretation.basis .sphere 12 136 4) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,10,135,[2],12,136,[3, 4],"S0_AdamsE2_ss",2786⟩ (by
    exact List.mem_of_getElem? (i := 254) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (10,135) (12,136) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 135 [2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 136 [3, 4] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem correction_source9_d4_zero_h255 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (10,135) (12,136)
    (I.interpretation.basis .sphere 10 135 4) (I.interpretation.basis .sphere 12 136 4) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,10,135,[4],12,136,[4],"S0_AdamsE2_ss",2787⟩ (by
    exact List.mem_of_getElem? (i := 255) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (10,135) (12,136) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 135 [4] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 136 [4] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem correction_source9_d4_zero_h224 (I : AdamsComputationTheorems D L G) : ReachesPage (sequence D .sphere) 1000 (9,134) (I.interpretation.basis .sphere 9 134 2) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.reaches,1000,9,134,[2],9,134,[],"S0_AdamsE2_ss",2695⟩ (by
    exact List.mem_of_getElem? (i := 224) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,hd⟩ := hrow
  change ReachesPage (sequence D .sphere) 1000 (9,134) x at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 134 [2] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
  rw [←hx] at hd
  simpa only [add_assoc] using hd

private theorem correction_source9_d4_zero_h225 (I : AdamsComputationTheorems D L G) : ReachesPage (sequence D .sphere) 7 (9,134) (I.interpretation.basis .sphere 9 134 3) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.reaches,7,9,134,[3],9,134,[],"S0_AdamsE2_ss",2696⟩ (by
    exact List.mem_of_getElem? (i := 225) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,hd⟩ := hrow
  change ReachesPage (sequence D .sphere) 7 (9,134) x at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 134 [3] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
  rw [←hx] at hd
  simpa only [add_assoc] using hd

set_option maxHeartbeats 800000 in
private theorem correction_source9_d4_zero (I : AdamsComputationTheorems D L G) :
    (sequence D .sphere).d 4 (9,134)=0 := by
  classical
  let E := sequence D .sphere
  have h226 : HasDifferential E 3 (9,134) (12,136)
      (I.interpretation.basis .sphere 9 134 1) (I.interpretation.basis .sphere 12 136 0) := correction_source9_d4_zero_h226 I
  have h227 : HasDifferential E 2 (9,134) (11,135)
      (I.interpretation.basis .sphere 9 134 0) (I.interpretation.basis .sphere 11 135 3 + I.interpretation.basis .sphere 11 135 4) := correction_source9_d4_zero_h227 I
  have h228 : HasDifferential E 2 (9,134) (11,135)
      (I.interpretation.basis .sphere 9 134 4) (I.interpretation.basis .sphere 11 135 4) := correction_source9_d4_zero_h228 I
  have h251 : HasDifferential E 2 (8,134) (10,135)
      (I.interpretation.basis .sphere 8 134 1) (I.interpretation.basis .sphere 10 135 3) := correction_source9_d4_zero_h251 I
  have h252 : HasDifferential E 3 (10,135) (13,137)
      (I.interpretation.basis .sphere 10 135 0) (I.interpretation.basis .sphere 13 137 0) := correction_source9_d4_zero_h252 I
  have h253 : HasDifferential E 2 (10,135) (12,136)
      (I.interpretation.basis .sphere 10 135 1) (I.interpretation.basis .sphere 12 136 1 + I.interpretation.basis .sphere 12 136 2) := correction_source9_d4_zero_h253 I
  have h254 : HasDifferential E 2 (10,135) (12,136)
      (I.interpretation.basis .sphere 10 135 2) (I.interpretation.basis .sphere 12 136 3 + I.interpretation.basis .sphere 12 136 4) := correction_source9_d4_zero_h254 I
  have h255 : HasDifferential E 2 (10,135) (12,136)
      (I.interpretation.basis .sphere 10 135 4) (I.interpretation.basis .sphere 12 136 4) := correction_source9_d4_zero_h255 I
  have h224 : ReachesPage E 1000 (9,134) (I.interpretation.basis .sphere 9 134 2) := correction_source9_d4_zero_h224 I
  have h225 : ReachesPage E 7 (9,134) (I.interpretation.basis .sphere 9 134 3) := correction_source9_d4_zero_h225 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,9,134,["391,1", "390,1", "69,1,82,1", "18,1,190,1", "0,1,375,1"]⟩ (by
    exact List.mem_of_getElem? (i := 173) (by rfl))
  change E.Page 2 (9,134) ≃ₗ[ℤ] (Fin 5 →₀ F2) at e
  change ∀ i : Fin 5, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 9 134 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 5) 1) = I.interpretation.basis .sphere 9 134 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 5) 1) = I.interpretation.basis .sphere 9 134 1 := he 1
  have he2 : e.symm (Finsupp.single (2:Fin 5) 1) = I.interpretation.basis .sphere 9 134 2 := he 2
  have he3 : e.symm (Finsupp.single (3:Fin 5) 1) = I.interpretation.basis .sphere 9 134 3 := he 3
  have he4 : e.symm (Finsupp.single (4:Fin 5) 1) = I.interpretation.basis .sphere 9 134 4 := he 4
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,10,135,["413,1", "412,1", "0,1,391,1", "0,1,390,1", "0,2,375,1"]⟩ (by
    exact List.mem_of_getElem? (i := 182) (by rfl))
  change E.Page 2 (10,135) ≃ₗ[ℤ] (Fin 5 →₀ F2) at f
  change ∀ i : Fin 5, f.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 10 135 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 5) 1) = I.interpretation.basis .sphere 10 135 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 5) 1) = I.interpretation.basis .sphere 10 135 1 := hf 1
  have hf2 : f.symm (Finsupp.single (2:Fin 5) 1) = I.interpretation.basis .sphere 10 135 2 := hf 2
  have hf3 : f.symm (Finsupp.single (3:Fin 5) 1) = I.interpretation.basis .sphere 10 135 3 := hf 3
  have hf4 : f.symm (Finsupp.single (4:Fin 5) 1) = I.interpretation.basis .sphere 10 135 4 := hf 4
  obtain ⟨g,hg⟩ := I.basis ⟨.sphere,12,136,["1,1,387,1", "0,1,410,1", "0,1,409,1", "0,2,389,1", "0,4,367,1"]⟩ (by
    exact List.mem_of_getElem? (i := 200) (by rfl))
  change E.Page 2 (12,136) ≃ₗ[ℤ] (Fin 5 →₀ F2) at g
  change ∀ i : Fin 5, g.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 12 136 i.val at hg
  have hg0 : g.symm (Finsupp.single (0:Fin 5) 1) = I.interpretation.basis .sphere 12 136 0 := hg 0
  have hg1 : g.symm (Finsupp.single (1:Fin 5) 1) = I.interpretation.basis .sphere 12 136 1 := hg 1
  have hg2 : g.symm (Finsupp.single (2:Fin 5) 1) = I.interpretation.basis .sphere 12 136 2 := hg 2
  have hg3 : g.symm (Finsupp.single (3:Fin 5) 1) = I.interpretation.basis .sphere 12 136 3 := hg 3
  have hg4 : g.symm (Finsupp.single (4:Fin 5) 1) = I.interpretation.basis .sphere 12 136 4 := hg 4
  obtain ⟨k,hk⟩ := I.basis ⟨.sphere,11,135,["411,1", "410,1", "409,1", "0,1,389,1", "0,3,367,1"]⟩ (by
    exact List.mem_of_getElem? (i := 191) (by rfl))
  change E.Page 2 (11,135) ≃ₗ[ℤ] (Fin 5 →₀ F2) at k
  change ∀ i : Fin 5, k.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 11 135 i.val at hk
  have hk0 : k.symm (Finsupp.single (0:Fin 5) 1) = I.interpretation.basis .sphere 11 135 0 := hk 0
  have hk1 : k.symm (Finsupp.single (1:Fin 5) 1) = I.interpretation.basis .sphere 11 135 1 := hk 1
  have hk2 : k.symm (Finsupp.single (2:Fin 5) 1) = I.interpretation.basis .sphere 11 135 2 := hk 2
  have hk3 : k.symm (Finsupp.single (3:Fin 5) 1) = I.interpretation.basis .sphere 11 135 3 := hk 3
  have hk4 : k.symm (Finsupp.single (4:Fin 5) 1) = I.interpretation.basis .sphere 11 135 4 := hk 4
  have dz {p : ℤ×ℤ} {x : E.Page 2 p} {r : ℤ} (hr : 3≤r)
      (hx : ReachesPage E r p x) : E.d 2 p x=0 := by
    obtain ⟨a,ha⟩ := hx
    obtain ⟨b,hb⟩ := represents_before (by decide : (2:ℤ)≤2) (by omega : (2:ℤ)≤r) ha
    rw [←hb.eq_on_page_two] at hb
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by omega) hb ⟨a,ha⟩
  have df0 : E.d 2 (10,135) (I.interpretation.basis .sphere 10 135 0)=0 := by
    obtain ⟨_,a,b,ha,_,_⟩ := h252
    exact dz (by decide) ⟨a,ha⟩
  have df1 : E.d 2 (10,135) (I.interpretation.basis .sphere 10 135 1)=
      I.interpretation.basis .sphere 12 136 1 + I.interpretation.basis .sphere 12 136 2 := h253.eq_on_page_two.2
  have df2 : E.d 2 (10,135) (I.interpretation.basis .sphere 10 135 2)=
      I.interpretation.basis .sphere 12 136 3 + I.interpretation.basis .sphere 12 136 4 := h254.eq_on_page_two.2
  have df3 : E.d 2 (10,135) (I.interpretation.basis .sphere 10 135 3)=0 := by
    have hh : E.d 2 (8,134) (I.interpretation.basis .sphere 8 134 1)=I.interpretation.basis .sphere 10 135 3 := h251.eq_on_page_two.2
    exact IsPageBoundary.d_eq_zero (E:=E) (r:=2) (p:=(8,134)) ⟨_,hh⟩
  have df4 : E.d 2 (10,135) (I.interpretation.basis .sphere 10 135 4)=
      I.interpretation.basis .sphere 12 136 4 := h255.eq_on_page_two.2
  have incoming_zero (x : E.Page 2 (10,135)) : g (E.d 2 (10,135) x) 0=0 := by
    have hall (a : Fin 5 →₀ F2) : g (E.d 2 (10,135) (f.symm a)) 0=0 := by
      induction a using Finsupp.induction with
      | zero => simp
      | @single_add i c a hi hci ih =>
        rw [map_add,map_add,map_add,Finsupp.add_apply,ih,add_zero]
        fin_cases c
        · simp
        · change g (E.d 2 (10,135) (f.symm (Finsupp.single i 1))) 0=0
          fin_cases i
          · change g (E.d 2 (10,135) (f.symm (Finsupp.single 0 1))) 0=0
            simp only [hf0,df0,map_zero,Finsupp.zero_apply]
          · change g (E.d 2 (10,135) (f.symm (Finsupp.single 1 1))) 0=0
            simp only [hf1,df1,map_add,←hg1,←hg2,LinearEquiv.apply_symm_apply,Finsupp.add_apply]
            norm_num [Finsupp.single_apply,Fin.ext_iff]
          · change g (E.d 2 (10,135) (f.symm (Finsupp.single 2 1))) 0=0
            simp only [hf2,df2,map_add,←hg3,←hg4,LinearEquiv.apply_symm_apply,Finsupp.add_apply]
            norm_num [Finsupp.single_apply,Fin.ext_iff]
          · change g (E.d 2 (10,135) (f.symm (Finsupp.single 3 1))) 0=0
            simp only [hf3,df3,map_zero,Finsupp.zero_apply]
          · change g (E.d 2 (10,135) (f.symm (Finsupp.single 4 1))) 0=0
            simp only [hf4,df4,←hg4,LinearEquiv.apply_symm_apply]
            norm_num [Finsupp.single_apply,Fin.ext_iff]
    simpa only [LinearEquiv.symm_apply_apply] using hall (f x)
  obtain ⟨_,a1,b1,ha1,hb1,hd⟩ := h226
  have hd' : E.d 3 (9,134) a1=b1 := hd
  have hbne : b1≠0 := by
    intro hb0
    obtain ⟨_,z,hx,hz⟩ := hb1
    have hh := (next_projection_zero_iff_incoming E 2 (by change (2:ℤ)≤2; omega) (10,135) z).mp (hz.trans hb0)
    change (Subobject.ofLE _ _ ((E.ssData (12,136)).Z_anti bot_le) ≫
      (E.ssData (12,136)).pageπ 0) z ∈ LinearMap.range (E.d 2 (10,135)).hom at hh
    change (Subobject.ofLE _ _ ((E.ssData (12,136)).Z_anti bot_le) ≫
      (E.ssData (12,136)).pageπ 0) z=I.interpretation.basis .sphere 12 136 0 at hx
    rw [hx] at hh
    obtain ⟨u,hu⟩ := hh
    have hzero := incoming_zero u
    rw [hu,←hg0,LinearEquiv.apply_symm_apply] at hzero
    norm_num [Finsupp.single_apply] at hzero
  obtain ⟨a2,ha2⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤1000) h224.choose_spec
  obtain ⟨a3,ha3⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤7) h225.choose_spec
  obtain ⟨b2,hb2⟩ := represents_before (by decide : (2:ℤ)≤4) (by decide : (4:ℤ)≤1000) h224.choose_spec
  obtain ⟨b3,hb3⟩ := represents_before (by decide : (2:ℤ)≤4) (by decide : (4:ℤ)≤7) h225.choose_spec
  have hd32 : E.d 3 (9,134) a2=0 := represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide) ha2 h224
  have hd33 : E.d 3 (9,134) a3=0 := represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide) ha3 h225
  have hd42 : E.d 4 (9,134) b2=0 := represents_d_zero_of_later (by change (2:ℤ)≤4; omega) (by decide) hb2 h224
  have hd43 : E.d 4 (9,134) b3=0 := represents_d_zero_of_later (by change (2:ℤ)≤4; omega) (by decide) hb3 h225
  have hd0 : E.d 2 (9,134) (I.interpretation.basis .sphere 9 134 0)=
      I.interpretation.basis .sphere 11 135 3 + I.interpretation.basis .sphere 11 135 4 := h227.eq_on_page_two.2
  have hd1 : E.d 2 (9,134) (I.interpretation.basis .sphere 9 134 1)=0 := dz (by decide) ⟨a1,ha1⟩
  have hd2 : E.d 2 (9,134) (I.interpretation.basis .sphere 9 134 2)=0 := dz (by decide) h224
  have hd3 : E.d 2 (9,134) (I.interpretation.basis .sphere 9 134 3)=0 := dz (by decide) h225
  have hd4 : E.d 2 (9,134) (I.interpretation.basis .sphere 9 134 4)=I.interpretation.basis .sphere 11 135 4 := h228.eq_on_page_two.2
  ext a
  change E.d 4 (9,134) a=0
  let A := E.ssData (9,134)
  haveI : Epi (A.pageπ 2) := inferInstanceAs (Epi (cokernel.π _))
  obtain ⟨z,hza⟩ := (ModuleCat.epi_iff_surjective (A.pageπ 2)).mp inferInstance a
  let x : E.Page 2 (9,134) := (Subobject.ofLE _ _ (A.Z_anti (by decide : (0:WithTop ℕ)≤2)) ≫ A.pageπ 0) z
  have hxa : RepresentsOnPage E 4 (9,134) x a := ⟨by decide,z,rfl,hza⟩
  have hc : E.d 2 (9,134) x=0 := dz (by decide) ⟨a,hxa⟩
  have heq : e x = Finsupp.single 0 (e x 0)+Finsupp.single 1 (e x 1)+Finsupp.single 2 (e x 2)+Finsupp.single 3 (e x 3)+Finsupp.single 4 (e x 4) := by
    apply Finsupp.ext
    intro i
    fin_cases i <;> simp
  have hxe : x=e.symm (Finsupp.single 0 (e x 0)+Finsupp.single 1 (e x 1)+Finsupp.single 2 (e x 2)+Finsupp.single 3 (e x 3)+Finsupp.single 4 (e x 4)) := by
    rw [←heq,LinearEquiv.symm_apply_apply]
  generalize hc0 : e x 0=c0 at hxe
  generalize hc1 : e x 1=c1 at hxe
  generalize hc2 : e x 2=c2 at hxe
  generalize hc3 : e x 3=c3 at hxe
  generalize hc4 : e x 4=c4 at hxe
  fin_cases c0 <;> fin_cases c1 <;> fin_cases c2 <;> fin_cases c3 <;> fin_cases c4
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_zero,add_zero] at hxe
    rw [hxe] at hc hxa
    rw [represents_unique hxa (RepresentsOnPage.zero (by decide : (2:ℤ)≤4)),map_zero]
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,zero_add,add_zero] at hxe
    rw [hxe] at hc hxa
    simp only [he4] at hc hxa
    simp only [hd4] at hc
    have hh := congrArg (fun y=>k y 4) hc
    simp only [map_zero,←hk4,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hh
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,zero_add,add_zero] at hxe
    rw [hxe] at hc hxa
    simp only [he3] at hc hxa
    rw [represents_unique hxa (hb3)]
    simp only [hd43]
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
    rw [hxe] at hc hxa
    simp only [he3, he4] at hc hxa
    simp only [map_add,hd3,hd4,zero_add] at hc
    have hh := congrArg (fun y=>k y 4) hc
    simp only [map_zero,←hk4,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hh
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,zero_add,add_zero] at hxe
    rw [hxe] at hc hxa
    simp only [he2] at hc hxa
    rw [represents_unique hxa (hb2)]
    simp only [hd42]
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
    rw [hxe] at hc hxa
    simp only [he2, he4] at hc hxa
    simp only [map_add,hd2,hd4,zero_add] at hc
    have hh := congrArg (fun y=>k y 4) hc
    simp only [map_zero,←hk4,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hh
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
    rw [hxe] at hc hxa
    simp only [he2, he3] at hc hxa
    rw [represents_unique hxa (represents_add_tail (hb2) hb3)]
    simp only [map_add,hd42,hd43,add_zero]
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
    rw [hxe] at hc hxa
    simp only [he2, he3, he4] at hc hxa
    simp only [map_add,hd2,hd3,hd4,zero_add,add_zero] at hc
    have hh := congrArg (fun y=>k y 4) hc
    simp only [map_zero,←hk4,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hh
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,zero_add,add_zero] at hxe
    rw [hxe] at hc hxa
    simp only [he1] at hc hxa
    have hh := represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<4) (ha1) ⟨a,hxa⟩
    exact (hbne (by simpa only [map_add,hd',hd32,hd33,add_zero] using hh)).elim
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
    rw [hxe] at hc hxa
    simp only [he1, he4] at hc hxa
    simp only [map_add,hd1,hd4,zero_add] at hc
    have hh := congrArg (fun y=>k y 4) hc
    simp only [map_zero,←hk4,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hh
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
    rw [hxe] at hc hxa
    simp only [he1, he3] at hc hxa
    have hh := represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<4) (represents_add_tail (ha1) ha3) ⟨a,hxa⟩
    exact (hbne (by simpa only [map_add,hd',hd32,hd33,add_zero] using hh)).elim
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
    rw [hxe] at hc hxa
    simp only [he1, he3, he4] at hc hxa
    simp only [map_add,hd1,hd3,hd4,zero_add,add_zero] at hc
    have hh := congrArg (fun y=>k y 4) hc
    simp only [map_zero,←hk4,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hh
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
    rw [hxe] at hc hxa
    simp only [he1, he2] at hc hxa
    have hh := represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<4) (represents_add_tail (ha1) ha2) ⟨a,hxa⟩
    exact (hbne (by simpa only [map_add,hd',hd32,hd33,add_zero] using hh)).elim
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
    rw [hxe] at hc hxa
    simp only [he1, he2, he4] at hc hxa
    simp only [map_add,hd1,hd2,hd4,zero_add,add_zero] at hc
    have hh := congrArg (fun y=>k y 4) hc
    simp only [map_zero,←hk4,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hh
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
    rw [hxe] at hc hxa
    simp only [he1, he2, he3] at hc hxa
    have hh := represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<4) (represents_add_tail (represents_add_tail (ha1) ha2) ha3) ⟨a,hxa⟩
    exact (hbne (by simpa only [map_add,hd',hd32,hd33,add_zero] using hh)).elim
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,zero_add] at hxe
    rw [hxe] at hc hxa
    simp only [he1, he2, he3, he4] at hc hxa
    simp only [map_add,hd1,hd2,hd3,hd4,zero_add,add_zero] at hc
    have hh := congrArg (fun y=>k y 4) hc
    simp only [map_zero,←hk4,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hh
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,add_zero] at hxe
    rw [hxe] at hc hxa
    simp only [he0] at hc hxa
    simp only [hd0] at hc
    have hh := congrArg (fun y=>k y 3) hc
    simp only [map_add,map_zero,←hk3,←hk4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hc hxa
    simp only [he0, he4] at hc hxa
    simp only [map_add,hd0,hd4] at hc
    have hh := congrArg (fun y=>k y 3) hc
    simp only [map_add,map_zero,←hk3,←hk4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hc hxa
    simp only [he0, he3] at hc hxa
    simp only [map_add,hd0,hd3,add_zero] at hc
    have hh := congrArg (fun y=>k y 3) hc
    simp only [map_add,map_zero,←hk3,←hk4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hc hxa
    simp only [he0, he3, he4] at hc hxa
    simp only [map_add,hd0,hd3,hd4,add_zero] at hc
    have hh := congrArg (fun y=>k y 3) hc
    simp only [map_add,map_zero,←hk3,←hk4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hc hxa
    simp only [he0, he2] at hc hxa
    simp only [map_add,hd0,hd2,add_zero] at hc
    have hh := congrArg (fun y=>k y 3) hc
    simp only [map_add,map_zero,←hk3,←hk4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hc hxa
    simp only [he0, he2, he4] at hc hxa
    simp only [map_add,hd0,hd2,hd4,add_zero] at hc
    have hh := congrArg (fun y=>k y 3) hc
    simp only [map_add,map_zero,←hk3,←hk4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hc hxa
    simp only [he0, he2, he3] at hc hxa
    simp only [map_add,hd0,hd2,hd3,add_zero] at hc
    have hh := congrArg (fun y=>k y 3) hc
    simp only [map_add,map_zero,←hk3,←hk4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hc hxa
    simp only [he0, he2, he3, he4] at hc hxa
    simp only [map_add,hd0,hd2,hd3,hd4,add_zero] at hc
    have hh := congrArg (fun y=>k y 3) hc
    simp only [map_add,map_zero,←hk3,←hk4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hc hxa
    simp only [he0, he1] at hc hxa
    simp only [map_add,hd0,hd1,add_zero] at hc
    have hh := congrArg (fun y=>k y 3) hc
    simp only [map_add,map_zero,←hk3,←hk4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hc hxa
    simp only [he0, he1, he4] at hc hxa
    simp only [map_add,hd0,hd1,hd4,add_zero] at hc
    have hh := congrArg (fun y=>k y 3) hc
    simp only [map_add,map_zero,←hk3,←hk4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hc hxa
    simp only [he0, he1, he3] at hc hxa
    simp only [map_add,hd0,hd1,hd3,add_zero] at hc
    have hh := congrArg (fun y=>k y 3) hc
    simp only [map_add,map_zero,←hk3,←hk4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hc hxa
    simp only [he0, he1, he3, he4] at hc hxa
    simp only [map_add,hd0,hd1,hd3,hd4,add_zero] at hc
    have hh := congrArg (fun y=>k y 3) hc
    simp only [map_add,map_zero,←hk3,←hk4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hc hxa
    simp only [he0, he1, he2] at hc hxa
    simp only [map_add,hd0,hd1,hd2,add_zero] at hc
    have hh := congrArg (fun y=>k y 3) hc
    simp only [map_add,map_zero,←hk3,←hk4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hc hxa
    simp only [he0, he1, he2, he4] at hc hxa
    simp only [map_add,hd0,hd1,hd2,hd4,add_zero] at hc
    have hh := congrArg (fun y=>k y 3) hc
    simp only [map_add,map_zero,←hk3,←hk4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hc hxa
    simp only [he0, he1, he2, he3] at hc hxa
    simp only [map_add,hd0,hd1,hd2,hd3,add_zero] at hc
    have hh := congrArg (fun y=>k y 3) hc
    simp only [map_add,map_zero,←hk3,←hk4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
    try simp only [map_add] at hxe
    rw [hxe] at hc hxa
    simp only [he0, he1, he2, he3, he4] at hc hxa
    simp only [map_add,hd0,hd1,hd2,hd3,hd4,add_zero] at hc
    have hh := congrArg (fun y=>k y 3) hc
    simp only [map_add,map_zero,←hk3,←hk4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hh

private theorem correction_incoming3_h251 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (8,134) (10,135)
    (I.interpretation.basis .sphere 8 134 1) (I.interpretation.basis .sphere 10 135 3) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,8,134,[1],10,135,[3],"S0_AdamsE2_ss",2783⟩ (by
    exact List.mem_of_getElem? (i := 251) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (8,134) (10,135) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 134 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 10 135 [3] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem correction_incoming3_h252 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 3 (10,135) (13,137)
    (I.interpretation.basis .sphere 10 135 0) (I.interpretation.basis .sphere 13 137 0) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,3,10,135,[0],13,137,[0],"S0_AdamsE2_ss",2784⟩ (by
    exact List.mem_of_getElem? (i := 252) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (10,135) (13,137) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 135 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 13 137 [0] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem correction_incoming3_h253 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (10,135) (12,136)
    (I.interpretation.basis .sphere 10 135 1) (I.interpretation.basis .sphere 12 136 1 + I.interpretation.basis .sphere 12 136 2) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,10,135,[1],12,136,[1, 2],"S0_AdamsE2_ss",2785⟩ (by
    exact List.mem_of_getElem? (i := 253) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (10,135) (12,136) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 135 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 136 [1, 2] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem correction_incoming3_h254 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (10,135) (12,136)
    (I.interpretation.basis .sphere 10 135 2) (I.interpretation.basis .sphere 12 136 3 + I.interpretation.basis .sphere 12 136 4) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,10,135,[2],12,136,[3, 4],"S0_AdamsE2_ss",2786⟩ (by
    exact List.mem_of_getElem? (i := 254) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (10,135) (12,136) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 135 [2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 136 [3, 4] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem correction_incoming3_h255 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (10,135) (12,136)
    (I.interpretation.basis .sphere 10 135 4) (I.interpretation.basis .sphere 12 136 4) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,10,135,[4],12,136,[4],"S0_AdamsE2_ss",2787⟩ (by
    exact List.mem_of_getElem? (i := 255) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (10,135) (12,136) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 135 [4] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 136 [4] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

set_option maxHeartbeats 800000 in
private theorem correction_incoming3 (I : AdamsComputationTheorems D L G) :
    ∃ b : (sequence D .sphere).Page 3 (13,137),
      RepresentsOnPage (sequence D .sphere) 3 (13,137) (I.interpretation.basis .sphere 13 137 0) b ∧
      ∀ a : (sequence D .sphere).Page 3 (10,135),
        (sequence D .sphere).d 3 (10,135) a=0 ∨ (sequence D .sphere).d 3 (10,135) a=b := by
  classical
  let E := sequence D .sphere
  have h251 : HasDifferential E 2 (8,134) (10,135)
      (I.interpretation.basis .sphere 8 134 1) (I.interpretation.basis .sphere 10 135 3) := correction_incoming3_h251 I
  have h252 : HasDifferential E 3 (10,135) (13,137)
      (I.interpretation.basis .sphere 10 135 0) (I.interpretation.basis .sphere 13 137 0) := correction_incoming3_h252 I
  have h253 : HasDifferential E 2 (10,135) (12,136)
      (I.interpretation.basis .sphere 10 135 1) (I.interpretation.basis .sphere 12 136 1 + I.interpretation.basis .sphere 12 136 2) := correction_incoming3_h253 I
  have h254 : HasDifferential E 2 (10,135) (12,136)
      (I.interpretation.basis .sphere 10 135 2) (I.interpretation.basis .sphere 12 136 3 + I.interpretation.basis .sphere 12 136 4) := correction_incoming3_h254 I
  have h255 : HasDifferential E 2 (10,135) (12,136)
      (I.interpretation.basis .sphere 10 135 4) (I.interpretation.basis .sphere 12 136 4) := correction_incoming3_h255 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,10,135,["413,1", "412,1", "0,1,391,1", "0,1,390,1", "0,2,375,1"]⟩ (by
    exact List.mem_of_getElem? (i := 182) (by rfl))
  change E.Page 2 (10,135) ≃ₗ[ℤ] (Fin 5 →₀ F2) at e
  change ∀ i : Fin 5, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 10 135 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 5) 1) = I.interpretation.basis .sphere 10 135 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 5) 1) = I.interpretation.basis .sphere 10 135 1 := he 1
  have he2 : e.symm (Finsupp.single (2:Fin 5) 1) = I.interpretation.basis .sphere 10 135 2 := he 2
  have he3 : e.symm (Finsupp.single (3:Fin 5) 1) = I.interpretation.basis .sphere 10 135 3 := he 3
  have he4 : e.symm (Finsupp.single (4:Fin 5) 1) = I.interpretation.basis .sphere 10 135 4 := he 4
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,12,136,["1,1,387,1", "0,1,410,1", "0,1,409,1", "0,2,389,1", "0,4,367,1"]⟩ (by
    exact List.mem_of_getElem? (i := 200) (by rfl))
  change E.Page 2 (12,136) ≃ₗ[ℤ] (Fin 5 →₀ F2) at f
  change ∀ i : Fin 5, f.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 12 136 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 5) 1) = I.interpretation.basis .sphere 12 136 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 5) 1) = I.interpretation.basis .sphere 12 136 1 := hf 1
  have hf2 : f.symm (Finsupp.single (2:Fin 5) 1) = I.interpretation.basis .sphere 12 136 2 := hf 2
  have hf3 : f.symm (Finsupp.single (3:Fin 5) 1) = I.interpretation.basis .sphere 12 136 3 := hf 3
  have hf4 : f.symm (Finsupp.single (4:Fin 5) 1) = I.interpretation.basis .sphere 12 136 4 := hf 4
  obtain ⟨_,a0,b0,ha0,hb0,hd⟩ := h252
  have hd' : E.d 3 (10,135) a0=b0 := hd
  have hz3 : RepresentsOnPage E 3 (10,135) (I.interpretation.basis .sphere 10 135 3) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide) h251
  have dz {p : ℤ×ℤ} {x : E.Page 2 p} (hx : ReachesPage E 3 p x) : E.d 2 p x=0 := by
    obtain ⟨a,ha⟩ := hx
    obtain ⟨b,hb⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤3) ha
    rw [←hb.eq_on_page_two] at hb
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide) hb ⟨a,ha⟩
  have hd0 : E.d 2 (10,135) (I.interpretation.basis .sphere 10 135 0)=0 := dz ⟨a0,ha0⟩
  have hd1 : E.d 2 (10,135) (I.interpretation.basis .sphere 10 135 1)=
      I.interpretation.basis .sphere 12 136 1 + I.interpretation.basis .sphere 12 136 2 := h253.eq_on_page_two.2
  have hd2 : E.d 2 (10,135) (I.interpretation.basis .sphere 10 135 2)=
      I.interpretation.basis .sphere 12 136 3 + I.interpretation.basis .sphere 12 136 4 := h254.eq_on_page_two.2
  have hd3 : E.d 2 (10,135) (I.interpretation.basis .sphere 10 135 3)=0 := dz ⟨0,hz3⟩
  have hd4 : E.d 2 (10,135) (I.interpretation.basis .sphere 10 135 4)=
      I.interpretation.basis .sphere 12 136 4 := h255.eq_on_page_two.2
  have frame (a : E.Page 3 (10,135)) : a=0 ∨ a=a0 := by
    let A := E.ssData (10,135)
    haveI : Epi (A.pageπ 1) := inferInstanceAs (Epi (cokernel.π _))
    obtain ⟨z,hza⟩ := (ModuleCat.epi_iff_surjective (A.pageπ 1)).mp inferInstance a
    let x : E.Page 2 (10,135) := (Subobject.ofLE _ _ (A.Z_anti (by decide : (0:WithTop ℕ)≤1)) ≫ A.pageπ 0) z
    have hxa : RepresentsOnPage E 3 (10,135) x a := ⟨by decide,z,rfl,hza⟩
    have hc : E.d 2 (10,135) x=0 := dz ⟨a,hxa⟩
    have heq : e x=Finsupp.single 0 (e x 0)+Finsupp.single 1 (e x 1)+Finsupp.single 2 (e x 2)+Finsupp.single 3 (e x 3)+Finsupp.single 4 (e x 4) := by
      apply Finsupp.ext
      intro i
      fin_cases i <;> simp
    have hxe : x=e.symm (Finsupp.single 0 (e x 0)+Finsupp.single 1 (e x 1)+Finsupp.single 2 (e x 2)+Finsupp.single 3 (e x 3)+Finsupp.single 4 (e x 4)) := by
      rw [←heq,LinearEquiv.symm_apply_apply]
    generalize hc0 : e x 0=c0 at hxe
    generalize hc1 : e x 1=c1 at hxe
    generalize hc2 : e x 2=c2 at hxe
    generalize hc3 : e x 3=c3 at hxe
    generalize hc4 : e x 4=c4 at hxe
    fin_cases c0 <;> fin_cases c1 <;> fin_cases c2 <;> fin_cases c3 <;> fin_cases c4
    · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
      try simp only [Finsupp.single_zero,map_zero,add_zero] at hxe
      rw [hxe] at hc hxa
      exact Or.inl (represents_unique hxa (RepresentsOnPage.zero (by decide : (2:ℤ)≤3)))
    · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
      try simp only [Finsupp.single_zero,zero_add,add_zero] at hxe
      rw [hxe] at hc hxa
      simp only [he4] at hc hxa
      simp only [hd4] at hc
      have hh := congrArg (fun y=>f y 4) hc
      simp only [map_zero,←hf4,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
      try simp only [Finsupp.single_zero,zero_add,add_zero] at hxe
      rw [hxe] at hc hxa
      simp only [he3] at hc hxa
      exact Or.inl (represents_unique hxa hz3)
    · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
      rw [hxe] at hc hxa
      simp only [he3, he4] at hc hxa
      simp only [map_add,hd3,hd4,zero_add] at hc
      have hh := congrArg (fun y=>f y 4) hc
      simp only [map_zero,←hf4,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
      try simp only [Finsupp.single_zero,zero_add,add_zero] at hxe
      rw [hxe] at hc hxa
      simp only [he2] at hc hxa
      simp only [hd2] at hc
      have hh := congrArg (fun y=>f y 3) hc
      simp only [map_add,map_zero,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
      rw [hxe] at hc hxa
      simp only [he2, he4] at hc hxa
      simp only [map_add,hd2,hd4] at hc
      have hh := congrArg (fun y=>f y 3) hc
      simp only [map_add,map_zero,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
      rw [hxe] at hc hxa
      simp only [he2, he3] at hc hxa
      simp only [map_add,hd2,hd3,add_zero] at hc
      have hh := congrArg (fun y=>f y 3) hc
      simp only [map_add,map_zero,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
      rw [hxe] at hc hxa
      simp only [he2, he3, he4] at hc hxa
      simp only [map_add,hd2,hd3,hd4,add_zero] at hc
      have hh := congrArg (fun y=>f y 3) hc
      simp only [map_add,map_zero,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
      try simp only [Finsupp.single_zero,zero_add,add_zero] at hxe
      rw [hxe] at hc hxa
      simp only [he1] at hc hxa
      simp only [hd1] at hc
      have hh := congrArg (fun y=>f y 1) hc
      simp only [map_add,map_zero,←hf1,←hf2,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
      rw [hxe] at hc hxa
      simp only [he1, he4] at hc hxa
      simp only [map_add,hd1,hd4] at hc
      have hh := congrArg (fun y=>f y 1) hc
      simp only [map_add,map_zero,←hf1,←hf2,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
      rw [hxe] at hc hxa
      simp only [he1, he3] at hc hxa
      simp only [map_add,hd1,hd3,add_zero] at hc
      have hh := congrArg (fun y=>f y 1) hc
      simp only [map_add,map_zero,←hf1,←hf2,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
      rw [hxe] at hc hxa
      simp only [he1, he3, he4] at hc hxa
      simp only [map_add,hd1,hd3,hd4,add_zero] at hc
      have hh := congrArg (fun y=>f y 1) hc
      simp only [map_add,map_zero,←hf1,←hf2,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
      rw [hxe] at hc hxa
      simp only [he1, he2] at hc hxa
      simp only [map_add,hd1,hd2] at hc
      have hh := congrArg (fun y=>f y 1) hc
      simp only [map_add,map_zero,←hf1,←hf2,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
      rw [hxe] at hc hxa
      simp only [he1, he2, he4] at hc hxa
      simp only [map_add,hd1,hd2,hd4] at hc
      have hh := congrArg (fun y=>f y 1) hc
      simp only [map_add,map_zero,←hf1,←hf2,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
      rw [hxe] at hc hxa
      simp only [he1, he2, he3] at hc hxa
      simp only [map_add,hd1,hd2,hd3,add_zero] at hc
      have hh := congrArg (fun y=>f y 1) hc
      simp only [map_add,map_zero,←hf1,←hf2,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,zero_add] at hxe
      rw [hxe] at hc hxa
      simp only [he1, he2, he3, he4] at hc hxa
      simp only [map_add,hd1,hd2,hd3,hd4,add_zero] at hc
      have hh := congrArg (fun y=>f y 1) hc
      simp only [map_add,map_zero,←hf1,←hf2,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
      try simp only [Finsupp.single_zero,add_zero] at hxe
      rw [hxe] at hc hxa
      simp only [he0] at hc hxa
      exact Or.inr (represents_unique hxa ha0)
    · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
      rw [hxe] at hc hxa
      simp only [he0, he4] at hc hxa
      simp only [map_add,hd0,hd4,zero_add] at hc
      have hh := congrArg (fun y=>f y 4) hc
      simp only [map_zero,←hf4,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
      rw [hxe] at hc hxa
      simp only [he0, he3] at hc hxa
      exact Or.inr (by simpa only [add_zero] using represents_unique hxa (represents_add_tail ha0 hz3))
    · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
      rw [hxe] at hc hxa
      simp only [he0, he3, he4] at hc hxa
      simp only [map_add,hd0,hd3,hd4,zero_add,add_zero] at hc
      have hh := congrArg (fun y=>f y 4) hc
      simp only [map_zero,←hf4,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
      rw [hxe] at hc hxa
      simp only [he0, he2] at hc hxa
      simp only [map_add,hd0,hd2,zero_add] at hc
      have hh := congrArg (fun y=>f y 3) hc
      simp only [map_add,map_zero,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
      rw [hxe] at hc hxa
      simp only [he0, he2, he4] at hc hxa
      simp only [map_add,hd0,hd2,hd4,zero_add] at hc
      have hh := congrArg (fun y=>f y 3) hc
      simp only [map_add,map_zero,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
      rw [hxe] at hc hxa
      simp only [he0, he2, he3] at hc hxa
      simp only [map_add,hd0,hd2,hd3,zero_add,add_zero] at hc
      have hh := congrArg (fun y=>f y 3) hc
      simp only [map_add,map_zero,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
      rw [hxe] at hc hxa
      simp only [he0, he2, he3, he4] at hc hxa
      simp only [map_add,hd0,hd2,hd3,hd4,zero_add,add_zero] at hc
      have hh := congrArg (fun y=>f y 3) hc
      simp only [map_add,map_zero,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
      rw [hxe] at hc hxa
      simp only [he0, he1] at hc hxa
      simp only [map_add,hd0,hd1,zero_add] at hc
      have hh := congrArg (fun y=>f y 1) hc
      simp only [map_add,map_zero,←hf1,←hf2,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
      rw [hxe] at hc hxa
      simp only [he0, he1, he4] at hc hxa
      simp only [map_add,hd0,hd1,hd4,zero_add] at hc
      have hh := congrArg (fun y=>f y 1) hc
      simp only [map_add,map_zero,←hf1,←hf2,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
      rw [hxe] at hc hxa
      simp only [he0, he1, he3] at hc hxa
      simp only [map_add,hd0,hd1,hd3,zero_add,add_zero] at hc
      have hh := congrArg (fun y=>f y 1) hc
      simp only [map_add,map_zero,←hf1,←hf2,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
      rw [hxe] at hc hxa
      simp only [he0, he1, he3, he4] at hc hxa
      simp only [map_add,hd0,hd1,hd3,hd4,zero_add,add_zero] at hc
      have hh := congrArg (fun y=>f y 1) hc
      simp only [map_add,map_zero,←hf1,←hf2,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
      rw [hxe] at hc hxa
      simp only [he0, he1, he2] at hc hxa
      simp only [map_add,hd0,hd1,hd2,zero_add] at hc
      have hh := congrArg (fun y=>f y 1) hc
      simp only [map_add,map_zero,←hf1,←hf2,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
      rw [hxe] at hc hxa
      simp only [he0, he1, he2, he4] at hc hxa
      simp only [map_add,hd0,hd1,hd2,hd4,zero_add] at hc
      have hh := congrArg (fun y=>f y 1) hc
      simp only [map_add,map_zero,←hf1,←hf2,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
      rw [hxe] at hc hxa
      simp only [he0, he1, he2, he3] at hc hxa
      simp only [map_add,hd0,hd1,hd2,hd3,zero_add,add_zero] at hc
      have hh := congrArg (fun y=>f y 1) hc
      simp only [map_add,map_zero,←hf1,←hf2,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
      try simp only [map_add] at hxe
      rw [hxe] at hc hxa
      simp only [he0, he1, he2, he3, he4] at hc hxa
      simp only [map_add,hd0,hd1,hd2,hd3,hd4,zero_add,add_zero] at hc
      have hh := congrArg (fun y=>f y 1) hc
      simp only [map_add,map_zero,←hf1,←hf2,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
  refine ⟨b0,hb0,?_⟩
  intro a
  rcases frame a with rfl|rfl
  · exact Or.inl (map_zero _)
  · exact Or.inr hd'

private theorem correction_nonzero_four_h279 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 3 (8,134) (11,136)
    (I.interpretation.basis .sphere 8 134 3) (I.interpretation.basis .sphere 11 136 1) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,3,8,134,[3],11,136,[1],"S0_AdamsE2_ss",2850⟩ (by
    exact List.mem_of_getElem? (i := 279) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (8,134) (11,136) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 134 [3] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 11 136 [1] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem correction_nonzero_four_h280 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 3 (8,134) (11,136)
    (I.interpretation.basis .sphere 8 134 2) (I.interpretation.basis .sphere 11 136 2) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,3,8,134,[2],11,136,[2],"S0_AdamsE2_ss",2851⟩ (by
    exact List.mem_of_getElem? (i := 280) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (8,134) (11,136) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 134 [2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 11 136 [2] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem correction_nonzero_four_h282 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 4 (11,136) (15,139)
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

private theorem correction_nonzero_four_h283 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (11,136) (13,137)
    (I.interpretation.basis .sphere 11 136 4) (I.interpretation.basis .sphere 13 137 3) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,11,136,[4],13,137,[3],"S0_AdamsE2_ss",2854⟩ (by
    exact List.mem_of_getElem? (i := 283) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (11,136) (13,137) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 11 136 [4] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 13 137 [3] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem correction_nonzero_four_h281 (I : AdamsComputationTheorems D L G) : ReachesPage (sequence D .sphere) 5 (11,136) (I.interpretation.basis .sphere 11 136 3) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.reaches,5,11,136,[3],11,136,[],"S0_AdamsE2_ss",2852⟩ (by
    exact List.mem_of_getElem? (i := 281) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,hd⟩ := hrow
  change ReachesPage (sequence D .sphere) 5 (11,136) x at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 11 136 [3] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
  rw [←hx] at hd
  simpa only [add_assoc] using hd

private theorem correction_nonzero_four (I : AdamsComputationTheorems D L G)
    {a : (sequence D .sphere).Page 4 (13,137)}
    (ha : RepresentsOnPage (sequence D .sphere) 4 (13,137)
      (I.interpretation.basis .sphere 13 137 1) a) : a≠0 := by
  classical
  let E := sequence D .sphere
  have h279 : HasDifferential E 3 (8,134) (11,136)
      (I.interpretation.basis .sphere 8 134 3) (I.interpretation.basis .sphere 11 136 1) := correction_nonzero_four_h279 I
  have h280 : HasDifferential E 3 (8,134) (11,136)
      (I.interpretation.basis .sphere 8 134 2) (I.interpretation.basis .sphere 11 136 2) := correction_nonzero_four_h280 I
  have h282 : HasDifferential E 4 (11,136) (15,139)
      (I.interpretation.basis .sphere 11 136 0) (I.interpretation.basis .sphere 15 139 0) := correction_nonzero_four_h282 I
  have h283 : HasDifferential E 2 (11,136) (13,137)
      (I.interpretation.basis .sphere 11 136 4) (I.interpretation.basis .sphere 13 137 3) := correction_nonzero_four_h283 I
  have h281 : ReachesPage E 5 (11,136) (I.interpretation.basis .sphere 11 136 3) := correction_nonzero_four_h281 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,13,137,["76,1,82,1", "9,1,251,1", "7,1,275,1", "0,5,367,1"]⟩ (by
    exact List.mem_of_getElem? (i := 208) (by rfl))
  change E.Page 2 (13,137) ≃ₗ[ℤ] (Fin 4 →₀ F2) at e
  change ∀ i : Fin 4, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 13 137 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 4) 1) = I.interpretation.basis .sphere 13 137 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 4) 1) = I.interpretation.basis .sphere 13 137 1 := he 1
  have he2 : e.symm (Finsupp.single (2:Fin 4) 1) = I.interpretation.basis .sphere 13 137 2 := he 2
  have he3 : e.symm (Finsupp.single (3:Fin 4) 1) = I.interpretation.basis .sphere 13 137 3 := he 3
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,11,136,["69,1,89,1", "1,1,389,1", "1,1,388,1", "0,2,391,1", "0,3,375,1"]⟩ (by
    exact List.mem_of_getElem? (i := 192) (by rfl))
  change E.Page 2 (11,136) ≃ₗ[ℤ] (Fin 5 →₀ F2) at f
  change ∀ i : Fin 5, f.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 11 136 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 5) 1) = I.interpretation.basis .sphere 11 136 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 5) 1) = I.interpretation.basis .sphere 11 136 1 := hf 1
  have hf2 : f.symm (Finsupp.single (2:Fin 5) 1) = I.interpretation.basis .sphere 11 136 2 := hf 2
  have hf3 : f.symm (Finsupp.single (3:Fin 5) 1) = I.interpretation.basis .sphere 11 136 3 := hf 3
  have hf4 : f.symm (Finsupp.single (4:Fin 5) 1) = I.interpretation.basis .sphere 11 136 4 := hf 4
  let ell (x : E.Page 2 (13,137)) : F2 := e x 1
  have hsub {r : ℤ} {p : ℤ×ℤ} {x y : E.Page 2 p} {a b : E.Page r p}
      (hx : RepresentsOnPage E r p x a) (hy : RepresentsOnPage E r p y b) :
      RepresentsOnPage E r p (x-y) (a-b) := by
    exact represents_sub_tail (by assumption) (by assumption)
  have dz {p : ℤ×ℤ} {x : E.Page 2 p} {r : ℤ} (hr : 3≤r)
      (hx : ReachesPage E r p x) : E.d 2 p x=0 := by
    obtain ⟨a,ha⟩ := hx
    obtain ⟨b,hb⟩ := represents_before (by decide : (2:ℤ)≤2) (by omega : (2:ℤ)≤r) ha
    rw [←hb.eq_on_page_two] at hb
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by omega) hb ⟨a,ha⟩
  have hd0 : E.d 2 (11,136) (I.interpretation.basis .sphere 11 136 0)=0 := by
    obtain ⟨_,a,b,ha,_,_⟩ := h282
    exact dz (by decide) ⟨a,ha⟩
  have hd1 : E.d 2 (11,136) (I.interpretation.basis .sphere 11 136 1)=0 := by
    obtain ⟨_,a,b,_,hb,_⟩ := h279
    exact dz (by decide) ⟨b,hb⟩
  have hd2 : E.d 2 (11,136) (I.interpretation.basis .sphere 11 136 2)=0 := by
    obtain ⟨_,a,b,_,hb,_⟩ := h280
    exact dz (by decide) ⟨b,hb⟩
  have hd3 : E.d 2 (11,136) (I.interpretation.basis .sphere 11 136 3)=0 := dz (by decide) h281
  have hd4 : E.d 2 (11,136) (I.interpretation.basis .sphere 11 136 4)=I.interpretation.basis .sphere 13 137 3 := h283.eq_on_page_two.2
  have incoming_zero (x : E.Page 2 (11,136)) : ell (E.d 2 (11,136) x)=0 := by
    have hall (a : Fin 5 →₀ F2) : ell (E.d 2 (11,136) (f.symm a))=0 := by
      dsimp only [ell]
      induction a using Finsupp.induction with
      | zero => simp
      | @single_add i c a hi hci ih =>
        rw [map_add,map_add,map_add,Finsupp.add_apply,ih,add_zero]
        fin_cases c
        · simp
        · change e (E.d 2 (11,136) (f.symm (Finsupp.single i 1))) 1=0
          fin_cases i
          · change e (E.d 2 (11,136) (f.symm (Finsupp.single 0 1))) 1=0
            simp only [hf0,hd0,map_zero,Finsupp.zero_apply]
          · change e (E.d 2 (11,136) (f.symm (Finsupp.single 1 1))) 1=0
            simp only [hf1,hd1,map_zero,Finsupp.zero_apply]
          · change e (E.d 2 (11,136) (f.symm (Finsupp.single 2 1))) 1=0
            simp only [hf2,hd2,map_zero,Finsupp.zero_apply]
          · change e (E.d 2 (11,136) (f.symm (Finsupp.single 3 1))) 1=0
            simp only [hf3,hd3,map_zero,Finsupp.zero_apply]
          · change e (E.d 2 (11,136) (f.symm (Finsupp.single 4 1))) 1=0
            rw [hf4,hd4,←he3,LinearEquiv.apply_symm_apply]
            norm_num [Finsupp.single_apply,Fin.ext_iff]
    simpa only [LinearEquiv.symm_apply_apply] using hall (f x)
  have nz3 {x : E.Page 2 (13,137)} (hx : ell x=1) {a : E.Page 3 (13,137)}
      (ha : RepresentsOnPage E 3 (13,137) x a) : a≠0 := by
    intro ha0
    obtain ⟨_,z,hz2,hz3⟩ := ha
    obtain ⟨u,hu⟩ := (next_projection_zero_iff_incoming E 2 (by change (2:ℤ)≤2; omega) (11,136) z).mp (hz3.trans ha0)
    change E.d 2 (11,136) u = (Subobject.ofLE _ _ ((E.ssData (13,137)).Z_anti bot_le) ≫ (E.ssData (13,137)).pageπ 0) z at hu
    change (Subobject.ofLE _ _ ((E.ssData (13,137)).Z_anti bot_le) ≫ (E.ssData (13,137)).pageπ 0) z=x at hz2
    have hh := incoming_zero u
    rw [hu,hz2,hx] at hh
    exact one_ne_zero hh
  obtain ⟨b0,hb0,hin3⟩ := correction_incoming3 I
  obtain ⟨_,z,hz2,hz4⟩ := ha
  let A := E.ssData (13,137)
  let i := Subobject.ofLE (A.Z 2) (A.Z 1) (A.Z_anti (by decide : (1:WithTop ℕ)≤2))
  let a3 := A.pageπ 1 (i z)
  have ha3 : RepresentsOnPage E 3 (13,137) (I.interpretation.basis .sphere 13 137 1) a3 := by
    refine ⟨by decide,i z,?_,rfl⟩
    change (i ≫ Subobject.ofLE (A.Z 1) (A.Z 0) _ ≫ A.pageπ 0) z = _
    dsimp only [i]
    rw [←Category.assoc,Subobject.ofLE_comp_ofLE]
    exact hz2
  have heOne : ell (I.interpretation.basis .sphere 13 137 1)=1 := by
    dsimp only [ell]
    rw [←he1,LinearEquiv.apply_symm_apply]
    simp
  have hane : a3≠0 := nz3 heOne ha3
  have hab : a3≠b0 := by
    intro hab
    have hx : ell (I.interpretation.basis .sphere 13 137 1-I.interpretation.basis .sphere 13 137 0)=1 := by
      dsimp only [ell]
      rw [map_sub,←he1,←he0,LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply]
      norm_num [Finsupp.sub_apply,Finsupp.single_apply,Fin.ext_iff]
    exact nz3 hx (hsub ha3 hb0) (sub_eq_zero.mpr hab)
  intro ha0
  obtain ⟨u,hu⟩ := (next_projection_zero_iff_incoming E 3 (by change (2:ℤ)≤3; omega) (10,135) z).mp (hz4.trans ha0)
  change E.d 3 (10,135) u=a3 at hu
  rcases hin3 u with h|h
  · exact hane (hu.symm.trans h)
  · exact hab (hu.symm.trans h)

private theorem stem125_af6_e5_zero_h157 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 3 (4,130) (7,132) (I.interpretation.basis .sphere 4 130 0) (I.interpretation.basis .sphere 7 132 0) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere, .equation, 3, 4, 130, [0], 7, 132, [0], "S0_AdamsE2_ss", 2437⟩ (by
    exact List.mem_of_getElem? (i := 157) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (4,130) (7,132) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 4 130 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 7 132 [0] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem stem125_af6_e5_zero_h163 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (5,130) (7,131) (I.interpretation.basis .sphere 5 130 0) (I.interpretation.basis .sphere 7 131 2) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere, .equation, 2, 5, 130, [0], 7, 131, [2], "S0_AdamsE2_ss", 2435⟩ (by
    exact List.mem_of_getElem? (i := 163) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (5,130) (7,131) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 5 130 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 7 131 [2] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem stem125_af6_e5_zero_h171 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 4 (6,131) (10,134) (I.interpretation.basis .sphere 6 131 0) (I.interpretation.basis .sphere 10 134 0 + I.interpretation.basis .sphere 10 134 3) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere, .equation, 4, 6, 131, [0], 10, 134, [0, 3], "S0_AdamsE2_ss", 2492⟩ (by
    exact List.mem_of_getElem? (i := 171) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 4 (6,131) (10,134) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 6 131 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 10 134 [0, 3] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem stem125_af6_e5_zero_h172 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 4 (6,131) (10,134) (I.interpretation.basis .sphere 6 131 1) (I.interpretation.basis .sphere 10 134 0 + I.interpretation.basis .sphere 10 134 1 + I.interpretation.basis .sphere 10 134 3 + I.interpretation.basis .sphere 10 134 4) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere, .equation, 4, 6, 131, [1], 10, 134, [0, 1, 3, 4], "S0_AdamsE2_ss", 2493⟩ (by
    exact List.mem_of_getElem? (i := 172) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 4 (6,131) (10,134) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 6 131 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 10 134 [0, 1, 3, 4] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem stem125_af6_e5_zero_h200 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 3 (8,133) (11,135) (I.interpretation.basis .sphere 8 133 0) (I.interpretation.basis .sphere 11 135 0) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere, .equation, 3, 8, 133, [0], 11, 135, [0], "S0_AdamsE2_ss", 2629⟩ (by
    exact List.mem_of_getElem? (i := 200) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (8,133) (11,135) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 133 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 11 135 [0] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem stem125_af6_e5_zero_h201 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (8,133) (10,134) (I.interpretation.basis .sphere 8 133 1) (I.interpretation.basis .sphere 10 134 2 + I.interpretation.basis .sphere 10 134 4) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere, .equation, 2, 8, 133, [1], 10, 134, [2, 4], "S0_AdamsE2_ss", 2630⟩ (by
    exact List.mem_of_getElem? (i := 201) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (8,133) (10,134) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 133 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 10 134 [2, 4] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem stem125_af6_e5_zero_h249 (I : AdamsComputationTheorems D L G) : ReachesPage (sequence D .sphere) 1000 (10,134) (I.interpretation.basis .sphere 10 134 4) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere, .reaches, 1000, 10, 134, [4], 10, 134, [], "S0_AdamsE2_ss", 2693⟩ (by
    exact List.mem_of_getElem? (i := 249) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨a,ha,h⟩ := hrow
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 134 [4] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha
  rw [←ha] at h
  exact h

private theorem stem125_af6_e5_zero (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (6,131)) := by
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
  obtain ⟨e8_133,he8_133⟩ := I.basis ⟨.sphere, 8, 133, ["376,1", "375,1"]⟩ (by
    exact List.mem_of_getElem? (i := 161) (by rfl))
  change E.Page 2 (8,133) ≃ₗ[ℤ] (Fin 2 →₀ F2) at e8_133
  change ∀i : Fin 2, e8_133.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 8 133 i.val at he8_133
  have he8_133_0 : e8_133.symm (Finsupp.single 0 1) = I.interpretation.basis .sphere 8 133 0 := he8_133 0
  have he8_133_1 : e8_133.symm (Finsupp.single 1 1) = I.interpretation.basis .sphere 8 133 1 := he8_133 1
  obtain ⟨e7_132,he7_132⟩ := I.basis ⟨.sphere, 7, 132, ["0,2,340,1"]⟩ (by
    exact List.mem_of_getElem? (i := 149) (by rfl))
  change E.Page 2 (7,132) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e7_132
  change ∀i : Fin 1, e7_132.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 7 132 i.val at he7_132
  have he7_132_0 : e7_132.symm (Finsupp.single 0 1) = I.interpretation.basis .sphere 7 132 0 := he7_132 0
  obtain ⟨e6_131,he6_131⟩ := I.basis ⟨.sphere, 6, 131, ["69,1,76,1", "0,1,340,1"]⟩ (by
    exact List.mem_of_getElem? (i := 137) (by rfl))
  change E.Page 2 (6,131) ≃ₗ[ℤ] (Fin 2 →₀ F2) at e6_131
  change ∀i : Fin 2, e6_131.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 6 131 i.val at he6_131
  have he6_131_0 : e6_131.symm (Finsupp.single 0 1) = I.interpretation.basis .sphere 6 131 0 := he6_131 0
  have he6_131_1 : e6_131.symm (Finsupp.single 1 1) = I.interpretation.basis .sphere 6 131 1 := he6_131 1
  obtain ⟨e5_130,he5_130⟩ := I.basis ⟨.sphere, 5, 130, ["340,1"]⟩ (by
    exact List.mem_of_getElem? (i := 126) (by rfl))
  change E.Page 2 (5,130) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e5_130
  change ∀i : Fin 1, e5_130.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 5 130 i.val at he5_130
  have he5_130_0 : e5_130.symm (Finsupp.single 0 1) = I.interpretation.basis .sphere 5 130 0 := he5_130 0
  obtain ⟨e7_131,he7_131⟩ := I.basis ⟨.sphere, 7, 131, ["353,1", "69,1,75,1", "0,1,339,1"]⟩ (by
    exact List.mem_of_getElem? (i := 148) (by rfl))
  change E.Page 2 (7,131) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e7_131
  change ∀i : Fin 3, e7_131.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 7 131 i.val at he7_131
  have he7_131_0 : e7_131.symm (Finsupp.single 0 1) = I.interpretation.basis .sphere 7 131 0 := he7_131 0
  have he7_131_1 : e7_131.symm (Finsupp.single 1 1) = I.interpretation.basis .sphere 7 131 1 := he7_131 1
  have he7_131_2 : e7_131.symm (Finsupp.single 2 1) = I.interpretation.basis .sphere 7 131 2 := he7_131 2
  have h157 : HasDifferential E 3 (4,130) (7,132) (I.interpretation.basis .sphere 4 130 0) (I.interpretation.basis .sphere 7 132 0) := stem125_af6_e5_zero_h157 I
  have h163 : HasDifferential E 2 (5,130) (7,131) (I.interpretation.basis .sphere 5 130 0) (I.interpretation.basis .sphere 7 131 2) := stem125_af6_e5_zero_h163 I
  have h171 : HasDifferential E 4 (6,131) (10,134) (I.interpretation.basis .sphere 6 131 0) (I.interpretation.basis .sphere 10 134 0 + I.interpretation.basis .sphere 10 134 3) := stem125_af6_e5_zero_h171 I
  have h172 : HasDifferential E 4 (6,131) (10,134) (I.interpretation.basis .sphere 6 131 1) (I.interpretation.basis .sphere 10 134 0 + I.interpretation.basis .sphere 10 134 1 + I.interpretation.basis .sphere 10 134 3 + I.interpretation.basis .sphere 10 134 4) := stem125_af6_e5_zero_h172 I
  have h200 : HasDifferential E 3 (8,133) (11,135) (I.interpretation.basis .sphere 8 133 0) (I.interpretation.basis .sphere 11 135 0) := stem125_af6_e5_zero_h200 I
  have h201 : HasDifferential E 2 (8,133) (10,134) (I.interpretation.basis .sphere 8 133 1) (I.interpretation.basis .sphere 10 134 2 + I.interpretation.basis .sphere 10 134 4) := stem125_af6_e5_zero_h201 I
  have h249 : ReachesPage E 1000 (10,134) (I.interpretation.basis .sphere 10 134 4) := stem125_af6_e5_zero_h249 I
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
  have generated_one {r : ℤ} (hr : 2≤r) {p : ℤ×ℤ}
      (e : E.Page 2 p ≃ₗ[ℤ] (Fin 1 →₀ F2)) (a : E.Page r p)
      (ha : RepresentsOnPage E r p (e.symm (Finsupp.single 0 1)) a)
      (x : E.Page r p) : x=0 ∨ x=a := by
    exact FinitePageCalculus.generated_one hr e a ha x
  have generated_two {r : ℤ} (hr : 2≤r) {p : ℤ×ℤ}
      (e : E.Page 2 p ≃ₗ[ℤ] (Fin 2 →₀ F2)) (a b : E.Page r p)
      (ha : RepresentsOnPage E r p (e.symm (Finsupp.single 0 1)) a)
      (hb : RepresentsOnPage E r p (e.symm (Finsupp.single 1 1)) b)
      (x : E.Page r p) : x=0 ∨ x=a ∨ x=b ∨ x=a+b := by
    exact FinitePageCalculus.generated_two hr e a b ha hb x
  have incoming2 (x : E.Page 2 (8,133)) : E.d 2 (8,133) x=0 ∨
      E.d 2 (8,133) x=I.interpretation.basis .sphere 10 134 2+I.interpretation.basis .sphere 10 134 4 := by
    obtain ⟨_,a,b,ha,hb,hd⟩ := h200
    have d0 := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) (hrep2 _) ⟨a,ha⟩
    have d1 := h201.eq_on_page_two.2
    change E.d 2 (8,133) (I.interpretation.basis .sphere 8 133 1)=_ at d1
    have h := generated_two (by decide : (2:ℤ)≤2) e8_133 _ _
      (by rw [he8_133_0]; exact hrep2 _) (by rw [he8_133_1]; exact hrep2 _) x
    rcases h with h|h|h|h
    · exact Or.inl (by rw [h,map_zero])
    · exact Or.inl (by rw [h,d0])
    · exact Or.inr (by rw [h,d1])
    · exact Or.inr (by rw [h,map_add,d0,d1,zero_add])
  have incoming3 : E.d 3 (7,132)=0 := by
    obtain ⟨_,a,b,ha,hb,hd⟩ := h157
    have hd0 : E.d 3 (7,132) b=0 := IsPageBoundary.d_eq_zero (E:=E) (r:=3) (p:=(4,130)) ⟨a,hd⟩
    ext x
    rcases generated_one (by decide : (2:ℤ)≤3) e7_132 b (by rw [he7_132_0]; exact hb) x with h|h
    · simp only [h,map_zero,ModuleCat.hom_zero]
    · simp only [h,hd0,ModuleCat.hom_zero,LinearMap.zero_apply]
  obtain ⟨_,a4,y4,ha4,hy4,hda4⟩ := h171
  obtain ⟨_,b4,z4,hb4,hz4,hdb4⟩ := h172
  have incoming4 (x : E.Page 4 (6,131)) : E.d 4 (6,131) x=0 ∨ E.d 4 (6,131) x=y4 ∨
      E.d 4 (6,131) x=z4 ∨ E.d 4 (6,131) x=y4+z4 := by
    have da : E.d 4 (6,131) a4=y4 := hda4
    have db : E.d 4 (6,131) b4=z4 := hdb4
    rcases generated_two (by decide : (2:ℤ)≤4) e6_131 a4 b4
      (by rw [he6_131_0]; exact ha4) (by rw [he6_131_1]; exact hb4) x with h|h|h|h
    · exact Or.inl (by rw [h,map_zero])
    · exact Or.inr (Or.inl (by rw [h,da]))
    · exact Or.inr (Or.inr (Or.inl (by rw [h,db])))
    · exact Or.inr (Or.inr (Or.inr (by rw [h,map_add,da,db])))
  have nonzero3_coord {x : E.Page 2 (10,134)} (j : Fin 5) (hj : j=0 ∨ j=1)
      (hx : e10_134 x j ≠ 0) {a : E.Page 3 (10,134)}
      (ha : RepresentsOnPage E 3 (10,134) x a) : a≠0 := by
    obtain ⟨_,z,hz2,hz3⟩ := ha
    intro ha0
    obtain ⟨b,hb⟩ := (next_projection_zero_iff_incoming E 2
      (by change (2:ℤ)≤2;omega) (8,133) z).mp (hz3.trans ha0)
    have he : E.d 2 (8,133) b=x := hb.trans hz2
    apply hx
    rcases incoming2 b with h|h
    · rw [←he,h,map_zero]
      rfl
    · rw [←he,h,←he10_134_2,←he10_134_4,map_add,LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply]
      rcases hj with rfl|rfl <;> simp
  have nonzero4_coord {x : E.Page 2 (10,134)} (j : Fin 5) (hj : j=0 ∨ j=1)
      (hx : e10_134 x j≠0) {a : E.Page 4 (10,134)}
      (ha : RepresentsOnPage E 4 (10,134) x a) : a≠0 := by
    obtain ⟨b,hb⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤4) ha
    exact represents_next_nonzero_of_incoming_zero_at
      (by change (2:ℤ)≤3;omega) (by decide : (2:ℤ)≤3) (by exact incoming3) ha hb
      (nonzero3_coord j hj hx hb)
  have yn : y4≠0 := nonzero4_coord 0 (Or.inl rfl) (by
    rw [←he10_134_0,←he10_134_3,map_add,LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply]
    simp) hy4
  have zn : z4≠0 := nonzero4_coord 1 (Or.inr rfl) (by
    rw [←he10_134_0,←he10_134_1,←he10_134_3,←he10_134_4]
    simp only [map_add,LinearEquiv.apply_symm_apply,Finsupp.add_apply]
    simp) hz4
  have yzn : y4+z4≠0 := nonzero4_coord 1 (Or.inr rfl) (by
    rw [←he10_134_0,←he10_134_1,←he10_134_3,←he10_134_4]
    simp only [map_add,LinearEquiv.apply_symm_apply,Finsupp.add_apply]
    simp) (hadd hy4 hz4)
  have da : E.d 4 (6,131) a4=y4 := hda4
  have db : E.d 4 (6,131) b4=z4 := hdb4
  have ker (x : E.Page 4 (6,131)) (hx : E.d 4 (6,131) x=0) : x=0 := by
    rcases generated_two (by decide : (2:ℤ)≤4) e6_131 a4 b4
      (by rw [he6_131_0];exact ha4) (by rw [he6_131_1];exact hb4) x with h|h|h|h
    · exact h
    · exact (yn (by simpa only [h,da] using hx)).elim
    · exact (zn (by simpa only [h,db] using hx)).elim
    · exact (yzn (by simpa only [h,map_add,da,db] using hx)).elim
  have hinj : Function.Injective (E.d 4 (6,131)) := (injective_iff_map_eq_zero _).mpr ker
  let S := E.pageShortComplex 4 ((6,131)-E.diffDeg 4)
  have hs : Function.Injective S.g := hinj
  have hsex : S.Exact := S.moduleCat_exact_iff.mpr (by
    intro z hz
    have hz0 : z=0 := hs (hz.trans (map_zero _).symm)
    exact ⟨0,by simp [hz0]⟩)
  have hzero := (S.exact_iff_isZero_homology).mp hsex
  exact ModuleCat.subsingleton_of_isZero ((pageHomologyIso E 4 (6,131)
    (by change (2:ℤ)≤4;omega)).isZero_iff.mpr hzero)

private theorem tail_af5_h163 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (5,130) (7,131)
    (I.interpretation.basis .sphere 5 130 0) (I.interpretation.basis .sphere 7 131 2) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,5,130,[0],7,131,[2],"S0_AdamsE2_ss",2435⟩ (by
    exact List.mem_of_getElem? (i := 163) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (5,130) (7,131) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 5 130 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 7 131 [2] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

/-- The complete stem-125 basis in Adams filtration five vanishes on E₅. -/
theorem stem125_filtration_five_page_five_subsingleton (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (5,130)) := by
  classical
  let E := sequence D .sphere
  have h163 : HasDifferential E 2 (5,130) (7,131)
      (I.interpretation.basis .sphere 5 130 0) (I.interpretation.basis .sphere 7 131 2) := tail_af5_h163 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,5,130,["340,1"]⟩ (by
    exact List.mem_of_getElem? (i := 126) (by rfl))
  change E.Page 2 (5,130) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e
  change ∀ i : Fin 1, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 5 130 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 1) 1) = I.interpretation.basis .sphere 5 130 0 := he 0
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,7,131,["353,1", "69,1,75,1", "0,1,339,1"]⟩ (by
    exact List.mem_of_getElem? (i := 148) (by rfl))
  change E.Page 2 (7,131) ≃ₗ[ℤ] (Fin 3 →₀ F2) at f
  change ∀ i : Fin 3, f.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 7 131 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 3) 1) = I.interpretation.basis .sphere 7 131 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 3) 1) = I.interpretation.basis .sphere 7 131 1 := hf 1
  have hf2 : f.symm (Finsupp.single (2:Fin 3) 1) = I.interpretation.basis .sphere 7 131 2 := hf 2
  have hd0 : E.d 2 (5,130) (I.interpretation.basis .sphere 5 130 0) =
      I.interpretation.basis .sphere 7 131 2 := h163.eq_on_page_two.2
  apply fifth_zero_of_second_kernel (E:=E) (by change (2:ℤ)≤2; omega) (5,130)
  intro x hx
  have heq : e x = (Finsupp.single 0 (e x 0)) := by
    apply Finsupp.ext
    intro i
    fin_cases i; simp
  have hxe : x = e.symm (Finsupp.single 0 (e x 0)) := by rw [←heq,LinearEquiv.symm_apply_apply]
  generalize hc0 : e x 0 = c0 at hxe
  fin_cases c0
  · change x = e.symm (Finsupp.single 0 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_zero] at hxe
    rw [hxe] at hx ⊢
    exact RepresentsOnPage.zero (E:=E) (p:=(5,130)) (r:=5) (by decide)
  · change x = e.symm (Finsupp.single 0 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [he0, hd0] at hx
    have hval := congrArg (fun y => f y 2) hx
    simp only [map_zero, ←hf2, LinearEquiv.apply_symm_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply, Fin.ext_iff] at hval

private theorem tail_af7_h157 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 3 (4,130) (7,132)
    (I.interpretation.basis .sphere 4 130 0) (I.interpretation.basis .sphere 7 132 0) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,3,4,130,[0],7,132,[0],"S0_AdamsE2_ss",2437⟩ (by
    exact List.mem_of_getElem? (i := 157) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (4,130) (7,132) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 4 130 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 7 132 [0] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem tail_af7 (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (7,132)) := by
  classical
  let E := sequence D .sphere
  have h157 : HasDifferential E 3 (4,130) (7,132)
      (I.interpretation.basis .sphere 4 130 0) (I.interpretation.basis .sphere 7 132 0) := tail_af7_h157 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,7,132,["0,2,340,1"]⟩ (by
    exact List.mem_of_getElem? (i := 149) (by rfl))
  change E.Page 2 (7,132) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e
  change ∀ i : Fin 1, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 7 132 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 1) 1) = I.interpretation.basis .sphere 7 132 0 := he 0
  apply fifth_zero_of_all_basis e
  intro i
  rw [he i]
  fin_cases i
  · exact differential_target_later_zero (by change (2:ℤ)≤3; omega) (by decide) h157

private theorem correction_survives1000_h323 (I : AdamsComputationTheorems D L G) : ReachesPage (sequence D .sphere) 1000 (13,137) (I.interpretation.basis .sphere 13 137 1) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.reaches,1000,13,137,[1],13,137,[],"S0_AdamsE2_ss",2916⟩ (by
    exact List.mem_of_getElem? (i := 323) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,hd⟩ := hrow
  change ReachesPage (sequence D .sphere) 1000 (13,137) x at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 13 137 [1] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
  rw [←hx] at hd
  simpa only [add_assoc] using hd

private theorem correction_survives1000 (I : AdamsComputationTheorems D L G) :
    SurvivesTo (sequence D .sphere) 1000 (13,137) (I.interpretation.basis .sphere 13 137 1) := by
  classical
  let E := sequence D .sphere
  have h323 : ReachesPage E 1000 (13,137) (I.interpretation.basis .sphere 13 137 1) := correction_survives1000_h323 I
  have empty (s : ℕ) (hs : s≤4) : Subsingleton (E.Page 2 (s,(s:ℤ)+125)) := by
    interval_cases s
    · change Subsingleton (E.Page 2 (0,125))
      obtain ⟨e,he⟩ := I.basis ⟨.sphere,0,125,[]⟩ (by
        exact List.mem_of_getElem? (i := 76) (by rfl))
      change E.Page 2 (0,125) ≃ₗ[ℤ] (Fin 0 →₀ F2) at e
      change ∀ i : Fin 0, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 0 125 i.val at he
      exact e.injective.subsingleton
    · change Subsingleton (E.Page 2 (1,126))
      obtain ⟨e,he⟩ := I.basis ⟨.sphere,1,126,[]⟩ (by
        exact List.mem_of_getElem? (i := 89) (by rfl))
      change E.Page 2 (1,126) ≃ₗ[ℤ] (Fin 0 →₀ F2) at e
      change ∀ i : Fin 0, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 1 126 i.val at he
      exact e.injective.subsingleton
    · change Subsingleton (E.Page 2 (2,127))
      obtain ⟨e,he⟩ := I.basis ⟨.sphere,2,127,[]⟩ (by
        exact List.mem_of_getElem? (i := 99) (by rfl))
      change E.Page 2 (2,127) ≃ₗ[ℤ] (Fin 0 →₀ F2) at e
      change ∀ i : Fin 0, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 2 127 i.val at he
      exact e.injective.subsingleton
    · change Subsingleton (E.Page 2 (3,128))
      obtain ⟨e,he⟩ := I.basis ⟨.sphere,3,128,[]⟩ (by
        exact List.mem_of_getElem? (i := 107) (by rfl))
      change E.Page 2 (3,128) ≃ₗ[ℤ] (Fin 0 →₀ F2) at e
      change ∀ i : Fin 0, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 3 128 i.val at he
      exact e.injective.subsingleton
    · change Subsingleton (E.Page 2 (4,129))
      obtain ⟨e,he⟩ := I.basis ⟨.sphere,4,129,[]⟩ (by
        exact List.mem_of_getElem? (i := 118) (by rfl))
      change E.Page 2 (4,129) ≃ₗ[ℤ] (Fin 0 →₀ F2) at e
      change ∀ i : Fin 0, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 4 129 i.val at he
      exact e.injective.subsingleton
  have incoming_late (r : ℤ) (hr : 4≤r) : E.d r ((13,137)-E.diffDeg r)=0 := by
    by_cases h9 : r<9
    · have hrs : r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by omega
      rcases hrs with rfl|rfl|rfl|rfl|rfl
      · exact correction_source9_d4_zero I
      · have he : Subsingleton (E.Page 5 (8,133)) :=
          adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum 4 5 8 133
            (by decide) (by decide) (correction_source8_four I)
        ext x
        change E.d 5 (8,133) x=0
        rw [he.elim x 0,map_zero]
      · have he : Subsingleton (E.Page 6 (7,132)) :=
          adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum 5 6 7 132
            (by decide) (by decide) (tail_af7 I)
        ext x
        change E.d 6 (7,132) x=0
        rw [he.elim x 0,map_zero]
      · have he : Subsingleton (E.Page 7 (6,131)) :=
          adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum 5 7 6 131
            (by decide) (by decide) (stem125_af6_e5_zero I)
        ext x
        change E.d 7 (6,131) x=0
        rw [he.elim x 0,map_zero]
      · have he : Subsingleton (E.Page 8 (5,130)) :=
          adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum 5 8 5 130
            (by decide) (by decide) (stem125_filtration_five_page_five_subsingleton I)
        ext x
        change E.d 8 (5,130) x=0
        rw [he.elim x 0,map_zero]
    · by_cases h14 : 14≤r
      · have he : Subsingleton (E.Page r (13-r,138-r)) :=
          adamsTowerInternal_page_subsingleton_of_negative H.unit SphereSpectrum r (13-r) (138-r) (by omega)
        ext x
        change E.d r (13-r,137-(r-1)) x=0
        have he' : Subsingleton (E.Page r (13-r,137-(r-1))) := by
          have ht : (137:ℤ)-(r-1)=138-r := by omega
          simpa only [ht] using he
        rw [he'.elim x 0,map_zero]
      · have hr9 : 9≤r := by omega
        have hr13 : r≤13 := by omega
        interval_cases r
        · have he : Subsingleton (E.Page 9 (4,129)) :=
            adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum 2 9 4 129
              (by decide) (by decide) (empty 4 (by decide))
          ext x
          change E.d 9 (4,129) x=0
          rw [he.elim x 0,map_zero]
        · have he : Subsingleton (E.Page 10 (3,128)) :=
            adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum 2 10 3 128
              (by decide) (by decide) (empty 3 (by decide))
          ext x
          change E.d 10 (3,128) x=0
          rw [he.elim x 0,map_zero]
        · have he : Subsingleton (E.Page 11 (2,127)) :=
            adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum 2 11 2 127
              (by decide) (by decide) (empty 2 (by decide))
          ext x
          change E.d 11 (2,127) x=0
          rw [he.elim x 0,map_zero]
        · have he : Subsingleton (E.Page 12 (1,126)) :=
            adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum 2 12 1 126
              (by decide) (by decide) (empty 1 (by decide))
          ext x
          change E.d 12 (1,126) x=0
          rw [he.elim x 0,map_zero]
        · have he : Subsingleton (E.Page 13 (0,125)) :=
            adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum 2 13 0 125
              (by decide) (by decide) (empty 0 (by decide))
          ext x
          change E.d 13 (0,125) x=0
          rw [he.elim x 0,map_zero]
  obtain ⟨a,ha⟩ := h323
  refine ⟨a,ha,?_⟩
  obtain ⟨_,z,hz2,hza⟩ := ha
  let A := E.ssData (13,137)
  let i := Subobject.ofLE (A.Z 998) (A.Z 2) (A.Z_anti (by decide : (2:WithTop ℕ)≤998))
  have rep4 : RepresentsOnPage E 4 (13,137) (I.interpretation.basis .sphere 13 137 1) (A.pageπ 2 (i z)) := by
    refine ⟨by decide,i z,?_,rfl⟩
    change (i ≫ Subobject.ofLE (A.Z 2) (A.Z 0) _ ≫ A.pageπ 0) z = _
    dsimp only [i]
    rw [←Category.assoc,Subobject.ofLE_comp_ofLE]
    exact hz2
  have hB : A.B ⊤=A.B 2 := boundaries_top_eq_of_d_eq_zero E 4 (by change (2:ℤ)≤4; omega) (13,137) incoming_late
  intro ha0
  have hb := (subobject_cokernel_π_eq_zero_iff (A.B 998) (A.Z 998) (A.B_le_Z _) z).mp (hza.trans ha0)
  have hb' := (ModuleCat.subobjectModule A.V).monotone (A.B_mono (show (998:WithTop ℕ)≤⊤ from le_top)) hb
  rw [hB] at hb'
  apply correction_nonzero_four I rep4
  apply (subobject_cokernel_π_eq_zero_iff (A.B 2) (A.Z 2) (A.B_le_Z _) (i z)).mpr
  change (i ≫ (A.Z 2).arrow) z ∈ _
  dsimp only [i]
  rwa [Subobject.ofLE_arrow]

private theorem named_correction_survives1000 (I : AdamsComputationTheorems D L G) :
    Derived.Survival I.interpretation 1000 correction := by
  classical

  have correction_label : I.interpretation.sphere 13 137 correction = I.interpretation.basis .sphere 13 137 1 := by
    have hmem : (⟨.sphere,13,137,["76,1,82,1", "9,1,251,1", "7,1,275,1", "0,5,367,1"]⟩ : Raw.Degree) ∈ Raw.degrees := by
      exact List.mem_of_getElem? (i := 208) (by rfl)
    have hc := I.monomials _ hmem rfl
    obtain ⟨z,hz,he⟩ := hc (1 : Fin 4)
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
  change SurvivesTo (sequence D .sphere) 1000 (13,137) _
  rw [correction_label]
  exact correction_survives1000 I

/-- Finite candidate/boundary reconstruction, including all linear
combinations.  These four claims require more than their four level-9000 rows:
use the complete basis and incoming staircase equations in the same Adams computation hypotheses. -/
theorem named_survive1000 (I : AdamsComputationTheorems D L G) :
    Derived.Survival I.interpretation 1000 U ∧
    Derived.Survival I.interpretation 1000 correction ∧
    Derived.Survival I.interpretation 1000 P ∧
    Derived.Survival I.interpretation 1000 Q := by
  obtain ⟨hu,hp,hq⟩ := named_upq_survives1000 I
  exact ⟨hu,named_correction_survives1000 I,hp,hq⟩
end

end
end KIP126.Computation.SphereAndCofiber
end
