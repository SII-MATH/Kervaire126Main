module

public import KIP126.Main.Computation.SphereAndCofiber.Bounds
public import KIP126.Main.Computation.SphereAndCofiber.Staircase
public import KIP126.Main.Computation.SphereAndCofiber.NamedSurvival
public import KIP126.Main.Computation.SphereAndCofiber.Candidates
public import KIP126.Main.Computation.SphereAndCofiber.High125
public import KIP126.Main.Computation.SphereAndCofiber.Stem125Vanishing
public import KIP126.Main.Computation.SphereAndCofiber.Stem125Differentials
public import KIP126.Main.Computation.SphereAndCofiber.CofiberAndFiltration
import all KIP126.Main.Computation.SphereAndCofiber.SphereSurvival
import all KIP126.Main.Computation.SphereAndCofiber.SphereDifferentials
import all KIP126.Main.Computation.SphereAndCofiber.SphereIncoming
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Legacy

/-!
# Sphere and Cν consequences for Section 7

The finite Adams computations are interpreted on the same comparison `D`
and the same sphere and tmf classes. The staircase hypotheses determine the
remaining incoming differential column needed for a nonzero d₃. Vanishing
and range arguments then give the local sphere consequences used in Main.
-/

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

section SphereFactsProof
open CategoryTheory.Limits KIP126.Algebra
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

open private sphere_basic_survival sphere_low_page_vanishing y_survives_five vx_empty_page
  from KIP126.Main.Computation.SphereAndCofiber.SphereSurvival
open private sphere_named_differentials sphere_product_obstructions
  from KIP126.Main.Computation.SphereAndCofiber.SphereDifferentials
open private sphere_t_incoming_and_survival
  t_incoming_t_incoming8_source_four t_incoming_t_incoming10_source_four
  t_incoming_t_incoming9_zero_h164 t_incoming_t_incoming11_zero_h151
  from KIP126.Main.Computation.SphereAndCofiber.SphereIncoming

/-- Four specified d₂ directions have zero coordinate along the E₃ target.
Vanishing of the remaining column excludes all incoming d₂ boundaries,
so the specified d₃ has nonzero target on E₃. -/
private theorem h4_d3_nonzero_of_remaining_span (I : AdamsComputationTheorems D L G)
    (hcol : (sequence D .sphere).d 2 (14,138)
      (I.interpretation.basis .sphere 14 138 2) ∈
      Submodule.span ℤ {I.interpretation.basis .sphere 16 139 1,
        I.interpretation.basis .sphere 16 139 2}) :
    Derived.Differential I.interpretation 3 (mulAt (atom .h4) (atom .x_109_12))
      (mulAt dataH1 (atom .x_122_15_2)) := by
  classical
  let E := sequence D .sphere
  have next_projection_zero_iff_incoming
      (E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ))
      (r : ℤ) (hr : E.r₀ ≤ r) (p : ℤ × ℤ)
      (z : (Subobject.underlying.obj ((E.ssData (p+E.diffDeg r)).Z
        ↑((r-E.r₀).toNat+1)) : ModuleCat.{v} ℤ)) :
      (E.ssData (p+E.diffDeg r)).pageπ ↑((r-E.r₀).toNat+1) z = 0 ↔
        (Subobject.ofLE _ _ ((E.ssData (p+E.diffDeg r)).Z_anti
          (by exact_mod_cast Nat.le_succ (r-E.r₀).toNat)) ≫
            (E.ssData (p+E.diffDeg r)).pageπ ↑(r-E.r₀).toNat) z ∈
          LinearMap.range (E.d r p).hom := by
    let D := E.ssData (p+E.diffDeg r)
    let n := (r-E.r₀).toNat
    have hnm : (↑n : WithTop ℕ) ≤ ↑(n+1) := by exact_mod_cast Nat.le_succ n
    let i := Subobject.ofLE (D.Z ↑(n+1)) (D.Z ↑n) (D.Z_anti hnm)
    let j := Subobject.ofLE (D.B ↑(n+1)) (D.Z ↑n)
      ((D.B_le_Z _).trans (D.Z_anti hnm))
    rw [← subobjectModule_image, E.B_succ r p hr, subobjectModule_image]
    change D.pageπ ↑(n+1) z = 0 ↔ (i ≫ D.pageπ ↑n) z ∈ LinearMap.range (j ≫ D.pageπ ↑n).hom
    constructor
    · intro hz
      obtain ⟨v, hv⟩ := (cokernel_π_eq_zero_iff_mem_range
        (Subobject.ofLE (D.B ↑(n+1)) (D.Z ↑(n+1)) (D.B_le_Z _)) z).mp hz
      refine ⟨v, ?_⟩
      rw [← hv]
      change (j ≫ D.pageπ ↑n) v =
        ((Subobject.ofLE (D.B ↑(n+1)) (D.Z ↑(n+1)) (D.B_le_Z _)) ≫ i ≫ D.pageπ ↑n) v
      congr 2
      dsimp only [i,j]
      rw [← Category.assoc, Subobject.ofLE_comp_ofLE]
    · rintro ⟨v, hv⟩
      apply (subobject_cokernel_π_eq_zero_iff (D.B ↑(n+1)) (D.Z ↑(n+1)) (D.B_le_Z _) z).mpr
      have hz : D.pageπ ↑n (i z-j v) = 0 := by
        rw [map_sub]
        exact sub_eq_zero.mpr hv.symm
      have hb := (subobject_cokernel_π_eq_zero_iff (D.B ↑n) (D.Z ↑n) (D.B_le_Z _) _).mp hz
      have hb' := (ModuleCat.subobjectModule D.V).monotone (D.B_mono hnm) hb
      have hv' : (D.Z ↑n).arrow (j v) ∈ (ModuleCat.subobjectModule D.V) (D.B ↑(n+1)) := by
        change (j ≫ (D.Z ↑n).arrow) v ∈ _
        dsimp only [j]
        rw [Subobject.ofLE_arrow]
        exact ⟨v, rfl⟩
      have hh := ((ModuleCat.subobjectModule D.V) (D.B ↑(n+1))).add_mem hb' hv'
      rw [map_sub, sub_add_cancel] at hh
      change (i ≫ (D.Z ↑n).arrow) z ∈ _ at hh
      dsimp only [i] at hh
      rwa [Subobject.ofLE_arrow] at hh
  have h308 : HasDifferential E 2 (12,137) (14,138)
      (I.interpretation.basis .sphere 12 137 1) (I.interpretation.basis .sphere 14 138 4) := by
    have hr := I.adamsStatements ⟨.sphere,.equation,2,12,137,[1],14,138,[4],"S0_AdamsE2_ss",2921⟩
      (by exact List.getElem_mem (l := Raw.claims) (n := 308) (by decide))
    dsimp only [AdamsStatement] at hr
    obtain ⟨a,ha,b,hb,hd⟩ := hr
    have vx : Raw.coordinatesValid Raw.degrees .sphere 12 137 [1] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 14 138 [4] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at hd
    exact hd
  have h309 : HasDifferential E 2 (12,137) (14,138)
      (I.interpretation.basis .sphere 12 137 0) (I.interpretation.basis .sphere 14 138 3) := by
    have hr := I.adamsStatements ⟨.sphere,.equation,2,12,137,[0],14,138,[3],"S0_AdamsE2_ss",2922⟩
      (by exact List.getElem_mem (l := Raw.claims) (n := 309) (by decide))
    dsimp only [AdamsStatement] at hr
    obtain ⟨a,ha,b,hb,hd⟩ := hr
    have vx : Raw.coordinatesValid Raw.degrees .sphere 12 137 [0] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 14 138 [3] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at hd
    exact hd
  have h324 : HasDifferential E 3 (13,137) (16,139)
      (I.interpretation.basis .sphere 13 137 2) (I.interpretation.basis .sphere 16 139 0) := by
    have hr := I.adamsStatements ⟨.sphere,.equation,3,13,137,[2],16,139,[0],"S0_AdamsE2_ss",2917⟩
      (by exact List.getElem_mem (l := Raw.claims) (n := 324) (by decide))
    dsimp only [AdamsStatement] at hr
    obtain ⟨a,ha,b,hb,hd⟩ := hr
    have vx : Raw.coordinatesValid Raw.degrees .sphere 13 137 [2] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 16 139 [0] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at hd
    exact hd
  have h366 : HasDifferential E 2 (14,138) (16,139)
      (I.interpretation.basis .sphere 14 138 1) (I.interpretation.basis .sphere 16 139 1 + I.interpretation.basis .sphere 16 139 2) := by
    have hr := I.adamsStatements ⟨.sphere,.equation,2,14,138,[1],16,139,[1, 2],"S0_AdamsE2_ss",3072⟩
      (by exact List.getElem_mem (l := Raw.claims) (n := 366) (by decide))
    dsimp only [AdamsStatement] at hr
    obtain ⟨a,ha,b,hb,hd⟩ := hr
    have vx : Raw.coordinatesValid Raw.degrees .sphere 14 138 [1] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 16 139 [1, 2] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at hd
    exact hd
  have h367 : HasDifferential E 2 (14,138) (16,139)
      (I.interpretation.basis .sphere 14 138 0 + I.interpretation.basis .sphere 14 138 1) (I.interpretation.basis .sphere 16 139 2) := by
    have hr := I.adamsStatements ⟨.sphere,.equation,2,14,138,[0, 1],16,139,[2],"S0_AdamsE2_ss",3073⟩
      (by exact List.getElem_mem (l := Raw.claims) (n := 367) (by decide))
    dsimp only [AdamsStatement] at hr
    obtain ⟨a,ha,b,hb,hd⟩ := hr
    have vx : Raw.coordinatesValid Raw.degrees .sphere 14 138 [0, 1] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 16 139 [2] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at hd
    exact hd
  obtain ⟨e,he⟩ := I.basis ⟨.sphere, 14, 138, ["440,1", "439,1", "23,1,190,1", "1,1,418,1", "1,1,417,1"]⟩
    (by exact List.getElem_mem (l := Raw.degrees) (n := 216) (by decide))
  change E.Page 2 (14,138) ≃ₗ[ℤ] (Fin 5 →₀ F2) at e
  change ∀ i : Fin 5, e.symm (Finsupp.single i 1) =
    I.interpretation.basis .sphere 14 138 i.val at he
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere, 16, 139, ["1,1,424,1", "0,1,438,1", "0,3,418,1"]⟩
    (by exact List.getElem_mem (l := Raw.degrees) (n := 230) (by decide))
  change E.Page 2 (16,139) ≃ₗ[ℤ] (Fin 3 →₀ F2) at f
  change ∀ i : Fin 3, f.symm (Finsupp.single i 1) =
    I.interpretation.basis .sphere 16 139 i.val at hf
  have hf0 : f.symm (Finsupp.single (0 : Fin 3) 1) = I.interpretation.basis .sphere 16 139 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1 : Fin 3) 1) = I.interpretation.basis .sphere 16 139 1 := hf 1
  have hf2 : f.symm (Finsupp.single (2 : Fin 3) 1) = I.interpretation.basis .sphere 16 139 2 := hf 2
  have d1 : E.d 2 (14,138) (I.interpretation.basis .sphere 14 138 1) =
      I.interpretation.basis .sphere 16 139 1 + I.interpretation.basis .sphere 16 139 2 :=
    h366.eq_on_page_two.2
  have d01 : E.d 2 (14,138)
      (I.interpretation.basis .sphere 14 138 0 + I.interpretation.basis .sphere 14 138 1) =
      I.interpretation.basis .sphere 16 139 2 := h367.eq_on_page_two.2
  have d3 : E.d 2 (14,138) (I.interpretation.basis .sphere 14 138 3) = 0 := by
    have hd := h309.eq_on_page_two.2
    change E.d 2 (12,137) _ = _ at hd
    rw [←hd]
    exact congrArg (fun f => f (I.interpretation.basis .sphere 12 137 0)) (E.d_comp_d 2 (12,137))
  have d4 : E.d 2 (14,138) (I.interpretation.basis .sphere 14 138 4) = 0 := by
    have hd := h308.eq_on_page_two.2
    change E.d 2 (12,137) _ = _ at hd
    rw [←hd]
    exact congrArg (fun f => f (I.interpretation.basis .sphere 12 137 1)) (E.d_comp_d 2 (12,137))
  have coord1 : f (E.d 2 (14,138) (I.interpretation.basis .sphere 14 138 1)) 0 = 0 := by
    rw [d1, ←hf1, ←hf2, map_add, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    norm_num [Finsupp.single_apply, Fin.ext_iff]
  have coord0 : f (E.d 2 (14,138) (I.interpretation.basis .sphere 14 138 0)) 0 = 0 := by
    have hh := congrArg (fun z => f z 0) d01
    simp only [map_add, Finsupp.add_apply, coord1, add_zero] at hh
    rw [hh, ←hf2, LinearEquiv.apply_symm_apply]
    norm_num [Finsupp.single_apply, Fin.ext_iff]
  have coord2 : f (E.d 2 (14,138) (I.interpretation.basis .sphere 14 138 2)) 0 = 0 := by
    let coord : E.Page 2 (16,139) →ₗ[ℤ] F2 :=
      (Finsupp.lapply (0 : Fin 3)).comp f.toLinearMap
    have hspan : Submodule.span ℤ {I.interpretation.basis .sphere 16 139 1,
        I.interpretation.basis .sphere 16 139 2} ≤ coord.ker := by
      apply Submodule.span_le.mpr
      intro z hz
      rcases Set.mem_insert_iff.mp hz with rfl | hz
      · change f (I.interpretation.basis .sphere 16 139 1) 0 = 0
        rw [← hf1, LinearEquiv.apply_symm_apply]
        norm_num [Finsupp.single_apply, Fin.ext_iff]
      · have hz' := Set.mem_singleton_iff.mp hz
        subst z
        change f (I.interpretation.basis .sphere 16 139 2) 0 = 0
        rw [← hf2, LinearEquiv.apply_symm_apply]
        norm_num [Finsupp.single_apply, Fin.ext_iff]
    exact hspan hcol
  have one (i : Fin 5) : f (E.d 2 (14,138) (e.symm (Finsupp.single i 1))) 0 = 0 := by
    rw [he]
    fin_cases i
    · exact coord0
    · exact coord1
    · exact coord2
    · simp only [d3, map_zero, Finsupp.zero_apply]
    · simp only [d4, map_zero, Finsupp.zero_apply]
  have all (c : Fin 5 →₀ F2) : f (E.d 2 (14,138) (e.symm c)) 0 = 0 := by
    induction c using Finsupp.induction with
    | zero => simp
    | @single_add i a c hi ha ih =>
      rw [map_add, map_add, map_add, Finsupp.add_apply, ih, add_zero]
      fin_cases a
      · simp
      · exact one i
  have image_zero (a : E.Page 2 (14,138)) : f (E.d 2 (14,138) a) 0 = 0 := by
    simpa only [LinearEquiv.symm_apply_apply] using all (e a)
  obtain ⟨hdeg,x3,y3,hx3,hy3,hd3⟩ := h324
  have yn : y3 ≠ 0 := by
    intro hy0
    obtain ⟨_,z,hz,hzy⟩ := hy3
    have hm := (next_projection_zero_iff_incoming E 2 (by change (2:ℤ)≤2; omega)
      (14,138) z).mp (hzy.trans hy0)
    change (Subobject.ofLE _ _ _ ≫ (E.ssData (16,139)).pageπ 0) z ∈
      LinearMap.range (E.d 2 (14,138)).hom at hm
    change (Subobject.ofLE _ _ _ ≫ (E.ssData (16,139)).pageπ 0) z =
      I.interpretation.basis .sphere 16 139 0 at hz
    rw [hz] at hm
    obtain ⟨a,ha⟩ := hm
    have hzero := image_zero a
    rw [ha, ←hf0, LinearEquiv.apply_symm_apply] at hzero
    norm_num at hzero
  have hd : HasNonzeroDifferential E 3 (13,137) (16,139)
      (I.interpretation.basis .sphere 13 137 2) (I.interpretation.basis .sphere 16 139 0) :=
    ⟨hdeg,x3,y3,hx3,hy3,hd3,yn⟩
  have source_label : I.interpretation.sphere 13 137 (mulAt (atom .h4) (atom .x_109_12)) =
      I.interpretation.basis .sphere 13 137 2 := by
    have hc := I.monomials ⟨.sphere, 13, 137, ["76,1,82,1", "9,1,251,1", "7,1,275,1", "0,5,367,1"]⟩
      (by exact List.getElem_mem (l := Raw.degrees) (n := 208) (by decide)) rfl
    obtain ⟨z,hz,he⟩ := hc (2 : Fin 4)
    have heq : (mulAt (atom .h4) (atom .x_109_12)) = z := by
      apply Subtype.ext
      rw [hz]
      change generator ⟨7,by decide⟩ * generator ⟨275,by decide⟩ = projection (monomialOfString "7,1,275,1")
      have hs : "7,1,275,1" ≠ "" := by decide
      have hp : (("7,1,275,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [7, 1, 275, 1] := by
        have split : "7,1,275,1".splitOn "," = ["7", "1", "275", "1"] := by
          simp +decide [String.splitOn,String.splitOnAux]
        rw [split]
        simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
          String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
      simp only [monomialOfString,if_neg hs,hp]
      norm_num [polynomialOfPowers,RawData.generatorCount,generator,map_mul,pow_two,mul_assoc]
    rw [heq]
    exact he
  have target_label : I.interpretation.sphere 16 139 (mulAt dataH1 (atom .x_122_15_2)) =
      I.interpretation.basis .sphere 16 139 0 := by
    have hc := I.monomials ⟨.sphere, 16, 139, ["1,1,424,1", "0,1,438,1", "0,3,418,1"]⟩
      (by exact List.getElem_mem (l := Raw.degrees) (n := 230) (by decide)) rfl
    obtain ⟨z,hz,he⟩ := hc (0 : Fin 3)
    have heq : (mulAt dataH1 (atom .x_122_15_2)) = z := by
      apply Subtype.ext
      rw [hz]
      change generator ⟨1,by decide⟩ * generator ⟨424,by decide⟩ = projection (monomialOfString "1,1,424,1")
      have hs : "1,1,424,1" ≠ "" := by decide
      have hp : (("1,1,424,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [1, 1, 424, 1] := by
        have split : "1,1,424,1".splitOn "," = ["1", "1", "424", "1"] := by
          simp +decide [String.splitOn,String.splitOnAux]
        rw [split]
        simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
          String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
      simp only [monomialOfString,if_neg hs,hp]
      norm_num [polynomialOfPowers,RawData.generatorCount,generator,map_mul,pow_two,mul_assoc]
    rw [heq]
    exact he
  change HasNonzeroDifferential E 3 (13,137) (16,139)
    (I.interpretation.sphere 13 137 (mulAt (atom .h4) (atom .x_109_12)))
    (I.interpretation.sphere 16 139 (mulAt dataH1 (atom .x_122_15_2)))
  rw [source_label, target_label]
  exact hd

/-- A zero remaining column is a sufficient special case of the coordinate condition. -/
private theorem h4_d3_nonzero_of_remaining_column (I : AdamsComputationTheorems D L G)
    (hcol : (sequence D .sphere).d 2 (14,138)
      (I.interpretation.basis .sphere 14 138 2) = 0) :
    Derived.Differential I.interpretation 3 (mulAt (atom .h4) (atom .x_109_12))
      (mulAt dataH1 (atom .x_122_15_2)) := by
  apply h4_d3_nonzero_of_remaining_span I
  rw [hcol]
  exact Submodule.zero_mem _

/-- Combine the finite computation consequences with the nonzero d₃ proved
using the staircase on the same coordinate interpretation. -/
private theorem sphere_facts_of_d3 (I : AdamsComputationTheorems D L G) (V : SphereVanishingLine H)
    (hd3 : Derived.Differential I.interpretation 3 (mulAt (atom .h4) (atom .x_109_12))
      (mulAt dataH1 (atom .x_122_15_2))) :
    Derived.SphereFacts I.interpretation := by
  classical
  obtain ⟨hd2h6, hd2x, hVX, hY⟩ := sphere_basic_survival I
  obtain ⟨hMiddle125, hAF11, hAF12, hxH2, stem125_e2_low⟩ := sphere_low_page_vanishing I
  obtain ⟨hD3sq, hD3x1264, hD7source⟩ := sphere_named_differentials I
  obtain ⟨hD2H0six, hH5B, hH1Correction, p_h2_boundary, q_h2_boundary, hTnotH0, hTnotH2⟩ := sphere_product_obstructions I
  obtain ⟨t_permanent_cycle, w_to_e6, w_d6_targets, t_only_incoming⟩ := sphere_t_incoming_and_survival I V
  obtain ⟨hU,hCorrection,hP,hQ⟩ := named_survive1000 I
  refine {
    d2_x_125_8 := hd2x
    d2_h6 := hd2h6
    d2_h0Six_h6 := hD2H0six
    d3_h4_x_109_12 := hd3
    d3_h0Sq_x_123_13_2 := hD3sq
    d3_x_126_4 := hD3x1264
    d7_source := hD7source
    d3_x_126_6_candidates := d3_x_126_6_candidates I
    w_to_e6 := w_to_e6
    t_permanent_cycle := t_permanent_cycle
    t_only_incoming := t_only_incoming
    w_d6_targets := w_d6_targets
    u_permanent := nonzero_permanent_of_survives1000 V 10 134 (by norm_num) (by norm_num) (by norm_num) _ hU
    correction_permanent := nonzero_permanent_of_survives1000 V 13 137 (by norm_num) (by norm_num) (by norm_num) _ hCorrection
    p_permanent := nonzero_permanent_of_survives1000 V 11 133 (by norm_num) (by norm_num) (by norm_num) _ hP
    q_permanent := nonzero_permanent_of_survives1000 V 12 134 (by norm_num) (by norm_num) (by norm_num) _ hQ
    v_to_e12 := hVX.1
    v_not_hit := hVX.2.1
    y_to_e5 := hY.1
    y_not_hit_through_six := by
      have source_six_zero (I : AdamsComputationTheorems D L G) :
          Subsingleton ((sequence D .sphere).Page 6 (5,131)) := by
        classical
        let E := sequence D .sphere
        obtain ⟨e, he⟩ := I.basis ⟨.sphere,5,131,["0,3,69,2"]⟩ (by
          exact List.mem_of_getElem? (i := 127) (by rfl))
        change E.Page 2 (5,131) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e
        change ∀ i : Fin 1, e.symm (Finsupp.single i 1) =
          I.interpretation.basis .sphere 5 131 i.val at he
        have hz : RepresentsOnPage E 6 (5,131) (I.interpretation.basis .sphere 5 131 0) 0 :=
          differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide)
            (t_incoming_t_incoming9_zero_h164 I)
        have hall (a : E.Page 6 (5,131)) : a = 0 := by
          obtain ⟨c,hc⟩ := page_generated_from_representatives (by decide : (2:ℤ)≤6)
            e (fun _ => 0) (by
              intro i
              rw [he i]
              fin_cases i
              exact hz) a
          simpa using hc
        exact ⟨fun a b => (hall a).trans (hall b).symm⟩

      have y_incoming_source_zero_through_six (I : AdamsComputationTheorems D L G) (r : ℤ)
          (hr : 5 ≤ r) (hr6 : r ≤ 6) :
          Subsingleton ((sequence D .sphere).Page r
            ((11,136) - (sequence D .sphere).diffDeg r)) := by
        interval_cases r
        · exact adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum
            4 5 6 132 (by decide) (by decide) (t_incoming_t_incoming8_source_four I)
        · exact source_six_zero I

      refine ⟨by decide, by decide, ?_⟩
      intro r hr hr6
      let E := sequence D .sphere
      rintro ⟨q,h,z,y,hy,hyn,hd⟩
      by_cases hlow : r < 5
      · obtain ⟨x,hx⟩ := page_has_representative hr z
        have hdiff : HasDifferential E r q (11,136) x
            (I.interpretation.sphere 11 136 Y) := ⟨h,z,y,hx,hy,hd⟩
        have hzero := differential_target_later_zero
          (by change (2:ℤ)≤r; exact hr) hlow hdiff
        obtain ⟨y5,hy5,hyn5⟩ := y_survives_five I
        exact hyn5 (represents_unique hy5 hzero)
      · have hq : q = (11,136) - E.diffDeg r := eq_sub_iff_add_eq.mpr h
        subst q
        haveI := y_incoming_source_zero_through_six I r (by omega) hr6
        have hz : z = 0 := Subsingleton.elim _ _
        rw [hz, map_zero] at hd
        exact hyn hd.symm
    x_to_e6 := hVX.2.2.1
    x_not_hit := hVX.2.2.2
    high_e5 := high125_component I
    h5Sq_B_zero := hH5B
    t_not_h0_multiple := hTnotH0
    t_not_h2_multiple := hTnotH2
    x_h2_zero := hxH2
    y_not_h2_multiple := hY.2
    h1_correction_zero := hH1Correction
    p_h2_boundary := p_h2_boundary
    q_h2_boundary := q_h2_boundary
    e2_stem125_low := stem125_e2_low
    e5_stem124_af11 := hAF11
    e4_stem124_af12 := hAF12
    e4_stem125_af12 := hMiddle125.1
    e5_stem125_af13 := hMiddle125.2
  }


/-- The specified d₃ has nonzero target on E₃. Staircase row 3005 makes the
last possible incoming d₂ column zero, and the other four columns have
zero coordinate along the target. -/
theorem d3_h4_x_109_12 {literature : KIP126.ExternalHypotheses.LiteratureHypotheses}
    (c : KIP126.ExternalHypotheses.ComputationHypotheses literature) :
    Derived.Differential c.sphereAndCofiber.interpretation 3 (mulAt (atom .h4) (atom .x_109_12))
      (mulAt dataH1 (atom .x_122_15_2)) := by
  exact h4_d3_nonzero_of_remaining_column c.sphereAndCofiber (staircase_af14_d2_eq_zero c)

/-- Local sphere consequences on the specified coordinate interpretation.
The staircase hypothesis supplies the additional row needed to prove that
the h₄ differential has nonzero target. -/
theorem sphere_facts {literature : KIP126.ExternalHypotheses.LiteratureHypotheses}
    (c : KIP126.ExternalHypotheses.ComputationHypotheses literature)
    (V : SphereVanishingLine standardFoundation.hf2) :
    Derived.SphereFacts c.sphereAndCofiber.interpretation := by
  exact sphere_facts_of_d3 c.sphereAndCofiber V (d3_h4_x_109_12 c)


end SphereFactsProof


end
end KIP126.Computation.SphereAndCofiber
end
