module

public import KIP126.Def.SpectralSequence.FinitePageCalculus.Proofs
public import KIP126.Main.Computation.Tmf
public import KIP126.Main.Computation.SphereAndCofiber.High125
public import KIP126.Main.Computation.SphereAndCofiber.Stem125Differentials
public import KIP126.Main.Literature.AdamsSynthetic.Theorems
public import KIP126.Def.Synthetic.Detection.Vanishing.Proofs
public import KIP126.Def.SpectralSequence.Basic.Category.Proofs

@[expose] public section

/-!
# The weight130 high-filtration argument of Proposition 7.8

LWX `prop:possible_h_6_sq` uses the actual group pi_(125,130) and its
lambda^10-divisible subgroup. It does not claim that all classical E5
components with AF>=15, AF!=25 vanish. The AF15 d5 source and AF18 d5
target in `Computation.SphereAndCofiber` are both nonzero on E5.

These are internal Main proof obligations on the same D and I. BHS gives
the synthetic E-infinity formulas, actual lambda maps and filtration
comparison. The finite C basis/differential reconstruction and the
independent vanishing line control the whole range; D.homotopySeparated
removes the infinitely filtered remainder. No selected survival, torsion
or exhaustion statement is added to Model, literature or C.
-/
namespace KIP126.Computation.SphereAndCofiber
open KIP126.SpectralSequence.FinitePageCalculus
open CategoryTheory
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology KIP126.Classical.Adams
open KIP126.SpectralSequence KIP126.Synthetic.Context
open KIP126.Synthetic.SpectralSequence KIP126.AdamsSynthetic
open KIP126.Literature.AdamsSynthetic
open KIP126.LinE2 KIP126.Computation.Near126
universe u v w
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H}
  {D : AdamsComparison H M Syn} {L : SphereAdamsClasses H} {G : TmfDetectionClasses H}

attribute [local irreducible] KIP126.LinE2.homogeneousPart

private theorem permanentQuotient_zero_of_page_five_zero (s t b : ℤ) (hb : 4 ≤ b)
    (hpage : Subsingleton ((sequence D .sphere).Page 5 (s, t))) :
    Subsingleton (PageRepresentatives.PermanentQuotient H SphereSpectrum b (s, t)) := by
  set_option backward.isDefEq.respectTransparency false in
    let E := (sequence D .sphere).ssData (s, t)
    haveI : Subsingleton (E.page 3) := hpage
    have hcycles : PageRepresentatives.permanentCycles H SphereSpectrum (s, t) ≤
        PageRepresentatives.boundaries H SphereSpectrum 4 (s, t) := by
      rintro x ⟨z, hz⟩
      let zf := (Subobject.ofLE (E.Z ⊤) (E.Z 3) (E.Z_anti le_top)) z
      have hzero : E.pageπ 3 zf = 0 := Subsingleton.elim _ _
      obtain ⟨y, hy⟩ := (cokernel_π_eq_zero_iff_mem_range
        (Subobject.ofLE (E.B 3) (E.Z 3) (E.B_le_Z 3)) zf).mp hzero
      refine ⟨y, ?_⟩
      change PageRepresentatives.boundaryMap H SphereSpectrum 3 (s, t) y = x
      have hfactor : Subobject.ofLE (E.B 3) (E.Z 3) (E.B_le_Z 3) ≫
          PageRepresentatives.cycleMap H SphereSpectrum 3 (s, t) =
          PageRepresentatives.boundaryMap H SphereSpectrum 3 (s, t) := by
        dsimp only [PageRepresentatives.cycleMap, PageRepresentatives.boundaryMap, E, sequence, object]
        rw [← Category.assoc, Subobject.ofLE_comp_ofLE]
      rw [← hfactor, CategoryTheory.comp_apply]
      apply (congrArg (PageRepresentatives.cycleMap H SphereSpectrum 3 (s, t)) hy).trans
      exact (congrArg (fun f => f z)
        (PageRepresentatives.cycleMap_factor H SphereSpectrum (s, t) 3 ⊤ le_top)).trans hz
    have hall : ∀ x : PageRepresentatives.PermanentQuotient H SphereSpectrum b (s, t), x = 0 := by
      rintro ⟨x⟩
      change KIP126.Algebra.NestedQuotient.projection _ _ x = 0
      apply (KIP126.Algebra.NestedQuotient.projection_eq_zero x).mpr
      exact PageRepresentatives.boundaries_monotone H SphereSpectrum (s, t) hb (hcycles x.property)
    exact ⟨fun x y => (hall x).trans (hall y).symm⟩

/-- At weight130, finite E5 vanishing at AF26..64 and the classical tail
bound kill the entire actual F26. BHS quotients by the relevant incoming
boundaries (lambda exponent s-5>=21 in this range). The proof must pass
from all associated grades to the actual group using D.homotopySeparated;
neither the finite table cutoff nor graded convergence alone suffices. -/
theorem stem125_weight130_filtration26_zero
    (I : AdamsComputationTheorems D L G) (BHS : SyntheticComparisonTheorems D) (V : SphereVanishingLine H)
    (a : BiHom 125 130 (S_0_0 : Syn))
    (ha : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 26 a) : a = 0 := by
  apply D.sphereConvergence.eq_zero_of_eInfty_isZero_ge 26 125 130
    (D.homotopySeparated .sphere 125 130) ?_ a ha
  intro j hj
  set_option backward.isDefEq.respectTransparency false in
    have hpage : Subsingleton ((sequence D .sphere).Page 5 (j, 125 + j)) := by
      by_cases h64 : j ≤ 64
      · have h := stem125_e5_zero_finite I j.toNat (by omega) (by omega)
        simpa only [Int.toNat_of_nonneg (show 0 ≤ j by omega), add_comm] using h
      · simpa only [add_comm] using sphere_page_zero_stem125_tail (D := D) V 5 j (by omega) (by omega)
    haveI : Subsingleton (PageRepresentatives.PermanentQuotient H SphereSpectrum
        (1 + (125 + j) - 130) (j, 125 + j)) :=
      permanentQuotient_zero_of_page_five_zero (D := D) j (125 + j) _ (by omega) hpage
    let e := BHS.eInfty.presentation.nuWindow SphereSpectrum (j, 125 + j) 130 (by omega)
    haveI : Subsingleton (((D.family.nu D.nu SphereSpectrum).sequence.ssData (j, 125 + j, 130)).eInfty) :=
      e.injective.subsingleton
    let hnu := ModuleCat.isZero_of_subsingleton
      (((D.family.nu D.nu SphereSpectrum).sequence.ssData (j, 125 + j, 130)).eInfty)
    let f := (D.family.functor.map D.nu.unitIso.hom).eInftyMap (j, 125 + j, 130)
    let g := (D.family.functor.map D.nu.unitIso.inv).eInftyMap (j, 125 + j, 130)
    have hfg : g ≫ f = 𝟙 _ := by
      dsimp only [f, g]
      rw [← SpectralSequenceMorphism.eInftyMap_comp, ← Functor.map_comp, Iso.inv_hom_id,
        CategoryTheory.Functor.map_id, SpectralSequenceMorphism.eInftyMap_id]
    apply (CategoryTheory.Limits.IsZero.iff_id_eq_zero _).mpr
    exact hfg.symm.trans (by rw [hnu.eq_of_src f 0, CategoryTheory.Limits.comp_zero])

section
attribute [local irreducible] adamsTowerSSData adamsTowerInternalD
open CategoryTheory.Limits KIP126.Algebra
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

private theorem h125_page15 (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 6 (15,140)) := by
  classical
  let E := sequence D .sphere
  have h354 : HasDifferential E 2 (13,139) (15,140)
      (I.interpretation.basis .sphere 13 139 1) (I.interpretation.basis .sphere 15 140 4) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,2,13,139,[1],15,140,[4],"S0_AdamsE2_ss",3150⟩ (by
      exact List.mem_of_getElem? (i := 354) (by rfl))
    dsimp only [AdamsStatement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (13,139) (15,140) x y at hd
    have vx : Raw.coordinatesValid Raw.degrees .sphere 13 139 [1] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 15 140 [4] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    simpa only [add_assoc] using hd
  have h355 : HasDifferential E 4 (11,137) (15,140)
      (I.interpretation.basis .sphere 11 137 2) (I.interpretation.basis .sphere 15 140 1) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,4,11,137,[2],15,140,[1],"S0_AdamsE2_ss",3151⟩ (by
      exact List.mem_of_getElem? (i := 355) (by rfl))
    dsimp only [AdamsStatement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 4 (11,137) (15,140) x y at hd
    have vx : Raw.coordinatesValid Raw.degrees .sphere 11 137 [2] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 15 140 [1] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    simpa only [add_assoc] using hd
  have h357 : HasDifferential E 2 (15,140) (17,141)
      (I.interpretation.basis .sphere 15 140 0) (I.interpretation.basis .sphere 17 141 3) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,2,15,140,[0],17,141,[3],"S0_AdamsE2_ss",3153⟩ (by
      exact List.mem_of_getElem? (i := 357) (by rfl))
    dsimp only [AdamsStatement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (15,140) (17,141) x y at hd
    have vx : Raw.coordinatesValid Raw.degrees .sphere 15 140 [0] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 17 141 [3] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    simpa only [add_assoc] using hd
  have h358 : HasDifferential E 2 (15,140) (17,141)
      (I.interpretation.basis .sphere 15 140 3) (I.interpretation.basis .sphere 17 141 1) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,2,15,140,[3],17,141,[1],"S0_AdamsE2_ss",3154⟩ (by
      exact List.mem_of_getElem? (i := 358) (by rfl))
    dsimp only [AdamsStatement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (15,140) (17,141) x y at hd
    have vx : Raw.coordinatesValid Raw.degrees .sphere 15 140 [3] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 17 141 [1] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    simpa only [add_assoc] using hd
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,15,140,["456,1", "67,1,107,1", "1,1,439,1", "0,1,449,1", "0,3,425,1"]⟩ (by
    unfold Raw.degrees
    iterate 224 apply List.mem_cons_of_mem
    exact List.mem_cons_self)
  change E.Page 2 (15,140) ≃ₗ[ℤ] (Fin 5 →₀ F2) at e
  change ∀ i : Fin 5, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 15 140 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 5) 1) = I.interpretation.basis .sphere 15 140 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 5) 1) = I.interpretation.basis .sphere 15 140 1 := he 1
  have he2 : e.symm (Finsupp.single (2:Fin 5) 1) = I.interpretation.basis .sphere 15 140 2 := he 2
  have he3 : e.symm (Finsupp.single (3:Fin 5) 1) = I.interpretation.basis .sphere 15 140 3 := he 3
  have he4 : e.symm (Finsupp.single (4:Fin 5) 1) = I.interpretation.basis .sphere 15 140 4 := he 4
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,17,141,["472,1", "0,2,448,1", "0,3,440,1", "0,3,439,1"]⟩ (by
    unfold Raw.degrees
    iterate 239 apply List.mem_cons_of_mem
    exact List.mem_cons_self)
  change E.Page 2 (17,141) ≃ₗ[ℤ] (Fin 4 →₀ F2) at f
  change ∀ i : Fin 4, f.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 17 141 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 4) 1) = I.interpretation.basis .sphere 17 141 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 4) 1) = I.interpretation.basis .sphere 17 141 1 := hf 1
  have hf2 : f.symm (Finsupp.single (2:Fin 4) 1) = I.interpretation.basis .sphere 17 141 2 := hf 2
  have hf3 : f.symm (Finsupp.single (3:Fin 4) 1) = I.interpretation.basis .sphere 17 141 3 := hf 3
  obtain ⟨x,y,hx,hy,hd⟩ := stem125_af15_nonzero_d5 I
  have vx : Raw.coordinatesValid Raw.degrees .sphere 15 140 [2]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 20 144 [0]=true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  obtain ⟨_,u,v,hu,hv,hd,hn⟩ := hd
  have hd' : E.d 5 (15,140) u=v := hd
  have hz1 : RepresentsOnPage E 5 (15,140) (I.interpretation.basis .sphere 15 140 1) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤4; omega) (by decide) h355
  have hz4 : RepresentsOnPage E 5 (15,140) (I.interpretation.basis .sphere 15 140 4) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide) h354
  have hd1 : E.d 2 (15,140) (I.interpretation.basis .sphere 15 140 1)=0 := by
    obtain ⟨b,hb⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤5) hz1
    rw [←hb.eq_on_page_two] at hb
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide) hb ⟨0,hz1⟩
  have hd2 : E.d 2 (15,140) (I.interpretation.basis .sphere 15 140 2)=0 := by
    obtain ⟨b,hb⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤5) hu
    rw [←hb.eq_on_page_two] at hb
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide) hb ⟨u,hu⟩
  have hd4 : E.d 2 (15,140) (I.interpretation.basis .sphere 15 140 4)=0 := by
    obtain ⟨b,hb⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤5) hz4
    rw [←hb.eq_on_page_two] at hb
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide) hb ⟨0,hz4⟩
  have hd0 : E.d 2 (15,140) (I.interpretation.basis .sphere 15 140 0)=I.interpretation.basis .sphere 17 141 3 := h357.eq_on_page_two.2
  have hd3 : E.d 2 (15,140) (I.interpretation.basis .sphere 15 140 3)=I.interpretation.basis .sphere 17 141 1 := h358.eq_on_page_two.2
  have frame : ∀a : E.Page 5 (15,140), a=0 ∨ a=u := by
    apply fifth_frame_of_second_kernel (E:=E) (by change (2:ℤ)≤2; omega) (15,140) u
    intro x hx
    have heq : e x = (Finsupp.single 0 (e x 0) + Finsupp.single 1 (e x 1) + Finsupp.single 2 (e x 2) + Finsupp.single 3 (e x 3) + Finsupp.single 4 (e x 4)) := by
      apply Finsupp.ext
      intro i
      fin_cases i <;> simp
    have hxe : x=e.symm (Finsupp.single 0 (e x 0) + Finsupp.single 1 (e x 1) + Finsupp.single 2 (e x 2) + Finsupp.single 3 (e x 3) + Finsupp.single 4 (e x 4)) := by rw [←heq,LinearEquiv.symm_apply_apply]
    generalize hc0 : e x 0=c0 at hxe
    generalize hc1 : e x 1=c1 at hxe
    generalize hc2 : e x 2=c2 at hxe
    generalize hc3 : e x 3=c3 at hxe
    generalize hc4 : e x 4=c4 at hxe
    fin_cases c0 <;> fin_cases c1 <;> fin_cases c2 <;> fin_cases c3 <;> fin_cases c4
    · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
      simp only [Finsupp.single_zero,map_zero,add_zero] at hxe
      rw [hxe] at hx ⊢
      exact ⟨0,RepresentsOnPage.zero (by decide),Or.inl rfl⟩
    · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
      simp only [Finsupp.single_zero,zero_add,add_zero] at hxe
      rw [hxe] at hx ⊢
      rw [he4]
      refine ⟨0,hz4,?_⟩
      left
      simp only []
    · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
      simp only [Finsupp.single_zero,zero_add,add_zero] at hxe
      rw [hxe] at hx ⊢
      simp only [he3, hd3] at hx
      have hval := congrArg (fun y => f y 1) hx
      simp only [map_zero,←hf1,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hval
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
    · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
      simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
      rw [hxe] at hx ⊢
      simp only [map_add, he3, he4, hd3, hd4, add_zero] at hx
      have hval := congrArg (fun y => f y 1) hx
      simp only [map_zero,←hf1,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hval
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
    · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
      simp only [Finsupp.single_zero,zero_add,add_zero] at hxe
      rw [hxe] at hx ⊢
      rw [he2]
      refine ⟨u,hu,?_⟩
      right
      simp only []
    · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
      simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
      rw [hxe] at hx ⊢
      rw [he2, he4]
      refine ⟨u + 0,represents_add_tail (hu) hz4,?_⟩
      right
      simp only [add_zero]
    · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
      simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
      rw [hxe] at hx ⊢
      simp only [map_add, he2, he3, hd2, hd3, zero_add] at hx
      have hval := congrArg (fun y => f y 1) hx
      simp only [map_zero,←hf1,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hval
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
    · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
      simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
      rw [hxe] at hx ⊢
      simp only [map_add, he2, he3, he4, hd2, hd3, hd4, zero_add, add_zero] at hx
      have hval := congrArg (fun y => f y 1) hx
      simp only [map_zero,←hf1,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hval
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
    · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
      simp only [Finsupp.single_zero,zero_add,add_zero] at hxe
      rw [hxe] at hx ⊢
      rw [he1]
      refine ⟨0,hz1,?_⟩
      left
      simp only []
    · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
      simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
      rw [hxe] at hx ⊢
      rw [he1, he4]
      refine ⟨0 + 0,represents_add_tail (hz1) hz4,?_⟩
      left
      simp only [add_zero]
    · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
      simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
      rw [hxe] at hx ⊢
      simp only [map_add, he1, he3, hd1, hd3, zero_add] at hx
      have hval := congrArg (fun y => f y 1) hx
      simp only [map_zero,←hf1,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hval
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
    · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
      simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
      rw [hxe] at hx ⊢
      simp only [map_add, he1, he3, he4, hd1, hd3, hd4, zero_add, add_zero] at hx
      have hval := congrArg (fun y => f y 1) hx
      simp only [map_zero,←hf1,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hval
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
    · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
      simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
      rw [hxe] at hx ⊢
      rw [he1, he2]
      refine ⟨0 + u,represents_add_tail (hz1) hu,?_⟩
      right
      simp only [zero_add]
    · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
      simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
      rw [hxe] at hx ⊢
      rw [he1, he2, he4]
      refine ⟨0 + u + 0,represents_add_tail (represents_add_tail (hz1) hu) hz4,?_⟩
      right
      simp only [zero_add,add_zero]
    · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
      simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
      rw [hxe] at hx ⊢
      simp only [map_add, he1, he2, he3, hd1, hd2, hd3, zero_add, add_zero] at hx
      have hval := congrArg (fun y => f y 1) hx
      simp only [map_zero,←hf1,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hval
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
    · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
      simp only [Finsupp.single_zero,map_add,zero_add] at hxe
      rw [hxe] at hx ⊢
      simp only [map_add, he1, he2, he3, he4, hd1, hd2, hd3, hd4, zero_add, add_zero] at hx
      have hval := congrArg (fun y => f y 1) hx
      simp only [map_zero,←hf1,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hval
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
    · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
      simp only [Finsupp.single_zero,add_zero] at hxe
      rw [hxe] at hx ⊢
      simp only [he0, hd0] at hx
      have hval := congrArg (fun y => f y 3) hx
      simp only [map_zero,←hf3,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hval
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
    · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
      simp only [Finsupp.single_zero,map_add,add_zero] at hxe
      rw [hxe] at hx ⊢
      simp only [map_add, he0, he4, hd0, hd4, add_zero] at hx
      have hval := congrArg (fun y => f y 3) hx
      simp only [map_zero,←hf3,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hval
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
    · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
      simp only [Finsupp.single_zero,map_add,add_zero] at hxe
      rw [hxe] at hx ⊢
      simp only [map_add, he0, he3, hd0, hd3] at hx
      have hval := congrArg (fun y => f y 3) hx
      simp only [map_add,map_zero,←hf1,←hf3,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hval
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
    · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
      simp only [Finsupp.single_zero,map_add,add_zero] at hxe
      rw [hxe] at hx ⊢
      simp only [map_add, he0, he3, he4, hd0, hd3, hd4, add_zero] at hx
      have hval := congrArg (fun y => f y 3) hx
      simp only [map_add,map_zero,←hf1,←hf3,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hval
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
    · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
      simp only [Finsupp.single_zero,map_add,add_zero] at hxe
      rw [hxe] at hx ⊢
      simp only [map_add, he0, he2, hd0, hd2, add_zero] at hx
      have hval := congrArg (fun y => f y 3) hx
      simp only [map_zero,←hf3,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hval
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
    · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
      simp only [Finsupp.single_zero,map_add,add_zero] at hxe
      rw [hxe] at hx ⊢
      simp only [map_add, he0, he2, he4, hd0, hd2, hd4, add_zero] at hx
      have hval := congrArg (fun y => f y 3) hx
      simp only [map_zero,←hf3,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hval
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
    · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
      simp only [Finsupp.single_zero,map_add,add_zero] at hxe
      rw [hxe] at hx ⊢
      simp only [map_add, he0, he2, he3, hd0, hd2, hd3, add_zero] at hx
      have hval := congrArg (fun y => f y 3) hx
      simp only [map_add,map_zero,←hf1,←hf3,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hval
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
    · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
      simp only [Finsupp.single_zero,map_add,add_zero] at hxe
      rw [hxe] at hx ⊢
      simp only [map_add, he0, he2, he3, he4, hd0, hd2, hd3, hd4, add_zero] at hx
      have hval := congrArg (fun y => f y 3) hx
      simp only [map_add,map_zero,←hf1,←hf3,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hval
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
    · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
      simp only [Finsupp.single_zero,map_add,add_zero] at hxe
      rw [hxe] at hx ⊢
      simp only [map_add, he0, he1, hd0, hd1, add_zero] at hx
      have hval := congrArg (fun y => f y 3) hx
      simp only [map_zero,←hf3,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hval
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
    · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
      simp only [Finsupp.single_zero,map_add,add_zero] at hxe
      rw [hxe] at hx ⊢
      simp only [map_add, he0, he1, he4, hd0, hd1, hd4, add_zero] at hx
      have hval := congrArg (fun y => f y 3) hx
      simp only [map_zero,←hf3,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hval
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
    · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
      simp only [Finsupp.single_zero,map_add,add_zero] at hxe
      rw [hxe] at hx ⊢
      simp only [map_add, he0, he1, he3, hd0, hd1, hd3, add_zero] at hx
      have hval := congrArg (fun y => f y 3) hx
      simp only [map_add,map_zero,←hf1,←hf3,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hval
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
    · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
      simp only [Finsupp.single_zero,map_add,add_zero] at hxe
      rw [hxe] at hx ⊢
      simp only [map_add, he0, he1, he3, he4, hd0, hd1, hd3, hd4, add_zero] at hx
      have hval := congrArg (fun y => f y 3) hx
      simp only [map_add,map_zero,←hf1,←hf3,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hval
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
    · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
      simp only [Finsupp.single_zero,map_add,add_zero] at hxe
      rw [hxe] at hx ⊢
      simp only [map_add, he0, he1, he2, hd0, hd1, hd2, add_zero] at hx
      have hval := congrArg (fun y => f y 3) hx
      simp only [map_zero,←hf3,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hval
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
    · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
      simp only [Finsupp.single_zero,map_add,add_zero] at hxe
      rw [hxe] at hx ⊢
      simp only [map_add, he0, he1, he2, he4, hd0, hd1, hd2, hd4, add_zero] at hx
      have hval := congrArg (fun y => f y 3) hx
      simp only [map_zero,←hf3,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hval
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
    · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
      simp only [Finsupp.single_zero,map_add,add_zero] at hxe
      rw [hxe] at hx ⊢
      simp only [map_add, he0, he1, he2, he3, hd0, hd1, hd2, hd3, add_zero] at hx
      have hval := congrArg (fun y => f y 3) hx
      simp only [map_add,map_zero,←hf1,←hf3,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hval
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
    · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
      simp only [map_add] at hxe
      rw [hxe] at hx ⊢
      simp only [map_add, he0, he1, he2, he3, he4, hd0, hd1, hd2, hd3, hd4, add_zero] at hx
      have hval := congrArg (fun y => f y 3) hx
      simp only [map_add,map_zero,←hf1,←hf3,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hval
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  have ker (a : E.Page 5 (15,140)) (ha : E.d 5 (15,140) a=0) : a=0 := by
    rcases frame a with hz|hz
    · exact hz
    · exact (hn (by simpa only [hz,hd'] using ha)).elim
  let S := E.pageShortComplex 5 ((15,140)-E.diffDeg 5)
  have hex : S.Exact := S.moduleCat_exact_iff.mpr (by
    intro a ha
    exact ⟨0,by rw [ker a ha,map_zero]⟩)
  exact ModuleCat.subsingleton_of_isZero ((pageHomologyIso E 5 (15,140)
    (by change (2:ℤ)≤5; omega)).isZero_iff.mpr ((S.exact_iff_isZero_homology).mp hex))

private theorem h125_page16 (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 6 (16,141)) := by
  classical
  let E := sequence D .sphere
  have h371 : HasDifferential E 2 (16,141) (18,142)
      (I.interpretation.basis .sphere 16 141 0) (I.interpretation.basis .sphere 18 142 0 + I.interpretation.basis .sphere 18 142 1) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,2,16,141,[0],18,142,[0, 1],"S0_AdamsE2_ss",3255⟩ (by
      exact List.mem_of_getElem? (i := 371) (by rfl))
    dsimp only [AdamsStatement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (16,141) (18,142) x y at hd
    have vx : Raw.coordinatesValid Raw.degrees .sphere 16 141 [0] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 18 142 [0, 1] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    simpa only [add_assoc] using hd
  have h372 : HasDifferential E 2 (16,141) (18,142)
      (I.interpretation.basis .sphere 16 141 3) (I.interpretation.basis .sphere 18 142 1) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,2,16,141,[3],18,142,[1],"S0_AdamsE2_ss",3256⟩ (by
      exact List.mem_of_getElem? (i := 372) (by rfl))
    dsimp only [AdamsStatement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (16,141) (18,142) x y at hd
    have vx : Raw.coordinatesValid Raw.degrees .sphere 16 141 [3] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 18 142 [1] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    simpa only [add_assoc] using hd
  have h370 : HasDifferential E 4 (12,138) (16,141)
      (I.interpretation.basis .sphere 12 138 3) (I.interpretation.basis .sphere 16 141 1) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,4,12,138,[3],16,141,[1],"S0_AdamsE2_ss",3254⟩ (by
      exact List.mem_of_getElem? (i := 370) (by rfl))
    dsimp only [AdamsStatement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 4 (12,138) (16,141) x y at hd
    have vx : Raw.coordinatesValid Raw.degrees .sphere 12 138 [3] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 16 141 [1] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    simpa only [add_assoc] using hd
  have h369 : HasDifferential E 2 (14,140) (16,141)
      (I.interpretation.basis .sphere 14 140 1) (I.interpretation.basis .sphere 16 141 2) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,2,14,140,[1],16,141,[2],"S0_AdamsE2_ss",3253⟩ (by
      exact List.mem_of_getElem? (i := 369) (by rfl))
    dsimp only [AdamsStatement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (14,140) (16,141) x y at hd
    have vx : Raw.coordinatesValid Raw.degrees .sphere 14 140 [1] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 16 141 [2] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    simpa only [add_assoc] using hd
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,16,141,["473,1", "1,1,448,1", "0,1,67,1,107,1", "0,2,449,1"]⟩ (by
    unfold Raw.degrees
    iterate 232 apply List.mem_cons_of_mem
    exact List.mem_cons_self)
  change E.Page 2 (16,141) ≃ₗ[ℤ] (Fin 4 →₀ F2) at e
  change ∀ i : Fin 4, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 16 141 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 4) 1) = I.interpretation.basis .sphere 16 141 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 4) 1) = I.interpretation.basis .sphere 16 141 1 := he 1
  have he2 : e.symm (Finsupp.single (2:Fin 4) 1) = I.interpretation.basis .sphere 16 141 2 := he 2
  have he3 : e.symm (Finsupp.single (3:Fin 4) 1) = I.interpretation.basis .sphere 16 141 3 := he 3
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,18,142,["0,1,472,1", "0,4,440,1"]⟩ (by
    unfold Raw.degrees
    iterate 245 apply List.mem_cons_of_mem
    exact List.mem_cons_self)
  change E.Page 2 (18,142) ≃ₗ[ℤ] (Fin 2 →₀ F2) at f
  change ∀ i : Fin 2, f.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 18 142 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 2) 1) = I.interpretation.basis .sphere 18 142 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 2) 1) = I.interpretation.basis .sphere 18 142 1 := hf 1
  have hd0 : E.d 2 (16,141) (I.interpretation.basis .sphere 16 141 0) =
      I.interpretation.basis .sphere 18 142 0 + I.interpretation.basis .sphere 18 142 1 := h371.eq_on_page_two.2
  have hd3 : E.d 2 (16,141) (I.interpretation.basis .sphere 16 141 3) =
      I.interpretation.basis .sphere 18 142 1 := h372.eq_on_page_two.2
  have hz370 : RepresentsOnPage E 6 (16,141) (I.interpretation.basis .sphere 16 141 1) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤4; omega) (by decide) h370
  have hc370 : E.d 2 (16,141) (I.interpretation.basis .sphere 16 141 1) = 0 := by
    obtain ⟨x,hx⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤6) hz370
    rw [←hx.eq_on_page_two] at hx
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide) hx ⟨0,hz370⟩
  have hd1 := hc370
  have hz369 : RepresentsOnPage E 6 (16,141) (I.interpretation.basis .sphere 16 141 2) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide) h369
  have hc369 : E.d 2 (16,141) (I.interpretation.basis .sphere 16 141 2) = 0 := by
    obtain ⟨x,hx⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤6) hz369
    rw [←hx.eq_on_page_two] at hx
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide) hx ⟨0,hz369⟩
  have hd2 := hc369
  apply sixth_zero_of_second_kernel (E:=E) (by change (2:ℤ)≤2; omega) (16,141)
  intro x hx
  have heq : e x = (Finsupp.single 0 (e x 0) + Finsupp.single 1 (e x 1) + Finsupp.single 2 (e x 2) + Finsupp.single 3 (e x 3)) := by
    apply Finsupp.ext
    intro i
    fin_cases i <;> simp
  have hxe : x = e.symm (Finsupp.single 0 (e x 0) + Finsupp.single 1 (e x 1) + Finsupp.single 2 (e x 2) + Finsupp.single 3 (e x 3)) := by rw [←heq,LinearEquiv.symm_apply_apply]
  generalize hc0 : e x 0 = c0 at hxe
  generalize hc1 : e x 1 = c1 at hxe
  generalize hc2 : e x 2 = c2 at hxe
  generalize hc3 : e x 3 = c3 at hxe
  fin_cases c0 <;> fin_cases c1 <;> fin_cases c2 <;> fin_cases c3
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_zero,add_zero] at hxe
    rw [hxe] at hx ⊢
    exact RepresentsOnPage.zero (E:=E) (p:=(16,141)) (r:=6) (by decide)
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [he3, hd3] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_zero, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    rw [he2]
    simpa only [add_assoc,add_left_comm,add_comm,zero_add] using (hz369)
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he2, he3, hd2, hd3, zero_add] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_zero, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    rw [he1]
    simpa only [add_assoc,add_left_comm,add_comm,zero_add] using (hz370)
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he1, he3, hd1, hd3, zero_add] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_zero, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    rw [he1, he2]
    simpa only [add_assoc,add_left_comm,add_comm,zero_add] using (represents_add_tail (hz370) hz369)
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,zero_add] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he1, he2, he3, hd1, hd2, hd3, zero_add, add_zero] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_zero, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [he0, hd0] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_add, map_zero, ←hf0, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.add_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he0, he3, hd0, hd3] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_add, map_zero, ←hf0, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.add_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he0, he2, hd0, hd2, add_zero] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_add, map_zero, ←hf0, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.add_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he0, he2, he3, hd0, hd2, hd3, add_zero] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_add, map_zero, ←hf0, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.add_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he0, he1, hd0, hd1, add_zero] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_add, map_zero, ←hf0, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.add_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he0, he1, he3, hd0, hd1, hd3, add_zero] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_add, map_zero, ←hf0, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.add_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he0, he1, he2, hd0, hd1, hd2, add_zero] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_add, map_zero, ←hf0, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.add_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2)) at hxe
    try simp only [map_add] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he0, he1, he2, he3, hd0, hd1, hd2, hd3, add_zero] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_add, map_zero, ←hf0, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.add_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval

private theorem h125_page17 (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 6 (17,142)) := by
  classical
  let E := sequence D .sphere
  have h387 : HasDifferential E 2 (17,142) (19,143)
      (I.interpretation.basis .sphere 17 142 1) (I.interpretation.basis .sphere 19 143 1) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,2,17,142,[1],19,143,[1],"S0_AdamsE2_ss",3320⟩ (by
      exact List.mem_of_getElem? (i := 387) (by rfl))
    dsimp only [AdamsStatement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (17,142) (19,143) x y at hd
    have vx : Raw.coordinatesValid Raw.degrees .sphere 17 142 [1] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 19 143 [1] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    simpa only [add_assoc] using hd
  have h386 : HasDifferential E 2 (15,141) (17,142)
      (I.interpretation.basis .sphere 15 141 0) (I.interpretation.basis .sphere 17 142 0) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,2,15,141,[0],17,142,[0],"S0_AdamsE2_ss",3319⟩ (by
      exact List.mem_of_getElem? (i := 386) (by rfl))
    dsimp only [AdamsStatement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (15,141) (17,142) x y at hd
    have vx : Raw.coordinatesValid Raw.degrees .sphere 15 141 [0] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 17 142 [0] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    simpa only [add_assoc] using hd
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,17,142,["0,2,67,1,107,1", "0,3,449,1"]⟩ (by
    unfold Raw.degrees
    iterate 240 apply List.mem_cons_of_mem
    exact List.mem_cons_self)
  change E.Page 2 (17,142) ≃ₗ[ℤ] (Fin 2 →₀ F2) at e
  change ∀ i : Fin 2, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 17 142 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 2) 1) = I.interpretation.basis .sphere 17 142 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 2) 1) = I.interpretation.basis .sphere 17 142 1 := he 1
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,19,143,["8,1,293,1", "0,5,440,1"]⟩ (by
    unfold Raw.degrees
    iterate 251 apply List.mem_cons_of_mem
    exact List.mem_cons_self)
  change E.Page 2 (19,143) ≃ₗ[ℤ] (Fin 2 →₀ F2) at f
  change ∀ i : Fin 2, f.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 19 143 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 2) 1) = I.interpretation.basis .sphere 19 143 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 2) 1) = I.interpretation.basis .sphere 19 143 1 := hf 1
  have hd1 : E.d 2 (17,142) (I.interpretation.basis .sphere 17 142 1) =
      I.interpretation.basis .sphere 19 143 1 := h387.eq_on_page_two.2
  have hz386 : RepresentsOnPage E 6 (17,142) (I.interpretation.basis .sphere 17 142 0) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide) h386
  have hc386 : E.d 2 (17,142) (I.interpretation.basis .sphere 17 142 0) = 0 := by
    obtain ⟨x,hx⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤6) hz386
    rw [←hx.eq_on_page_two] at hx
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide) hx ⟨0,hz386⟩
  have hd0 := hc386
  apply sixth_zero_of_second_kernel (E:=E) (by change (2:ℤ)≤2; omega) (17,142)
  intro x hx
  have heq : e x = (Finsupp.single 0 (e x 0) + Finsupp.single 1 (e x 1)) := by
    apply Finsupp.ext
    intro i
    fin_cases i <;> simp
  have hxe : x = e.symm (Finsupp.single 0 (e x 0) + Finsupp.single 1 (e x 1)) := by rw [←heq,LinearEquiv.symm_apply_apply]
  generalize hc0 : e x 0 = c0 at hxe
  generalize hc1 : e x 1 = c1 at hxe
  fin_cases c0 <;> fin_cases c1
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_zero,add_zero] at hxe
    rw [hxe] at hx ⊢
    exact RepresentsOnPage.zero (E:=E) (p:=(17,142)) (r:=6) (by decide)
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,zero_add] at hxe
    rw [hxe] at hx ⊢
    simp only [he1, hd1] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_zero, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,add_zero] at hxe
    rw [hxe] at hx ⊢
    rw [he0]
    simpa only [add_assoc,add_left_comm,add_comm,zero_add] using (hz386)
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2)) at hxe
    try simp only [map_add] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he0, he1, hd0, hd1, zero_add] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_zero, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval

private theorem h125_page18 (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 6 (18,143)) := by
  classical
  let E := sequence D .sphere
  have h398 : HasDifferential E 2 (18,143) (20,144)
      (I.interpretation.basis .sphere 18 143 1) (I.interpretation.basis .sphere 20 144 1) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,2,18,143,[1],20,144,[1],"S0_AdamsE2_ss",3392⟩ (by
      exact List.mem_of_getElem? (i := 398) (by rfl))
    dsimp only [AdamsStatement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (18,143) (20,144) x y at hd
    have vx : Raw.coordinatesValid Raw.degrees .sphere 18 143 [1] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 20 144 [1] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    simpa only [add_assoc] using hd
  have h397 : HasDifferential E 5 (13,139) (18,143)
      (I.interpretation.basis .sphere 13 139 0) (I.interpretation.basis .sphere 18 143 0) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,5,13,139,[0],18,143,[0],"S0_AdamsE2_ss",3391⟩ (by
      exact List.mem_of_getElem? (i := 397) (by rfl))
    dsimp only [AdamsStatement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 5 (13,139) (18,143) x y at hd
    have vx : Raw.coordinatesValid Raw.degrees .sphere 13 139 [0] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 18 143 [0] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    simpa only [add_assoc] using hd
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,18,143,["8,2,209,1", "0,4,449,1"]⟩ (by
    unfold Raw.degrees
    iterate 246 apply List.mem_cons_of_mem
    exact List.mem_cons_self)
  change E.Page 2 (18,143) ≃ₗ[ℤ] (Fin 2 →₀ F2) at e
  change ∀ i : Fin 2, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 18 143 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 2) 1) = I.interpretation.basis .sphere 18 143 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 2) 1) = I.interpretation.basis .sphere 18 143 1 := he 1
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,20,144,["8,2,212,1", "0,6,440,1"]⟩ (by
    unfold Raw.degrees
    iterate 256 apply List.mem_cons_of_mem
    exact List.mem_cons_self)
  change E.Page 2 (20,144) ≃ₗ[ℤ] (Fin 2 →₀ F2) at f
  change ∀ i : Fin 2, f.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 20 144 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 2) 1) = I.interpretation.basis .sphere 20 144 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 2) 1) = I.interpretation.basis .sphere 20 144 1 := hf 1
  have hd1 : E.d 2 (18,143) (I.interpretation.basis .sphere 18 143 1) =
      I.interpretation.basis .sphere 20 144 1 := h398.eq_on_page_two.2
  have hz397 : RepresentsOnPage E 6 (18,143) (I.interpretation.basis .sphere 18 143 0) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤5; omega) (by decide) h397
  have hc397 : E.d 2 (18,143) (I.interpretation.basis .sphere 18 143 0) = 0 := by
    obtain ⟨x,hx⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤6) hz397
    rw [←hx.eq_on_page_two] at hx
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide) hx ⟨0,hz397⟩
  have hd0 := hc397
  apply sixth_zero_of_second_kernel (E:=E) (by change (2:ℤ)≤2; omega) (18,143)
  intro x hx
  have heq : e x = (Finsupp.single 0 (e x 0) + Finsupp.single 1 (e x 1)) := by
    apply Finsupp.ext
    intro i
    fin_cases i <;> simp
  have hxe : x = e.symm (Finsupp.single 0 (e x 0) + Finsupp.single 1 (e x 1)) := by rw [←heq,LinearEquiv.symm_apply_apply]
  generalize hc0 : e x 0 = c0 at hxe
  generalize hc1 : e x 1 = c1 at hxe
  fin_cases c0 <;> fin_cases c1
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_zero,add_zero] at hxe
    rw [hxe] at hx ⊢
    exact RepresentsOnPage.zero (E:=E) (p:=(18,143)) (r:=6) (by decide)
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,zero_add] at hxe
    rw [hxe] at hx ⊢
    simp only [he1, hd1] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_zero, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,add_zero] at hxe
    rw [hxe] at hx ⊢
    rw [he0]
    simpa only [add_assoc,add_left_comm,add_comm,zero_add] using (hz397)
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2)) at hxe
    try simp only [map_add] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he0, he1, hd0, hd1, zero_add] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_zero, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval

private theorem h125_page19 (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 6 (19,144)) := by
  classical
  apply adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum 4 6 19 144 (by decide) (by decide)
  let E := sequence D .sphere
  have h408 : HasDifferential E 3 (19,144) (22,146)
      ((I.interpretation.basis .sphere 19 144 0)) ((I.interpretation.basis .sphere 22 146 1)) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,3,19,144,[0],22,146,[1],"S0_AdamsE2_ss",3486⟩ (by
      exact List.mem_of_getElem? (i := 408) (by rfl))
    dsimp only [AdamsStatement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 3 (19,144) (22,146) x y at hd
    have vx : Raw.coordinatesValid Raw.degrees .sphere 19 144 [0] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 22 146 [1] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  have h409 : HasDifferential E 2 (19,144) (21,145)
      ((I.interpretation.basis .sphere 19 144 2)) ((I.interpretation.basis .sphere 21 145 1)) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,2,19,144,[2],21,145,[1],"S0_AdamsE2_ss",3487⟩ (by
      exact List.mem_of_getElem? (i := 409) (by rfl))
    dsimp only [AdamsStatement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (19,144) (21,145) x y at hd
    have vx : Raw.coordinatesValid Raw.degrees .sphere 19 144 [2] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 21 145 [1] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  have h410 : HasDifferential E 2 (19,144) (21,145)
      ((I.interpretation.basis .sphere 19 144 1)) ((I.interpretation.basis .sphere 21 145 0)) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,2,19,144,[1],21,145,[0],"S0_AdamsE2_ss",3488⟩ (by
      exact List.mem_of_getElem? (i := 410) (by rfl))
    dsimp only [AdamsStatement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (19,144) (21,145) x y at hd
    have vx : Raw.coordinatesValid Raw.degrees .sphere 19 144 [1] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 21 145 [0] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  have h418 : HasDifferential E 2 (18,144) (20,145)
      ((I.interpretation.basis .sphere 18 144 0)) ((I.interpretation.basis .sphere 20 145 1)) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,2,18,144,[0],20,145,[1],"S0_AdamsE2_ss",3556⟩ (by
      exact List.mem_of_getElem? (i := 418) (by rfl))
    dsimp only [AdamsStatement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (18,144) (20,145) x y at hd
    have vx : Raw.coordinatesValid Raw.degrees .sphere 18 144 [0] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 20 145 [1] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  have h419 : HasDifferential E 3 (20,145) (23,147)
      ((I.interpretation.basis .sphere 20 145 0)) ((I.interpretation.basis .sphere 23 147 2)) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,3,20,145,[0],23,147,[2],"S0_AdamsE2_ss",3557⟩ (by
      exact List.mem_of_getElem? (i := 419) (by rfl))
    dsimp only [AdamsStatement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 3 (20,145) (23,147) x y at hd
    have vx : Raw.coordinatesValid Raw.degrees .sphere 20 145 [0] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 23 147 [2] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  have h420 : HasDifferential E 2 (20,145) (22,146)
      ((I.interpretation.basis .sphere 20 145 2)) ((I.interpretation.basis .sphere 22 146 3)) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,2,20,145,[2],22,146,[3],"S0_AdamsE2_ss",3558⟩ (by
      exact List.mem_of_getElem? (i := 420) (by rfl))
    dsimp only [AdamsStatement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (20,145) (22,146) x y at hd
    have vx : Raw.coordinatesValid Raw.degrees .sphere 20 145 [2] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 22 146 [3] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,19,144,["13,1,266,1", "8,1,13,1,188,1", "0,5,449,1"]⟩ (by
    unfold Raw.degrees
    iterate 252 apply List.mem_cons_of_mem
    exact List.mem_cons_self)
  change E.Page 2 (19,144) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e
  change ∀ i : Fin 3, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 19 144 i.val at he
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,20,145,["510,1", "0,1,8,1,13,1,188,1", "0,6,449,1"]⟩ (by
    unfold Raw.degrees
    iterate 257 apply List.mem_cons_of_mem
    exact List.mem_cons_self)
  change E.Page 2 (20,145) ≃ₗ[ℤ] (Fin 3 →₀ F2) at f
  change ∀ i : Fin 3, f.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 20 145 i.val at hf
  obtain ⟨g,hg⟩ := I.basis ⟨.sphere,22,146,["517,1", "13,2,168,1", "8,1,316,1", "0,8,440,1"]⟩ (by
    unfold Raw.degrees
    iterate 265 apply List.mem_cons_of_mem
    exact List.mem_cons_self)
  change E.Page 2 (22,146) ≃ₗ[ℤ] (Fin 4 →₀ F2) at g
  change ∀ i : Fin 4, g.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 22 146 i.val at hg
  obtain ⟨k,hk⟩ := I.basis ⟨.sphere,21,145,["0,1,8,2,212,1", "0,7,440,1"]⟩ (by
    unfold Raw.degrees
    iterate 260 apply List.mem_cons_of_mem
    exact List.mem_cons_self)
  change E.Page 2 (21,145) ≃ₗ[ℤ] (Fin 2 →₀ F2) at k
  change ∀ i : Fin 2, k.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 21 145 i.val at hk
  have d20 : E.d 2 (19,144) (I.interpretation.basis .sphere 19 144 0) = 0 := by
    obtain ⟨_,x,y,hx,hy,hd⟩ := h408
    obtain ⟨x2,hx2⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide) hx
    rw [←hx2.eq_on_page_two] at hx2
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega)
      (by decide) hx2 ⟨_,hx⟩
  have d21 : E.d 2 (19,144) (I.interpretation.basis .sphere 19 144 1) =
      I.interpretation.basis .sphere 21 145 0 := h410.eq_on_page_two.2
  have d22 : E.d 2 (19,144) (I.interpretation.basis .sphere 19 144 2) =
      I.interpretation.basis .sphere 21 145 1 := h409.eq_on_page_two.2
  have df0 : E.d 2 (20,145) (I.interpretation.basis .sphere 20 145 0) = 0 := by
    obtain ⟨_,x,y,hx,hy,hd⟩ := h419
    obtain ⟨x2,hx2⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide) hx
    rw [←hx2.eq_on_page_two] at hx2
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega)
      (by decide) hx2 ⟨_,hx⟩
  have df1 : E.d 2 (20,145) (I.interpretation.basis .sphere 20 145 1) = 0 := by
    have hd : E.d 2 (18,144) (I.interpretation.basis .sphere 18 144 0) =
      I.interpretation.basis .sphere 20 145 1 := h418.eq_on_page_two.2
    exact IsPageBoundary.d_eq_zero (E:=E) (r:=2) (p:=(18,144)) ⟨_,hd⟩
  have df2 : E.d 2 (20,145) (I.interpretation.basis .sphere 20 145 2) =
      I.interpretation.basis .sphere 22 146 3 := h420.eq_on_page_two.2
  have incoming (x : E.Page 2 (20,145)) : g (E.d 2 (20,145) x) 1 = 0 := by
    have hall (a : Fin 3 →₀ F2) : g (E.d 2 (20,145) (f.symm a)) 1 = 0 := by
      induction a using Finsupp.induction with
      | zero => simp
      | @single_add i c a hi hci ih =>
        rw [map_add,map_add,map_add,Finsupp.add_apply,ih,add_zero]
        fin_cases c
        · simp
        · change g (E.d 2 (20,145) (f.symm (Finsupp.single i 1))) 1 = 0
          rw [hf i]
          fin_cases i
          · rw [df0]; exact congrArg (fun z : Fin 4 →₀ F2 => z 1) g.map_zero
          · rw [df1]; exact congrArg (fun z : Fin 4 →₀ F2 => z 1) g.map_zero
          · rw [df2]
            rw [show I.interpretation.basis .sphere 22 146 3 = g.symm (Finsupp.single 3 1) from (hg 3).symm,LinearEquiv.apply_symm_apply]
            norm_num [Finsupp.single_apply,Fin.ext_iff]
    simpa only [LinearEquiv.symm_apply_apply] using hall (f x)
  obtain ⟨_,a,b,ha,hb,hd⟩ := h408
  have hd' : E.d 3 (19,144) a = b := hd
  have hbne : b ≠ 0 := by
    intro hb0
    obtain ⟨_,z,hx,hz⟩ := hb
    have hh := (next_projection_zero_iff_incoming E 2 (by change (2:ℤ)≤2; omega) (20,145) z).mp (hz.trans hb0)
    change (Subobject.ofLE _ _ ((E.ssData (22,146)).Z_anti bot_le) ≫
      (E.ssData (22,146)).pageπ 0) z ∈ LinearMap.range (E.d 2 (20,145)).hom at hh
    change (Subobject.ofLE _ _ ((E.ssData (22,146)).Z_anti bot_le) ≫
      (E.ssData (22,146)).pageπ 0) z = I.interpretation.basis .sphere 22 146 1 at hx
    rw [hx] at hh
    obtain ⟨u,hu⟩ := hh
    have hzero := incoming u
    rw [hu] at hzero
    rw [show I.interpretation.basis .sphere 22 146 1 = g.symm (Finsupp.single 1 1) from (hg 1).symm,LinearEquiv.apply_symm_apply] at hzero
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hzero
  have frame (q : E.Page 3 (19, 144)) : q=0 ∨ q=a := by
    let A := E.ssData (19, 144)
    haveI : Epi (A.pageπ 1) := inferInstanceAs (Epi (cokernel.π _))
    obtain ⟨z,hz⟩ := (ModuleCat.epi_iff_surjective (A.pageπ 1)).mp inferInstance q
    let x : E.Page 2 (19, 144) := (Subobject.ofLE _ _ (A.Z_anti bot_le) ≫ A.pageπ 0) z
    have hx : RepresentsOnPage E 3 (19, 144) x q := ⟨by decide,z,rfl,hz⟩
    have hc : E.d 2 (19, 144) x = 0 := by
      obtain ⟨z,hz⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤3) hx
      rw [←hz.eq_on_page_two] at hz
      exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide) hz ⟨q,hx⟩
    have heq : e x = Finsupp.single 0 (e x 0) + Finsupp.single 1 (e x 1) + Finsupp.single 2 (e x 2) := by
      ext i
      fin_cases i <;> simp
    have hxe : x=e.symm (Finsupp.single 0 (e x 0) + Finsupp.single 1 (e x 1) + Finsupp.single 2 (e x 2)) := by
      rw [←heq,LinearEquiv.symm_apply_apply]
    generalize h0 : e x 0 = c0 at hxe
    generalize h1 : e x 1 = c1 at hxe
    generalize h2 : e x 2 = c2 at hxe
    fin_cases c0 <;> fin_cases c1 <;> fin_cases c2
    · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2)) at hxe
      simp only [Finsupp.single_zero,add_zero,map_zero] at hxe
      rw [hxe] at hx
      exact Or.inl (represents_unique hx (RepresentsOnPage.zero (by decide)))
    · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2)) at hxe
      simp only [Finsupp.single_zero,zero_add,add_zero] at hxe
      rw [show e.symm (Finsupp.single 2 1) = I.interpretation.basis .sphere 19 144 2 from he 2] at hxe
      have hh := congrArg (fun y => k y 1) hc
      rw [hxe] at hh
      simp only [d22] at hh
      simp only [show I.interpretation.basis .sphere 21 145 1 = k.symm (Finsupp.single 1 1) from (hk 1).symm] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2)) at hxe
      simp only [Finsupp.single_zero,zero_add,add_zero] at hxe
      rw [show e.symm (Finsupp.single 1 1) = I.interpretation.basis .sphere 19 144 1 from he 1] at hxe
      have hh := congrArg (fun y => k y 0) hc
      rw [hxe] at hh
      simp only [d21] at hh
      simp only [show I.interpretation.basis .sphere 21 145 0 = k.symm (Finsupp.single 0 1) from (hk 0).symm] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2)) at hxe
      simp only [Finsupp.single_zero,zero_add,map_add] at hxe
      rw [show e.symm (Finsupp.single 1 1) = I.interpretation.basis .sphere 19 144 1 from he 1] at hxe
      rw [show e.symm (Finsupp.single 2 1) = I.interpretation.basis .sphere 19 144 2 from he 2] at hxe
      have hh := congrArg (fun y => k y 0) hc
      rw [hxe] at hh
      simp only [map_add,d21,d22] at hh
      simp only [show I.interpretation.basis .sphere 21 145 0 = k.symm (Finsupp.single 0 1) from (hk 0).symm, show I.interpretation.basis .sphere 21 145 1 = k.symm (Finsupp.single 1 1) from (hk 1).symm] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2)) at hxe
      simp only [Finsupp.single_zero,add_zero] at hxe
      rw [show e.symm (Finsupp.single 0 1) = I.interpretation.basis .sphere 19 144 0 from he 0] at hxe
      rw [hxe] at hx
      exact Or.inr (represents_unique hx (by simpa only [he] using ha))
    · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2)) at hxe
      simp only [Finsupp.single_zero,add_zero,map_add] at hxe
      rw [show e.symm (Finsupp.single 0 1) = I.interpretation.basis .sphere 19 144 0 from he 0] at hxe
      rw [show e.symm (Finsupp.single 2 1) = I.interpretation.basis .sphere 19 144 2 from he 2] at hxe
      have hh := congrArg (fun y => k y 1) hc
      rw [hxe] at hh
      simp only [map_add,d20,d22] at hh
      simp only [show I.interpretation.basis .sphere 21 145 1 = k.symm (Finsupp.single 1 1) from (hk 1).symm] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2)) at hxe
      simp only [Finsupp.single_zero,add_zero,map_add] at hxe
      rw [show e.symm (Finsupp.single 0 1) = I.interpretation.basis .sphere 19 144 0 from he 0] at hxe
      rw [show e.symm (Finsupp.single 1 1) = I.interpretation.basis .sphere 19 144 1 from he 1] at hxe
      have hh := congrArg (fun y => k y 0) hc
      rw [hxe] at hh
      simp only [map_add,d20,d21] at hh
      simp only [show I.interpretation.basis .sphere 21 145 0 = k.symm (Finsupp.single 0 1) from (hk 0).symm] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2)) at hxe
      simp only [map_add] at hxe
      rw [show e.symm (Finsupp.single 0 1) = I.interpretation.basis .sphere 19 144 0 from he 0] at hxe
      rw [show e.symm (Finsupp.single 1 1) = I.interpretation.basis .sphere 19 144 1 from he 1] at hxe
      rw [show e.symm (Finsupp.single 2 1) = I.interpretation.basis .sphere 19 144 2 from he 2] at hxe
      have hh := congrArg (fun y => k y 0) hc
      rw [hxe] at hh
      simp only [map_add,d20,d21,d22] at hh
      simp only [show I.interpretation.basis .sphere 21 145 0 = k.symm (Finsupp.single 0 1) from (hk 0).symm, show I.interpretation.basis .sphere 21 145 1 = k.symm (Finsupp.single 1 1) from (hk 1).symm] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
  have hker (q : E.Page 3 (19,144)) (hq : E.d 3 (19,144) q=0) : q=0 := by
    rcases frame q with hh|hh
    · exact hh
    · exact (hbne (by simpa only [hh,hd'] using hq)).elim
  let S := E.pageShortComplex 3 ((19,144)-E.diffDeg 3)
  have hs : S.Exact := S.moduleCat_exact_iff.mpr (by
    intro x hx
    exact ⟨0,by rw [hker x hx,map_zero]⟩)
  exact ModuleCat.subsingleton_of_isZero ((pageHomologyIso E 3 (19,144)
    (by change (2:ℤ)≤3; omega)).isZero_iff.mpr ((S.exact_iff_isZero_homology).mp hs))


private theorem stem125_sixth_pages_15_19 (I : AdamsComputationTheorems D L G)
    (s : ℕ) (hs : 15 ≤ s) (hs' : s ≤ 19) :
    Subsingleton ((sequence D .sphere).Page 6 (s,(s:ℤ)+125)) := by
  classical

  interval_cases s
  · exact h125_page15 I
  · exact h125_page16 I
  · exact h125_page17 I
  · exact h125_page18 I
  · exact h125_page19 I

private theorem h125_page20 (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 6 (20,145)) := by
  classical
  apply adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum 4 6 20 145 (by decide) (by decide)
  let E := sequence D .sphere
  have h418 : HasDifferential E 2 (18,144) (20,145)
      ((I.interpretation.basis .sphere 18 144 0)) ((I.interpretation.basis .sphere 20 145 1)) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,2,18,144,[0],20,145,[1],"S0_AdamsE2_ss",3556⟩ (by
      exact List.mem_of_getElem? (i := 418) (by rfl))
    dsimp only [AdamsStatement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (18,144) (20,145) x y at hd
    have vx : Raw.coordinatesValid Raw.degrees .sphere 18 144 [0] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 20 145 [1] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  have h419 : HasDifferential E 3 (20,145) (23,147)
      ((I.interpretation.basis .sphere 20 145 0)) ((I.interpretation.basis .sphere 23 147 2)) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,3,20,145,[0],23,147,[2],"S0_AdamsE2_ss",3557⟩ (by
      exact List.mem_of_getElem? (i := 419) (by rfl))
    dsimp only [AdamsStatement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 3 (20,145) (23,147) x y at hd
    have vx : Raw.coordinatesValid Raw.degrees .sphere 20 145 [0] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 23 147 [2] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  have h420 : HasDifferential E 2 (20,145) (22,146)
      ((I.interpretation.basis .sphere 20 145 2)) ((I.interpretation.basis .sphere 22 146 3)) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,2,20,145,[2],22,146,[3],"S0_AdamsE2_ss",3558⟩ (by
      exact List.mem_of_getElem? (i := 420) (by rfl))
    dsimp only [AdamsStatement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (20,145) (22,146) x y at hd
    have vx : Raw.coordinatesValid Raw.degrees .sphere 20 145 [2] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 22 146 [3] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  have h426 : HasDifferential E 4 (17,143) (21,146)
      ((I.interpretation.basis .sphere 17 143 1)) ((I.interpretation.basis .sphere 21 146 0)) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,4,17,143,[1],21,146,[0],"S0_AdamsE2_ss",3629⟩ (by
      exact List.mem_of_getElem? (i := 426) (by rfl))
    dsimp only [AdamsStatement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 4 (17,143) (21,146) x y at hd
    have vx : Raw.coordinatesValid Raw.degrees .sphere 17 143 [1] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 21 146 [0] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  have h427 : HasDifferential E 2 (21,146) (23,147)
      ((I.interpretation.basis .sphere 21 146 2)) ((I.interpretation.basis .sphere 23 147 3)) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,2,21,146,[2],23,147,[3],"S0_AdamsE2_ss",3630⟩ (by
      exact List.mem_of_getElem? (i := 427) (by rfl))
    dsimp only [AdamsStatement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (21,146) (23,147) x y at hd
    have vx : Raw.coordinatesValid Raw.degrees .sphere 21 146 [2] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 23 147 [3] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  have h428 : HasDifferential E 2 (21,146) (23,147)
      ((I.interpretation.basis .sphere 21 146 1)) ((I.interpretation.basis .sphere 23 147 1) + (I.interpretation.basis .sphere 23 147 2)) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,2,21,146,[1],23,147,[1, 2],"S0_AdamsE2_ss",3631⟩ (by
      exact List.mem_of_getElem? (i := 428) (by rfl))
    dsimp only [AdamsStatement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (21,146) (23,147) x y at hd
    have vx : Raw.coordinatesValid Raw.degrees .sphere 21 146 [1] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 23 147 [1, 2] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,20,145,["510,1", "0,1,8,1,13,1,188,1", "0,6,449,1"]⟩ (by
    unfold Raw.degrees
    iterate 257 apply List.mem_cons_of_mem
    exact List.mem_cons_self)
  change E.Page 2 (20,145) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e
  change ∀ i : Fin 3, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 20 145 i.val at he
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,21,146,["518,1", "9,1,292,1", "0,7,449,1"]⟩ (by
    unfold Raw.degrees
    iterate 261 apply List.mem_cons_of_mem
    exact List.mem_cons_self)
  change E.Page 2 (21,146) ≃ₗ[ℤ] (Fin 3 →₀ F2) at f
  change ∀ i : Fin 3, f.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 21 146 i.val at hf
  obtain ⟨g,hg⟩ := I.basis ⟨.sphere,23,147,["8,1,327,1", "8,1,13,1,23,1,80,1", "0,1,8,1,316,1", "0,9,440,1"]⟩ (by
    unfold Raw.degrees
    iterate 270 apply List.mem_cons_of_mem
    exact List.mem_cons_self)
  change E.Page 2 (23,147) ≃ₗ[ℤ] (Fin 4 →₀ F2) at g
  change ∀ i : Fin 4, g.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 23 147 i.val at hg
  obtain ⟨k,hk⟩ := I.basis ⟨.sphere,22,146,["517,1", "13,2,168,1", "8,1,316,1", "0,8,440,1"]⟩ (by
    unfold Raw.degrees
    iterate 265 apply List.mem_cons_of_mem
    exact List.mem_cons_self)
  change E.Page 2 (22,146) ≃ₗ[ℤ] (Fin 4 →₀ F2) at k
  change ∀ i : Fin 4, k.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 22 146 i.val at hk
  have d20 : E.d 2 (20,145) (I.interpretation.basis .sphere 20 145 0) = 0 := by
    obtain ⟨_,x,y,hx,hy,hd⟩ := h419
    obtain ⟨x2,hx2⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide) hx
    rw [←hx2.eq_on_page_two] at hx2
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega)
      (by decide) hx2 ⟨_,hx⟩
  have d21 : E.d 2 (20,145) (I.interpretation.basis .sphere 20 145 1) = 0 := by
    have hd : E.d 2 (18,144) (I.interpretation.basis .sphere 18 144 0) =
      I.interpretation.basis .sphere 20 145 1 := h418.eq_on_page_two.2
    exact IsPageBoundary.d_eq_zero (E:=E) (r:=2) (p:=(18,144)) ⟨_,hd⟩
  have d22 : E.d 2 (20,145) (I.interpretation.basis .sphere 20 145 2) =
      I.interpretation.basis .sphere 22 146 3 := h420.eq_on_page_two.2
  have df0 : E.d 2 (21,146) (I.interpretation.basis .sphere 21 146 0) = 0 := by
    obtain ⟨_,x,y,hx,hy,hd⟩ := h426
    obtain ⟨x2,hx2⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide) hy
    rw [←hx2.eq_on_page_two] at hx2
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega)
      (by decide) hx2 ⟨_,hy⟩
  have df1 : E.d 2 (21,146) (I.interpretation.basis .sphere 21 146 1) =
      I.interpretation.basis .sphere 23 147 1 + I.interpretation.basis .sphere 23 147 2 := h428.eq_on_page_two.2
  have df2 : E.d 2 (21,146) (I.interpretation.basis .sphere 21 146 2) =
      I.interpretation.basis .sphere 23 147 3 := h427.eq_on_page_two.2
  have incoming (x : E.Page 2 (21,146)) : g (E.d 2 (21,146) x) 1 = g (E.d 2 (21,146) x) 2 := by
    have hall (a : Fin 3 →₀ F2) : g (E.d 2 (21,146) (f.symm a)) 1 = g (E.d 2 (21,146) (f.symm a)) 2 := by
      induction a using Finsupp.induction with
      | zero => simp
      | @single_add i c a hi hci ih =>
        simp only [map_add,Finsupp.add_apply]
        rw [ih]
        congr 1
        fin_cases c
        · simp
        · change g (E.d 2 (21,146) (f.symm (Finsupp.single i 1))) 1 = g (E.d 2 (21,146) (f.symm (Finsupp.single i 1))) 2
          rw [hf i]
          fin_cases i
          · rw [df0]
            simp only [map_zero,Finsupp.zero_apply]
          · rw [df1,map_add,Finsupp.add_apply,Finsupp.add_apply]
            rw [show I.interpretation.basis .sphere 23 147 1 = g.symm (Finsupp.single 1 1) from (hg 1).symm,
              show I.interpretation.basis .sphere 23 147 2 = g.symm (Finsupp.single 2 1) from (hg 2).symm]
            norm_num [Finsupp.single_apply,Fin.ext_iff]
          · rw [df2]
            rw [show I.interpretation.basis .sphere 23 147 3 = g.symm (Finsupp.single 3 1) from (hg 3).symm]
            norm_num [Finsupp.single_apply,Fin.ext_iff]
    simpa only [LinearEquiv.symm_apply_apply] using hall (f x)
  obtain ⟨_,a,b,ha,hb,hd⟩ := h419
  have hd' : E.d 3 (20,145) a = b := hd
  have hbne : b ≠ 0 := by
    intro hb0
    obtain ⟨_,z,hx,hz⟩ := hb
    have hh := (next_projection_zero_iff_incoming E 2 (by change (2:ℤ)≤2; omega) (21,146) z).mp (hz.trans hb0)
    change (Subobject.ofLE _ _ ((E.ssData (23,147)).Z_anti bot_le) ≫
      (E.ssData (23,147)).pageπ 0) z ∈ LinearMap.range (E.d 2 (21,146)).hom at hh
    change (Subobject.ofLE _ _ ((E.ssData (23,147)).Z_anti bot_le) ≫
      (E.ssData (23,147)).pageπ 0) z = I.interpretation.basis .sphere 23 147 2 at hx
    rw [hx] at hh
    obtain ⟨u,hu⟩ := hh
    have hzero := incoming u
    rw [hu] at hzero
    rw [show I.interpretation.basis .sphere 23 147 2 = g.symm (Finsupp.single 2 1) from (hg 2).symm,LinearEquiv.apply_symm_apply] at hzero
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hzero
  have hboundary : RepresentsOnPage E 3 (20,145) (I.interpretation.basis .sphere 20 145 1) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) h418
  have hadd {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)}
      {r : ℤ} {p : ℤ × ℤ} {x y : E.Page 2 p} {a b : E.Page r p}
      (hx : RepresentsOnPage E r p x a) (hy : RepresentsOnPage E r p y b) :
      RepresentsOnPage E r p (x+y) (a+b) := by
    obtain ⟨hr,z,hz,ha⟩ := hx
    obtain ⟨_,w,hw,hb⟩ := hy
    exact ⟨hr,z+w,by rw [map_add,hz,hw],by rw [map_add,ha,hb]⟩
  have frame (q : E.Page 3 (20, 145)) : q=0 ∨ q=a := by
    let A := E.ssData (20, 145)
    haveI : Epi (A.pageπ 1) := inferInstanceAs (Epi (cokernel.π _))
    obtain ⟨z,hz⟩ := (ModuleCat.epi_iff_surjective (A.pageπ 1)).mp inferInstance q
    let x : E.Page 2 (20, 145) := (Subobject.ofLE _ _ (A.Z_anti bot_le) ≫ A.pageπ 0) z
    have hx : RepresentsOnPage E 3 (20, 145) x q := ⟨by decide,z,rfl,hz⟩
    have hc : E.d 2 (20, 145) x = 0 := by
      obtain ⟨z,hz⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤3) hx
      rw [←hz.eq_on_page_two] at hz
      exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide) hz ⟨q,hx⟩
    have heq : e x = Finsupp.single 0 (e x 0) + Finsupp.single 1 (e x 1) + Finsupp.single 2 (e x 2) := by
      ext i
      fin_cases i <;> simp
    have hxe : x=e.symm (Finsupp.single 0 (e x 0) + Finsupp.single 1 (e x 1) + Finsupp.single 2 (e x 2)) := by
      rw [←heq,LinearEquiv.symm_apply_apply]
    generalize h0 : e x 0 = c0 at hxe
    generalize h1 : e x 1 = c1 at hxe
    generalize h2 : e x 2 = c2 at hxe
    fin_cases c0 <;> fin_cases c1 <;> fin_cases c2
    · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2)) at hxe
      simp only [Finsupp.single_zero,add_zero,map_zero] at hxe
      rw [hxe] at hx
      exact Or.inl (represents_unique hx (RepresentsOnPage.zero (by decide)))
    · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2)) at hxe
      simp only [Finsupp.single_zero,zero_add,add_zero] at hxe
      rw [show e.symm (Finsupp.single 2 1) = I.interpretation.basis .sphere 20 145 2 from he 2] at hxe
      have hh := congrArg (fun y => k y 3) hc
      rw [hxe] at hh
      simp only [d22] at hh
      simp only [show I.interpretation.basis .sphere 22 146 3 = k.symm (Finsupp.single 3 1) from (hk 3).symm] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2)) at hxe
      simp only [Finsupp.single_zero,zero_add,add_zero] at hxe
      rw [show e.symm (Finsupp.single 1 1) = I.interpretation.basis .sphere 20 145 1 from he 1] at hxe
      rw [hxe] at hx
      exact Or.inl (represents_unique hx (by simpa only [he] using hboundary))
    · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2)) at hxe
      simp only [Finsupp.single_zero,zero_add,map_add] at hxe
      rw [show e.symm (Finsupp.single 1 1) = I.interpretation.basis .sphere 20 145 1 from he 1] at hxe
      rw [show e.symm (Finsupp.single 2 1) = I.interpretation.basis .sphere 20 145 2 from he 2] at hxe
      have hh := congrArg (fun y => k y 3) hc
      rw [hxe] at hh
      simp only [map_add,d21,d22] at hh
      simp only [show I.interpretation.basis .sphere 22 146 3 = k.symm (Finsupp.single 3 1) from (hk 3).symm] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2)) at hxe
      simp only [Finsupp.single_zero,add_zero] at hxe
      rw [show e.symm (Finsupp.single 0 1) = I.interpretation.basis .sphere 20 145 0 from he 0] at hxe
      rw [hxe] at hx
      exact Or.inr (represents_unique hx (by simpa only [he] using ha))
    · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2)) at hxe
      simp only [Finsupp.single_zero,add_zero,map_add] at hxe
      rw [show e.symm (Finsupp.single 0 1) = I.interpretation.basis .sphere 20 145 0 from he 0] at hxe
      rw [show e.symm (Finsupp.single 2 1) = I.interpretation.basis .sphere 20 145 2 from he 2] at hxe
      have hh := congrArg (fun y => k y 3) hc
      rw [hxe] at hh
      simp only [map_add,d20,d22] at hh
      simp only [show I.interpretation.basis .sphere 22 146 3 = k.symm (Finsupp.single 3 1) from (hk 3).symm] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2)) at hxe
      simp only [Finsupp.single_zero,add_zero,map_add] at hxe
      rw [show e.symm (Finsupp.single 0 1) = I.interpretation.basis .sphere 20 145 0 from he 0] at hxe
      rw [show e.symm (Finsupp.single 1 1) = I.interpretation.basis .sphere 20 145 1 from he 1] at hxe
      rw [hxe] at hx
      exact Or.inr (represents_unique hx (by simpa only [he,add_zero] using hadd ha hboundary))
    · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2)) at hxe
      simp only [map_add] at hxe
      rw [show e.symm (Finsupp.single 0 1) = I.interpretation.basis .sphere 20 145 0 from he 0] at hxe
      rw [show e.symm (Finsupp.single 1 1) = I.interpretation.basis .sphere 20 145 1 from he 1] at hxe
      rw [show e.symm (Finsupp.single 2 1) = I.interpretation.basis .sphere 20 145 2 from he 2] at hxe
      have hh := congrArg (fun y => k y 3) hc
      rw [hxe] at hh
      simp only [map_add,d20,d21,d22] at hh
      simp only [show I.interpretation.basis .sphere 22 146 3 = k.symm (Finsupp.single 3 1) from (hk 3).symm] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
  have hker (q : E.Page 3 (20,145)) (hq : E.d 3 (20,145) q=0) : q=0 := by
    rcases frame q with hh|hh
    · exact hh
    · exact (hbne (by simpa only [hh,hd'] using hq)).elim
  let S := E.pageShortComplex 3 ((20,145)-E.diffDeg 3)
  have hs : S.Exact := S.moduleCat_exact_iff.mpr (by
    intro x hx
    exact ⟨0,by rw [hker x hx,map_zero]⟩)
  exact ModuleCat.subsingleton_of_isZero ((pageHomologyIso E 3 (20,145)
    (by change (2:ℤ)≤3; omega)).isZero_iff.mpr ((S.exact_iff_isZero_homology).mp hs))

private theorem h125_page21 (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 6 (21,146)) := by
  classical
  let E := sequence D .sphere
  have h428 : HasDifferential E 2 (21,146) (23,147)
      (I.interpretation.basis .sphere 21 146 1) (I.interpretation.basis .sphere 23 147 1 + I.interpretation.basis .sphere 23 147 2) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,2,21,146,[1],23,147,[1, 2],"S0_AdamsE2_ss",3631⟩ (by
      exact List.mem_of_getElem? (i := 428) (by rfl))
    dsimp only [AdamsStatement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (21,146) (23,147) x y at hd
    have vx : Raw.coordinatesValid Raw.degrees .sphere 21 146 [1] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 23 147 [1, 2] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    simpa only [add_assoc] using hd
  have h427 : HasDifferential E 2 (21,146) (23,147)
      (I.interpretation.basis .sphere 21 146 2) (I.interpretation.basis .sphere 23 147 3) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,2,21,146,[2],23,147,[3],"S0_AdamsE2_ss",3630⟩ (by
      exact List.mem_of_getElem? (i := 427) (by rfl))
    dsimp only [AdamsStatement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (21,146) (23,147) x y at hd
    have vx : Raw.coordinatesValid Raw.degrees .sphere 21 146 [2] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 23 147 [3] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    simpa only [add_assoc] using hd
  have h426 : HasDifferential E 4 (17,143) (21,146)
      (I.interpretation.basis .sphere 17 143 1) (I.interpretation.basis .sphere 21 146 0) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,4,17,143,[1],21,146,[0],"S0_AdamsE2_ss",3629⟩ (by
      exact List.mem_of_getElem? (i := 426) (by rfl))
    dsimp only [AdamsStatement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 4 (17,143) (21,146) x y at hd
    have vx : Raw.coordinatesValid Raw.degrees .sphere 17 143 [1] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 21 146 [0] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    simpa only [add_assoc] using hd
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,21,146,["518,1", "9,1,292,1", "0,7,449,1"]⟩ (by
    unfold Raw.degrees
    iterate 261 apply List.mem_cons_of_mem
    exact List.mem_cons_self)
  change E.Page 2 (21,146) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e
  change ∀ i : Fin 3, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 21 146 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 3) 1) = I.interpretation.basis .sphere 21 146 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 3) 1) = I.interpretation.basis .sphere 21 146 1 := he 1
  have he2 : e.symm (Finsupp.single (2:Fin 3) 1) = I.interpretation.basis .sphere 21 146 2 := he 2
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,23,147,["8,1,327,1", "8,1,13,1,23,1,80,1", "0,1,8,1,316,1", "0,9,440,1"]⟩ (by
    unfold Raw.degrees
    iterate 270 apply List.mem_cons_of_mem
    exact List.mem_cons_self)
  change E.Page 2 (23,147) ≃ₗ[ℤ] (Fin 4 →₀ F2) at f
  change ∀ i : Fin 4, f.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 23 147 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 4) 1) = I.interpretation.basis .sphere 23 147 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 4) 1) = I.interpretation.basis .sphere 23 147 1 := hf 1
  have hf2 : f.symm (Finsupp.single (2:Fin 4) 1) = I.interpretation.basis .sphere 23 147 2 := hf 2
  have hf3 : f.symm (Finsupp.single (3:Fin 4) 1) = I.interpretation.basis .sphere 23 147 3 := hf 3
  have hd1 : E.d 2 (21,146) (I.interpretation.basis .sphere 21 146 1) =
      I.interpretation.basis .sphere 23 147 1 + I.interpretation.basis .sphere 23 147 2 := h428.eq_on_page_two.2
  have hd2 : E.d 2 (21,146) (I.interpretation.basis .sphere 21 146 2) =
      I.interpretation.basis .sphere 23 147 3 := h427.eq_on_page_two.2
  have hz426 : RepresentsOnPage E 6 (21,146) (I.interpretation.basis .sphere 21 146 0) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤4; omega) (by decide) h426
  have hc426 : E.d 2 (21,146) (I.interpretation.basis .sphere 21 146 0) = 0 := by
    obtain ⟨x,hx⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤6) hz426
    rw [←hx.eq_on_page_two] at hx
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide) hx ⟨0,hz426⟩
  have hd0 := hc426
  apply sixth_zero_of_second_kernel (E:=E) (by change (2:ℤ)≤2; omega) (21,146)
  intro x hx
  have heq : e x = (Finsupp.single 0 (e x 0) + Finsupp.single 1 (e x 1) + Finsupp.single 2 (e x 2)) := by
    apply Finsupp.ext
    intro i
    fin_cases i <;> simp
  have hxe : x = e.symm (Finsupp.single 0 (e x 0) + Finsupp.single 1 (e x 1) + Finsupp.single 2 (e x 2)) := by rw [←heq,LinearEquiv.symm_apply_apply]
  generalize hc0 : e x 0 = c0 at hxe
  generalize hc1 : e x 1 = c1 at hxe
  generalize hc2 : e x 2 = c2 at hxe
  fin_cases c0 <;> fin_cases c1 <;> fin_cases c2
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_zero,add_zero] at hxe
    rw [hxe] at hx ⊢
    exact RepresentsOnPage.zero (E:=E) (p:=(21,146)) (r:=6) (by decide)
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [he2, hd2] at hx
    have hval := congrArg (fun y => f y 3) hx
    simp only [map_zero, ←hf3, LinearEquiv.apply_symm_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [he1, hd1] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_add, map_zero, ←hf1, ←hf2, LinearEquiv.apply_symm_apply, Finsupp.add_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,zero_add] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he1, he2, hd1, hd2] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_add, map_zero, ←hf1, ←hf2, ←hf3, LinearEquiv.apply_symm_apply, Finsupp.add_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,add_zero] at hxe
    rw [hxe] at hx ⊢
    rw [he0]
    simpa only [add_assoc,add_left_comm,add_comm,zero_add] using (hz426)
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he0, he2, hd0, hd2, zero_add] at hx
    have hval := congrArg (fun y => f y 3) hx
    simp only [map_zero, ←hf3, LinearEquiv.apply_symm_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he0, he1, hd0, hd1, zero_add] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_add, map_zero, ←hf1, ←hf2, LinearEquiv.apply_symm_apply, Finsupp.add_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2)) at hxe
    try simp only [map_add] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he0, he1, he2, hd0, hd1, hd2, zero_add] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_add, map_zero, ←hf1, ←hf2, ←hf3, LinearEquiv.apply_symm_apply, Finsupp.add_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval

private theorem h125_page22 (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 6 (22,147)) := by
  classical
  let E := sequence D .sphere
  have h439 : HasDifferential E 2 (22,147) (24,148)
      (I.interpretation.basis .sphere 22 147 2) (I.interpretation.basis .sphere 24 148 0) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,2,22,147,[2],24,148,[0],"S0_AdamsE2_ss",3747⟩ (by
      exact List.mem_of_getElem? (i := 439) (by rfl))
    dsimp only [AdamsStatement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (22,147) (24,148) x y at hd
    have vx : Raw.coordinatesValid Raw.degrees .sphere 22 147 [2] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 24 148 [0] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    simpa only [add_assoc] using hd
  have h438 : HasDifferential E 2 (22,147) (24,148)
      (I.interpretation.basis .sphere 22 147 3) (I.interpretation.basis .sphere 24 148 1) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,2,22,147,[3],24,148,[1],"S0_AdamsE2_ss",3746⟩ (by
      exact List.mem_of_getElem? (i := 438) (by rfl))
    dsimp only [AdamsStatement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (22,147) (24,148) x y at hd
    have vx : Raw.coordinatesValid Raw.degrees .sphere 22 147 [3] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 24 148 [1] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    simpa only [add_assoc] using hd
  have h436 : HasDifferential E 4 (18,144) (22,147)
      (I.interpretation.basis .sphere 18 144 1) (I.interpretation.basis .sphere 22 147 1) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,4,18,144,[1],22,147,[1],"S0_AdamsE2_ss",3744⟩ (by
      exact List.mem_of_getElem? (i := 436) (by rfl))
    dsimp only [AdamsStatement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 4 (18,144) (22,147) x y at hd
    have vx : Raw.coordinatesValid Raw.degrees .sphere 18 144 [1] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 22 147 [1] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    simpa only [add_assoc] using hd
  have h437 : HasDifferential E 4 (18,144) (22,147)
      (I.interpretation.basis .sphere 18 144 2 + I.interpretation.basis .sphere 18 144 3) (I.interpretation.basis .sphere 22 147 0 + I.interpretation.basis .sphere 22 147 3) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,4,18,144,[2, 3],22,147,[0, 3],"S0_AdamsE2_ss",3745⟩ (by
      exact List.mem_of_getElem? (i := 437) (by rfl))
    dsimp only [AdamsStatement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 4 (18,144) (22,147) x y at hd
    have vx : Raw.coordinatesValid Raw.degrees .sphere 18 144 [2, 3] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 22 147 [0, 3] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    simpa only [add_assoc] using hd
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,22,147,["17,1,255,1", "13,3,101,1", "0,1,9,1,292,1", "0,8,449,1"]⟩ (by
    unfold Raw.degrees
    iterate 266 apply List.mem_cons_of_mem
    exact List.mem_cons_self)
  change E.Page 2 (22,147) ≃ₗ[ℤ] (Fin 4 →₀ F2) at e
  change ∀ i : Fin 4, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 22 147 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 4) 1) = I.interpretation.basis .sphere 22 147 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 4) 1) = I.interpretation.basis .sphere 22 147 1 := he 1
  have he2 : e.symm (Finsupp.single (2:Fin 4) 1) = I.interpretation.basis .sphere 22 147 2 := he 2
  have he3 : e.symm (Finsupp.single (3:Fin 4) 1) = I.interpretation.basis .sphere 22 147 3 := he 3
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,24,148,["0,2,8,1,316,1", "0,10,440,1"]⟩ (by
    unfold Raw.degrees
    iterate 275 apply List.mem_cons_of_mem
    exact List.mem_cons_self)
  change E.Page 2 (24,148) ≃ₗ[ℤ] (Fin 2 →₀ F2) at f
  change ∀ i : Fin 2, f.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 24 148 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 2) 1) = I.interpretation.basis .sphere 24 148 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 2) 1) = I.interpretation.basis .sphere 24 148 1 := hf 1
  have hd2 : E.d 2 (22,147) (I.interpretation.basis .sphere 22 147 2) =
      I.interpretation.basis .sphere 24 148 0 := h439.eq_on_page_two.2
  have hd3 : E.d 2 (22,147) (I.interpretation.basis .sphere 22 147 3) =
      I.interpretation.basis .sphere 24 148 1 := h438.eq_on_page_two.2
  have hz436 : RepresentsOnPage E 6 (22,147) (I.interpretation.basis .sphere 22 147 1) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤4; omega) (by decide) h436
  have hc436 : E.d 2 (22,147) (I.interpretation.basis .sphere 22 147 1) = 0 := by
    obtain ⟨x,hx⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤6) hz436
    rw [←hx.eq_on_page_two] at hx
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide) hx ⟨0,hz436⟩
  have hd1 := hc436
  have hz437 : RepresentsOnPage E 6 (22,147) (I.interpretation.basis .sphere 22 147 0 + I.interpretation.basis .sphere 22 147 3) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤4; omega) (by decide) h437
  have hc437 : E.d 2 (22,147) (I.interpretation.basis .sphere 22 147 0 + I.interpretation.basis .sphere 22 147 3) = 0 := by
    obtain ⟨x,hx⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤6) hz437
    rw [←hx.eq_on_page_two] at hx
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide) hx ⟨0,hz437⟩
  have hd0 : E.d 2 (22,147) (I.interpretation.basis .sphere 22 147 0) =
      I.interpretation.basis .sphere 24 148 1 := by
    have hn : -(I.interpretation.basis .sphere 24 148 1) = I.interpretation.basis .sphere 24 148 1 := by
      apply f.injective
      rw [map_neg,←hf1,LinearEquiv.apply_symm_apply]
      ext i
      simp only [Finsupp.neg_apply]
      exact ZMod.neg_eq_self_mod_two _
    have hh := hc437
    rw [map_add,hd3] at hh
    exact (eq_neg_of_add_eq_zero_left hh).trans hn
  apply sixth_zero_of_second_kernel (E:=E) (by change (2:ℤ)≤2; omega) (22,147)
  intro x hx
  have heq : e x = (Finsupp.single 0 (e x 0) + Finsupp.single 1 (e x 1) + Finsupp.single 2 (e x 2) + Finsupp.single 3 (e x 3)) := by
    apply Finsupp.ext
    intro i
    fin_cases i <;> simp
  have hxe : x = e.symm (Finsupp.single 0 (e x 0) + Finsupp.single 1 (e x 1) + Finsupp.single 2 (e x 2) + Finsupp.single 3 (e x 3)) := by rw [←heq,LinearEquiv.symm_apply_apply]
  generalize hc0 : e x 0 = c0 at hxe
  generalize hc1 : e x 1 = c1 at hxe
  generalize hc2 : e x 2 = c2 at hxe
  generalize hc3 : e x 3 = c3 at hxe
  fin_cases c0 <;> fin_cases c1 <;> fin_cases c2 <;> fin_cases c3
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_zero,add_zero] at hxe
    rw [hxe] at hx ⊢
    exact RepresentsOnPage.zero (E:=E) (p:=(22,147)) (r:=6) (by decide)
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [he3, hd3] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_zero, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [he2, hd2] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_zero, ←hf0, LinearEquiv.apply_symm_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he2, he3, hd2, hd3] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_add, map_zero, ←hf0, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.add_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    rw [he1]
    simpa only [add_assoc,add_left_comm,add_comm,zero_add] using (hz436)
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he1, he3, hd1, hd3, zero_add] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_zero, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he1, he2, hd1, hd2, zero_add] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_zero, ←hf0, LinearEquiv.apply_symm_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,zero_add] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he1, he2, he3, hd1, hd2, hd3, zero_add] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_add, map_zero, ←hf0, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.add_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [he0, hd0] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_zero, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    rw [he0, he3]
    simpa only [add_assoc,add_left_comm,add_comm,zero_add] using (hz437)
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he0, he2, hd0, hd2] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_add, map_zero, ←hf0, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.add_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he0, he2, he3, hd0, hd2, hd3] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_add, map_zero, ←hf0, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.add_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he0, he1, hd0, hd1, add_zero] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_zero, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    rw [he0, he1, he3]
    simpa only [add_assoc,add_left_comm,add_comm,zero_add] using (represents_add_tail (hz436) hz437)
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he0, he1, he2, hd0, hd1, hd2, add_zero] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_add, map_zero, ←hf0, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.add_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2)) at hxe
    try simp only [map_add] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he0, he1, he2, he3, hd0, hd1, hd2, hd3, add_zero] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_add, map_zero, ←hf0, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.add_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval

private theorem h125_page23 (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 6 (23,148)) := by
  classical
  apply adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum 4 6 23 148 (by decide) (by decide)
  let E := sequence D .sphere
  have h445 : HasDifferential E 3 (23,148) (26,150)
      ((I.interpretation.basis .sphere 23 148 0)) ((I.interpretation.basis .sphere 26 150 2)) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,3,23,148,[0],26,150,[2],"S0_AdamsE2_ss",3812⟩ (by
      exact List.mem_of_getElem? (i := 445) (by rfl))
    dsimp only [AdamsStatement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 3 (23,148) (26,150) x y at hd
    have vx : Raw.coordinatesValid Raw.degrees .sphere 23 148 [0] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 26 150 [2] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  have h446 : HasDifferential E 2 (23,148) (25,149)
      ((I.interpretation.basis .sphere 23 148 1)) ((I.interpretation.basis .sphere 25 149 2)) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,2,23,148,[1],25,149,[2],"S0_AdamsE2_ss",3813⟩ (by
      exact List.mem_of_getElem? (i := 446) (by rfl))
    dsimp only [AdamsStatement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (23,148) (25,149) x y at hd
    have vx : Raw.coordinatesValid Raw.degrees .sphere 23 148 [1] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 25 149 [2] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  have h453 : HasDifferential E 2 (24,149) (26,150)
      ((I.interpretation.basis .sphere 24 149 0)) ((I.interpretation.basis .sphere 26 150 1)) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,2,24,149,[0],26,150,[1],"S0_AdamsE2_ss",3896⟩ (by
      exact List.mem_of_getElem? (i := 453) (by rfl))
    dsimp only [AdamsStatement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (24,149) (26,150) x y at hd
    have vx : Raw.coordinatesValid Raw.degrees .sphere 24 149 [0] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 26 150 [1] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,23,148,["0,2,9,1,292,1", "0,9,449,1"]⟩ (by
    unfold Raw.degrees
    iterate 271 apply List.mem_cons_of_mem
    exact List.mem_cons_self)
  change E.Page 2 (23,148) ≃ₗ[ℤ] (Fin 2 →₀ F2) at e
  change ∀ i : Fin 2, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 23 148 i.val at he
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,24,149,["9,1,13,1,194,1"]⟩ (by
    unfold Raw.degrees
    iterate 276 apply List.mem_cons_of_mem
    exact List.mem_cons_self)
  change E.Page 2 (24,149) ≃ₗ[ℤ] (Fin 1 →₀ F2) at f
  change ∀ i : Fin 1, f.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 24 149 i.val at hf
  obtain ⟨g,hg⟩ := I.basis ⟨.sphere,26,150,["557,1", "8,1,13,4,23,1", "8,3,9,1,101,1", "0,1,17,1,260,1"]⟩ (by
    unfold Raw.degrees
    iterate 285 apply List.mem_cons_of_mem
    exact List.mem_cons_self)
  change E.Page 2 (26,150) ≃ₗ[ℤ] (Fin 4 →₀ F2) at g
  change ∀ i : Fin 4, g.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 26 150 i.val at hg
  obtain ⟨k,hk⟩ := I.basis ⟨.sphere,25,149,["17,1,260,1", "8,1,9,1,219,1", "0,11,440,1"]⟩ (by
    unfold Raw.degrees
    iterate 280 apply List.mem_cons_of_mem
    exact List.mem_cons_self)
  change E.Page 2 (25,149) ≃ₗ[ℤ] (Fin 3 →₀ F2) at k
  change ∀ i : Fin 3, k.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 25 149 i.val at hk
  have d20 : E.d 2 (23,148) (I.interpretation.basis .sphere 23 148 0) = 0 := by
    obtain ⟨_,x,y,hx,hy,hd⟩ := h445
    obtain ⟨x2,hx2⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide) hx
    rw [←hx2.eq_on_page_two] at hx2
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega)
      (by decide) hx2 ⟨_,hx⟩
  have d21 : E.d 2 (23,148) (I.interpretation.basis .sphere 23 148 1) =
      I.interpretation.basis .sphere 25 149 2 := h446.eq_on_page_two.2
  have df0 : E.d 2 (24,149) (I.interpretation.basis .sphere 24 149 0) =
      I.interpretation.basis .sphere 26 150 1 := h453.eq_on_page_two.2
  have incoming (x : E.Page 2 (24,149)) : g (E.d 2 (24,149) x) 2 = 0 := by
    have hall (a : Fin 1 →₀ F2) : g (E.d 2 (24,149) (f.symm a)) 2 = 0 := by
      induction a using Finsupp.induction with
      | zero => simp
      | @single_add i c a hi hci ih =>
        rw [map_add,map_add,map_add,Finsupp.add_apply,ih,add_zero]
        fin_cases c
        · simp
        · change g (E.d 2 (24,149) (f.symm (Finsupp.single i 1))) 2 = 0
          rw [hf i]
          fin_cases i
          rw [df0]
          rw [show I.interpretation.basis .sphere 26 150 1 = g.symm (Finsupp.single 1 1) from (hg 1).symm,LinearEquiv.apply_symm_apply]
          norm_num [Finsupp.single_apply,Fin.ext_iff]
    simpa only [LinearEquiv.symm_apply_apply] using hall (f x)
  obtain ⟨_,a,b,ha,hb,hd⟩ := h445
  have hd' : E.d 3 (23,148) a = b := hd
  have hbne : b ≠ 0 := by
    intro hb0
    obtain ⟨_,z,hx,hz⟩ := hb
    have hh := (next_projection_zero_iff_incoming E 2 (by change (2:ℤ)≤2; omega) (24,149) z).mp (hz.trans hb0)
    change (Subobject.ofLE _ _ ((E.ssData (26,150)).Z_anti bot_le) ≫
      (E.ssData (26,150)).pageπ 0) z ∈ LinearMap.range (E.d 2 (24,149)).hom at hh
    change (Subobject.ofLE _ _ ((E.ssData (26,150)).Z_anti bot_le) ≫
      (E.ssData (26,150)).pageπ 0) z = I.interpretation.basis .sphere 26 150 2 at hx
    rw [hx] at hh
    obtain ⟨u,hu⟩ := hh
    have hzero := incoming u
    rw [hu] at hzero
    rw [show I.interpretation.basis .sphere 26 150 2 = g.symm (Finsupp.single 2 1) from (hg 2).symm,LinearEquiv.apply_symm_apply] at hzero
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hzero
  have frame (q : E.Page 3 (23, 148)) : q=0 ∨ q=a := by
    let A := E.ssData (23, 148)
    haveI : Epi (A.pageπ 1) := inferInstanceAs (Epi (cokernel.π _))
    obtain ⟨z,hz⟩ := (ModuleCat.epi_iff_surjective (A.pageπ 1)).mp inferInstance q
    let x : E.Page 2 (23, 148) := (Subobject.ofLE _ _ (A.Z_anti bot_le) ≫ A.pageπ 0) z
    have hx : RepresentsOnPage E 3 (23, 148) x q := ⟨by decide,z,rfl,hz⟩
    have hc : E.d 2 (23, 148) x = 0 := by
      obtain ⟨z,hz⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤3) hx
      rw [←hz.eq_on_page_two] at hz
      exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide) hz ⟨q,hx⟩
    have heq : e x = Finsupp.single 0 (e x 0) + Finsupp.single 1 (e x 1) := by
      ext i
      fin_cases i <;> simp
    have hxe : x=e.symm (Finsupp.single 0 (e x 0) + Finsupp.single 1 (e x 1)) := by
      rw [←heq,LinearEquiv.symm_apply_apply]
    generalize h0 : e x 0 = c0 at hxe
    generalize h1 : e x 1 = c1 at hxe
    fin_cases c0 <;> fin_cases c1
    · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2)) at hxe
      simp only [Finsupp.single_zero,add_zero,map_zero] at hxe
      rw [hxe] at hx
      exact Or.inl (represents_unique hx (RepresentsOnPage.zero (by decide)))
    · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2)) at hxe
      simp only [Finsupp.single_zero,zero_add] at hxe
      rw [show e.symm (Finsupp.single 1 1) = I.interpretation.basis .sphere 23 148 1 from he 1] at hxe
      have hh := congrArg (fun y => k y 2) hc
      rw [hxe] at hh
      simp only [d21] at hh
      simp only [show I.interpretation.basis .sphere 25 149 2 = k.symm (Finsupp.single 2 1) from (hk 2).symm] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2)) at hxe
      simp only [Finsupp.single_zero,add_zero] at hxe
      rw [show e.symm (Finsupp.single 0 1) = I.interpretation.basis .sphere 23 148 0 from he 0] at hxe
      rw [hxe] at hx
      exact Or.inr (represents_unique hx (by simpa only [he] using ha))
    · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2)) at hxe
      simp only [map_add] at hxe
      rw [show e.symm (Finsupp.single 0 1) = I.interpretation.basis .sphere 23 148 0 from he 0] at hxe
      rw [show e.symm (Finsupp.single 1 1) = I.interpretation.basis .sphere 23 148 1 from he 1] at hxe
      have hh := congrArg (fun y => k y 2) hc
      rw [hxe] at hh
      simp only [map_add,d20,d21] at hh
      simp only [show I.interpretation.basis .sphere 25 149 2 = k.symm (Finsupp.single 2 1) from (hk 2).symm] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
  have hker (q : E.Page 3 (23,148)) (hq : E.d 3 (23,148) q=0) : q=0 := by
    rcases frame q with hh|hh
    · exact hh
    · exact (hbne (by simpa only [hh,hd'] using hq)).elim
  let S := E.pageShortComplex 3 ((23,148)-E.diffDeg 3)
  have hs : S.Exact := S.moduleCat_exact_iff.mpr (by
    intro x hx
    exact ⟨0,by rw [hker x hx,map_zero]⟩)
  exact ModuleCat.subsingleton_of_isZero ((pageHomologyIso E 3 (23,148)
    (by change (2:ℤ)≤3; omega)).isZero_iff.mpr ((S.exact_iff_isZero_homology).mp hs))

private theorem h125_page24 (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 6 (24,149)) := by
  classical
  let E := sequence D .sphere
  have h453 : HasDifferential E 2 (24,149) (26,150)
      (I.interpretation.basis .sphere 24 149 0) (I.interpretation.basis .sphere 26 150 1) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,2,24,149,[0],26,150,[1],"S0_AdamsE2_ss",3896⟩ (by
      exact List.mem_of_getElem? (i := 453) (by rfl))
    dsimp only [AdamsStatement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (24,149) (26,150) x y at hd
    have vx : Raw.coordinatesValid Raw.degrees .sphere 24 149 [0] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 26 150 [1] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    simpa only [add_assoc] using hd
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,24,149,["9,1,13,1,194,1"]⟩ (by
    unfold Raw.degrees
    iterate 276 apply List.mem_cons_of_mem
    exact List.mem_cons_self)
  change E.Page 2 (24,149) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e
  change ∀ i : Fin 1, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 24 149 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 1) 1) = I.interpretation.basis .sphere 24 149 0 := he 0
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,26,150,["557,1", "8,1,13,4,23,1", "8,3,9,1,101,1", "0,1,17,1,260,1"]⟩ (by
    unfold Raw.degrees
    iterate 285 apply List.mem_cons_of_mem
    exact List.mem_cons_self)
  change E.Page 2 (26,150) ≃ₗ[ℤ] (Fin 4 →₀ F2) at f
  change ∀ i : Fin 4, f.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 26 150 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 4) 1) = I.interpretation.basis .sphere 26 150 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 4) 1) = I.interpretation.basis .sphere 26 150 1 := hf 1
  have hf2 : f.symm (Finsupp.single (2:Fin 4) 1) = I.interpretation.basis .sphere 26 150 2 := hf 2
  have hf3 : f.symm (Finsupp.single (3:Fin 4) 1) = I.interpretation.basis .sphere 26 150 3 := hf 3
  have hd0 : E.d 2 (24,149) (I.interpretation.basis .sphere 24 149 0) =
      I.interpretation.basis .sphere 26 150 1 := h453.eq_on_page_two.2
  apply sixth_zero_of_second_kernel (E:=E) (by change (2:ℤ)≤2; omega) (24,149)
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
    exact RepresentsOnPage.zero (E:=E) (p:=(24,149)) (r:=6) (by decide)
  · change x = e.symm (Finsupp.single 0 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [he0, hd0] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_zero, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval

/-- The precise high-filtration elimination in pi_(125,130).
In AF15..24 the finite records and BHS weight130 formula leave no
associated grade. In particular the d5 source at AF15 is not a permanent
cycle, and the AF18 d5 target has lambda exponent13>=4. Boundary-lift
arguments may choose a lambda^4-torsion lift; arbitrary lifts can differ
by higher filtration, which this range calculation must retain and remove.
This is not a claim that every lift of that target is lambda^4-torsion. -/

private theorem stem125_sixth_pages_20_24 (I : AdamsComputationTheorems D L G)
    (s : ℕ) (hs : 20 ≤ s) (hs' : s ≤ 24) :
    Subsingleton ((sequence D .sphere).Page 6 (s,(s:ℤ)+125)) := by
  classical

  interval_cases s
  · exact h125_page20 I
  · exact h125_page21 I
  · exact h125_page22 I
  · exact h125_page23 I
  · exact h125_page24 I


-- In stem 125 and weight 130, filtrations 15 through 25 coincide.
set_option linter.unusedVariables false in
theorem stem125_weight130_filtration15_eq25
    (I : AdamsComputationTheorems D L G) (BHS : SyntheticComparisonTheorems D) (V : SphereVanishingLine H)
    (a : BiHom 125 130 (S_0_0 : Syn)) :
    FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 15 a ↔
      FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 25 a := by
  apply D.sphereConvergence.filtrationAtLeast_iff_of_eInfty_isZero
    15 25 125 130 (by omega) ?_ a
  intro j hj h25
  -- Remaining obligation: the BHS weight130 quotient is zero throughout
  -- this interval, including the d5 source and target discussed above.
  classical

  have permanentQuotient_zero_of_page_six_zero (s t b : ℤ) (hb : 5 ≤ b)
      (hpage : Subsingleton ((sequence D .sphere).Page 6 (s, t))) :
      Subsingleton (PageRepresentatives.PermanentQuotient H SphereSpectrum b (s, t)) := by
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
          dsimp only [PageRepresentatives.cycleMap, PageRepresentatives.boundaryMap, E, sequence, object]
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

  have hfinite : ∀ s : ℕ, 15 ≤ s → s ≤ 24 → Subsingleton ((sequence D .sphere).Page 6 (s,(s:ℤ)+125)) := by
    intro s hs hs'
    by_cases h : s ≤ 19
    · exact stem125_sixth_pages_15_19 I s hs h
    · exact stem125_sixth_pages_20_24 I s (by omega) hs'

  set_option backward.isDefEq.respectTransparency false in
    have hpage : Subsingleton ((sequence D .sphere).Page 6 (j,125+j)) := by
      have h := hfinite j.toNat (by omega) (by omega)
      simpa only [Int.toNat_of_nonneg (show 0≤j by omega),add_comm] using h
    haveI : Subsingleton (PageRepresentatives.PermanentQuotient H SphereSpectrum
        (1+(125+j)-130) (j,125+j)) :=
      permanentQuotient_zero_of_page_six_zero j (125+j) _ (by omega) hpage
    let e := BHS.eInfty.presentation.nuWindow SphereSpectrum (j,125+j) 130 (by omega)
    haveI : Subsingleton (((D.family.nu D.nu SphereSpectrum).sequence.ssData (j,125+j,130)).eInfty) := e.injective.subsingleton
    let hnu := ModuleCat.isZero_of_subsingleton
      (((D.family.nu D.nu SphereSpectrum).sequence.ssData (j,125+j,130)).eInfty)
    let f := (D.family.functor.map D.nu.unitIso.hom).eInftyMap (j,125+j,130)
    let g := (D.family.functor.map D.nu.unitIso.inv).eInftyMap (j,125+j,130)
    have hfg : g ≫ f = 𝟙 _ := by
      dsimp only [f,g]
      rw [←SpectralSequenceMorphism.eInftyMap_comp,←Functor.map_comp,Iso.inv_hom_id,
        CategoryTheory.Functor.map_id,SpectralSequenceMorphism.eInftyMap_id]
    apply (CategoryTheory.Limits.IsZero.iff_id_eq_zero _).mpr
    exact hfg.symm.trans (by rw [hnu.eq_of_src f 0,CategoryTheory.Limits.comp_zero])
end

/-- Transport BHS filtration/lambda divisibility from nu(S) along the
specified D.nu.unitIso. The exponent is 125+15-130=10 and the lift has
weight140. The comparison concerns the untruncated sphere only. -/
theorem stem125_weight130_filtration15_iff_lambda10
    (BHS : SyntheticComparisonTheorems D) (a : BiHom 125 130 (S_0_0 : Syn)) :
    FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 15 a ↔
      ∃ b : BiHom 125 140 (S_0_0 : Syn), lambdaMultiply 10 b = a := by
  set_option backward.isDefEq.respectTransparency false in
    have hmap {X Y : Syn} (f : X ⟶ Y) {m w s : ℤ} (x : BiHom m w X)
        (hx : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) s x) :
        FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) s (x ≫ f) := by
      obtain ⟨z, hz⟩ := hx
      refine ⟨z ≫ adamsTowerInduced (nuCoefficientUnit H.unit D.nu) f s.toNat, ?_⟩
      change (z ≫ adamsTowerInduced (nuCoefficientUnit H.unit D.nu) f s.toNat) ≫
        adamsTowerMap (nuCoefficientUnit H.unit D.nu) Y 0 s.toNat _ = x ≫ f
      change z ≫ adamsTowerMap (nuCoefficientUnit H.unit D.nu) X 0 s.toNat _ = x at hz
      rw [Category.assoc, adamsTowerInduced_map, ← Category.assoc, hz]
      rfl
    have h := BHS.filtration_lambda .sphere 125 130 15 (by omega)
      (a ≫ D.nu.unitIso.inv)
    change FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 15 (a ≫ D.nu.unitIso.inv) ↔
      ∃ b : BiHom 125 140 (D.nu.functor.obj SphereSpectrum),
        lambdaMultiply 10 b = a ≫ D.nu.unitIso.inv at h
    constructor
    · intro ha
      obtain ⟨b, hb⟩ := h.mp (hmap D.nu.unitIso.inv a ha)
      refine ⟨b ≫ D.nu.unitIso.hom, ?_⟩
      simpa [lambdaMultiply, Category.assoc] using
        congrArg (fun x => x ≫ D.nu.unitIso.hom) hb
    · rintro ⟨b, hb⟩
      have ha := h.mpr ⟨b ≫ D.nu.unitIso.inv, by
        simpa only [lambdaMultiply, Category.assoc] using
          congrArg (fun x => x ≫ D.nu.unitIso.inv) hb⟩
      have ha' := hmap D.nu.unitIso.hom (a ≫ D.nu.unitIso.inv) ha
      simpa [Category.assoc] using ha'

/-- All first-quotient G lifts have the same lambda^20 image in weight130.
Their difference is retained as a higher-filtration error, then killed by
`stem125_weight130_filtration26_zero`. This is representative independence
at weight130, not uniqueness of the lifts in weight150. -/
theorem high125_lift_unique_at_weight130
    (I : AdamsComputationTheorems D L G) (BHS : SyntheticComparisonTheorems D) (V : SphereVanishingLine H)
    (b b' : BiHom 125 150 (S_0_0 : Syn))
    (hb : D.sphereFirstQuotient 25 150 (quotientClass 1 b) =
      I.interpretation.sphere 25 150 highClass)
    (hb' : D.sphereFirstQuotient 25 150 (quotientClass 1 b') =
      I.interpretation.sphere 25 150 highClass) :
    lambdaMultiply 20 b = lambdaMultiply 20 b' := by
  have h := D.comparisonCompatible.homotopy_lambda 25 150 20 b
  have h' := D.comparisonCompatible.homotopy_lambda 25 150 20 b'
  rw [hb] at h
  rw [hb'] at h'
  have hsub := detects_sub_filtration D.sphereConvergence (25, 150, 130) h h'
  exact sub_eq_zero.mp (stem125_weight130_filtration26_zero I BHS V
    (lambdaMultiply 20 b - lambdaMultiply 20 b') hsub)

private theorem high125_nu_first_quotient (I : AdamsComputationTheorems D L G)
    (b : BiHom 125 150 (S_0_0 : Syn))
    (hb : D.sphereFirstQuotient 25 150 (quotientClass 1 b) =
      I.interpretation.sphere 25 150 highClass) :
    quotientClass 1 (b ≫ D.nu.unitIso.inv ≫ SyntheticCategory.biShift_zero.inv.app _) =
      firstLabel D .sphere 25 150 (G.high125 M) := by
  set_option backward.isDefEq.respectTransparency false in
    apply (D.firstQuotient SphereSpectrum 0 25 150).injective
    change (D.firstQuotient SphereSpectrum 0 25 150)
        (quotientClass 1 (b ≫ D.nu.unitIso.inv ≫ SyntheticCategory.biShift_zero.inv.app _)) =
      (D.firstQuotient SphereSpectrum 0 25 150)
        ((D.firstQuotient SphereSpectrum 0 25 150).symm (G.high125 M))
    rw [AddEquiv.apply_symm_apply, ← high125_label I, ← hb]
    change (D.firstQuotient SphereSpectrum 0 25 150) _ =
      (D.firstQuotient SphereSpectrum 0 25 150)
        (quotientClass 1 b ≫ XModLambdaN.map
          (D.nu.unitIso.inv ≫ SyntheticCategory.biShift_zero.inv.app _) 1)
    apply congrArg (D.firstQuotient SphereSpectrum 0 25 150)
    simp only [quotientClass, Category.assoc, XModLambdaN.incl_naturality,
      D.quotientFunctoriality.map_comp]

/-- The word lambda-free is expressed by every actual finite power, not
just nonvanishing at weight130. BHS lifetime applies to the permanent G
label and every chosen first-quotient lift; the same sphere/nu unit
comparison transports the result to b. -/
theorem high125_lift_lambda_powers_nonzero
    (I : AdamsComputationTheorems D L G) (R : RealizationDetectionData D)
    (hhigh : NonzeroSurvival (sequence D .sphere) (25,150) (G.high125 M))
    (b : BiHom 125 150 (S_0_0 : Syn))
    (hb : D.sphereFirstQuotient 25 150 (quotientClass 1 b) =
      I.interpretation.sphere 25 150 highClass) :
    ∀ k : ℕ, lambdaMultiply k b ≠ 0 := by
  set_option backward.isDefEq.respectTransparency false in
    let b₀ : BiHom 125 150 (nuZero D .sphere) :=
      b ≫ D.nu.unitIso.inv ≫ SyntheticCategory.biShift_zero.inv.app _
    have hb₀ := high125_nu_first_quotient I b hb
    obtain ⟨z, hz, hnz⟩ := hhigh
    have hpermanent : G.high125 M ∈ PageRepresentatives.permanentCycles
        H SphereSpectrum (25, 150) := ⟨z, hz⟩
    intro k
    let E := (sequence D .sphere).ssData (25, 150)
    let n : WithTop ℕ := ↑(((k : ℤ) + 2 - 2).toNat)
    let zf := (Subobject.ofLE (E.Z ⊤) (E.Z n) (E.Z_anti le_top)) z
    have hsurvives : SurvivesTo (sequence D .sphere) ((k : ℤ) + 2) (25, 150)
        (G.high125 M) := by
      have hrep : RepresentsOnPage (sequence D .sphere) ((k : ℤ) + 2) (25, 150)
          (G.high125 M) (E.pageπ n zf) := by
        refine ⟨by omega, ?_⟩
        change ∃ y : (Subobject.underlying.obj (E.Z n) : ModuleCat ℤ),
          (Subobject.ofLE (E.Z n) (E.Z 0) (E.Z_anti bot_le) ≫ E.pageπ 0) y = G.high125 M ∧
            E.pageπ n y = E.pageπ n zf
        refine ⟨zf, ?_, rfl⟩
        dsimp only [zf]
        rw [← CategoryTheory.comp_apply, ← Category.assoc, Subobject.ofLE_comp_ofLE]
        exact hz
      refine ⟨E.pageπ n zf, hrep, ?_⟩
      intro hzero
      change E.pageπ n zf = 0 at hzero
      have hproj := E.infinity_projection_eq_of_page_projection_eq n z 0
        (by change E.pageπ n zf = _; simpa only [map_zero] using hzero)
      exact hnz (by simpa only [map_zero] using hproj)
    have hlife := R.detection.lifetime .sphere 25 150 (k + 1) (by omega)
      (G.high125 M) b₀ hpermanent (by simpa only [Nat.cast_add, Nat.cast_one,
        add_assoc, one_add_one_eq_two, sequence, object, ClassicalObject.obj] using hsurvives) hb₀
    change lambdaMultiply (k + 1 - 1) b₀ ≠ 0 at hlife
    have hk : k + 1 - 1 = k := by omega
    rw [hk] at hlife
    intro hzero
    apply hlife
    dsimp only [b₀]
    have h := congrArg (fun x => x ≫ D.nu.unitIso.inv ≫
      SyntheticCategory.biShift_zero.inv.app _) hzero
    simpa only [lambdaMultiply, Category.assoc, CategoryTheory.Limits.zero_comp] using h

/-- The two-element filtration subgroup used in Proposition 7.8.
The first-quotient comparison identifies the lift of G with the specified
E₂ class, and its λ²⁰ multiple spans F¹⁵. The nonzero permanence of G is
proved by `high125_nonzero_survival_of_computation`. -/
theorem high125_weight130_exhaustion
    (I : AdamsComputationTheorems D L G) (BHS : SyntheticComparisonTheorems D) (R : RealizationDetectionData D)
    (V : SphereVanishingLine H)
    (hhigh : NonzeroSurvival (sequence D .sphere) (25,150) (G.high125 M)) :
    ∃ b : BiHom 125 150 (S_0_0 : Syn),
      D.sphereFirstQuotient 25 150 (quotientClass 1 b) =
        I.interpretation.sphere 25 150 highClass ∧
      lambdaMultiply 20 b ≠ 0 ∧
      ∀ a : BiHom 125 130 (S_0_0 : Syn),
        FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 15 a ↔
          a = 0 ∨ a = lambdaMultiply 20 b := by
  set_option backward.isDefEq.respectTransparency false in
    have hhigh' := hhigh
    obtain ⟨zg, hzg, _⟩ := hhigh'
    have hp : G.high125 M ∈ PageRepresentatives.permanentCycles H SphereSpectrum (25,150) :=
      ⟨zg, hzg⟩
    obtain ⟨b₀, hb₀⟩ := (BHS.permanent_lift .sphere 25 150 (G.high125 M)).mp hp
    let b : BiHom 125 150 (S_0_0 : Syn) :=
      b₀ ≫ SyntheticCategory.biShift_zero.hom.app _ ≫ D.nu.unitIso.hom
    have hb : D.sphereFirstQuotient 25 150 (quotientClass 1 b) =
        I.interpretation.sphere 25 150 highClass := by
      rw [high125_label I]
      have heq : quotientClass 1 b ≫ XModLambdaN.map
          (D.nu.unitIso.inv ≫ SyntheticCategory.biShift_zero.inv.app _) 1 =
          quotientClass 1 b₀ := by
        have hc : b ≫ (D.nu.unitIso.inv ≫ SyntheticCategory.biShift_zero.inv.app _) = b₀ := by
          simp only [b, ClassicalObject.obj, Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id_app,
            Functor.id_obj]
          exact Category.comp_id b₀
        calc
          _ = quotientClass 1 (b ≫ (D.nu.unitIso.inv ≫ SyntheticCategory.biShift_zero.inv.app _)) := by
            dsimp only [quotientClass]
            rw [Category.assoc, ← XModLambdaN.incl_naturality, ← Category.assoc]
          _ = _ := congrArg (quotientClass 1) hc
      change (D.firstQuotient SphereSpectrum 0 25 150)
        (quotientClass 1 b ≫ XModLambdaN.map
          (D.nu.unitIso.inv ≫ SyntheticCategory.biShift_zero.inv.app _) 1) = _
      rw [heq, hb₀]
      exact (D.firstQuotient SphereSpectrum 0 25 150).apply_symm_apply (G.high125 M)
    have hn : lambdaMultiply 20 b ≠ 0 := high125_lift_lambda_powers_nonzero I R hhigh b hb 20
    let E := (sequence D .sphere).ssData (25, 150)
    let Z := PageRepresentatives.permanentCycles H SphereSpectrum (25, 150)
    let B := PageRepresentatives.boundaries H SphereSpectrum 21 (25, 150)
    let proj := KIP126.Algebra.NestedQuotient.projection Z B
    let pg : Z := ⟨G.high125 M, hp⟩
    obtain ⟨yg, hrep, _, hex⟩ := high125_component I
    obtain ⟨_, w, hw, hwy⟩ := hrep
    change (Subobject.underlying.obj (E.Z 3) : ModuleCat ℤ) at w
    rw [high125_label I] at hw
    change E.page 3 at yg
    change E.pageπ 3 w = yg at hwy
    change (Subobject.ofLE (E.Z 3) (E.Z 0) (E.Z_anti bot_le) ≫ E.pageπ 0) w = G.high125 M at hw
    have hboundary (y : (Subobject.underlying.obj (E.Z 3) : ModuleCat ℤ))
        (hy : E.pageπ 3 y = 0) :
        (Subobject.ofLE (E.Z 3) (E.Z 0) (E.Z_anti bot_le) ≫ E.pageπ 0) y ∈ B := by
      obtain ⟨v, hv⟩ := (cokernel_π_eq_zero_iff_mem_range
        (Subobject.ofLE (E.B 3) (E.Z 3) (E.B_le_Z 3)) y).mp hy
      apply PageRepresentatives.boundaries_monotone H SphereSpectrum (25, 150) (by decide : (4 : ℤ) ≤ 21)
      refine ⟨v, ?_⟩
      change (Subobject.ofLE (E.B 3) (E.Z 0) _ ≫ E.pageπ 0) v = _
      have hf : Subobject.ofLE (E.B 3) (E.Z 3) (E.B_le_Z 3) ≫
          Subobject.ofLE (E.Z 3) (E.Z 0) (E.Z_anti bot_le) =
          Subobject.ofLE (E.B 3) (E.Z 0) ((E.B_le_Z 3).trans (E.Z_anti bot_le)) := by
        rw [Subobject.ofLE_comp_ofLE]
      rw [← hf, Category.assoc]
      exact congrArg (fun q => (Subobject.ofLE (E.Z 3) (E.Z 0) (E.Z_anti bot_le) ≫ E.pageπ 0) q) hv
    have hq : ∀ x : KIP126.Algebra.NestedQuotient.Space Z B, x = 0 ∨ x = proj pg := by
      rintro ⟨x⟩
      obtain ⟨z, hz⟩ := x.property
      let zf := (Subobject.ofLE (E.Z ⊤) (E.Z 3) (E.Z_anti le_top)) z
      have hlabel : (Subobject.ofLE (E.Z 3) (E.Z 0) (E.Z_anti bot_le) ≫ E.pageπ 0) zf = x.val := by
        dsimp only [zf]
        rw [← CategoryTheory.comp_apply, ← Category.assoc, Subobject.ofLE_comp_ofLE]
        exact hz
      change proj x = 0 ∨ proj x = proj pg
      obtain hx | hx := hex (E.pageπ 3 zf)
      · left
        apply (KIP126.Algebra.NestedQuotient.projection_eq_zero x).mpr
        exact hlabel ▸ hboundary zf hx
      · right
        apply sub_eq_zero.mp
        rw [← map_sub]
        apply (KIP126.Algebra.NestedQuotient.projection_eq_zero (x-pg)).mpr
        have hzero : E.pageπ 3 (zf - w) = 0 := by
          rw [map_sub, hx, hwy, sub_self]
        have hd := hboundary (zf - w) hzero
        change x.val - G.high125 M ∈ B
        simpa only [map_sub, hlabel, hw] using hd
    let enu := BHS.eInfty.presentation.nuWindow SphereSpectrum (25, 150) 130 (by decide)
    let f := (D.family.functor.map D.nu.unitIso.hom).eInftyMap (25, 150, 130)
    let g := (D.family.functor.map D.nu.unitIso.inv).eInftyMap (25, 150, 130)
    have hfg : g ≫ f = 𝟙 _ := by
      dsimp only [f, g]
      rw [← SpectralSequenceMorphism.eInftyMap_comp, ← Functor.map_comp, Iso.inv_hom_id,
        CategoryTheory.Functor.map_id, SpectralSequenceMorphism.eInftyMap_id]
    have hg : Function.Injective g := by
      intro x y hxy
      have h := congrArg f hxy
      simpa only [← CategoryTheory.comp_apply, hfg, ModuleCat.id_apply] using h
    let qmap := enu.toLinearMap.comp g.hom
    have hqi : Function.Injective qmap := enu.injective.comp hg
    have htwo (x y : ((D.family.sphere).sequence.ssData (25, 150, 130)).eInfty) :
        x = 0 ∨ y = 0 ∨ x = y := by
      obtain hx | hx := hq (qmap x)
      · exact Or.inl (hqi (by simpa only [map_zero] using hx))
      obtain hy | hy := hq (qmap y)
      · exact Or.inr (Or.inl (hqi (by simpa only [map_zero] using hy)))
      · exact Or.inr (Or.inr (hqi (hx.trans hy.symm)))
    let F := towerFiltration (nuCoefficientUnit H.unit D.nu) (S_0_0 : Syn)
    have hzero (x : (Subobject.underlying.obj (F.F 25 (125, 130)) : ModuleCat ℤ))
        (hx : F.toAssociatedGraded 25 (125, 130) x = 0) : (F.F 25 (125, 130)).arrow x = 0 := by
      have hmem := (subobject_cokernel_π_eq_zero_iff (F.F 26 (125, 130))
        (F.F 25 (125, 130)) (F.mono 25 (125, 130)) x).mp hx
      apply stem125_weight130_filtration26_zero I BHS V _
      simpa only [F, towerFiltration, OrderIso.apply_symm_apply, FiltrationAtLeast] using hmem
    have hgen : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 25 (lambdaMultiply 20 b) := by
      obtain ⟨_, _, a, ha, _⟩ := D.comparisonCompatible.homotopy_lambda 25 150 20 b
      change _ ∈ towerFiltrationSubmodule (nuCoefficientUnit H.unit D.nu) S_0_0 25 (125,130)
      have hmem : _ ∈ (ModuleCat.subobjectModule _)
          ((towerFiltration (nuCoefficientUnit H.unit D.nu) S_0_0).F 25 (125,130)) := ⟨a, ha⟩
      simpa only [towerFiltration, OrderIso.apply_symm_apply] using hmem
    have hmember (a : BiHom 125 130 (S_0_0 : Syn))
        (ha : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 25 a) :
        ∃ x : (Subobject.underlying.obj (F.F 25 (125, 130)) : ModuleCat ℤ),
          (F.F 25 (125, 130)).arrow x = a := by
      change a ∈ (ModuleCat.subobjectModule _) (F.F 25 (125,130))
      simpa only [F, towerFiltration, OrderIso.apply_symm_apply, FiltrationAtLeast] using ha
    obtain ⟨bg, hbg⟩ := hmember _ hgen
    refine ⟨b, hb, hn, fun a => ?_⟩
    constructor
    · intro ha
      obtain ⟨x, hx⟩ := hmember a ((stem125_weight130_filtration15_eq25 I BHS V a).mp ha)
      let e := D.sphereConvergence.identification (25,150,130)
      have hcases := htwo (e.inv (F.toAssociatedGraded 25 (125,130) x))
        (e.inv (F.toAssociatedGraded 25 (125,130) bg))
      rcases hcases with h | h | h
      · left
        rw [← hx]
        apply hzero
        exact e.toLinearEquiv.symm.map_eq_zero_iff.mp h
      · exact (hn (hbg ▸ hzero bg (e.toLinearEquiv.symm.map_eq_zero_iff.mp h))).elim
      · right
        apply sub_eq_zero.mp
        have h' : F.toAssociatedGraded 25 (125,130) (x-bg) = 0 := by
          rw [map_sub, e.toLinearEquiv.symm.injective h, sub_self]
        have h'' := hzero (x-bg) h'
        simpa only [map_sub, hx, hbg] using h''
    · rintro (rfl | rfl)
      · exact (towerFiltrationSubmodule _ _ _ _).zero_mem
      · exact (stem125_weight130_filtration15_eq25 I BHS V _).mpr hgen

/-- The same exhaustion with every numerical and source premise exposed.
The source tmf product gives one nonzero classical image; the earlier
Main theorem obtains G's nonzero permanence using C, V, classical
separation and multiplicative detection. Thus the hhigh premise above is
produced without the Proposition7.8 exhaustion being assumed in A or C. -/
theorem high125_weight130_exhaustion_of_source
    (I : AdamsComputationTheorems D L G) (BHS : SyntheticComparisonTheorems D) (R : RealizationDetectionData D)
    (V : SphereVanishingLine H) (S : ClassicalSphereSeparated H)
    (source : TmfDetectionData H) (hsource : TmfSourceResults source)
    (comparison : TmfDetectorComparison D G source) (multiplicative : ClassicalProductDetection D) :
    ∃ b : BiHom 125 150 (S_0_0 : Syn),
      D.sphereFirstQuotient 25 150 (quotientClass 1 b) =
        I.interpretation.sphere 25 150 highClass ∧
      lambdaMultiply 20 b ≠ 0 ∧
      ∀ a : BiHom 125 130 (S_0_0 : Syn),
        FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 15 a ↔
          a = 0 ∨ a = lambdaMultiply 20 b := by
  exact high125_weight130_exhaustion I BHS R V
    (KIP126.Main.Computation.high125_nonzero_survival_of_computation
      D I V S source hsource comparison multiplicative)

/-- Every nonzero high-filtration class has the specified classical G
detector after the SAME realization. This is the input to the tmf
detection argument. The source sphere is transported to nu(S) by the
existing unit iso; no new realization or detected representative is chosen. -/
theorem high125_weight130_nonzero_classical_detection
    (I : AdamsComputationTheorems D L G) (BHS : SyntheticComparisonTheorems D) (R : RealizationDetectionData D)
    (V : SphereVanishingLine H)
    (hhigh : NonzeroSurvival (sequence D .sphere) (25,150) (G.high125 M))
    (a : BiHom 125 130 (S_0_0 : Syn))
    (ha : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 15 a) (hne : a ≠ 0) :
    TowerDetection.Detects (D.classicalConvergence .sphere) (25,150)
      (G.high125 M) (realizeNu D R.coordinates .sphere (a ≫ D.nu.unitIso.inv)) := by
  set_option backward.isDefEq.respectTransparency false in
    obtain ⟨b, hb, _, hexhaust⟩ := high125_weight130_exhaustion I BHS R V hhigh
    obtain hzero | rfl := (hexhaust a).mp ha
    · exact (hne hzero).elim
    · let b₀ : BiHom 125 150 (nuZero D .sphere) :=
        b ≫ D.nu.unitIso.inv ≫ SyntheticCategory.biShift_zero.inv.app _
      have hd := R.detection.detection .sphere 25 150 (G.high125 M) b₀ hhigh
        (high125_nu_first_quotient I b hb)
      have hzero : realizeNuZero D R.coordinates .sphere b₀ =
          realizeNu D R.coordinates .sphere (b ≫ D.nu.unitIso.inv) := by
        simp only [realizeNuZero, b₀, ClassicalObject.obj, Category.assoc, Iso.inv_hom_id_app,
          Functor.id_obj, Category.comp_id]
      have hlambda : lambdaMultiply 20 b ≫ D.nu.unitIso.inv =
          lambdaMultiply 20 (𝟙 (Smn (Syn := Syn) 125 150)) ≫
            (b ≫ D.nu.unitIso.inv) := by
        simp only [lambdaMultiply, Category.assoc, Category.id_comp]
      have hreal : realizeNu D R.coordinates .sphere
          (lambdaMultiply 20 b ≫ D.nu.unitIso.inv) =
          realizeNu D R.coordinates .sphere (b ≫ D.nu.unitIso.inv) := by
        rw [hlambda]
        simp only [realizeNu, Functor.map_comp, ← Category.assoc, R.coordinates.lambda]
      rw [hreal]
      rw [hzero] at hd
      exact hd

/-- Equivalent lambda-divisibility form of the same full subgroup statement.
The lambda^10 source has weight140; the distinguished lambda^20 generator
has weight150 before multiplication. No ambiguous lambda-free label or
classical E5 vanishing is substituted for these actual maps. -/
theorem high125_weight130_lambda10_exhaustion
    (I : AdamsComputationTheorems D L G) (BHS : SyntheticComparisonTheorems D) (R : RealizationDetectionData D)
    (V : SphereVanishingLine H)
    (hhigh : NonzeroSurvival (sequence D .sphere) (25,150) (G.high125 M)) :
    ∃ b : BiHom 125 150 (S_0_0 : Syn),
      D.sphereFirstQuotient 25 150 (quotientClass 1 b) =
        I.interpretation.sphere 25 150 highClass ∧
      lambdaMultiply 20 b ≠ 0 ∧
      ∀ a : BiHom 125 130 (S_0_0 : Syn),
        (∃ c : BiHom 125 140 (S_0_0 : Syn), lambdaMultiply 10 c = a) ↔
          a = 0 ∨ a = lambdaMultiply 20 b := by
  obtain ⟨b, hb, hn, hexhaust⟩ := high125_weight130_exhaustion I BHS R V hhigh
  exact ⟨b, hb, hn, fun a =>
    (stem125_weight130_filtration15_iff_lambda10 BHS a).symm.trans (hexhaust a)⟩

end
end KIP126.Computation.SphereAndCofiber
