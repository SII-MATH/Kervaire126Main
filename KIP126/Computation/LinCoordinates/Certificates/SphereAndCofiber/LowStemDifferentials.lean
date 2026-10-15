module

public import KIP126.Computation.LinCoordinates.Certificates.SphereAndCofiber
public import KIP126.Def.ClassicalAdams.SphereVanishing.Proofs
public import KIP126.Def.SpectralSequence.Basic.PageHomology.Data

/-! Finite low-stem differential certificates used in the Section 7 λ arguments. -/

@[expose] public section

namespace KIP126.Computation.SphereAndCofiber
open CategoryTheory
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology KIP126.Classical.Adams
open KIP126.SpectralSequence KIP126.Synthetic.Context KIP126.AdamsSynthetic
open KIP126.Synthetic.SpectralSequence
universe u v w
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H}
  {D : AdamsComparison H M Syn} {L : SphereAdamsClasses H} {G : KIP126.Literature.AdamsSynthetic.TmfDetectionClasses H}
  {η : BiHom 1 2 (S_0_0 : Syn)}

/-- Filtration zero vanishes by the existing Eilenberg--Mac Lane sphere
calculation, and negative filtration vanishes in the actual tower. This
half-plane does not require a computation input. -/
theorem no_outgoing_stem63_nonpositive
    (q : ℤ) (hq : q ≤ 0) : NoOutgoingAt (sequence D .sphere) q (q+63) := by
  intro r _ x
  have hzero : Subsingleton ((sequence D .sphere).Page r (q, q+63)) := by
    by_cases hq0 : q = 0
    · subst q
      exact sphereAdamsInternal_filtration_zero_subsingleton H r 63 (by decide)
    · exact adamsTowerInternal_page_subsingleton_of_negative H.unit SphereSpectrum
        r q (q+63) (by omega)
  rw [hzero.elim x 0, map_zero]

/-- E2 is empty at stem125, AF0..4; negative AF is zero. This covers
weights <=130 in synthetic stem124, hence all iterates starting at 128. -/
theorem no_outgoing_stem125_low (I : AdamsComputationTheorems D L G)
    (q : ℤ) (hq : q ≤ 4) : NoOutgoingAt (sequence D .sphere) q (q+125) := by
  set_option maxRecDepth 10000 in
    intro r hr x
    have hz : Subsingleton ((sequence D .sphere).Page r (q,q+125)) := by
      by_cases hneg : q < 0
      · exact adamsTowerInternal_page_subsingleton_of_negative H.unit SphereSpectrum r q (q+125) hneg
      · have hq0 : 0 ≤ q := by omega
        have hd : (⟨.sphere, q.toNat, (q+125).toNat, []⟩ : Raw.Degree) ∈ Raw.degrees := by
          interval_cases q <;> simp [Raw.degrees]
        obtain ⟨e, _⟩ := I.basis _ hd
        change Page D .sphere q.toNat (q+125).toNat ≃ₗ[ℤ]
          (Fin 0 →₀ KIP126.Algebra.F2) at e
        have he : Subsingleton (Page D .sphere q.toNat (q+125).toNat) :=
          e.injective.subsingleton
        apply adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum 2 r q (q+125) (by omega) hr
        simpa only [Page, sequence, object, ClassicalObject.obj, Int.toNat_of_nonneg hq0, Int.toNat_of_nonneg (by omega : 0 ≤ q+125),
          Int.toNat_of_nonneg] using he
    rw [hz.elim x 0, map_zero]

open CategoryTheory.Limits in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
set_option maxRecDepth 10000 in
/-- The complete stem-63 bases in filtrations 1 through 6 leave only
permanent classes after d₂; nonpositive filtrations vanish. -/
theorem stem63_no_late_differentials (I : AdamsComputationTheorems D L G) (V : SphereVanishingLine H)
    (q : ℤ) (hq : q≤6) (r : ℤ) (hr : 3≤r)
    (a : (sequence D .sphere).Page r (q,q+63)) :
    (sequence D .sphere).d r (q,q+63) a=0 := by
  have represents_unique {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)}
        {r : ℤ} {p : ℤ × ℤ} {x : E.Page 2 p} {a b : E.Page r p}
      (ha : RepresentsOnPage E r p x a) (hb : RepresentsOnPage E r p x b) : a = b := by
    obtain ⟨hr, z, hz, hza⟩ := ha
    obtain ⟨_, z', hz', hzb⟩ := hb
    let D := E.ssData p
    let n : WithTop ℕ := ↑(2 - E.r₀).toNat
    let m : WithTop ℕ := ↑(r - E.r₀).toNat
    have hnm : n ≤ m := by
      dsimp only [n, m]
      exact_mod_cast (show (2-E.r₀).toNat ≤ (r-E.r₀).toNat by omega)
    apply sub_eq_zero.mp
    rw [← hza, ← hzb, ← map_sub]
    apply (subobject_cokernel_π_eq_zero_iff (D.B m) (D.Z m) (D.B_le_Z m) _).mpr
    have heq : D.pageπ n ((Subobject.ofLE _ _ (D.Z_anti hnm)) (z-z')) = 0 := by
      change (Subobject.ofLE _ _ (D.Z_anti hnm) ≫ D.pageπ n) (z-z') = 0
      rw [map_sub, hz, hz', sub_self]
    have hh := (subobject_cokernel_π_eq_zero_iff (D.B n) (D.Z n) (D.B_le_Z n) _).mp heq
    have he : (D.Z n).arrow ((Subobject.ofLE _ _ (D.Z_anti hnm)) (z-z')) =
        (D.Z m).arrow (z-z') := ConcreteCategory.congr_hom (Subobject.ofLE_arrow (D.Z_anti hnm)) _
    rw [he] at hh
    exact (ModuleCat.subobjectModule D.V).monotone (D.B_mono hnm) hh
  have represents_d_zero_of_later {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)}
        {r : ℤ} {p : ℤ × ℤ} {x : E.Page 2 p} {t : ℤ} (hr0 : E.r₀ ≤ r) (hrt : r < t)
      {a : E.Page r p} (ha : RepresentsOnPage E r p x a)
      (ht : ReachesPage E t p x) : E.d r p a = 0 := by
    obtain ⟨b, ht2, z, hz, _⟩ := ht
    let D := E.ssData p
    let nt : WithTop ℕ := ↑(t-E.r₀).toNat
    let nr : WithTop ℕ := ↑(r-E.r₀).toNat
    let ns : WithTop ℕ := ↑((r-E.r₀).toNat+1)
    have hrs : nr ≤ ns := by
      dsimp only [nr, ns]
      exact_mod_cast (show (r-E.r₀).toNat ≤ (r-E.r₀).toNat+1 by omega)
    have hst : ns ≤ nt := by
      dsimp only [ns, nt]
      exact_mod_cast (show (r-E.r₀).toNat+1 ≤ (t-E.r₀).toNat by omega)
    let zr := (Subobject.ofLE (D.Z nt) (D.Z nr) (D.Z_anti (hrs.trans hst))) z
    have hrep : RepresentsOnPage E r p x (D.pageπ nr zr) := by
      refine ⟨ha.1, zr, ?_, rfl⟩
      dsimp only [zr]
      rw [← CategoryTheory.comp_apply, ← Category.assoc, Subobject.ofLE_comp_ofLE]
      exact hz
    rw [represents_unique ha hrep]
    change D.pageπ nr zr ∈ LinearMap.ker (E.d r p).hom
    rw [← subobjectModule_kernel, E.Z_succ r p hr0, subobjectModule_image]
    refine ⟨(Subobject.ofLE (D.Z nt) (D.Z ns) (D.Z_anti hst)) z, ?_⟩
    change (Subobject.ofLE (D.Z ns) (D.Z nr) (D.Z_anti hrs) ≫ D.pageπ nr)
      ((Subobject.ofLE (D.Z nt) (D.Z ns) (D.Z_anti hst)) z) = D.pageπ nr zr
    rw [← CategoryTheory.comp_apply, ← Category.assoc, Subobject.ofLE_comp_ofLE]
    rfl
  have permanent_reaches {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ×ℤ)}
      {p : ℤ×ℤ} {x : E.Page 2 p} (hx : IsPermanentCycle E p x)
      (r : ℤ) (hr : 2≤r) : ReachesPage E r p x := by
    obtain ⟨z,hz⟩ := hx
    let A := E.ssData p
    let zr := (Subobject.ofLE (A.Z ⊤) (A.Z ↑(r-E.r₀).toNat) (A.Z_anti le_top)) z
    refine ⟨A.pageπ _ zr,hr,zr,?_,rfl⟩
    dsimp only [zr]
    rw [← CategoryTheory.comp_apply,← Category.assoc,Subobject.ofLE_comp_ofLE]
    exact hz
  have rep2_self {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ×ℤ)}
      {p : ℤ×ℤ} (x : E.Page 2 p) : RepresentsOnPage E 2 p x x := by
    let A := E.ssData p
    haveI : Epi (A.pageπ ↑(2-E.r₀).toNat) := inferInstanceAs (Epi (cokernel.π _))
    obtain ⟨z,rfl⟩ := (ModuleCat.epi_iff_surjective (A.pageπ ↑(2-E.r₀).toNat)).mp inferInstance x
    exact ⟨by decide,z,by simp only [Subobject.ofLE_refl,Category.id_comp]; rfl,rfl⟩
  have permanent_zero {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ×ℤ)}
      {p : ℤ×ℤ} : IsPermanentCycle E p 0 := ⟨0,map_zero _⟩
  have late_zero_of_kernel_permanent
      (E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ×ℤ)) (hE : E.r₀≤2) (p : ℤ×ℤ)
      (hker : ∀ x : E.Page 2 p, E.d 2 p x=0 → IsPermanentCycle E p x)
      (r : ℤ) (hr : 3≤r) (a : E.Page r p) : E.d r p a=0 := by
    let A := E.ssData p
    haveI : Epi (A.pageπ ↑(r-E.r₀).toNat) := inferInstanceAs (Epi (cokernel.π _))
    obtain ⟨z,hz⟩ := (ModuleCat.epi_iff_surjective (A.pageπ ↑(r-E.r₀).toNat)).mp inferInstance a
    let x : E.Page 2 p := (Subobject.ofLE _ _ (A.Z_anti (by
      exact_mod_cast (show (2-E.r₀).toNat≤(r-E.r₀).toNat by omega))) ≫ A.pageπ _) z
    have hx : RepresentsOnPage E r p x a := ⟨by omega,z,rfl,hz⟩
    have hd : E.d 2 p x=0 := represents_d_zero_of_later hE (by omega) (rep2_self x) ⟨a,hx⟩
    exact represents_d_zero_of_later (by omega) (by omega : r<r+1) hx
      (permanent_reaches (hker x hd) (r+1) (by omega))
  have kernel_perm_fin1
      {E : KIP126.SpectralSequence (ModuleCat ℤ) (ℤ×ℤ)} {p : ℤ×ℤ}
      (e : E.Page 2 p ≃ₗ[ℤ] (Fin 1 →₀ KIP126.Algebra.F2))
      (hn : E.d 2 p (e.symm (Finsupp.single 0 1)) ≠ 0)
      (x : E.Page 2 p) (hx : E.d 2 p x=0) : IsPermanentCycle E p x := by
    have he : e x = Finsupp.single 0 (e x 0) := by
      apply Finsupp.ext
      intro i
      fin_cases i
      simp
    have hxe : x=e.symm (Finsupp.single 0 (e x 0)) := by rw [← he,LinearEquiv.symm_apply_apply]
    generalize hc : e x 0 = a at hxe
    fin_cases a
    · simp only [show (⟨0,by decide⟩:KIP126.Algebra.F2)=0 from rfl,Finsupp.single_zero,map_zero] at hxe
      rw [hxe]
      exact permanent_zero (E:=E) (p:=p)
    · change x=e.symm (Finsupp.single 0 1) at hxe
      exact (hn (hxe ▸ hx)).elim
  have kernel_perm_fin2
      {E : KIP126.SpectralSequence (ModuleCat ℤ) (ℤ×ℤ)} (hE : E.r₀≤2) {p : ℤ×ℤ}
      (e : E.Page 2 p ≃ₗ[ℤ] (Fin 2 →₀ KIP126.Algebra.F2))
      (hp : IsPermanentCycle E p (e.symm (Finsupp.single 0 1)))
      (hn : E.d 2 p (e.symm (Finsupp.single 1 1)) ≠ 0)
      (x : E.Page 2 p) (hx : E.d 2 p x=0) : IsPermanentCycle E p x := by
    have hd0 : E.d 2 p (e.symm (Finsupp.single 0 1))=0 :=
      represents_d_zero_of_later hE (by decide : (2:ℤ)<3) (rep2_self _) (permanent_reaches hp 3 (by decide))
    have he : e x = Finsupp.single 0 (e x 0) + Finsupp.single 1 (e x 1) := by
      apply Finsupp.ext
      intro i
      fin_cases i <;> simp
    have hxe : x=e.symm (Finsupp.single 0 (e x 0) + Finsupp.single 1 (e x 1)) := by rw [← he,LinearEquiv.symm_apply_apply]
    generalize hc0 : e x 0 = a at hxe
    generalize hc1 : e x 1 = b at hxe
    fin_cases a <;> fin_cases b
    all_goals simp only [show (⟨0,by decide⟩:KIP126.Algebra.F2)=0 from rfl,show (⟨1,by decide⟩:KIP126.Algebra.F2)=1 from rfl,Finsupp.single_zero,map_zero,zero_add,add_zero,map_add] at hxe
    · rw [hxe]; exact permanent_zero (E:=E) (p:=p)
    · exact (hn (by simpa only [hxe] using hx)).elim
    · rw [hxe]; exact hp
    · exact (hn (by simpa only [hxe,map_add,hd0,zero_add] using hx)).elim
  have stem63_q1_late (I : AdamsComputationTheorems D L G) (V : SphereVanishingLine H)
      (r : ℤ) (hr : 3≤r) (a : (sequence D .sphere).Page r (1,64)) :
      (sequence D .sphere).d r (1,64) a=0 := by
    let E := sequence D .sphere
    obtain ⟨e,he⟩ := I.basis ⟨.sphere, 1, 64, ["69,1"]⟩ (by
      unfold Raw.degrees
      iterate 85 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    change E.Page 2 (1,64) ≃ₗ[ℤ] (Fin 1 →₀ KIP126.Algebra.F2) at e
    change ∀ i : Fin 1, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 1 64 i.val at he
    obtain ⟨f,hf⟩ := I.basis ⟨.sphere, 3, 65, ["0,1,18,2"]⟩ (by
      unfold Raw.degrees
      iterate 102 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    change E.Page 2 (3,65) ≃ₗ[ℤ] (Fin 1 →₀ KIP126.Algebra.F2) at f
    change ∀ i : Fin 1, f.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 3 65 i.val at hf
    have hdiff : HasDifferential E 2 (1,64) (3,65)
        (I.interpretation.basis .sphere 1 64 0) (I.interpretation.basis .sphere 3 65 0) := by
      have hrow := I.adamsStatements ⟨.sphere, .equation, 2, 1, 64, [0], 3, 65, [0], "S0_AdamsE2_ss", 401⟩ (by
        unfold Raw.claims
        iterate 142 apply List.mem_cons_of_mem
        exact List.mem_cons_self)
      dsimp only [AdamsStatement] at hrow
      obtain ⟨x,hx,y,hy,h⟩ := hrow
      change HasDifferential E 2 (1,64) (3,65) x y at h
      have vx : Raw.coordinatesValid Raw.degrees .sphere 1 64 [0] = true := rfl
      have vy : Raw.coordinatesValid Raw.degrees .sphere 3 65 [0] = true := rfl
      simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
      rw [← hx,← hy] at h
      exact h
    have es : e.symm (Finsupp.single 0 1) = I.interpretation.basis .sphere 1 64 0 := he 0
    have ft : f.symm (Finsupp.single 0 1) = I.interpretation.basis .sphere 3 65 0 := hf 0
    have hn : E.d 2 (1,64) (e.symm (Finsupp.single 0 1)) ≠ 0 := by
      rw [es]
      have hd : E.d 2 (1,64) (I.interpretation.basis .sphere 1 64 0) =
          I.interpretation.basis .sphere 3 65 0 := hdiff.eq_on_page_two.choose_spec
      rw [hd,← ft]
      intro hz
      have hh := congrArg (fun z => f z 0) hz
      simp at hh
    exact late_zero_of_kernel_permanent E (by change (2:ℤ)≤2; omega) (1,64)
      (kernel_perm_fin1 e hn) r hr a
  have stem63_q2_late (I : AdamsComputationTheorems D L G) (V : SphereVanishingLine H)
      (r : ℤ) (hr : 3≤r) (a : (sequence D .sphere).Page r (2,65)) :
      (sequence D .sphere).d r (2,65) a=0 := by
    let E := sequence D .sphere
    obtain ⟨e,he⟩ := I.basis ⟨.sphere, 2, 65, ["0,1,69,1"]⟩ (by
      unfold Raw.degrees
      iterate 95 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    change E.Page 2 (2,65) ≃ₗ[ℤ] (Fin 1 →₀ KIP126.Algebra.F2) at e
    change ∀ i : Fin 1, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 2 65 i.val at he
    obtain ⟨f,hf⟩ := I.basis ⟨.sphere, 4, 66, ["0,2,18,2"]⟩ (by
      unfold Raw.degrees
      iterate 113 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    change E.Page 2 (4,66) ≃ₗ[ℤ] (Fin 1 →₀ KIP126.Algebra.F2) at f
    change ∀ i : Fin 1, f.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 4 66 i.val at hf
    have hdiff : HasDifferential E 2 (2,65) (4,66)
        (I.interpretation.basis .sphere 2 65 0) (I.interpretation.basis .sphere 4 66 0) := by
      have hrow := I.adamsStatements ⟨.sphere, .equation, 2, 2, 65, [0], 4, 66, [0], "S0_AdamsE2_ss", 417⟩ (by
        unfold Raw.claims
        iterate 145 apply List.mem_cons_of_mem
        exact List.mem_cons_self)
      dsimp only [AdamsStatement] at hrow
      obtain ⟨x,hx,y,hy,h⟩ := hrow
      change HasDifferential E 2 (2,65) (4,66) x y at h
      have vx : Raw.coordinatesValid Raw.degrees .sphere 2 65 [0] = true := rfl
      have vy : Raw.coordinatesValid Raw.degrees .sphere 4 66 [0] = true := rfl
      simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
      rw [← hx,← hy] at h
      exact h
    have es : e.symm (Finsupp.single 0 1) = I.interpretation.basis .sphere 2 65 0 := he 0
    have ft : f.symm (Finsupp.single 0 1) = I.interpretation.basis .sphere 4 66 0 := hf 0
    have hn : E.d 2 (2,65) (e.symm (Finsupp.single 0 1)) ≠ 0 := by
      rw [es]
      have hd : E.d 2 (2,65) (I.interpretation.basis .sphere 2 65 0) =
          I.interpretation.basis .sphere 4 66 0 := hdiff.eq_on_page_two.choose_spec
      rw [hd,← ft]
      intro hz
      have hh := congrArg (fun z => f z 0) hz
      simp at hh
    exact late_zero_of_kernel_permanent E (by change (2:ℤ)≤2; omega) (2,65)
      (kernel_perm_fin1 e hn) r hr a
  have stem63_q3_late (I : AdamsComputationTheorems D L G) (V : SphereVanishingLine H)
      (r : ℤ) (hr : 3≤r) (a : (sequence D .sphere).Page r (3,66)) :
      (sequence D .sphere).d r (3,66) a=0 := by
    let E := sequence D .sphere
    obtain ⟨e,he⟩ := I.basis ⟨.sphere, 3, 66, ["1,1,18,2", "0,2,69,1"]⟩ (by
      unfold Raw.degrees
      iterate 103 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    change E.Page 2 (3,66) ≃ₗ[ℤ] (Fin 2 →₀ KIP126.Algebra.F2) at e
    change ∀ i : Fin 2, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 3 66 i.val at he
    obtain ⟨f,hf⟩ := I.basis ⟨.sphere, 5, 67, ["76,1", "1,1,70,1", "0,3,18,2"]⟩ (by
      unfold Raw.degrees
      iterate 121 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    change E.Page 2 (5,67) ≃ₗ[ℤ] (Fin 3 →₀ KIP126.Algebra.F2) at f
    change ∀ i : Fin 3, f.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 5 67 i.val at hf
    have hdiff : HasDifferential E 2 (3,66) (5,67)
        (I.interpretation.basis .sphere 3 66 1) (I.interpretation.basis .sphere 5 67 2) := by
      have hrow := I.adamsStatements ⟨.sphere, .equation, 2, 3, 66, [1], 5, 67, [2], "S0_AdamsE2_ss", 437⟩ (by
        unfold Raw.claims
        iterate 150 apply List.mem_cons_of_mem
        exact List.mem_cons_self)
      dsimp only [AdamsStatement] at hrow
      obtain ⟨x,hx,y,hy,h⟩ := hrow
      change HasDifferential E 2 (3,66) (5,67) x y at h
      have vx : Raw.coordinatesValid Raw.degrees .sphere 3 66 [1] = true := rfl
      have vy : Raw.coordinatesValid Raw.degrees .sphere 5 67 [2] = true := rfl
      simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
      rw [← hx,← hy] at h
      exact h
    have es : e.symm (Finsupp.single 1 1) = I.interpretation.basis .sphere 3 66 1 := he 1
    have ft : f.symm (Finsupp.single 2 1) = I.interpretation.basis .sphere 5 67 2 := hf 2
    have hn : E.d 2 (3,66) (e.symm (Finsupp.single 1 1)) ≠ 0 := by
      rw [es]
      have hd : E.d 2 (3,66) (I.interpretation.basis .sphere 3 66 1) =
          I.interpretation.basis .sphere 5 67 2 := hdiff.eq_on_page_two.choose_spec
      rw [hd,← ft]
      intro hz
      have hh := congrArg (fun z => f z 2) hz
      simp at hh
    have hp : IsPermanentCycle E (3,66) (e.symm (Finsupp.single 0 1)) := by
      have es0 : e.symm (Finsupp.single 0 1) = I.interpretation.basis .sphere 3 66 0 := he 0
      rw [es0]
      apply permanent_cycle_of_reaches1000 V 3 66 (by norm_num) (by norm_num)
      have hrow := I.adamsStatements ⟨.sphere, .reaches, 1000, 3, 66, [0], 3, 66, [], "S0_AdamsE2_ss", 436⟩ (by
        unfold Raw.claims
        iterate 149 apply List.mem_cons_of_mem
        exact List.mem_cons_self)
      dsimp only [AdamsStatement] at hrow
      obtain ⟨x,hx,h⟩ := hrow
      have vx : Raw.coordinatesValid Raw.degrees .sphere 3 66 [0] = true := rfl
      simp only [E2Interpretation.coordinateSum,vx,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
      rw [← hx] at h
      exact h
    exact late_zero_of_kernel_permanent E (by change (2:ℤ)≤2; omega) (3,66)
      (kernel_perm_fin2 (by change (2:ℤ)≤2; omega) e hp hn) r hr a
  have stem63_q4_late (I : AdamsComputationTheorems D L G) (V : SphereVanishingLine H)
      (r : ℤ) (hr : 3≤r) (a : (sequence D .sphere).Page r (4,67)) :
      (sequence D .sphere).d r (4,67) a=0 := by
    let E := sequence D .sphere
    obtain ⟨e,he⟩ := I.basis ⟨.sphere, 4, 67, ["0,3,69,1"]⟩ (by
      unfold Raw.degrees
      iterate 114 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    change E.Page 2 (4,67) ≃ₗ[ℤ] (Fin 1 →₀ KIP126.Algebra.F2) at e
    change ∀ i : Fin 1, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 4 67 i.val at he
    obtain ⟨f,hf⟩ := I.basis ⟨.sphere, 6, 68, ["18,1,24,1", "0,4,18,2"]⟩ (by
      unfold Raw.degrees
      iterate 131 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    change E.Page 2 (6,68) ≃ₗ[ℤ] (Fin 2 →₀ KIP126.Algebra.F2) at f
    change ∀ i : Fin 2, f.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 6 68 i.val at hf
    have hdiff : HasDifferential E 2 (4,67) (6,68)
        (I.interpretation.basis .sphere 4 67 0) (I.interpretation.basis .sphere 6 68 1) := by
      have hrow := I.adamsStatements ⟨.sphere, .equation, 2, 4, 67, [0], 6, 68, [1], "S0_AdamsE2_ss", 455⟩ (by
        unfold Raw.claims
        iterate 155 apply List.mem_cons_of_mem
        exact List.mem_cons_self)
      dsimp only [AdamsStatement] at hrow
      obtain ⟨x,hx,y,hy,h⟩ := hrow
      change HasDifferential E 2 (4,67) (6,68) x y at h
      have vx : Raw.coordinatesValid Raw.degrees .sphere 4 67 [0] = true := rfl
      have vy : Raw.coordinatesValid Raw.degrees .sphere 6 68 [1] = true := rfl
      simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
      rw [← hx,← hy] at h
      exact h
    have es : e.symm (Finsupp.single 0 1) = I.interpretation.basis .sphere 4 67 0 := he 0
    have ft : f.symm (Finsupp.single 1 1) = I.interpretation.basis .sphere 6 68 1 := hf 1
    have hn : E.d 2 (4,67) (e.symm (Finsupp.single 0 1)) ≠ 0 := by
      rw [es]
      have hd : E.d 2 (4,67) (I.interpretation.basis .sphere 4 67 0) =
          I.interpretation.basis .sphere 6 68 1 := hdiff.eq_on_page_two.choose_spec
      rw [hd,← ft]
      intro hz
      have hh := congrArg (fun z => f z 1) hz
      simp at hh
    exact late_zero_of_kernel_permanent E (by change (2:ℤ)≤2; omega) (4,67)
      (kernel_perm_fin1 e hn) r hr a
  have stem63_q5_late (I : AdamsComputationTheorems D L G) (V : SphereVanishingLine H)
      (r : ℤ) (hr : 3≤r) (a : (sequence D .sphere).Page r (5,68)) :
      (sequence D .sphere).d r (5,68) a=0 := by
    let E := sequence D .sphere
    obtain ⟨e,he⟩ := I.basis ⟨.sphere, 5, 68, ["0,4,69,1"]⟩ (by
      unfold Raw.degrees
      iterate 122 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    change E.Page 2 (5,68) ≃ₗ[ℤ] (Fin 1 →₀ KIP126.Algebra.F2) at e
    change ∀ i : Fin 1, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 5 68 i.val at he
    obtain ⟨f,hf⟩ := I.basis ⟨.sphere, 7, 69, ["0,5,18,2"]⟩ (by
      unfold Raw.degrees
      iterate 142 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    change E.Page 2 (7,69) ≃ₗ[ℤ] (Fin 1 →₀ KIP126.Algebra.F2) at f
    change ∀ i : Fin 1, f.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 7 69 i.val at hf
    have hdiff : HasDifferential E 2 (5,68) (7,69)
        (I.interpretation.basis .sphere 5 68 0) (I.interpretation.basis .sphere 7 69 0) := by
      have hrow := I.adamsStatements ⟨.sphere, .equation, 2, 5, 68, [0], 7, 69, [0], "S0_AdamsE2_ss", 471⟩ (by
        unfold Raw.claims
        iterate 162 apply List.mem_cons_of_mem
        exact List.mem_cons_self)
      dsimp only [AdamsStatement] at hrow
      obtain ⟨x,hx,y,hy,h⟩ := hrow
      change HasDifferential E 2 (5,68) (7,69) x y at h
      have vx : Raw.coordinatesValid Raw.degrees .sphere 5 68 [0] = true := rfl
      have vy : Raw.coordinatesValid Raw.degrees .sphere 7 69 [0] = true := rfl
      simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
      rw [← hx,← hy] at h
      exact h
    have es : e.symm (Finsupp.single 0 1) = I.interpretation.basis .sphere 5 68 0 := he 0
    have ft : f.symm (Finsupp.single 0 1) = I.interpretation.basis .sphere 7 69 0 := hf 0
    have hn : E.d 2 (5,68) (e.symm (Finsupp.single 0 1)) ≠ 0 := by
      rw [es]
      have hd : E.d 2 (5,68) (I.interpretation.basis .sphere 5 68 0) =
          I.interpretation.basis .sphere 7 69 0 := hdiff.eq_on_page_two.choose_spec
      rw [hd,← ft]
      intro hz
      have hh := congrArg (fun z => f z 0) hz
      simp at hh
    exact late_zero_of_kernel_permanent E (by change (2:ℤ)≤2; omega) (5,68)
      (kernel_perm_fin1 e hn) r hr a
  have stem63_q6_late (I : AdamsComputationTheorems D L G) (V : SphereVanishingLine H)
      (r : ℤ) (hr : 3≤r) (a : (sequence D .sphere).Page r (6,69)) :
      (sequence D .sphere).d r (6,69) a=0 := by
    let E := sequence D .sphere
    obtain ⟨e,he⟩ := I.basis ⟨.sphere, 6, 69, ["1,1,76,1", "0,5,69,1"]⟩ (by
      unfold Raw.degrees
      iterate 132 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    change E.Page 2 (6,69) ≃ₗ[ℤ] (Fin 2 →₀ KIP126.Algebra.F2) at e
    change ∀ i : Fin 2, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 6 69 i.val at he
    obtain ⟨f,hf⟩ := I.basis ⟨.sphere, 8, 70, ["83,1", "82,1", "0,6,18,2"]⟩ (by
      unfold Raw.degrees
      iterate 155 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    change E.Page 2 (8,70) ≃ₗ[ℤ] (Fin 3 →₀ KIP126.Algebra.F2) at f
    change ∀ i : Fin 3, f.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 8 70 i.val at hf
    have hdiff : HasDifferential E 2 (6,69) (8,70)
        (I.interpretation.basis .sphere 6 69 1) (I.interpretation.basis .sphere 8 70 2) := by
      have hrow := I.adamsStatements ⟨.sphere, .equation, 2, 6, 69, [1], 8, 70, [2], "S0_AdamsE2_ss", 494⟩ (by
        unfold Raw.claims
        iterate 169 apply List.mem_cons_of_mem
        exact List.mem_cons_self)
      dsimp only [AdamsStatement] at hrow
      obtain ⟨x,hx,y,hy,h⟩ := hrow
      change HasDifferential E 2 (6,69) (8,70) x y at h
      have vx : Raw.coordinatesValid Raw.degrees .sphere 6 69 [1] = true := rfl
      have vy : Raw.coordinatesValid Raw.degrees .sphere 8 70 [2] = true := rfl
      simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
      rw [← hx,← hy] at h
      exact h
    have es : e.symm (Finsupp.single 1 1) = I.interpretation.basis .sphere 6 69 1 := he 1
    have ft : f.symm (Finsupp.single 2 1) = I.interpretation.basis .sphere 8 70 2 := hf 2
    have hn : E.d 2 (6,69) (e.symm (Finsupp.single 1 1)) ≠ 0 := by
      rw [es]
      have hd : E.d 2 (6,69) (I.interpretation.basis .sphere 6 69 1) =
          I.interpretation.basis .sphere 8 70 2 := hdiff.eq_on_page_two.choose_spec
      rw [hd,← ft]
      intro hz
      have hh := congrArg (fun z => f z 2) hz
      simp at hh
    have hp : IsPermanentCycle E (6,69) (e.symm (Finsupp.single 0 1)) := by
      have es0 : e.symm (Finsupp.single 0 1) = I.interpretation.basis .sphere 6 69 0 := he 0
      rw [es0]
      apply permanent_cycle_of_reaches1000 V 6 69 (by norm_num) (by norm_num)
      have hrow := I.adamsStatements ⟨.sphere, .reaches, 1000, 6, 69, [0], 6, 69, [], "S0_AdamsE2_ss", 493⟩ (by
        unfold Raw.claims
        iterate 168 apply List.mem_cons_of_mem
        exact List.mem_cons_self)
      dsimp only [AdamsStatement] at hrow
      obtain ⟨x,hx,h⟩ := hrow
      have vx : Raw.coordinatesValid Raw.degrees .sphere 6 69 [0] = true := rfl
      simp only [E2Interpretation.coordinateSum,vx,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
      rw [← hx] at h
      exact h
    exact late_zero_of_kernel_permanent E (by change (2:ℤ)≤2; omega) (6,69)
      (kernel_perm_fin2 (by change (2:ℤ)≤2; omega) e hp hn) r hr a
  by_cases hq0 : q≤0
  · exact no_outgoing_stem63_nonpositive q hq0 r (by omega) a
  interval_cases q
  · exact stem63_q1_late I V r hr a
  · exact stem63_q2_late I V r hr a
  · exact stem63_q3_late I V r hr a
  · exact stem63_q4_late I V r hr a
  · exact stem63_q5_late I V r hr a
  · exact stem63_q6_late I V r hr a

end
end KIP126.Computation.SphereAndCofiber
