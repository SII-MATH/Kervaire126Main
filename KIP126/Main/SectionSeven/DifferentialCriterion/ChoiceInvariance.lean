module

public import KIP126.Def.AdamsSynthetic.SectionSeven.AlphaOne
public import KIP126.Main.SectionSeven.Lambda

@[expose] public section

namespace KIP126.Main.SectionSeven.DifferentialCriterion
open KIP126.SpectralSequence.FinitePageCalculus
open CategoryTheory CategoryTheory.Limits KIP126.Algebra
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.SpectralSequence
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Kervaire KIP126.AdamsSynthetic KIP126.AdamsSynthetic.SectionSeven
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
private theorem theta_square_choice_d2_s1_t64_basis0 (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (1,64) (3,65) (I.interpretation.basis .sphere 1 64 0) (I.interpretation.basis .sphere 3 65 0) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere, .equation, 2, 1, 64, [0], 3, 65, [0], "S0_AdamsE2_ss", 401⟩ (by
    exact List.mem_of_getElem? (i := 142) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (1,64) (3,65) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 1 64 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 3 65 [0] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem theta_square_choice_d2_s2_t65_basis0 (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (2,65) (4,66) (I.interpretation.basis .sphere 2 65 0) (I.interpretation.basis .sphere 4 66 0) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere, .equation, 2, 2, 65, [0], 4, 66, [0], "S0_AdamsE2_ss", 417⟩ (by
    exact List.mem_of_getElem? (i := 145) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (2,65) (4,66) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 2 65 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 4 66 [0] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem theta_square_choice_d2_s3_t66_basis1 (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (3,66) (5,67) (I.interpretation.basis .sphere 3 66 1) (I.interpretation.basis .sphere 5 67 2) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere, .equation, 2, 3, 66, [1], 5, 67, [2], "S0_AdamsE2_ss", 437⟩ (by
    exact List.mem_of_getElem? (i := 150) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (3,66) (5,67) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 3 66 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 5 67 [2] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem theta_square_choice_d3_s5_t67_basis1 (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 3 (5,67) (8,69) (I.interpretation.basis .sphere 5 67 1) (I.interpretation.basis .sphere 8 69 0) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere, .equation, 3, 5, 67, [1], 8, 69, [0], "S0_AdamsE2_ss", 453⟩ (by
    exact List.mem_of_getElem? (i := 160) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (5,67) (8,69) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 5 67 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 8 69 [0] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem theta_square_choice_d2_s4_t67_basis0 (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (4,67) (6,68) (I.interpretation.basis .sphere 4 67 0) (I.interpretation.basis .sphere 6 68 1) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere, .equation, 2, 4, 67, [0], 6, 68, [1], "S0_AdamsE2_ss", 455⟩ (by
    exact List.mem_of_getElem? (i := 155) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (4,67) (6,68) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 4 67 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 6 68 [1] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem theta_square_choice_differential_target_later_zero {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)} {r : ℤ} {t : ℤ} {p : ℤ × ℤ} {q : ℤ × ℤ} {x : E.Page 2 p} {y : E.Page 2 q}
    (hr0 : E.r₀ ≤ r) (hrt : r < t)
    (h : HasDifferential E r p q x y) : RepresentsOnPage E t q y 0 := by
  classical
  obtain ⟨rfl, xr, yr, hx, hy, hd⟩ := h
  simp only [eqToHom_refl, Category.comp_id] at hd
  obtain ⟨hr, z, hz2, hzr⟩ := hy
  let A := E.ssData (p + E.diffDeg r)
  let n : ℕ := (r-E.r₀).toNat
  let n₀ : WithTop ℕ := ↑(2-E.r₀).toNat
  let m : WithTop ℕ := ↑(t-E.r₀).toNat
  have hnm : (↑(n+1) : WithTop ℕ) ≤ m := by
    dsimp only [n,m]
    exact_mod_cast (show (r-E.r₀).toNat+1 ≤ (t-E.r₀).toNat by omega)
  have hn0 : n₀ ≤ ↑n := by
    dsimp only [n₀,n]
    exact_mod_cast (show (2-E.r₀).toNat ≤ (r-E.r₀).toNat by omega)
  have hn1 : (↑n : WithTop ℕ) ≤ ↑(n+1) := by exact_mod_cast Nat.le_succ n
  have hdmem : yr ∈ LinearMap.range (E.d r p).hom := ⟨xr, hd⟩
  rw [← subobjectModule_image, E.B_succ r p hr0, subobjectModule_image] at hdmem
  obtain ⟨b, hb⟩ := hdmem
  let j := Subobject.ofLE (A.B ↑(n+1)) (A.Z ↑n)
    ((A.B_le_Z _).trans (A.Z_anti hn1))
  have hb' : A.pageπ ↑n (j b) = yr := hb
  have hdif : A.pageπ ↑n (z-j b) = 0 := by rw [map_sub, hzr, hb', sub_self]
  have hmem := (subobject_cokernel_π_eq_zero_iff (A.B ↑n) (A.Z ↑n) (A.B_le_Z _) _).mp hdif
  have hmem' := (ModuleCat.subobjectModule A.V).monotone (A.B_mono hn1) hmem
  have hj : (A.Z ↑n).arrow (j b) ∈ (ModuleCat.subobjectModule A.V) (A.B ↑(n+1)) := by
    change (j ≫ (A.Z ↑n).arrow) b ∈ _
    dsimp only [j]
    rw [Subobject.ofLE_arrow]
    exact ⟨b,rfl⟩
  have hzmem := ((ModuleCat.subobjectModule A.V) (A.B ↑(n+1))).add_mem hmem' hj
  rw [map_sub, sub_add_cancel] at hzmem
  obtain ⟨b', hb'⟩ := hzmem
  let i := Subobject.ofLE (A.B ↑(n+1)) (A.Z m) ((A.B_mono hnm).trans (A.B_le_Z _))
  refine ⟨by omega, i b', ?_, ?_⟩
  · have he : (Subobject.ofLE (A.Z m) (A.Z n₀) (A.Z_anti (hn0.trans (hn1.trans hnm))))
        (i b') = (Subobject.ofLE (A.Z ↑n) (A.Z n₀) (A.Z_anti hn0)) z := by
      apply (ModuleCat.mono_iff_injective (A.Z n₀).arrow).mp inferInstance
      change (i ≫ Subobject.ofLE (A.Z m) (A.Z n₀) _ ≫ (A.Z n₀).arrow) b' =
        (Subobject.ofLE (A.Z ↑n) (A.Z n₀) _ ≫ (A.Z n₀).arrow) z
      simpa only [Category.assoc, i, Subobject.ofLE_arrow] using hb'
    exact (congrArg (fun v => A.pageπ n₀ v) he).trans hz2
  · apply (subobject_cokernel_π_eq_zero_iff (A.B m) (A.Z m) (A.B_le_Z _) _).mpr
    change (i ≫ (A.Z m).arrow) b' ∈ _
    dsimp only [i]
    rw [Subobject.ofLE_arrow]
    exact (ModuleCat.subobjectModule A.V).monotone (A.B_mono hnm) ⟨b',rfl⟩

private theorem theta_square_choice_next_projection_zero_iff_incoming
    (E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ))
    (r : ℤ) (hr : E.r₀ ≤ r) (p : ℤ × ℤ)
    (z : (Subobject.underlying.obj ((E.ssData (p+E.diffDeg r)).Z
      ↑((r-E.r₀).toNat+1)) : ModuleCat ℤ)) :
    (E.ssData (p+E.diffDeg r)).pageπ ↑((r-E.r₀).toNat+1) z = 0 ↔
      (Subobject.ofLE _ _ ((E.ssData (p+E.diffDeg r)).Z_anti
        (by exact_mod_cast Nat.le_succ (r-E.r₀).toNat)) ≫
          (E.ssData (p+E.diffDeg r)).pageπ ↑(r-E.r₀).toNat) z ∈
        LinearMap.range (E.d r p).hom := by
  classical
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

private theorem theta_square_choice_next_nonzero_of_not_hit {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)} {r : ℤ} {p : ℤ × ℤ} {x : E.Page 2 p}
    (hr0 : E.r₀ ≤ r) (hr : 2 ≤ r)
    {a : E.Page (r+1) p} {b : E.Page r p}
    (ha : RepresentsOnPage E (r+1) p x a) (hb : RepresentsOnPage E r p x b)
    (hne : b ≠ 0) (hnot : ¬ HitOnPage E r p x) : a ≠ 0 := by
  classical
  generalize hq : p-E.diffDeg r=q
  have hp : p=q+E.diffDeg r := by rw [←hq]; abel
  subst p
  obtain ⟨_,z,hz,hza⟩ := ha
  let A := E.ssData (q+E.diffDeg r)
  have hi : (r+1-E.r₀).toNat=(r-E.r₀).toNat+1 := by omega
  have hnm : (↑(r-E.r₀).toNat : WithTop ℕ) ≤ ↑(r+1-E.r₀).toNat := by
    exact_mod_cast (show (r-E.r₀).toNat≤(r+1-E.r₀).toNat by omega)
  let br := (Subobject.ofLE _ _ (A.Z_anti hnm) ≫ A.pageπ ↑(r-E.r₀).toNat) z
  have hbr : RepresentsOnPage E r (q+E.diffDeg r) x br := by
    refine ⟨hr, (Subobject.ofLE _ _ (A.Z_anti hnm)) z, ?_, rfl⟩
    rw [← CategoryTheory.comp_apply, ← Category.assoc, Subobject.ofLE_comp_ofLE]
    exact hz
  have heb : br=b := represents_unique hbr hb
  intro ha0
  have hv := theta_square_choice_next_projection_zero_iff_incoming E r hr0 q
  have hv' : ∀ zz : (Subobject.underlying.obj (A.Z ↑(r+1-E.r₀).toNat) : ModuleCat ℤ),
      A.pageπ ↑(r+1-E.r₀).toNat zz=0 ↔
        (Subobject.ofLE _ _ (A.Z_anti hnm) ≫ A.pageπ ↑(r-E.r₀).toNat) zz∈
          LinearMap.range (E.d r q).hom := by
    have transport (m : ℕ) (hm : m=(r-E.r₀).toNat+1)
        (hge : (↑(r-E.r₀).toNat : WithTop ℕ)≤↑m) :
        ∀ zz : (Subobject.underlying.obj (A.Z ↑m) : ModuleCat ℤ),
          A.pageπ ↑m zz=0 ↔
            (Subobject.ofLE _ _ (A.Z_anti hge) ≫ A.pageπ ↑(r-E.r₀).toNat) zz∈
              LinearMap.range (E.d r q).hom := by
      subst m
      exact hv
    exact transport _ hi hnm
  have hmem : br∈LinearMap.range (E.d r q).hom := by
    exact (hv' z).mp (hza.trans ha0)
  obtain ⟨c,hc⟩ := hmem
  apply hnot
  refine ⟨q, rfl, c,b,hb,hne,?_⟩
  simpa only [eqToHom_refl, Category.comp_id] using hc.trans heb

private theorem theta_square_choice_theta_choice_late_page_generic
    (E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ×ℤ))
    (hr0 : E.r₀≤2) (hdeg2 : E.diffDeg 2=(2,1))
    (b5 : Fin 3 → E.Page 2 (5,67)) (b6 : Fin 2 → E.Page 2 (6,68))
    (b7 : Fin 2 → E.Page 2 (7,68)) (b8 : Fin 1 → E.Page 2 (8,69))
    (e5 : E.Page 2 (5,67) ≃ₗ[ℤ] (Fin 3 →₀ KIP126.Algebra.F2))
    (he5 : ∀i:Fin 3, e5.symm (Finsupp.single i 1)=b5 i)
    (e6 : E.Page 2 (6,68) ≃ₗ[ℤ] (Fin 2 →₀ KIP126.Algebra.F2))
    (he6 : ∀i:Fin 2, e6.symm (Finsupp.single i 1)=b6 i)
    (e7 : E.Page 2 (7,68) ≃ₗ[ℤ] (Fin 2 →₀ KIP126.Algebra.F2))
    (he7 : ∀i:Fin 2, e7.symm (Finsupp.single i 1)=b7 i)
    (e8 : E.Page 2 (8,69) ≃ₗ[ℤ] (Fin 1 →₀ KIP126.Algebra.F2))
    (he8 : ∀i:Fin 1, e8.symm (Finsupp.single i 1)=b8 i)
    (h3 : HasDifferential E 3 (5,67) (8,69) (b5 1) (b8 0))
    (h2out : HasDifferential E 2 (5,67) (7,68) (b5 0) (b7 0+b7 1))
    (hz567 : RepresentsOnPage E 3 (5,67) (b5 2) 0)
    (hd60 : E.d 2 (6,68) (b6 0)=0)
    (hd61 : E.d 2 (6,68) (b6 1)=0) :
    Subsingleton (E.Page 4 (5,67)) := by
  classical
  classical
  change E.d 2 (6,68) (b6 0)=0 at hd60
  change E.d 2 (6,68) (b6 1)=0 at hd61
  have he60 : e6.symm (Finsupp.single 0 1)=b6 0 := he6 0
  have he61 : e6.symm (Finsupp.single 1 1)=b6 1 := he6 1
  have he70 : e7.symm (Finsupp.single 0 1)=b7 0 := he7 0
  have he71 : e7.symm (Finsupp.single 1 1)=b7 1 := he7 1
  have he80 : e8.symm (Finsupp.single 0 1)=b8 0 := he8 0
  have hd6 (x:E.Page 2 (6,68)) : E.d 2 (6,68) x=0 := by
    have hex : e6 x=Finsupp.single 0 (e6 x 0)+Finsupp.single 1 (e6 x 1) := by
      apply Finsupp.ext
      intro i
      fin_cases i <;> simp
    have hx : x=e6.symm (Finsupp.single 0 (e6 x 0)+Finsupp.single 1 (e6 x 1)) := by
      rw [←hex,LinearEquiv.symm_apply_apply]
    generalize h0 : e6 x 0=c0 at hx
    generalize h1 : e6 x 1=c1 at hx
    fin_cases c0 <;> fin_cases c1
    · change x=e6.symm (Finsupp.single 0 (0:KIP126.Algebra.F2)+Finsupp.single 1 (0:KIP126.Algebra.F2)) at hx
      simp only [Finsupp.single_zero,map_zero,add_zero] at hx
      rw [hx]
      simp only [map_zero]
    · change x=e6.symm (Finsupp.single 0 (0:KIP126.Algebra.F2)+Finsupp.single 1 (1:KIP126.Algebra.F2)) at hx
      simp only [Finsupp.single_zero,zero_add,he61] at hx
      rw [hx]
      simp only [hd61]
    · change x=e6.symm (Finsupp.single 0 (1:KIP126.Algebra.F2)+Finsupp.single 1 (0:KIP126.Algebra.F2)) at hx
      simp only [Finsupp.single_zero,add_zero,he60] at hx
      rw [hx]
      simp only [hd60]
    · change x=e6.symm (Finsupp.single 0 (1:KIP126.Algebra.F2)+Finsupp.single 1 (1:KIP126.Algebra.F2)) at hx
      simp only [map_add,he60,he61] at hx
      rw [hx]
      simp only [map_add,hd60,hd61,add_zero]
  obtain ⟨heq,a3,b3,ha3,hb3,hdb⟩ := h3
  have hne2 : b8 0≠0 := by
    intro hz
    have he := congrArg (fun v=>e8 v 0) hz
    rw [←he80,LinearEquiv.apply_symm_apply,e8.map_zero] at he
    norm_num at he
  have hnot : ¬HitOnPage E 2 (8,69) (b8 0) := by
    rintro ⟨q,hq,c,d,hd,hdne,hcd⟩
    have hq' : q=(6,68) := by
      rw [hdeg2] at hq
      apply Prod.ext
      · have h := congrArg Prod.fst hq
        change q.1+2=8 at h
        omega
      · have h := congrArg Prod.snd hq
        change q.2+(2-1)=69 at h
        omega
    subst q
    change (eqToHom (congrArg (E.Page 2) hq)) (E.d 2 (6,68) c)=d at hcd
    rw [hd6,map_zero] at hcd
    exact hdne hcd.symm
  obtain ⟨b2,hb2⟩ := reaches_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤3) ⟨b3,hb3⟩
  have hbn : b3≠0 := theta_square_choice_next_nonzero_of_not_hit hr0
    (by decide : (2:ℤ)≤2) hb3 hb2 (by rw [←hb2.eq_on_page_two]; exact hne2) hnot
  have hd0 : E.d 2 (5,67) (b5 0)≠0 := by
    intro h0
    have h := h2out.eq_on_page_two.2
    change (eqToHom (congrArg (E.Page 2) h2out.1)) (E.d 2 (5,67) (b5 0))=b7 0+b7 1 at h
    rw [h0,map_zero] at h
    have he := congrArg (fun v=>e7 v 0) h
    rw [e7.map_zero,e7.map_add,←he70,←he71,LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply] at he
    norm_num at he
  have hall := choice_frame_of_three_basis (E:=E) (r:=3) (p:=(5,67)) (by decide : (2:ℤ)<3)
    hr0 e5 _ _ _ (he5 0) (he5 1) (he5 2) a3 ha3 hz567 hd0
  have hdn : E.d 3 (5,67) a3≠0 := by
    intro hz
    apply hbn
    rw [←hdb]
    change (eqToHom (congrArg (E.Page 3) heq)) (E.d 3 (5,67) a3)=0
    rw [hz,map_zero]
  exact choice_next_zero_of_single_frame_nonzero_differential (E:=E) (r:=3) (p:=(5,67)) (by decide : (2:ℤ)≤3)
    (by omega : E.r₀≤3) a3 hdn hall

private theorem theta_square_choice_theta_choice_raw_relations (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G) :
    HasDifferential (sequence D .sphere) 2 (1,64) (3,65) (I.interpretation.basis .sphere 1 64 0) (I.interpretation.basis .sphere 3 65 0) ∧
    HasDifferential (sequence D .sphere) 2 (2,65) (4,66) (I.interpretation.basis .sphere 2 65 0) (I.interpretation.basis .sphere 4 66 0) ∧
    HasDifferential (sequence D .sphere) 2 (3,66) (5,67) (I.interpretation.basis .sphere 3 66 1) (I.interpretation.basis .sphere 5 67 2) ∧
    HasDifferential (sequence D .sphere) 3 (5,67) (8,69) (I.interpretation.basis .sphere 5 67 1) (I.interpretation.basis .sphere 8 69 0) ∧
    HasDifferential (sequence D .sphere) 2 (5,67) (7,68) (I.interpretation.basis .sphere 5 67 0) (I.interpretation.basis .sphere 7 68 0+I.interpretation.basis .sphere 7 68 1) ∧
    HasDifferential (sequence D .sphere) 2 (4,67) (6,68) (I.interpretation.basis .sphere 4 67 0) (I.interpretation.basis .sphere 6 68 1) ∧
    ReachesPage (sequence D .sphere) 1000 (6,68) (I.interpretation.basis .sphere 6 68 0) := by
  classical
  classical
  let E := sequence D .sphere
  have h365 : HasDifferential E 2 (1,64) (3,65) (I.interpretation.basis .sphere 1 64 0) (I.interpretation.basis .sphere 3 65 0) := theta_square_choice_d2_s1_t64_basis0 I
  have h466 : HasDifferential E 2 (2,65) (4,66) (I.interpretation.basis .sphere 2 65 0) (I.interpretation.basis .sphere 4 66 0) := theta_square_choice_d2_s2_t65_basis0 I
  have h567 : HasDifferential E 2 (3,66) (5,67) (I.interpretation.basis .sphere 3 66 1) (I.interpretation.basis .sphere 5 67 2) := theta_square_choice_d2_s3_t66_basis1 I
  have h3 : HasDifferential E 3 (5,67) (8,69) (I.interpretation.basis .sphere 5 67 1) (I.interpretation.basis .sphere 8 69 0) := theta_square_choice_d3_s5_t67_basis1 I
  have h2out : HasDifferential E 2 (5,67) (7,68) (I.interpretation.basis .sphere 5 67 0) (I.interpretation.basis .sphere 7 68 0+I.interpretation.basis .sphere 7 68 1) := by
    have hrow := I.adamsStatements ⟨.sphere, .equation, 2, 5, 67, [0], 7, 68, [0, 1], "S0_AdamsE2_ss", 454⟩ (by
      exact List.mem_of_getElem? (i := 161) (by rfl))
    dsimp only [AdamsStatement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (5,67) (7,68) x y at hd
    have vx : Raw.coordinatesValid Raw.degrees .sphere 5 67 [0] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 7 68 [0, 1] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  have h668 : HasDifferential E 2 (4,67) (6,68) (I.interpretation.basis .sphere 4 67 0) (I.interpretation.basis .sphere 6 68 1) := theta_square_choice_d2_s4_t67_basis0 I
  have hcycle : ReachesPage E 1000 (6,68) (I.interpretation.basis .sphere 6 68 0) := by
    have hrow := I.adamsStatements ⟨.sphere, .reaches, 1000, 6, 68, [0], 6, 68, [], "S0_AdamsE2_ss", 470⟩ (by
      exact List.mem_of_getElem? (i := 167) (by rfl))
    dsimp only [AdamsStatement] at hrow
    obtain ⟨x,hx,hd⟩ := hrow
    change ReachesPage E 1000 (6,68) x at hd
    have vx : Raw.coordinatesValid Raw.degrees .sphere 6 68 [0] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
    rw [←hx] at hd
    exact hd
  exact ⟨h365,h466,h567,h3,h2out,h668,hcycle⟩

private theorem theta_square_choice_theta_choice_late_page (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G)
    (e5 : (sequence D .sphere).Page 2 (5,67) ≃ₗ[ℤ] (Fin 3 →₀ F2))
    (he5 : ∀i:Fin 3, e5.symm (Finsupp.single i 1)=I.interpretation.basis .sphere 5 67 i.val)
    (e6 : (sequence D .sphere).Page 2 (6,68) ≃ₗ[ℤ] (Fin 2 →₀ F2))
    (he6 : ∀i:Fin 2, e6.symm (Finsupp.single i 1)=I.interpretation.basis .sphere 6 68 i.val)
    (e7 : (sequence D .sphere).Page 2 (7,68) ≃ₗ[ℤ] (Fin 2 →₀ F2))
    (he7 : ∀i:Fin 2, e7.symm (Finsupp.single i 1)=I.interpretation.basis .sphere 7 68 i.val)
    (e8 : (sequence D .sphere).Page 2 (8,69) ≃ₗ[ℤ] (Fin 1 →₀ F2))
    (he8 : ∀i:Fin 1, e8.symm (Finsupp.single i 1)=I.interpretation.basis .sphere 8 69 i.val)
    (h3 : HasDifferential (sequence D .sphere) 3 (5,67) (8,69) (I.interpretation.basis .sphere 5 67 1) (I.interpretation.basis .sphere 8 69 0))
    (h2out : HasDifferential (sequence D .sphere) 2 (5,67) (7,68) (I.interpretation.basis .sphere 5 67 0) (I.interpretation.basis .sphere 7 68 0+I.interpretation.basis .sphere 7 68 1))
    (hz567 : RepresentsOnPage (sequence D .sphere) 3 (5,67) (I.interpretation.basis .sphere 5 67 2) 0)
    (hd60 : (sequence D .sphere).d 2 (6,68) (I.interpretation.basis .sphere 6 68 0)=0)
    (hd61 : (sequence D .sphere).d 2 (6,68) (I.interpretation.basis .sphere 6 68 1)=0) :
    Subsingleton ((sequence D .sphere).Page 4 (5,67)) := by
  classical
  exact theta_square_choice_theta_choice_late_page_generic (sequence D .sphere) (by change (2:ℤ)≤2; omega) rfl
    (fun i=>I.interpretation.basis .sphere 5 67 i.val)
    (fun i=>I.interpretation.basis .sphere 6 68 i.val)
    (fun i=>I.interpretation.basis .sphere 7 68 i.val)
    (fun i=>I.interpretation.basis .sphere 8 69 i.val)
    e5 he5 e6 he6 e7 he7 e8 he8 h3 h2out hz567 hd60 hd61

private theorem theta_square_choice_theta_choice_finite_pages (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 3 (3,65)) ∧
    Subsingleton ((sequence D .sphere).Page 3 (4,66)) ∧
    Subsingleton ((sequence D .sphere).Page 4 (5,67)) := by
  classical
  classical
  let E := sequence D .sphere
  obtain ⟨h365,h466,h567,h3,h2out,h668,hcycle⟩ := theta_square_choice_theta_choice_raw_relations I
  obtain ⟨e3,he3⟩ := I.basis ⟨.sphere, 3, 65, ["0,1,18,2"]⟩ (by
    exact List.mem_of_getElem? (i := 102) (by rfl))
  change E.Page 2 (3,65) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e3
  change ∀i:Fin 1, e3.symm (Finsupp.single i 1)=I.interpretation.basis .sphere 3 65 i.val at he3
  obtain ⟨e4,he4⟩ := I.basis ⟨.sphere, 4, 66, ["0,2,18,2"]⟩ (by
    exact List.mem_of_getElem? (i := 113) (by rfl))
  change E.Page 2 (4,66) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e4
  change ∀i:Fin 1, e4.symm (Finsupp.single i 1)=I.interpretation.basis .sphere 4 66 i.val at he4
  obtain ⟨e5,he5⟩ := I.basis ⟨.sphere, 5, 67, ["76,1", "1,1,70,1", "0,3,18,2"]⟩ (by
    exact List.mem_of_getElem? (i := 121) (by rfl))
  change E.Page 2 (5,67) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e5
  change ∀i:Fin 3, e5.symm (Finsupp.single i 1)=I.interpretation.basis .sphere 5 67 i.val at he5
  obtain ⟨e6,he6⟩ := I.basis ⟨.sphere, 6, 68, ["18,1,24,1", "0,4,18,2"]⟩ (by
    exact List.mem_of_getElem? (i := 131) (by rfl))
  change E.Page 2 (6,68) ≃ₗ[ℤ] (Fin 2 →₀ F2) at e6
  change ∀i:Fin 2, e6.symm (Finsupp.single i 1)=I.interpretation.basis .sphere 6 68 i.val at he6
  obtain ⟨e7,he7⟩ := I.basis ⟨.sphere, 7, 68, ["0,1,75,1", "0,1,74,1"]⟩ (by
    exact List.mem_of_getElem? (i := 141) (by rfl))
  change E.Page 2 (7,68) ≃ₗ[ℤ] (Fin 2 →₀ F2) at e7
  change ∀i:Fin 2, e7.symm (Finsupp.single i 1)=I.interpretation.basis .sphere 7 68 i.val at he7
  obtain ⟨e8,he8⟩ := I.basis ⟨.sphere, 8, 69, ["0,2,74,1"]⟩ (by
    exact List.mem_of_getElem? (i := 154) (by rfl))
  change E.Page 2 (8,69) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e8
  change ∀i:Fin 1, e8.symm (Finsupp.single i 1)=I.interpretation.basis .sphere 8 69 i.val at he8
  have he60 : e6.symm (Finsupp.single 0 1)=I.interpretation.basis .sphere 6 68 0 := he6 0
  have he61 : e6.symm (Finsupp.single 1 1)=I.interpretation.basis .sphere 6 68 1 := he6 1
  have he70 : e7.symm (Finsupp.single 0 1)=I.interpretation.basis .sphere 7 68 0 := he7 0
  have he71 : e7.symm (Finsupp.single 1 1)=I.interpretation.basis .sphere 7 68 1 := he7 1
  have he80 : e8.symm (Finsupp.single 0 1)=I.interpretation.basis .sphere 8 69 0 := he8 0
  have dz (r:ℤ) (hr:2<r) (p:ℤ×ℤ) (x:E.Page 2 p)
      (hx:ReachesPage E r p x) : E.d 2 p x=0 := by
    obtain ⟨x2,hx2⟩ := reaches_before (by decide : (2:ℤ)≤2) (by omega : (2:ℤ)≤r) hx
    have hh := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) hr hx2 hx
    simpa only [hx2.eq_on_page_two] using hh
  have hz365 := theta_square_choice_differential_target_later_zero (by change (2:ℤ)≤2; omega)
    (by decide : (2:ℤ)<3) h365
  have hz466 := theta_square_choice_differential_target_later_zero (by change (2:ℤ)≤2; omega)
    (by decide : (2:ℤ)<3) h466
  have hz567 := theta_square_choice_differential_target_later_zero (by change (2:ℤ)≤2; omega)
    (by decide : (2:ℤ)<3) h567
  have hz668 := theta_square_choice_differential_target_later_zero (by change (2:ℤ)≤2; omega)
    (by decide : (2:ℤ)<3) h668
  refine ⟨choice_single_basis_zero_page (by decide : (2:ℤ)≤3) e3 _ (he3 0) hz365,
    choice_single_basis_zero_page (by decide : (2:ℤ)≤3) e4 _ (he4 0) hz466,?_⟩
  have hd60 := dz 1000 (by decide) (6,68) _ hcycle
  have hd61 := dz 3 (by decide) (6,68) _ ⟨0,hz668⟩
  exact theta_square_choice_theta_choice_late_page I e5 he5 e6 he6 e7 he7 e8 he8 h3 h2out hz567 hd60 hd61

private theorem theta_square_choice_theta_square_difference (D : AdamsComparison H M Syn)
    (θ θ' : BiHom 62 64 (S_0_0 : Syn)) (h2 : θ'+θ'=0) :
    sphereProduct θ θ-sphereProduct θ' θ'=sphereProduct (θ-θ') (θ-θ') := by
  classical
  let d := θ-θ'
  have ht : θ=θ'+d := by dsimp only [d]; abel
  have hc : sphereProduct d θ'=sphereProduct θ' d := by
    have h := D.sphereProductCommutative 62 64 62 64 d θ'
    norm_num [homotopyRegrade] at h
    exact h
  have hz : sphereProduct θ' d+sphereProduct d θ'=0 := by
    rw [hc]
    dsimp only [sphereProduct]
    rw [←Preadditive.comp_add,←Preadditive.add_comp,←Functor.map_add,h2,Functor.map_zero,
      zero_comp,comp_zero]
  have hs : sphereProduct (θ'+d) (θ'+d)=sphereProduct θ' θ'+sphereProduct d d := by
    have he : sphereProduct (θ'+d) (θ'+d)=
        sphereProduct θ' θ'+sphereProduct θ' d+(sphereProduct d θ'+sphereProduct d d) := by
      simp only [sphereProduct,Functor.map_add,Preadditive.add_comp,Preadditive.comp_add]
      abel
    rw [he]
    calc
      _ = sphereProduct θ' θ'+(sphereProduct θ' d+sphereProduct d θ')+sphereProduct d d := by abel
      _ = _ := by rw [hz,add_zero]
  change sphereProduct θ θ-sphereProduct θ' θ'=sphereProduct d d
  rw [ht,hs,add_sub_cancel_left]

private theorem theta_square_choice_detects_of_difference_in_next_filtration
    {H' : Syn} {unit : S_0_0 ⟶ H'} {F : SyntheticAdamsFamily Syn} {X : Syn}
    (c : TowerConvergence unit F X) (i : Tridegree)
    {x : (F.obj X).E₂ i} {a b : BiHom (i.2.1-i.1) i.2.2 X}
    (ha : Detects c i x a) (hb : FiltrationAtLeast unit (i.1+1) (b-a)) :
    Detects c i x b := by
  classical
  obtain ⟨e,he,a',ha',hga⟩ := ha
  let P := towerFiltration unit X
  let p := (i.2.1-i.1,i.2.2)
  have hmem : b-a∈(ModuleCat.subobjectModule (syntheticHomotopy X p)) (P.F (i.1+1) p) := by
    simpa only [P,p,FiltrationAtLeast,towerFiltration,OrderIso.apply_symm_apply] using hb
  obtain ⟨z,hz⟩ := hmem
  let j := Subobject.ofLE (P.F (i.1+1) p) (P.F i.1 p) (P.mono i.1 p)
  refine ⟨e,he,a'+j z,?_,?_⟩
  · rw [map_add]
    have hj : (P.F i.1 p).arrow (j z)=(P.F (i.1+1) p).arrow z :=
      ConcreteCategory.congr_hom (Subobject.ofLE_arrow (P.mono i.1 p)) z
    rw [hj,ha',hz]
    abel
  · rw [map_add]
    have hj : P.toAssociatedGraded i.1 p (j z)=0 :=
      ConcreteCategory.congr_hom (cokernel.condition j) z
    rw [hj,add_zero]
    exact hga

private theorem theta_square_choice_realization_additive {D : AdamsComparison H M Syn} : D.recovery.realization.Additive := by
  classical
  letI := D.recovery.adjunction.isLeftAdjoint
  letI := Limits.preservesBinaryBiproducts_of_preservesBinaryCoproducts D.recovery.realization
  exact Functor.additive_of_preservesBinaryBiproducts _

private theorem theta_square_choice_realization_injective_of_lambda_powers
    (kernel : KIP126.Literature.AdamsSynthetic.RealizationKernel D) (X : SyntheticObject) (m wt : ℤ)
    (h : LambdaPowersInjectiveAt m wt (X.obj D.nu D.hopfAndDetector)) :
    Function.Injective (fun a : BiHom m wt (X.obj D.nu D.hopfAndDetector) =>
      D.recovery.realization.map a) := by
  classical
  letI := theta_square_choice_realization_additive (D := D)
  intro a b hab
  apply sub_eq_zero.mp
  obtain ⟨k, hk⟩ := (kernel X m wt (a-b)).mp (by simp only [Functor.map_sub, hab, sub_self])
  apply h k
  simpa only [lambdaMultiply, Category.comp_id, Category.assoc, Limits.comp_zero] using hk

private theorem theta_square_choice_theta_degree_order_two (BHS : SyntheticComparisonTheorems D)
    (RL : RealizationDetectionData D) {η : BiHom 1 2 (S_0_0 : Syn)}
    (CL : ClassicalTheorems D η) (theta : BiHom 62 64 (S_0_0 : Syn)) :
    theta+theta=0 := by
  classical
  have hnu : LambdaPowersInjectiveAt 62 64 (D.nu.functor.obj SphereSpectrum) := by
    apply nu_lambda_powers_injective_of_source_halfplane BHS .sphere 62 64
    intro q hq
    simpa only [ClassicalObject.obj,KIP126.Computation.SphereAndCofiber.sequence,KIP126.Computation.SphereAndCofiber.object,add_assoc,show (62:ℤ)+1=63 by norm_num] using
      no_outgoing_stem63_nonpositive (D:=D) q (by omega)
  have hsphere : LambdaPowersInjectiveAt 62 64 (S_0_0 : Syn) := by
    intro n a b hab
    apply (cancel_mono D.nu.unitIso.inv).mp
    apply hnu n
    simpa only [lambdaMultiply,Category.assoc] using
      congrArg (fun z=>z ≫ D.nu.unitIso.inv) hab
  have hinj := theta_square_choice_realization_injective_of_lambda_powers BHS.realization_kernel
    .sphere 62 64 hsphere
  letI := D.recovery.adjunction.isLeftAdjoint
  letI := Limits.preservesBinaryBiproducts_of_preservesBinaryCoproducts D.recovery.realization
  letI : D.recovery.realization.Additive := Functor.additive_of_preservesBinaryBiproducts _
  apply hinj
  simp only [Functor.map_add,Functor.map_zero]
  let α : HomotopyGroup (C:=C) 62 SphereSpectrum :=
    (RL.coordinates.sphere 62 64).hom ≫ D.recovery.realization.map theta ≫
      D.recovery.realization.map D.nu.unitIso.inv ≫ D.recovery.nuRealizationIso.hom.app SphereSpectrum
  have h := CL.stem62_exponent_two α
  apply (cancel_epi (RL.coordinates.sphere 62 64).hom).mp
  apply (cancel_mono (D.recovery.realization.map D.nu.unitIso.inv)).mp
  apply (cancel_mono ((D.recovery.nuRealizationIso.app SphereSpectrum).hom)).mp
  erw [Preadditive.comp_add,Preadditive.add_comp,Preadditive.add_comp,
    Limits.comp_zero,Limits.zero_comp,Limits.zero_comp]
  repeat erw [Category.assoc]
  exact h

private theorem theta_square_choice_theta_choice_filtration_gap_of_pages
    (BHS : SyntheticComparisonTheorems D)
    (hpages : Subsingleton ((sequence D .sphere).Page 3 (3,65)) ∧
      Subsingleton ((sequence D .sphere).Page 3 (4,66)) ∧
      Subsingleton ((sequence D .sphere).Page 4 (5,67)))
    (θ θ' : BiHom 62 64 (S_0_0 : Syn))
    (hθ : ThetaChoice M D.toAdamsComparisonData θ) (hθ' : ThetaChoice M D.toAdamsComparisonData θ') :
    FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 6 (θ-θ') := by
  classical
  have hlambda0 (a : BiHom 62 64 (S_0_0 : Syn)) : lambdaMultiply 0 a=a := by
    have hc := D.shiftCoherence.right_unit (62,64) (S_0_0 : Syn)
    have he : (SyntheticCategory.biShift_comp (62,64) (0,0)).hom.app (S_0_0 : Syn)=
        SyntheticCategory.biShift_zero.hom.app (Smn 62 64 : Syn) := by
      change (biShiftAddIso (62,64) (0,0) (62,64) (by decide)).hom.app _=_ at hc
      simpa only [biShiftAddIso,Iso.trans_hom,NatTrans.comp_app,eqToIso.hom,
        eqToHom_app,eqToHom_refl,Category.comp_id,Smn] using hc
    dsimp only [lambdaMultiply,lambdaPow]
    simp only [eqToHom_refl,Category.id_comp]
    rw [←he]
    change (SyntheticCategory.biShift_comp (62,64) (0,0)).inv.app (S_0_0 : Syn) ≫
      (SyntheticCategory.biShift_comp (62,64) (0,0)).hom.app (S_0_0 : Syn) ≫ a=a
    rw [←Category.assoc,Iso.inv_hom_id_app,Category.id_comp]
  have ht := D.comparisonCompatible.homotopy_lambda 2 64 0 θ
  have ht' := D.comparisonCompatible.homotopy_lambda 2 64 0 θ'
  rw [hlambda0,hθ] at ht
  rw [hlambda0,hθ'] at ht'
  have h3 : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 3 (θ-θ') :=
    detects_sub_filtration D.sphereConvergence (2,64,64) ht ht'
  have permanentQuotient_zero_of_page_3_zero (s t b : ℤ) (hb : 2 ≤ b)
      (hpage : Subsingleton ((sequence D .sphere).Page 3 (s, t))) :
      Subsingleton (PageRepresentatives.PermanentQuotient H SphereSpectrum b (s, t)) := by
    set_option backward.isDefEq.respectTransparency false in
      let E := (sequence D .sphere).ssData (s, t)
      haveI : Subsingleton (E.page 1) := hpage
      have hcycles : PageRepresentatives.permanentCycles H SphereSpectrum (s, t) ≤
          PageRepresentatives.boundaries H SphereSpectrum 2 (s, t) := by
        rintro x ⟨z, hz⟩
        let zf := (Subobject.ofLE (E.Z ⊤) (E.Z 1) (E.Z_anti le_top)) z
        have hzero : E.pageπ 1 zf = 0 := Subsingleton.elim _ _
        obtain ⟨y, hy⟩ := (cokernel_π_eq_zero_iff_mem_range
          (Subobject.ofLE (E.B 1) (E.Z 1) (E.B_le_Z 1)) zf).mp hzero
        refine ⟨y, ?_⟩
        change PageRepresentatives.boundaryMap H SphereSpectrum 1 (s, t) y = x
        have hfactor : Subobject.ofLE (E.B 1) (E.Z 1) (E.B_le_Z 1) ≫
            PageRepresentatives.cycleMap H SphereSpectrum 1 (s, t) =
            PageRepresentatives.boundaryMap H SphereSpectrum 1 (s, t) := by
          dsimp only [PageRepresentatives.cycleMap, PageRepresentatives.boundaryMap, E, Computation.SphereAndCofiber.sequence, object]
          rw [← Category.assoc, Subobject.ofLE_comp_ofLE]
        rw [← hfactor, CategoryTheory.comp_apply]
        apply (congrArg (PageRepresentatives.cycleMap H SphereSpectrum 1 (s, t)) hy).trans
        exact (congrArg (fun f => f z)
          (PageRepresentatives.cycleMap_factor H SphereSpectrum (s, t) 1 ⊤ le_top)).trans hz
      have hall : ∀ x : PageRepresentatives.PermanentQuotient H SphereSpectrum b (s, t), x = 0 := by
        rintro ⟨x⟩
        change KIP126.Algebra.NestedQuotient.projection _ _ x = 0
        apply (KIP126.Algebra.NestedQuotient.projection_eq_zero x).mpr
        exact PageRepresentatives.boundaries_monotone H SphereSpectrum (s, t) hb (hcycles x.property)
      exact ⟨fun x y => (hall x).trans (hall y).symm⟩

  have permanentQuotient_zero_of_page_4_zero (s t b : ℤ) (hb : 3 ≤ b)
      (hpage : Subsingleton ((sequence D .sphere).Page 4 (s, t))) :
      Subsingleton (PageRepresentatives.PermanentQuotient H SphereSpectrum b (s, t)) := by
    set_option backward.isDefEq.respectTransparency false in
      let E := (sequence D .sphere).ssData (s, t)
      haveI : Subsingleton (E.page 2) := hpage
      have hcycles : PageRepresentatives.permanentCycles H SphereSpectrum (s, t) ≤
          PageRepresentatives.boundaries H SphereSpectrum 3 (s, t) := by
        rintro x ⟨z, hz⟩
        let zf := (Subobject.ofLE (E.Z ⊤) (E.Z 2) (E.Z_anti le_top)) z
        have hzero : E.pageπ 2 zf = 0 := Subsingleton.elim _ _
        obtain ⟨y, hy⟩ := (cokernel_π_eq_zero_iff_mem_range
          (Subobject.ofLE (E.B 2) (E.Z 2) (E.B_le_Z 2)) zf).mp hzero
        refine ⟨y, ?_⟩
        change PageRepresentatives.boundaryMap H SphereSpectrum 2 (s, t) y = x
        have hfactor : Subobject.ofLE (E.B 2) (E.Z 2) (E.B_le_Z 2) ≫
            PageRepresentatives.cycleMap H SphereSpectrum 2 (s, t) =
            PageRepresentatives.boundaryMap H SphereSpectrum 2 (s, t) := by
          dsimp only [PageRepresentatives.cycleMap, PageRepresentatives.boundaryMap, E, Computation.SphereAndCofiber.sequence, object]
          rw [← Category.assoc, Subobject.ofLE_comp_ofLE]
        rw [← hfactor, CategoryTheory.comp_apply]
        apply (congrArg (PageRepresentatives.cycleMap H SphereSpectrum 2 (s, t)) hy).trans
        exact (congrArg (fun f => f z)
          (PageRepresentatives.cycleMap_factor H SphereSpectrum (s, t) 2 ⊤ le_top)).trans hz
      have hall : ∀ x : PageRepresentatives.PermanentQuotient H SphereSpectrum b (s, t), x = 0 := by
        rintro ⟨x⟩
        change KIP126.Algebra.NestedQuotient.projection _ _ x = 0
        apply (KIP126.Algebra.NestedQuotient.projection_eq_zero x).mpr
        exact PageRepresentatives.boundaries_monotone H SphereSpectrum (s, t) hb (hcycles x.property)
      exact ⟨fun x y => (hall x).trans (hall y).symm⟩

  apply (D.sphereConvergence.filtrationAtLeast_iff_of_eInfty_isZero
    3 6 62 64 (by omega) ?_ (θ-θ')).mp h3
  intro j hj hj'
  haveI : Subsingleton (PageRepresentatives.PermanentQuotient H SphereSpectrum
      (1+(62+j)-64) (j,62+j)) := by
    interval_cases j
    · exact permanentQuotient_zero_of_page_3_zero 3 65 2 (by omega) hpages.1
    · exact permanentQuotient_zero_of_page_3_zero 4 66 3 (by omega) hpages.2.1
    · exact permanentQuotient_zero_of_page_4_zero 5 67 4 (by omega) hpages.2.2
  let e := BHS.eInfty.presentation.nuWindow SphereSpectrum (j,62+j) 64 (by omega)
  haveI : Subsingleton (((D.family.nu D.nu SphereSpectrum).sequence.ssData (j,62+j,64)).eInfty) := e.injective.subsingleton
  let hnu := ModuleCat.isZero_of_subsingleton
    (((D.family.nu D.nu SphereSpectrum).sequence.ssData (j,62+j,64)).eInfty)
  let f := (D.family.functor.map D.nu.unitIso.hom).eInftyMap (j,62+j,64)
  let g := (D.family.functor.map D.nu.unitIso.inv).eInftyMap (j,62+j,64)
  have hfg : g ≫ f = 𝟙 _ := by
    dsimp only [f,g]
    rw [←SpectralSequenceMorphism.eInftyMap_comp,←CategoryTheory.Functor.map_comp,Iso.inv_hom_id,
      CategoryTheory.Functor.map_id,SpectralSequenceMorphism.eInftyMap_id]
  apply (CategoryTheory.Limits.IsZero.iff_id_eq_zero _).mpr
  exact hfg.symm.trans (by rw [hnu.eq_of_src f 0,CategoryTheory.Limits.comp_zero])

private theorem theta_square_choice_theta_choice_square_detection_invariance_of_pages
    (BHS : SyntheticComparisonTheorems D) (RL : RealizationDetectionData D)
    {η : BiHom 1 2 (S_0_0 : Syn)} (CL : ClassicalTheorems D η)
    (AF : SphereActionFiltrationCompatible D)
    (hpages : Subsingleton ((sequence D .sphere).Page 3 (3,65)) ∧
      Subsingleton ((sequence D .sphere).Page 3 (4,66)) ∧
      Subsingleton ((sequence D .sphere).Page 4 (5,67)))
    (θ θ' : BiHom 62 64 (S_0_0 : Syn))
    (hθ : ThetaChoice M D.toAdamsComparisonData θ) (hθ' : ThetaChoice M D.toAdamsComparisonData θ')
    (hc : Theta5SquareNonzeroDetectionAt M D.toAdamsComparisonData L θ') : Theta5SquareNonzeroDetectionAt M D.toAdamsComparisonData L θ := by
  classical
  have hd := theta_square_choice_theta_choice_filtration_gap_of_pages BHS hpages θ θ' hθ hθ'
  have hsq : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 12
      (sphereProduct θ θ-sphereProduct θ' θ') := by
    rw [theta_square_choice_theta_square_difference D θ θ' (theta_square_choice_theta_degree_order_two BHS RL CL θ')]
    exact AF .sphere 62 64 62 64 6 6 (θ-θ') (θ-θ') hd hd
  refine ⟨?_,hc.2⟩
  apply theta_square_choice_detects_of_difference_in_next_filtration D.sphereConvergence (10,134,128) hc.1
  exact towerFiltrationSubmodule_antitone (nuCoefficientUnit H.unit D.nu)
    (S_0_0 : Syn) (124,128) (by decide : (11:ℤ)≤12) hsq

private theorem theta_square_choice_theta_choice_square_detection_invariance (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G)
    (BHS : SyntheticComparisonTheorems D) (RL : RealizationDetectionData D)
    {η : BiHom 1 2 (S_0_0 : Syn)} (CL : ClassicalTheorems D η)
    (AF : SphereActionFiltrationCompatible D)
    (θ θ' : BiHom 62 64 (S_0_0 : Syn))
    (hθ : ThetaChoice M D.toAdamsComparisonData θ) (hθ' : ThetaChoice M D.toAdamsComparisonData θ')
    (hc : Theta5SquareNonzeroDetectionAt M D.toAdamsComparisonData L θ') : Theta5SquareNonzeroDetectionAt M D.toAdamsComparisonData L θ := by
  classical
  exact theta_square_choice_theta_choice_square_detection_invariance_of_pages BHS RL CL AF (theta_square_choice_theta_choice_finite_pages I) θ θ' hθ hθ' hc

private theorem theta_square_choice_invariance (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G)
    (BHS : SyntheticComparisonTheorems D) (RL : RealizationDetectionData D) (CL : ClassicalTheorems D η)
    (AF : SphereActionFiltrationCompatible D)
    (theta theta' : BiHom 62 64 (S_0_0 : Syn))
    (h : ThetaChoice M D.toAdamsComparisonData theta) (h' : ThetaChoice M D.toAdamsComparisonData theta')
    (hc : Theta5SquareNonzeroDetectionAt M D.toAdamsComparisonData L theta') : Theta5SquareNonzeroDetectionAt M D.toAdamsComparisonData L theta := by
  classical
  exact theta_square_choice_theta_choice_square_detection_invariance I BHS RL CL AF theta theta' h h' hc
end
end KIP126.Main.SectionSeven.DifferentialCriterion
