module
public import KIP126.Main.Conditions
public import KIP126.ProofTools.Operations
public import KIP126.ProofTools.Representatives
import all KIP126.Main.Internal.Selected.NormalizedFacts
import all KIP126.Main.Internal.QuotientCalculus

/-! The complete finite error calculation from Section7/NuNinth:268–928,
bbac1fc05843 (MIT). Shared representative lemmas replace identical local
copies; every finite basis and differential row is retained. -/
@[expose] section
namespace KIP126.Main.Internal.Selected.NuError
open CategoryTheory CategoryTheory.Limits KIP126.Core.Algebra
open KIP126.Core.SpectralSequence KIP126.Core.SpectralSequence.FinitePageCalculus
open KIP126.AdamsSynthetic.Standard (model)
open KIP126.Literature KIP126.Kervaire.Route
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000

private def denormalize (p : ℤ×ℤ) : Normalized.sphere.Page 2 p ⟶ model.classical.sphere.Page 2 p :=
  eqToHom (congrArg (fun E : KIP126.Core.SpectralSequence (ModuleCat ℤ) (ℤ×ℤ) => E.Page 2 p) Normalized.sphere_eq)

private theorem denormalize_basis (s t i : ℕ) : denormalize (s,t) (Normalized.basis .sphere s t i)=
    KIP126.Computation.Table.basis .sphere s t i := by
  dsimp only [denormalize,Normalized.basis]
  rw [←ModuleCat.comp_apply,eqToHom_trans,eqToHom_refl]
  rfl

private theorem denormalize_label (p : ℤ×ℤ) (x : model.classical.sphere.Page 2 p) :
    denormalize p (Normalized.label p x)=x := by
  dsimp only [denormalize,Normalized.label]
  rw [←ModuleCat.comp_apply,eqToHom_trans,eqToHom_refl]
  rfl

private theorem normalized_reaches (r : ℤ) (p : ℤ×ℤ) (x : model.classical.sphere.Page 2 p)
    (hx : ReachesPage model.classical.sphere r p x) :
    ReachesPage Normalized.sphere r p (Normalized.label p x) := by
  have tr (E E' : KIP126.Core.SpectralSequence (ModuleCat ℤ) (ℤ×ℤ)) (h : E=E')
      (x : E.Page 2 p) (hx : ReachesPage E r p x) :
      ReachesPage E' r p ((eqToHom (congrArg (fun A => A.Page 2 p) h)) x) := by
    subst E'
    simpa only [eqToHom_refl,ModuleCat.id_apply] using hx
  exact tr _ _ Normalized.sphere_eq.symm x hx

private theorem actual_reaches (r : ℤ) (p : ℤ×ℤ) (x : Normalized.sphere.Page 2 p)
    (hx : ReachesPage Normalized.sphere r p x) :
    ReachesPage model.classical.sphere r p (denormalize p x) := by
  have tr (E E' : KIP126.Core.SpectralSequence (ModuleCat ℤ) (ℤ×ℤ)) (h : E=E')
      (x : E.Page 2 p) (hx : ReachesPage E r p x) :
      ReachesPage E' r p ((eqToHom (congrArg (fun A => A.Page 2 p) h)) x) := by
    subst E'
    simpa only [eqToHom_refl,ModuleCat.id_apply] using hx
  exact tr _ _ Normalized.sphere_eq x hx

private theorem actual_zero_representative (r : ℤ) (p : ℤ×ℤ) (x : Normalized.sphere.Page 2 p)
    (hx : RepresentsOnPage Normalized.sphere r p x 0) :
    RepresentsOnPage model.classical.sphere r p (denormalize p x) 0 := by
  have tr (E E' : KIP126.Core.SpectralSequence (ModuleCat ℤ) (ℤ×ℤ)) (h : E=E')
      (x : E.Page 2 p) (hx : RepresentsOnPage E r p x 0) :
      RepresentsOnPage E' r p ((eqToHom (congrArg (fun A => A.Page 2 p) h)) x) 0 := by
    subst E'
    simpa only [eqToHom_refl,ModuleCat.id_apply] using hx
  exact tr _ _ Normalized.sphere_eq x hx

private def nCycles (c : ℤ) (p : ℤ×ℤ) : Submodule ℤ (Normalized.sphere.Page 2 p) :=
  (cycles model .sphere c p).comap (denormalize p).hom
private def nBoundaries (b : ℤ) (p : ℤ×ℤ) : Submodule ℤ (Normalized.sphere.Page 2 p) :=
  (boundaries model .sphere b p).comap (denormalize p).hom

private theorem nCycle_of_reaches (r : ℤ) (hr : 2≤r) (p : ℤ×ℤ)
    (x : Normalized.sphere.Page 2 p) (hx : ReachesPage Normalized.sphere r p x) :
    x∈nCycles (r-1) p :=
  ((KIP126.ProofTools.isCycle_iff_reaches model .sphere r hr p _).mpr (actual_reaches r p x hx)).2

private theorem boundary_of_zero_representative {r : ℤ} {p : ℤ×ℤ} {x : Normalized.sphere.Page 2 p}
    (hx : RepresentsOnPage Normalized.sphere r p x 0) : x∈nBoundaries (r-1) p :=
  represents_zero_mem_boundary model .sphere r p _ (actual_zero_representative r p x hx)

private theorem middle_add {E : KIP126.Core.SpectralSequence (ModuleCat ℤ) (ℤ × ℤ)} {r : ℤ} {p : ℤ × ℤ} {x y : E.Page 2 p} {a b : E.Page r p}
    (hx : KIP126.Core.SpectralSequence.RepresentsOnPage E r p x a) (hy : KIP126.Core.SpectralSequence.RepresentsOnPage E r p y b) :
    KIP126.Core.SpectralSequence.RepresentsOnPage E r p (x+y) (a+b) := by
  obtain ⟨hr,z,hz,ha⟩ := hx
  obtain ⟨_,w,hw,hb⟩ := hy
  exact ⟨hr,z+w,by rw [map_add,hz,hw],by rw [map_add,ha,hb]⟩
private theorem middle_if {E : KIP126.Core.SpectralSequence (ModuleCat ℤ) (ℤ × ℤ)} {r : ℤ} {p : ℤ × ℤ} {x : E.Page 2 p} {a : E.Page r p}
    (c : F2) (h : KIP126.Core.SpectralSequence.RepresentsOnPage E r p x a) :
    KIP126.Core.SpectralSequence.RepresentsOnPage E r p (if c=0 then 0 else x) (if c=0 then 0 else a) := by
  split
  · exact KIP126.Core.SpectralSequence.RepresentsOnPage.zero h.1
  · exact h
private theorem middle_expand {N : ℕ} (f : Fin N →₀ F2) :
    f = ∑ i : Fin N, if f i=0 then 0 else Finsupp.single i 1 := by
  ext i
  simp only [Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single i]
  · generalize f i=b
    fin_cases b <;> simp
  · intro j hj hji
    by_cases hf : f j=0
    · simp [hf]
    · simp [hf,hji]
  · simp
private theorem middle_rep2 {E : KIP126.Core.SpectralSequence (ModuleCat ℤ) (ℤ × ℤ)}
    {p : ℤ × ℤ} {r : ℤ} {x : E.Page 2 p} {a : E.Page r p} (hr : 2≤r)
    (ha : KIP126.Core.SpectralSequence.RepresentsOnPage E r p x a) : KIP126.Core.SpectralSequence.RepresentsOnPage E 2 p x x := by
  obtain ⟨b,hb⟩ := represents_before (by decide : (2:ℤ)≤2) hr ha
  rw [←hb.eq_on_page_two] at hb
  exact hb
private theorem nu9_af12_kernel
    (x : Normalized.Page .sphere 12 137)
    (dx : (Normalized.sphere).d 2 (12,137) x = 0) :
    KIP126.Core.SpectralSequence.RepresentsOnPage (Normalized.sphere) 4 (12,137) x 0 := by
  let E := Normalized.sphere
  have h260 : KIP126.Core.SpectralSequence.HasDifferential E 2 (10,136) (12,137)
      ((Normalized.basis .sphere 10 136 0)) ((Normalized.basis .sphere 12 137 2)) := by
    have hrow := Normalized.result ⟨.sphere,.equation,2,10,136,[0],12,137,[2],"S0_AdamsE2_ss",2859⟩ (by
      unfold KIP126.Computation.Table.Raw.claims
      iterate 260 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    dsimp only [Normalized.Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change KIP126.Core.SpectralSequence.HasDifferential E 2 (10,136) (12,137) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 10 136 [0] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 12 137 [2] = true := rfl
    simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  have h234 : KIP126.Core.SpectralSequence.HasDifferential E 3 (9,135) (12,137)
      ((Normalized.basis .sphere 9 135 3)) ((Normalized.basis .sphere 12 137 3)) := by
    have hrow := Normalized.result ⟨.sphere,.equation,3,9,135,[3],12,137,[3],"S0_AdamsE2_ss",2793⟩ (by
      unfold KIP126.Computation.Table.Raw.claims
      iterate 234 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    dsimp only [Normalized.Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change KIP126.Core.SpectralSequence.HasDifferential E 3 (9,135) (12,137) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 9 135 [3] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 12 137 [3] = true := rfl
    simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  have h307 : KIP126.Core.SpectralSequence.HasDifferential E 3 (9,135) (12,137)
      ((Normalized.basis .sphere 9 135 0) + (Normalized.basis .sphere 9 135 3)) ((Normalized.basis .sphere 12 137 4)) := by
    have hrow := Normalized.result ⟨.sphere,.equation,3,9,135,[0, 3],12,137,[4],"S0_AdamsE2_ss",2920⟩ (by
      unfold KIP126.Computation.Table.Raw.claims
      iterate 307 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    dsimp only [Normalized.Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change KIP126.Core.SpectralSequence.HasDifferential E 3 (9,135) (12,137) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 9 135 [0, 3] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 12 137 [4] = true := rfl
    simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  have h308 : KIP126.Core.SpectralSequence.HasDifferential E 2 (12,137) (14,138)
      ((Normalized.basis .sphere 12 137 1)) ((Normalized.basis .sphere 14 138 4)) := by
    have hrow := Normalized.result ⟨.sphere,.equation,2,12,137,[1],14,138,[4],"S0_AdamsE2_ss",2921⟩ (by
      unfold KIP126.Computation.Table.Raw.claims
      iterate 308 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    dsimp only [Normalized.Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change KIP126.Core.SpectralSequence.HasDifferential E 2 (12,137) (14,138) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 12 137 [1] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 14 138 [4] = true := rfl
    simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  have h309 : KIP126.Core.SpectralSequence.HasDifferential E 2 (12,137) (14,138)
      ((Normalized.basis .sphere 12 137 0)) ((Normalized.basis .sphere 14 138 3)) := by
    have hrow := Normalized.result ⟨.sphere,.equation,2,12,137,[0],14,138,[3],"S0_AdamsE2_ss",2922⟩ (by
      unfold KIP126.Computation.Table.Raw.claims
      iterate 309 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    dsimp only [Normalized.Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change KIP126.Core.SpectralSequence.HasDifferential E 2 (12,137) (14,138) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 12 137 [0] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 14 138 [3] = true := rfl
    simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  obtain ⟨e,he⟩ := Normalized.basis_correct ⟨.sphere,12,137,["426,1", "425,1", "0,1,69,1,89,1", "0,3,391,1", "0,4,375,1"]⟩ (by
    unfold KIP126.Computation.Table.Raw.degrees
    iterate 201 apply List.mem_cons_of_mem
    exact List.mem_cons_self)
  change E.Page 2 (12,137) ≃ₗ[ℤ] (Fin 5 →₀ F2) at e
  change ∀ i : Fin 5, e.symm (Finsupp.single i 1) = Normalized.basis .sphere 12 137 i.val at he
  obtain ⟨f,hf⟩ := Normalized.basis_correct ⟨.sphere,14,138,["440,1", "439,1", "23,1,190,1", "1,1,418,1", "1,1,417,1"]⟩ (by
    unfold KIP126.Computation.Table.Raw.degrees
    iterate 216 apply List.mem_cons_of_mem
    exact List.mem_cons_self)
  change E.Page 2 (14,138) ≃ₗ[ℤ] (Fin 5 →₀ F2) at f
  change ∀ i : Fin 5, f.symm (Finsupp.single i 1) = Normalized.basis .sphere 14 138 i.val at hf
  have he0 : e.symm (Finsupp.single (0:Fin 5) 1) = Normalized.basis .sphere 12 137 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 5) 1) = Normalized.basis .sphere 12 137 1 := he 1
  have he2 : e.symm (Finsupp.single (2:Fin 5) 1) = Normalized.basis .sphere 12 137 2 := he 2
  have he3 : e.symm (Finsupp.single (3:Fin 5) 1) = Normalized.basis .sphere 12 137 3 := he 3
  have he4 : e.symm (Finsupp.single (4:Fin 5) 1) = Normalized.basis .sphere 12 137 4 := he 4
  have hf0 : f.symm (Finsupp.single (0:Fin 5) 1) = Normalized.basis .sphere 14 138 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 5) 1) = Normalized.basis .sphere 14 138 1 := hf 1
  have hf2 : f.symm (Finsupp.single (2:Fin 5) 1) = Normalized.basis .sphere 14 138 2 := hf 2
  have hf3 : f.symm (Finsupp.single (3:Fin 5) 1) = Normalized.basis .sphere 14 138 3 := hf 3
  have hf4 : f.symm (Finsupp.single (4:Fin 5) 1) = Normalized.basis .sphere 14 138 4 := hf 4
  have hz2 : KIP126.Core.SpectralSequence.RepresentsOnPage E 4 (12,137) (Normalized.basis .sphere 12 137 2) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4) h260
  have d2 : E.d 2 (12,137) (Normalized.basis .sphere 12 137 2)=0 :=
    represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4)
      (middle_rep2 (by decide) hz2) ⟨0,hz2⟩
  have hz3 : KIP126.Core.SpectralSequence.RepresentsOnPage E 4 (12,137) (Normalized.basis .sphere 12 137 3) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<4) h234
  have d3 : E.d 2 (12,137) (Normalized.basis .sphere 12 137 3)=0 :=
    represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4)
      (middle_rep2 (by decide) hz3) ⟨0,hz3⟩
  have hz4 : KIP126.Core.SpectralSequence.RepresentsOnPage E 4 (12,137) (Normalized.basis .sphere 12 137 4) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<4) h307
  have d4 : E.d 2 (12,137) (Normalized.basis .sphere 12 137 4)=0 :=
    represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4)
      (middle_rep2 (by decide) hz4) ⟨0,hz4⟩
  have d0 : E.d 2 (12,137) (Normalized.basis .sphere 12 137 0)=Normalized.basis .sphere 14 138 3 := h309.eq_on_page_two.2
  have d1 : E.d 2 (12,137) (Normalized.basis .sphere 12 137 1)=Normalized.basis .sphere 14 138 4 := h308.eq_on_page_two.2
  let c : Fin 5 → F2 := e x
  have hcoef := congrArg e.symm (middle_expand (e x))
  simp only [LinearEquiv.symm_apply_apply,map_sum,map_add,Fin.sum_univ_succ,apply_ite,map_zero] at hcoef
  change x=(if c 0=0 then 0 else e.symm (Finsupp.single 0 1)) + ((if c 1=0 then 0 else e.symm (Finsupp.single 1 1)) + ((if c 2=0 then 0 else e.symm (Finsupp.single 2 1)) + ((if c 3=0 then 0 else e.symm (Finsupp.single 3 1)) + ((if c 4=0 then 0 else e.symm (Finsupp.single 4 1)) + 0)))) at hcoef
  simp only [he0,he1,he2,he3,he4,add_zero] at hcoef
  have hd := congrArg (E.d 2 (12,137)) hcoef
  rw [dx] at hd
  simp only [map_add,apply_ite,map_zero] at hd
  simp only [d0,d1,d2,d3,d4,ite_self,add_zero] at hd
  have c0 : c 0=0 := by
    by_contra h0
    simp only [h0,ite_false] at hd
    by_cases h1 : c 1=0
    all_goals simp only [h1,ite_true,ite_false] at hd
    all_goals have hh := congrArg (fun z => f z 3) hd
    all_goals simp only [map_add,map_zero,Finsupp.add_apply,Finsupp.zero_apply,←hf3,←hf4,LinearEquiv.apply_symm_apply] at hh
    all_goals norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
  have c1 : c 1=0 := by
    by_contra h1
    simp only [c0,h1,ite_true,ite_false,zero_add] at hd
    have hh := congrArg (fun z => f z 4) hd
    simp only [map_zero,Finsupp.zero_apply,←hf4,LinearEquiv.apply_symm_apply] at hh
    norm_num [Finsupp.single_apply] at hh
  rw [hcoef]
  simp only [c0,c1,ite_true,zero_add]
  have hh := middle_add (middle_if (c 2) hz2) (middle_add (middle_if (c 3) hz3) (middle_if (c 4) hz4))
  simpa only [ite_self,zero_add] using hh
private theorem nu9_af13_cosets  :
    Normalized.basis .sphere 13 138 1 ∈ nCycles 2 (13,138) ∧
    ∀ x : Normalized.Page .sphere 13 138,
      x ∈ nBoundaries 4 (13,138) ∨
      x - Normalized.basis .sphere 13 138 1 ∈ nBoundaries 4 (13,138) := by
  let E := Normalized.sphere
  have h231 : KIP126.Core.SpectralSequence.HasDifferential E 4 (9,135) (13,138)
      ((Normalized.basis .sphere 9 135 2)) ((Normalized.basis .sphere 13 138 0)) := by
    have hrow := Normalized.result ⟨.sphere,.equation,4,9,135,[2],13,138,[0],"S0_AdamsE2_ss",2790⟩ (by
      unfold KIP126.Computation.Table.Raw.claims
      iterate 231 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    dsimp only [Normalized.Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change KIP126.Core.SpectralSequence.HasDifferential E 4 (9,135) (13,138) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 9 135 [2] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 13 138 [0] = true := rfl
    simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  have h232 : KIP126.Core.SpectralSequence.HasDifferential E 4 (9,135) (13,138)
      ((Normalized.basis .sphere 9 135 1)) ((Normalized.basis .sphere 13 138 2)) := by
    have hrow := Normalized.result ⟨.sphere,.equation,4,9,135,[1],13,138,[2],"S0_AdamsE2_ss",2791⟩ (by
      unfold KIP126.Computation.Table.Raw.claims
      iterate 232 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    dsimp only [Normalized.Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change KIP126.Core.SpectralSequence.HasDifferential E 4 (9,135) (13,138) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 9 135 [1] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 13 138 [2] = true := rfl
    simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  have h288 : KIP126.Core.SpectralSequence.HasDifferential E 2 (11,137) (13,138)
      ((Normalized.basis .sphere 11 137 0)) ((Normalized.basis .sphere 13 138 3)) := by
    have hrow := Normalized.result ⟨.sphere,.equation,2,11,137,[0],13,138,[3],"S0_AdamsE2_ss",2927⟩ (by
      unfold KIP126.Computation.Table.Raw.claims
      iterate 288 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    dsimp only [Normalized.Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change KIP126.Core.SpectralSequence.HasDifferential E 2 (11,137) (13,138) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 11 137 [0] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 13 138 [3] = true := rfl
    simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  have h289 : KIP126.Core.SpectralSequence.HasDifferential E 2 (11,137) (13,138)
      ((Normalized.basis .sphere 11 137 3)) ((Normalized.basis .sphere 13 138 4)) := by
    have hrow := Normalized.result ⟨.sphere,.equation,2,11,137,[3],13,138,[4],"S0_AdamsE2_ss",2928⟩ (by
      unfold KIP126.Computation.Table.Raw.claims
      iterate 289 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    dsimp only [Normalized.Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change KIP126.Core.SpectralSequence.HasDifferential E 2 (11,137) (13,138) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 11 137 [3] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 13 138 [4] = true := rfl
    simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  have h329 : KIP126.Core.SpectralSequence.HasDifferential E 3 (13,138) (16,140)
      ((Normalized.basis .sphere 13 138 1)) ((Normalized.basis .sphere 16 140 1)) := by
    have hrow := Normalized.result ⟨.sphere,.equation,3,13,138,[1],16,140,[1],"S0_AdamsE2_ss",3012⟩ (by
      unfold KIP126.Computation.Table.Raw.claims
      iterate 329 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    dsimp only [Normalized.Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change KIP126.Core.SpectralSequence.HasDifferential E 3 (13,138) (16,140) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 13 138 [1] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 16 140 [1] = true := rfl
    simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd

  obtain ⟨e,he⟩ := Normalized.basis_correct ⟨.sphere,13,138,["24,1,190,1", "3,1,335,1", "0,1,425,1", "0,4,391,1", "0,5,375,1"]⟩ (by
    unfold KIP126.Computation.Table.Raw.degrees
    iterate 209 apply List.mem_cons_of_mem
    exact List.mem_cons_self)
  change E.Page 2 (13,138) ≃ₗ[ℤ] (Fin 5 →₀ F2) at e
  change ∀ i : Fin 5, e.symm (Finsupp.single i 1) = Normalized.basis .sphere 13 138 i.val at he

  have he0 : e.symm (Finsupp.single (0:Fin 5) 1) = Normalized.basis .sphere 13 138 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 5) 1) = Normalized.basis .sphere 13 138 1 := he 1
  have he2 : e.symm (Finsupp.single (2:Fin 5) 1) = Normalized.basis .sphere 13 138 2 := he 2
  have he3 : e.symm (Finsupp.single (3:Fin 5) 1) = Normalized.basis .sphere 13 138 3 := he 3
  have he4 : e.symm (Finsupp.single (4:Fin 5) 1) = Normalized.basis .sphere 13 138 4 := he 4

  constructor
  · obtain ⟨_, a, b, ha, hb, hd⟩ := h329
    exact nCycle_of_reaches 3 (by decide) (13,138) _ ⟨a,ha⟩
  · intro x
    let P := nBoundaries 4 (13,138)
    have hb0 : Normalized.basis .sphere 13 138 0 ∈ P :=
      boundary_of_zero_representative (r:=5) (p:=(13,138))
        (differential_target_later_zero (by change (2:ℤ)≤4; omega)
          (by decide : (4:ℤ)<5) h231)
    have hb2 : Normalized.basis .sphere 13 138 2 ∈ P :=
      boundary_of_zero_representative (r:=5) (p:=(13,138))
        (differential_target_later_zero (by change (2:ℤ)≤4; omega)
          (by decide : (4:ℤ)<5) h232)
    have hb3 : Normalized.basis .sphere 13 138 3 ∈ P :=
      boundary_of_zero_representative (r:=5) (p:=(13,138))
        (differential_target_later_zero (by change (2:ℤ)≤2; omega)
          (by decide : (2:ℤ)<5) h288)
    have hb4 : Normalized.basis .sphere 13 138 4 ∈ P :=
      boundary_of_zero_representative (r:=5) (p:=(13,138))
        (differential_target_later_zero (by change (2:ℤ)≤2; omega)
          (by decide : (2:ℤ)<5) h289)
    have hif (c : F2) {a : Normalized.Page .sphere 13 138} (h : a ∈ P) :
        (if c=0 then 0 else a) ∈ P := by
      split
      · exact P.zero_mem
      · exact h
    let c : Fin 5 → F2 := e x
    have hcoef := congrArg e.symm (middle_expand (e x))
    simp only [LinearEquiv.symm_apply_apply,map_sum,map_add,Fin.sum_univ_succ,apply_ite,map_zero] at hcoef
    change x=(if c 0=0 then 0 else e.symm (Finsupp.single 0 1)) + ((if c 1=0 then 0 else e.symm (Finsupp.single 1 1)) + ((if c 2=0 then 0 else e.symm (Finsupp.single 2 1)) + ((if c 3=0 then 0 else e.symm (Finsupp.single 3 1)) + ((if c 4=0 then 0 else e.symm (Finsupp.single 4 1)) + 0)))) at hcoef
    simp only [he0,he1,he2,he3,he4,add_zero] at hcoef
    have hm := P.add_mem (hif (c 0) hb0)
      (P.add_mem (hif (c 2) hb2) (P.add_mem (hif (c 3) hb3) (hif (c 4) hb4)))
    by_cases hc : c 1=0
    · left
      change x ∈ P
      rw [hcoef]
      simpa only [hc,ite_true,zero_add] using hm
    · right
      change x - Normalized.basis .sphere 13 138 1 ∈ P
      rw [hcoef]
      simp only [hc,ite_false]
      convert hm using 1 <;> first | rfl | abel


private theorem nu9_af12_cycles_boundary :
    cycles model .sphere 2 (12,137) ≤ boundaries model .sphere 3 (12,137) := by
  intro x hx
  have hr : ReachesPage model.classical.sphere 3 (12,137) x :=
    (KIP126.ProofTools.isCycle_iff_reaches model .sphere 3 (by decide) (12,137) x).mp ⟨by decide,hx⟩
  obtain ⟨a,ha⟩ := normalized_reaches 3 (12,137) x hr
  have hd : Normalized.sphere.d 2 (12,137) (Normalized.label (12,137) x)=0 :=
    represents_d_zero_of_later (by decide : Normalized.sphere.r₀≤2) (by decide : (2:ℤ)<3)
      (middle_rep2 (by decide) ha) ⟨a,ha⟩
  have h := boundary_of_zero_representative (nu9_af12_kernel _ hd)
  change denormalize (12,137) (Normalized.label (12,137) x)∈boundaries model .sphere 3 (12,137) at h
  rwa [denormalize_label] at h

private theorem nu9_error_data :
    Subsingleton (CycleQuotient model .sphere 2 8 (12,137)) ∧
    KIP126.Computation.Table.basis .sphere 13 138 1 ∈ cycles model .sphere 2 (13,138) ∧
    ∀ x : model.classical.sphere.Page 2 (13,138),
      x∈boundaries model .sphere 9 (13,138) ∨
      x-(show model.classical.sphere.Page 2 (13,138) from KIP126.Computation.Table.basis .sphere 13 138 1)∈boundaries model .sphere 9 (13,138) := by
  constructor
  · have hz (x : CycleQuotient model .sphere 2 8 (12,137)) : x=0 := by
      obtain ⟨x,rfl⟩ := Quotient.exists_rep x
      exact (subquotientClass_eq_zero_iff _ _ _).mpr
        (boundaries_monotone model .sphere (12,137) (by decide : (3:ℤ)≤8)
          (nu9_af12_cycles_boundary x.property))
    exact ⟨fun x y => (hz x).trans (hz y).symm⟩
  obtain ⟨hc,hcosets⟩ := nu9_af13_cosets
  constructor
  · change denormalize (13,138) (Normalized.basis .sphere 13 138 1)∈cycles model .sphere 2 (13,138) at hc
    exact (denormalize_basis 13 138 1) ▸ hc
  · intro x
    rcases hcosets (Normalized.label (13,138) x) with h0|h1
    · left
      change denormalize (13,138) (Normalized.label (13,138) x)∈boundaries model .sphere 4 (13,138) at h0
      rw [denormalize_label] at h0
      exact boundaries_monotone model .sphere (13,138) (by decide : (4:ℤ)≤9) h0
    · right
      change denormalize (13,138) (Normalized.label (13,138) x-Normalized.basis .sphere 13 138 1)∈
        boundaries model .sphere 4 (13,138) at h1
      rw [map_sub,denormalize_label] at h1
      have hh : x-(show model.classical.sphere.Page 2 (13,138) from KIP126.Computation.Table.basis .sphere 13 138 1)∈
          boundaries model .sphere 4 (13,138) := (denormalize_basis 13 138 1) ▸ h1
      exact boundaries_monotone model .sphere (13,138) (by decide : (4:ℤ)≤9) hh

end
end KIP126.Main.Internal.Selected.NuError
