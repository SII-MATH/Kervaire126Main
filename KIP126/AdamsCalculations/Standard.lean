module

public import KIP126.E2Computation.Standard
import KIP126.AdamsCalculations.Table
import KIP126.Literature.Standard.FiniteQuotientNormalized
import KIP126.SpectralSequence.Computation.Morphism.Proofs
import KIP126.SpectralSequence.Computation.PageThree.Proofs
import Mathlib.GroupTheory.Index
import Mathlib.Data.Finsupp.Fintype
import KIP126.AdamsCalculations.Table.Archive
import KIP126.E2Computation.Table.Values
import KIP126.E2Computation.Table.Relations
import KIP126.AdamsSynthetic.Standard.ClassicalSupport

import KIP126.SpectralSequence.FinitePageCalculus.Proofs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Batteries.Data.String.Lemmas
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.CharP.Two
import all Init.Data.List.SplitOn.Basic
import all Init.Data.String.Legacy
import all Init.Data.String.Search
import all Init.Data.String.Slice

/-! Later Adams-page differentials, survival and boundary calculations.
The fixed classes and E₂ algebra are imported from E2Computation. -/

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

@[expose] section
namespace KIP126.Computation.Standard
open CategoryTheory KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.AdamsSynthetic.Standard
open CategoryTheory.Limits KIP126.Core.Algebra
open KIP126.Core.SpectralSequence.FinitePageCalculus KIP126.Computation.Table

universe v

private theorem page_zero_of_initial_zero
    (E : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ×ℤ))
    (r : ℤ) (hr : 2 ≤ r) (p : ℤ×ℤ) (h2 : Subsingleton (E.Page 2 p)) :
    Subsingleton (E.Page r p) := by
  have hz (a : E.Page r p) : a=0 := by
    obtain ⟨x,hx⟩ := page_has_initial_representative hr a
    rw [h2.elim x 0] at hx
    exact represents_unique hx (RepresentsOnPage.zero hr)
  exact ⟨fun a b=>(hz a).trans (hz b).symm⟩

private theorem initial_sphere_zero (s t : ℕ) (ht : t ≤ 261)
    (hdim : basisDimension s t=0) :
    Subsingleton (model.classical.sphere.Page 2 (s,t)) := by
  let e := coordinates s t ht
  have hn : archive.basisCount s t=0 := (archive_dimension s t ht).trans hdim
  haveI : Subsingleton (Fin (archive.basisCount s t) →₀ ZMod 2) := by
    rw [hn]
    infer_instance
  exact e.injective.subsingleton

private theorem no_earlier_hit_of_survival
    {E : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ×ℤ)}
    {r n : ℤ} {p : ℤ×ℤ} {x : E.Page 2 p}
    (hstart : E.r₀ ≤ r) (hr : 2 ≤ r) (hrt : r<n)
    (hsurv : SurvivesTo E n p x) : ¬ HitOnPage E r p x := by
  rintro ⟨q,hq,z,y,hy,_,hd⟩
  obtain ⟨a,ha⟩ := page_has_initial_representative hr z
  have hdiff : HasDifferential E r q p a x := ⟨hq,z,y,ha,hy,hd⟩
  have hz := differential_target_later_zero hstart hrt hdiff
  obtain ⟨b,hb,hbn⟩ := hsurv
  exact hbn (represents_unique hb hz)

private theorem one_basis_kernel_zero
    {A : Type v} {B : Type v} [AddCommGroup A] [Module ℤ A]
    [AddCommGroup B] [Module ℤ B]
    (e : A ≃ₗ[ℤ] (Fin 1 →₀ F2)) (δ : A →ₗ[ℤ] B)
    (hne : δ (e.symm (Finsupp.single 0 1))≠0) :
    ∀ x, δ x=0 → x=0 := by
  classical
  intro x hx
  have hex := finite_basis_expansion e x
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero] at hex
  change x=(if e x 0=0 then 0 else e.symm (Finsupp.single 0 1)) at hex
  by_cases h : e x 0=0
  · simpa only [h,ite_true] using hex
  · have xx : x=e.symm (Finsupp.single 0 1) := by simpa only [h,ite_false] using hex
    exact (hne (xx ▸ hx)).elim

private theorem later_d_zero_of_second_kernel_zero
    {E : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ×ℤ)}
    (hs : E.r₀≤2) {p : ℤ×ℤ} {r : ℤ} (hr : 3≤r)
    (hker : ∀ x : E.Page 2 p, E.d 2 p x=0 → x=0) : E.d r p=0 := by
  apply d_zero_of_second_kernel_extends hs hr
  intro x hx
  rw [hker x hx]
  exact ⟨0,RepresentsOnPage.zero (by omega)⟩

public theorem w_to_e6 : SurvivesTo model.classical.sphere 6 (8,134) W := by
  classical
  let E := model.classical.sphere
  have hs2 : E.r₀≤2 := by
    change model.classical.sphere.r₀≤2
    rw [model.classical.firstPage]
  have h152 : ReachesPage E 14 (3,130) (basis .sphere 3 130 0) := by
    have hrow := result ⟨.sphere, .reaches, 14, 3, 130, [0], 3, 130, [], "S0_AdamsE2_ss", 2438⟩ (by
      exact List.mem_of_getElem? (i := 152) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,h⟩ := hrow
    have vx : Raw.coordinatesValid Raw.degrees .sphere 3 130 [0]=true := rfl
    simp only [decode,vx,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      add_zero,Option.some.injEq] at ha
    rw [←ha] at h
    exact h
  have h153 : HasDifferential E 2 (3,130) (5,131)
      (basis .sphere 3 130 1) (basis .sphere 5 131 0) := by
    have hrow := result ⟨.sphere, .equation, 2, 3, 130, [1], 5, 131, [0], "S0_AdamsE2_ss", 2439⟩ (by
      exact List.mem_of_getElem? (i := 153) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 2 (3,130) (5,131) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 3 130 [1]=true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 5 131 [0]=true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    exact h
  have h158 : HasDifferential E 2 (4,131) (6,132)
      (basis .sphere 4 131 0) (basis .sphere 6 132 1) := by
    have hrow := result ⟨.sphere, .equation, 2, 4, 131, [0], 6, 132, [1], "S0_AdamsE2_ss", 2495⟩ (by
      exact List.mem_of_getElem? (i := 158) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 2 (4,131) (6,132) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 4 131 [0]=true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 6 132 [1]=true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    exact h
  have h165 : HasDifferential E 2 (5,132) (7,133)
      (basis .sphere 5 132 0) (basis .sphere 7 133 1) := by
    have hrow := result ⟨.sphere, .equation, 2, 5, 132, [0], 7, 133, [1], "S0_AdamsE2_ss", 2575⟩ (by
      exact List.mem_of_getElem? (i := 165) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 2 (5,132) (7,133) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 5 132 [0]=true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 7 133 [1]=true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    exact h
  have h175 : ReachesPage E 4 (6,133) (basis .sphere 6 133 0) := by
    have hrow := result ⟨.sphere, .reaches, 4, 6, 133, [0], 6, 133, [], "S0_AdamsE2_ss", 2633⟩ (by
      exact List.mem_of_getElem? (i := 175) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,h⟩ := hrow
    have vx : Raw.coordinatesValid Raw.degrees .sphere 6 133 [0]=true := rfl
    simp only [decode,vx,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      add_zero,Option.some.injEq] at ha
    rw [←ha] at h
    exact h
  have h176 : HasDifferential E 2 (6,133) (8,134)
      (basis .sphere 6 133 1) (basis .sphere 8 134 5) := by
    have hrow := result ⟨.sphere, .equation, 2, 6, 133, [1], 8, 134, [5], "S0_AdamsE2_ss", 2634⟩ (by
      exact List.mem_of_getElem? (i := 176) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 2 (6,133) (8,134) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 6 133 [1]=true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 8 134 [5]=true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    exact h
  have h204 : ReachesPage E 6 (8,134) (basis .sphere 8 134 0 + basis .sphere 8 134 3) := by
    have hrow := result ⟨.sphere, .reaches, 6, 8, 134, [0, 3], 8, 134, [], "S0_AdamsE2_ss", 2702⟩ (by
      exact List.mem_of_getElem? (i := 204) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,h⟩ := hrow
    have vx : Raw.coordinatesValid Raw.degrees .sphere 8 134 [0, 3]=true := rfl
    simp only [decode,vx,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      add_zero,Option.some.injEq] at ha
    rw [←ha] at h
    exact h
  obtain ⟨g,hg⟩ := basis_correct ⟨.sphere, 8, 134, ["395,1", "394,1", "393,1", "392,1", "69,1,85,1", "0,6,69,2"]⟩ (by
    exact List.mem_of_getElem? (i := 162) (by rfl))
  change E.Page 2 (8,134) ≃ₗ[ℤ] (Fin 6 →₀ F2) at g
  change ∀ i : Fin 6, g.symm (Finsupp.single i 1)=basis .sphere 8 134 i.val at hg
  obtain ⟨e,he⟩ := basis_correct ⟨.sphere, 6, 133, ["377,1", "0,5,324,1"]⟩ (by
    exact List.mem_of_getElem? (i := 139) (by rfl))
  change E.Page 2 (6,133) ≃ₗ[ℤ] (Fin 2 →₀ F2) at e
  change ∀ i : Fin 2, e.symm (Finsupp.single i 1)=basis .sphere 6 133 i.val at he
  obtain ⟨f3,hf3⟩ := basis_correct ⟨.sphere, 5, 132, ["0,4,324,1"]⟩ (by
    exact List.mem_of_getElem? (i := 128) (by rfl))
  change E.Page 2 (5,132) ≃ₗ[ℤ] (Fin 1 →₀ F2) at f3
  change ∀ i : Fin 1, f3.symm (Finsupp.single i 1)=basis .sphere 5 132 i.val at hf3
  obtain ⟨f4,hf4⟩ := basis_correct ⟨.sphere, 4, 131, ["0,3,324,1"]⟩ (by
    exact List.mem_of_getElem? (i := 120) (by rfl))
  change E.Page 2 (4,131) ≃ₗ[ℤ] (Fin 1 →₀ F2) at f4
  change ∀ i : Fin 1, f4.symm (Finsupp.single i 1)=basis .sphere 4 131 i.val at hf4
  obtain ⟨f5,hf5⟩ := basis_correct ⟨.sphere, 3, 130, ["1,1,69,2", "0,2,324,1"]⟩ (by
    exact List.mem_of_getElem? (i := 109) (by rfl))
  change E.Page 2 (3,130) ≃ₗ[ℤ] (Fin 2 →₀ F2) at f5
  change ∀ i : Fin 2, f5.symm (Finsupp.single i 1)=basis .sphere 3 130 i.val at hf5
  obtain ⟨q3,hq3⟩ := basis_correct ⟨.sphere, 7, 133, ["1,1,69,1,76,1", "0,5,69,2"]⟩ (by
    exact List.mem_of_getElem? (i := 150) (by rfl))
  change E.Page 2 (7,133) ≃ₗ[ℤ] (Fin 2 →₀ F2) at q3
  change ∀ i : Fin 2, q3.symm (Finsupp.single i 1)=basis .sphere 7 133 i.val at hq3
  obtain ⟨q4,hq4⟩ := basis_correct ⟨.sphere, 6, 132, ["368,1", "0,4,69,2"]⟩ (by
    exact List.mem_of_getElem? (i := 138) (by rfl))
  change E.Page 2 (6,132) ≃ₗ[ℤ] (Fin 2 →₀ F2) at q4
  change ∀ i : Fin 2, q4.symm (Finsupp.single i 1)=basis .sphere 6 132 i.val at hq4
  obtain ⟨q5,hq5⟩ := basis_correct ⟨.sphere, 5, 131, ["0,3,69,2"]⟩ (by
    exact List.mem_of_getElem? (i := 127) (by rfl))
  change E.Page 2 (5,131) ≃ₗ[ℤ] (Fin 1 →₀ F2) at q5
  change ∀ i : Fin 1, q5.symm (Finsupp.single i 1)=basis .sphere 5 131 i.val at hq5
  have Wb : W=basis .sphere 8 134 0+basis .sphere 8 134 3 := by
    have v0 := basis_value ⟨.named .x_126_8_4,0⟩ (by decide)
    have v3 := basis_value ⟨.named .x_126_8,3⟩ (by decide)
    change basis .sphere 8 134 0=atom .x_126_8_4 at v0
    change basis .sphere 8 134 3=atom .x_126_8 at v3
    dsimp only [W]
    rw [←v0,←v3]
  have gb (i : Fin 6) : g (basis .sphere 8 134 i.val)=Finsupp.single i 1 := by
    rw [←hg i,LinearEquiv.apply_symm_apply]
  have gb0 : g (basis .sphere 8 134 0)=Finsupp.single (0 : Fin 6) 1 := gb 0
  have gb3 : g (basis .sphere 8 134 3)=Finsupp.single (3 : Fin 6) 1 := gb 3
  have gb5 : g (basis .sphere 8 134 5)=Finsupp.single (5 : Fin 6) 1 := gb 5
  have coordW : g W 0=1 := by
    rw [Wb,map_add,gb0,gb3]
    norm_num [Finsupp.single_apply,Fin.ext_iff]
  have coord5 : g (basis .sphere 8 134 5) 0=0 := by
    rw [gb5]
    norm_num [Finsupp.single_apply,Fin.ext_iff]
  have hw6 : ReachesPage E 6 (8,134) W := by rw [Wb];exact h204
  obtain ⟨w6,hw6⟩ := hw6
  obtain ⟨w3,hw3⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤6) hw6
  obtain ⟨w4,hw4⟩ := represents_before (by decide : (2:ℤ)≤4) (by decide : (4:ℤ)≤6) hw6
  obtain ⟨w5,hw5⟩ := represents_before (by decide : (2:ℤ)≤5) (by decide : (5:ℤ)≤6) hw6
  let δ : E.Page 2 (6,133) ⟶ E.Page 2 (8,134) :=
    E.d 2 (6,133) ≫ eqToHom (congrArg (E.Page 2) h176.target_degree)
  have d0 : δ (basis .sphere 6 133 0)=0 := by
    have hd := represents_d_zero_of_later hs2 (by decide : (2:ℤ)<4)
      (represents_two_self _) h175
    change (E.d 2 (6,133) ≫ _) _=0
    rw [ModuleCat.comp_apply,hd,map_zero]
  have d1 : δ (basis .sphere 6 133 1)=basis .sphere 8 134 5 := h176.eq_on_page_two.2
  have δbit (b : F2) (a : E.Page 2 (6,133)) :
      δ (if b=0 then 0 else a)=if b=0 then 0 else δ a := by
    by_cases hb : b=0 <;> simp only [hb,ite_true,ite_false,map_zero]
  have incoming (x : E.Page 2 (6,133)) : g (δ x) 0=0 := by
    have hx := finite_basis_expansion e x
    simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,he,add_zero] at hx
    change x=(if e x 0=0 then 0 else basis .sphere 6 133 0)+
      (if e x 1=0 then 0 else basis .sphere 6 133 1) at hx
    have hh := congrArg δ hx
    simp only [map_add,δbit,d0,d1,ite_self,zero_add] at hh
    rw [hh]
    by_cases h : e x 1=0
    · simp only [h,ite_true,map_zero,Finsupp.zero_apply]
    · simpa only [h,ite_false] using coord5
  have w3ne : w3≠0 := by
    apply represents_next_nonzero_of_not_incoming_at h176.target_degree hs2 (by decide)
      hw3 (represents_two_self W)
    intro x hx
    have hh := congrArg (fun a=>g a 0) hx
    exact zero_ne_one ((incoming x).symm.trans (hh.trans coordW))
  have q3ne : basis .sphere 7 133 1≠0 := by
    have hq31 : q3.symm (Finsupp.single (1 : Fin 2) 1)=basis .sphere 7 133 1 := hq3 1
    rw [←hq31]
    exact basis_vector_ne_zero q3 1
  have q4ne : basis .sphere 6 132 1≠0 := by
    have hq41 : q4.symm (Finsupp.single (1 : Fin 2) 1)=basis .sphere 6 132 1 := hq4 1
    rw [←hq41]
    exact basis_vector_ne_zero q4 1
  have q5ne : basis .sphere 5 131 0≠0 := by
    have hq50 : q5.symm (Finsupp.single (0 : Fin 1) 1)=basis .sphere 5 131 0 := hq5 0
    rw [←hq50]
    exact basis_vector_ne_zero q5 0
  have d3bne : E.d 2 (5,132) (f3.symm (Finsupp.single 0 1))≠0 := by
    have hf30 : f3.symm (Finsupp.single (0 : Fin 1) 1)=basis .sphere 5 132 0 := hf3 0
    rw [hf30]
    intro hx
    have hh := h165.eq_on_page_two.2
    rw [ModuleCat.comp_apply,hx,map_zero] at hh
    exact q3ne hh.symm
  have d4bne : E.d 2 (4,131) (f4.symm (Finsupp.single 0 1))≠0 := by
    have hf40 : f4.symm (Finsupp.single (0 : Fin 1) 1)=basis .sphere 4 131 0 := hf4 0
    rw [hf40]
    intro hx
    have hh := h158.eq_on_page_two.2
    rw [ModuleCat.comp_apply,hx,map_zero] at hh
    exact q4ne hh.symm
  have hin3 : E.d 3 (5,132)=0 :=
    later_d_zero_of_second_kernel_zero hs2 (by decide)
      (one_basis_kernel_zero f3 (E.d 2 (5,132)).hom d3bne)
  have hin4 : E.d 4 (4,131)=0 :=
    later_d_zero_of_second_kernel_zero hs2 (by decide)
      (one_basis_kernel_zero f4 (E.d 2 (4,131)).hom d4bne)
  have d50 : E.d 2 (3,130) (basis .sphere 3 130 0)=0 :=
    represents_d_zero_of_later hs2 (by decide : (2:ℤ)<14) (represents_two_self _) h152
  have d51ne : E.d 2 (3,130) (basis .sphere 3 130 1)≠0 := by
    intro hx
    have hh := h153.eq_on_page_two.2
    rw [ModuleCat.comp_apply,hx,map_zero] at hh
    exact q5ne hh.symm
  have d5bit (b : F2) (a : E.Page 2 (3,130)) :
      E.d 2 (3,130) (if b=0 then 0 else a)=if b=0 then 0 else E.d 2 (3,130) a := by
    by_cases hb : b=0 <;> simp only [hb,ite_true,ite_false,map_zero]
  have hin5 : E.d 5 (3,130)=0 := by
    apply d_zero_of_second_kernel_extends hs2 (by decide : (3:ℤ)≤5)
    intro x hx
    have hex := finite_basis_expansion f5 x
    simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,hf5,add_zero] at hex
    change x=(if f5 x 0=0 then 0 else basis .sphere 3 130 0)+
      (if f5 x 1=0 then 0 else basis .sphere 3 130 1) at hex
    have hd := congrArg (E.d 2 (3,130)) hex
    simp only [map_add,d5bit,d50,ite_self,zero_add] at hd
    have h1 : f5 x 1=0 := by
      by_contra hh
      apply d51ne
      simpa only [hx,hh,ite_false] using hd.symm
    have xx : x=(if f5 x 0=0 then 0 else basis .sphere 3 130 0) := by
      simpa only [h1,ite_true,add_zero] using hex
    obtain ⟨a,ha⟩ := reaches_before (by decide : (2:ℤ)≤6) (by decide : (6:ℤ)≤14) h152
    have rep := represents_bit (f5 x 0) ha
    rw [←xx] at rep
    exact ⟨_,rep⟩
  have deg3 : (5,132)+E.diffDeg 3=(8,134) := by
    simp only [E,Classical.Adams.ClassicalAdamsFamily.sphere,Classical.Adams.ClassicalAdamsFamily.obj,
      model.classical.differentialDegree,Prod.mk_add_mk,Int.reduceAdd,Int.reduceSub]
  have deg4 : (4,131)+E.diffDeg 4=(8,134) := by
    simp only [E,Classical.Adams.ClassicalAdamsFamily.sphere,Classical.Adams.ClassicalAdamsFamily.obj,
      model.classical.differentialDegree,Prod.mk_add_mk,Int.reduceAdd,Int.reduceSub]
  have deg5 : (3,130)+E.diffDeg 5=(8,134) := by
    simp only [E,Classical.Adams.ClassicalAdamsFamily.sphere,Classical.Adams.ClassicalAdamsFamily.obj,
      model.classical.differentialDegree,Prod.mk_add_mk,Int.reduceAdd,Int.reduceSub]
  have w4ne : w4≠0 := represents_next_nonzero_of_incoming_zero_at
    (hs2.trans (by decide : (2:ℤ)≤3)) (by decide) hin3 hw4 hw3 w3ne deg3
  have w5ne : w5≠0 := represents_next_nonzero_of_incoming_zero_at
    (hs2.trans (by decide : (2:ℤ)≤4)) (by decide) hin4 hw5 hw4 w4ne deg4
  have w6ne : w6≠0 := represents_next_nonzero_of_incoming_zero_at
    (hs2.trans (by decide : (2:ℤ)≤5)) (by decide) hin5 hw6 hw5 w5ne deg5
  exact ⟨w6,hw6,w6ne⟩

/-- The archived continuation reaches E₁₀₀₀; the positive-stem Adams
vanishing line forces every later outgoing target to vanish. -/
public theorem t_permanent_cycle : IsPermanentCycle model.classical.sphere (14,139) T := by
  let E := model.classical.sphere
  have hreach : ReachesPage E 1000 (14,139) T := by
    have hrow := result
      ⟨.sphere,.reaches,1000,14,139,[1],14,139,[],"S0_AdamsE2_ss",3080⟩ (by
        exact List.mem_of_getElem? (i := 342) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨x,hx,h⟩ := hrow
    have vx : Raw.coordinatesValid Raw.degrees .sphere 14 139 [1]=true := rfl
    simp only [decode,vx,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      add_zero,Option.some.injEq] at hx
    rw [←hx,basis_T] at h
    exact h
  apply isPermanentCycle_of_reachesPage E 1000
    (by change model.classical.sphere.r₀ ≤ 1000; rw [model.classical.firstPage]; omega)
    (14,139) T hreach
  intro r hr
  have hdeg : (14,139)+E.diffDeg r=(14+r,138+r) := by
    simp only [E,ClassicalAdamsFamily.sphere,ClassicalAdamsFamily.obj,
      model.classical.differentialDegree,Prod.mk_add_mk]
    congr 1; omega
  have h2 : Subsingleton (E.Page 2 ((14,139)+E.diffDeg r)) := by
    rw [hdeg]
    exact KIP126.Literature.Standard.sphereVanishing (14+r) (138+r) (by omega) (by omega)
  have hz := page_zero_of_initial_zero E r (by omega) _ h2
  ext a
  exact hz.elim _ _


/- Fixed U: complete incoming basis frames through page five, and one common
infinite representative from the original reach-1000 row and actual vanishing. -/
section ArchiveUPermanenceConstruction
private theorem uPermanentPageZero
    (E : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ×ℤ))
    (r : ℤ) (hr : 2 ≤ r) (p : ℤ×ℤ) (h2 : Subsingleton (E.Page 2 p)) :
    Subsingleton (E.Page r p) := by
  have hz (a : E.Page r p) : a=0 := by
    obtain ⟨x,hx⟩ := page_has_initial_representative hr a
    rw [h2.elim x 0] at hx
    exact represents_unique hx (RepresentsOnPage.zero hr)
  exact ⟨fun a b=>(hz a).trans (hz b).symm⟩

private theorem uPermanentInitialZero (s t : ℕ) (ht : t ≤ 261)
    (hdim : basisDimension s t=0) :
    Subsingleton (model.classical.sphere.Page 2 (s,t)) := by
  let e := coordinates s t ht
  have hn : archive.basisCount s t=0 := (archive_dimension s t ht).trans hdim
  haveI : Subsingleton (Fin (archive.basisCount s t) →₀ ZMod 2) := by
    rw [hn]
    infer_instance
  exact e.injective.subsingleton

private theorem uPermanentNonzeroOfPermanentFinite
    (E : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ))
    (N : ℤ) (hN : E.r₀ ≤ N) (p : ℤ × ℤ) (x : E.Page 2 p)
    (hperm : IsPermanentCycle E p x) (hsurv : SurvivesTo E N p x)
    (hin : ∀ r : ℤ, N ≤ r → E.d r (p-E.diffDeg r)=0) :
    NonzeroSurvival E p x := by
  let D := E.ssData p
  let n₂ : WithTop ℕ := ↑(2-E.r₀).toNat
  let n : WithTop ℕ := ↑(N-E.r₀).toNat
  obtain ⟨z,hz⟩ := hperm
  obtain ⟨a,ha,hane⟩ := hsurv
  let zN := Subobject.ofLE (D.Z ⊤) (D.Z n) (D.Z_anti le_top) z
  have hrep : RepresentsOnPage E N p x (D.pageπ n zN) := by
    refine ⟨ha.1,zN,?_,rfl⟩
    dsimp only [zN]
    rw [← CategoryTheory.comp_apply, ← Category.assoc, Subobject.ofLE_comp_ofLE]
    exact hz
  refine ⟨z,hz,?_⟩
  intro hz0
  apply hane
  rw [represents_unique ha hrep]
  have hB : D.B ⊤ = D.B n := boundaries_top_eq_of_d_eq_zero E N hN p hin
  have hb := (subobject_cokernel_π_eq_zero_iff (D.B ⊤) (D.Z ⊤) (D.B_le_Z ⊤) z).mp hz0
  apply (subobject_cokernel_π_eq_zero_iff (D.B n) (D.Z n) (D.B_le_Z n) zN).mpr
  change (Subobject.ofLE (D.Z ⊤) (D.Z n) (D.Z_anti le_top) ≫ (D.Z n).arrow) z ∈ _
  rw [Subobject.ofLE_arrow]
  rwa [← hB]

private theorem uPermanentD157 : HasDifferential model.classical.sphere 3 (4,130) (7,132)
    (basis .sphere 4 130 0) (basis .sphere 7 132 0) := by
  have hrow := result ⟨.sphere, .equation, 3, 4, 130, [0], 7, 132, [0], "S0_AdamsE2_ss", 2437⟩ (by
    exact List.mem_of_getElem? (i := 157) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential model.classical.sphere 3 (4,130) (7,132) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 4 130 [0]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 7 132 [0]=true := rfl
  delta decode at ha hb
  simp (config := { congrConsts := false }) only [vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem uPermanentD163 : HasDifferential model.classical.sphere 2 (5,130) (7,131)
    (basis .sphere 5 130 0) (basis .sphere 7 131 2) := by
  have hrow := result ⟨.sphere, .equation, 2, 5, 130, [0], 7, 131, [2], "S0_AdamsE2_ss", 2435⟩ (by
    exact List.mem_of_getElem? (i := 163) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential model.classical.sphere 2 (5,130) (7,131) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 5 130 [0]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 7 131 [2]=true := rfl
  delta decode at ha hb
  simp (config := { congrConsts := false }) only [vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem uPermanentD171 : HasDifferential model.classical.sphere 4 (6,131) (10,134)
    (basis .sphere 6 131 0) (basis .sphere 10 134 0 + basis .sphere 10 134 3) := by
  have hrow := result ⟨.sphere, .equation, 4, 6, 131, [0], 10, 134, [0, 3], "S0_AdamsE2_ss", 2492⟩ (by
    exact List.mem_of_getElem? (i := 171) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential model.classical.sphere 4 (6,131) (10,134) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 6 131 [0]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 10 134 [0, 3]=true := rfl
  delta decode at ha hb
  simp (config := { congrConsts := false }) only [vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem uPermanentD172 : HasDifferential model.classical.sphere 4 (6,131) (10,134)
    (basis .sphere 6 131 1) (basis .sphere 10 134 0 + basis .sphere 10 134 1 + basis .sphere 10 134 3 + basis .sphere 10 134 4) := by
  have hrow := result ⟨.sphere, .equation, 4, 6, 131, [1], 10, 134, [0, 1, 3, 4], "S0_AdamsE2_ss", 2493⟩ (by
    exact List.mem_of_getElem? (i := 172) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential model.classical.sphere 4 (6,131) (10,134) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 6 131 [1]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 10 134 [0, 1, 3, 4]=true := rfl
  delta decode at ha hb
  simp (config := { congrConsts := false }) only [vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem uPermanentD200 : HasDifferential model.classical.sphere 3 (8,133) (11,135)
    (basis .sphere 8 133 0) (basis .sphere 11 135 0) := by
  have hrow := result ⟨.sphere, .equation, 3, 8, 133, [0], 11, 135, [0], "S0_AdamsE2_ss", 2629⟩ (by
    exact List.mem_of_getElem? (i := 200) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential model.classical.sphere 3 (8,133) (11,135) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 133 [0]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 11 135 [0]=true := rfl
  delta decode at ha hb
  simp (config := { congrConsts := false }) only [vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem uPermanentD201 : HasDifferential model.classical.sphere 2 (8,133) (10,134)
    (basis .sphere 8 133 1) (basis .sphere 10 134 2 + basis .sphere 10 134 4) := by
  have hrow := result ⟨.sphere, .equation, 2, 8, 133, [1], 10, 134, [2, 4], "S0_AdamsE2_ss", 2630⟩ (by
    exact List.mem_of_getElem? (i := 201) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential model.classical.sphere 2 (8,133) (10,134) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 133 [1]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 10 134 [2, 4]=true := rfl
  delta decode at ha hb
  simp (config := { congrConsts := false }) only [vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem uPermanentReaches1000 : ReachesPage model.classical.sphere 1000 (10,134) U := by
  have hrow := result ⟨.sphere, .reaches, 1000, 10, 134, [4], 10, 134, [], "S0_AdamsE2_ss", 2693⟩ (by
    exact List.mem_of_getElem? (i := 249) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,h⟩ := hrow
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 134 [4]=true := rfl
  delta decode at ha
  simp (config := { congrConsts := false }) only [vx,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha
  rw [←ha,basis_U] at h
  exact h

private theorem uPermanentIncomingThreeZero : model.classical.sphere.d 3 (7,132)=0 := by
  obtain ⟨a,ha,hda⟩ := differential_target_cycle uPermanentD157
  obtain ⟨e,he⟩ := basis_correct ⟨.sphere,7,132,["0,2,340,1"]⟩ (by
    exact List.mem_of_getElem? (i := 149) (by rfl))
  change model.classical.sphere.Page 2 (7,132) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e
  change ∀ i : Fin 1, e.symm (Finsupp.single i 1)=basis .sphere 7 132 i.val at he
  apply d_zero_of_complete_representatives (by decide : (2:ℤ)≤3) e
  intro i
  have hi : i=0 := Subsingleton.elim _ _
  subst i
  refine ⟨a,?_,hda⟩
  rw [he]
  exact ha

private noncomputable def uPermanentFunctional
    (e : model.classical.sphere.Page 2 (10,134) ≃ₗ[ℤ] (Fin 5 →₀ F2)) :
    model.classical.sphere.Page 2 (10,134) →ₗ[ℤ] F2 where
  toFun x := e x 1 + e x 2 + e x 4
  map_add' := by
    intro x y
    simp only [map_add,Finsupp.add_apply]
    abel
  map_smul' := by
    intro n x
    simp only [map_smul,Finsupp.smul_apply,smul_add,RingHom.id_apply]

private theorem uPermanentSurvivesFive : SurvivesTo model.classical.sphere 5 (10,134) U := by
  classical
  let E := model.classical.sphere
  have hs2 : E.r₀≤2 := by
    change model.classical.sphere.r₀≤2
    rw [model.classical.firstPage]
  obtain ⟨u5,hu5⟩ := reaches_before (by decide : (2:ℤ)≤5) (by decide : (5:ℤ)≤1000)
    uPermanentReaches1000
  obtain ⟨u4,hu4⟩ := represents_before (by decide : (2:ℤ)≤4) (by decide : (4:ℤ)≤5) hu5
  obtain ⟨u3,hu3⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤4) hu4
  obtain ⟨e,he⟩ := basis_correct ⟨.sphere,10,134,["389,1", "388,1", "1,1,366,1", "0,1,373,1", "0,2,367,1"]⟩ (by
    exact List.mem_of_getElem? (i := 181) (by rfl))
  change E.Page 2 (10,134) ≃ₗ[ℤ] (Fin 5 →₀ F2) at e
  change ∀ i : Fin 5, e.symm (Finsupp.single i 1)=basis .sphere 10 134 i.val at he
  let L := uPermanentFunctional e
  have ev (i : Fin 5) : e (basis .sphere 10 134 i.val)=Finsupp.single i 1 := by
    rw [←he i,LinearEquiv.apply_symm_apply]
  have Lv (i : Fin 5) : L (basis .sphere 10 134 i.val)=
      (Finsupp.single i (1:F2)) 1+(Finsupp.single i (1:F2)) 2+(Finsupp.single i (1:F2)) 4 := by
    change e (basis .sphere 10 134 i.val) 1+e (basis .sphere 10 134 i.val) 2+
      e (basis .sphere 10 134 i.val) 4=_
    rw [ev]
  have L0 : L (basis .sphere 10 134 0)=0 := by
    simpa [Finsupp.single_apply] using Lv 0
  have L1 : L (basis .sphere 10 134 1)=1 := by
    simpa [Finsupp.single_apply] using Lv 1
  have L2 : L (basis .sphere 10 134 2)=1 := by
    simpa [Finsupp.single_apply] using Lv 2
  have L3 : L (basis .sphere 10 134 3)=0 := by
    simpa [Finsupp.single_apply] using Lv 3
  have L4 : L (basis .sphere 10 134 4)=1 := by
    simpa [Finsupp.single_apply] using Lv 4
  have LU : L U=1 := by rw [←basis_U]; exact L4
  have deg2 : (8,133)+E.diffDeg 2=(10,134) := by
    simp only [E,ClassicalAdamsFamily.sphere,ClassicalAdamsFamily.obj,
      model.classical.differentialDegree,Prod.mk_add_mk,Int.reduceAdd,Int.reduceSub]
  let d2 : E.Page 2 (8,133) ⟶ E.Page 2 (10,134) :=
    E.d 2 (8,133) ≫ eqToHom (congrArg (E.Page 2) deg2)
  obtain ⟨_,a3,_,ha3,_,_⟩ := uPermanentD200
  have d20 : d2 (basis .sphere 8 133 0)=0 := by
    have hh : E.d 2 (8,133) (basis .sphere 8 133 0)=0 :=
      represents_d_zero_of_later hs2 (by decide) (represents_two_self _) ⟨a3,ha3⟩
    change (eqToHom (congrArg (E.Page 2) deg2)) (E.d 2 (8,133) (basis .sphere 8 133 0))=0
    rw [hh,map_zero]
  have d21 : d2 (basis .sphere 8 133 1)=basis .sphere 10 134 2+basis .sphere 10 134 4 :=
    uPermanentD201.eq_on_page_two.choose_spec
  obtain ⟨f,hf⟩ := basis_correct ⟨.sphere,8,133,["376,1", "375,1"]⟩ (by
    exact List.mem_of_getElem? (i := 161) (by rfl))
  change E.Page 2 (8,133) ≃ₗ[ℤ] (Fin 2 →₀ F2) at f
  change ∀ i : Fin 2, f.symm (Finsupp.single i 1)=basis .sphere 8 133 i.val at hf
  have each0 (i : Fin 2) : L (d2 (f.symm (Finsupp.single i 1)))=0 := by
    rw [hf i]
    fin_cases i
    · rw [d20,map_zero]
    · rw [d21,map_add,L2,L4]
      rfl
  have image0 (v : E.Page 2 (8,133)) : L (d2 v)=0 := by
    rw [finite_basis_expansion f v]
    simp only [map_sum]
    apply Finset.sum_eq_zero
    intro i hi
    by_cases hc : f v i=0
    · simp only [hc,ite_true,map_zero]
    · simp only [hc,ite_false]
      exact each0 i
  have avoid2 (x : E.Page 2 (10,134)) (hx : L x=1) (v : E.Page 2 (8,133)) : d2 v≠x := by
    intro h
    have hh := congrArg L h
    rw [image0,hx] at hh
    exact zero_ne_one hh
  have marked3 (x : E.Page 2 (10,134)) {x3 : E.Page 3 (10,134)}
      (hx3 : RepresentsOnPage E 3 (10,134) x x3) (hx : L x=1) : x3≠0 :=
    represents_next_nonzero_of_not_incoming_at deg2 hs2 (by decide)
      hx3 (represents_two_self x) (avoid2 x hx)
  have deg3 : (7,132)+E.diffDeg 3=(10,134) := by
    simp only [E,ClassicalAdamsFamily.sphere,ClassicalAdamsFamily.obj,
      model.classical.differentialDegree,Prod.mk_add_mk,Int.reduceAdd,Int.reduceSub]
  have marked4 (x : E.Page 2 (10,134)) {x3 : E.Page 3 (10,134)} {x4 : E.Page 4 (10,134)}
      (hx4 : RepresentsOnPage E 4 (10,134) x x4)
      (hx3 : RepresentsOnPage E 3 (10,134) x x3) (hx : L x=1) : x4≠0 :=
    represents_next_nonzero_of_incoming_zero_at (hs2.trans (by decide : (2:ℤ)≤3)) (by decide)
      uPermanentIncomingThreeZero hx4 hx3 (marked3 x hx3 hx) deg3
  obtain ⟨deg4,a0,c0,ha0,hc0,hd0⟩ := uPermanentD171
  obtain ⟨_,a1,c1,ha1,hc1,hd1⟩ := uPermanentD172
  obtain ⟨c03,hc03⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤4) hc0
  obtain ⟨c13,hc13⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤4) hc1
  let c0init : E.Page 2 (10,134) := basis .sphere 10 134 0+basis .sphere 10 134 3
  let c1init : E.Page 2 (10,134) := basis .sphere 10 134 0+basis .sphere 10 134 1+
    basis .sphere 10 134 3+basis .sphere 10 134 4
  have Lc0 : L c0init=0 := by
    dsimp only [c0init]
    rw [map_add,L0,L3,add_zero]
  have Lc1 : L c1init=0 := by
    dsimp only [c1init]
    rw [map_add,map_add,map_add,L0,L1,L3,L4]
    rfl
  have u4ne : u4≠0 := marked4 U hu4 hu3 LU
  have diff0 : u4-c0≠0 := marked4 (U-c0init) (represents_sub hu4 hc0) (represents_sub hu3 hc03)
    (by rw [map_sub,LU,Lc0,sub_zero])
  have diff1 : u4-c1≠0 := marked4 (U-c1init) (represents_sub hu4 hc1) (represents_sub hu3 hc13)
    (by rw [map_sub,LU,Lc1,sub_zero])
  have diff01 : u4-(c0+c1)≠0 := marked4 (U-(c0init+c1init))
    (represents_sub hu4 (represents_add_tail hc0 hc1))
    (represents_sub hu3 (represents_add_tail hc03 hc13))
    (by rw [map_sub,map_add,LU,Lc0,Lc1,add_zero,sub_zero])
  obtain ⟨g,hg⟩ := basis_correct ⟨.sphere,6,131,["69,1,76,1", "0,1,340,1"]⟩ (by
    exact List.mem_of_getElem? (i := 137) (by rfl))
  change E.Page 2 (6,131) ≃ₗ[ℤ] (Fin 2 →₀ F2) at g
  change ∀ i : Fin 2, g.symm (Finsupp.single i 1)=basis .sphere 6 131 i.val at hg
  have ga0 : RepresentsOnPage E 4 (6,131) (g.symm (Finsupp.single 0 1)) a0 := by rw [hg]; exact ha0
  have ga1 : RepresentsOnPage E 4 (6,131) (g.symm (Finsupp.single 1 1)) a1 := by rw [hg]; exact ha1
  have avoid4 (v : E.Page 4 (6,131)) :
      (E.d 4 (6,131) ≫ eqToHom (congrArg (E.Page 4) deg4)) v≠u4 := by
    rcases generated_two (by decide : (2:ℤ)≤4) g a0 a1 ga0 ga1 v with h|h|h|h
    · rw [h,map_zero]
      exact Ne.symm u4ne
    · rw [h,hd0]
      intro hh
      exact diff0 (sub_eq_zero.mpr hh.symm)
    · rw [h,hd1]
      intro hh
      exact diff1 (sub_eq_zero.mpr hh.symm)
    · rw [h,map_add,hd0,hd1]
      intro hh
      exact diff01 (sub_eq_zero.mpr hh.symm)
  exact ⟨u5,hu5,represents_next_nonzero_of_not_incoming_at deg4
    (hs2.trans (by decide : (2:ℤ)≤4)) (by decide) hu5 hu4 avoid4⟩

private theorem uPermanentSourceE3Zero :
    Subsingleton (model.classical.sphere.Page 3 (5,130)) := by
  classical
  let E := model.classical.sphere
  have hs2 : E.r₀≤2 := by
    change model.classical.sphere.r₀≤2
    rw [model.classical.firstPage]
  obtain ⟨e,he⟩ := basis_correct ⟨.sphere,7,131,["353,1", "69,1,75,1", "0,1,339,1"]⟩ (by
    exact List.mem_of_getElem? (i := 148) (by rfl))
  change E.Page 2 (7,131) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e
  change ∀ i : Fin 3, e.symm (Finsupp.single i 1)=basis .sphere 7 131 i.val at he
  have targetne : basis .sphere 7 131 2≠0 := by
    have he2 : e.symm (Finsupp.single (⟨2,by decide⟩ : Fin 3) 1)=basis .sphere 7 131 2 := he ⟨2,by decide⟩
    rw [←he2]
    exact basis_vector_ne_zero e 2
  have deg2 : (5,130)+E.diffDeg 2=(7,131) := by
    simp only [E,ClassicalAdamsFamily.sphere,ClassicalAdamsFamily.obj,
      model.classical.differentialDegree,Prod.mk_add_mk,Int.reduceAdd,Int.reduceSub]
  have hd : (E.d 2 (5,130) ≫ eqToHom (congrArg (E.Page 2) deg2))
      (basis .sphere 5 130 0)=basis .sphere 7 131 2 :=
    uPermanentD163.eq_on_page_two.choose_spec
  obtain ⟨f,hf⟩ := basis_correct ⟨.sphere,5,130,["340,1"]⟩ (by
    exact List.mem_of_getElem? (i := 126) (by rfl))
  change E.Page 2 (5,130) ≃ₗ[ℤ] (Fin 1 →₀ F2) at f
  change ∀ i : Fin 1, f.symm (Finsupp.single i 1)=basis .sphere 5 130 i.val at hf
  have sourcecases (x : E.Page 2 (5,130)) : x=0 ∨ x=basis .sphere 5 130 0 := by
    have hex := finite_basis_expansion f x
    simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,hf,add_zero] at hex
    change x=(if f x 0=0 then 0 else basis .sphere 5 130 0) at hex
    by_cases hz : f x 0=0
    · exact Or.inl (by simpa only [hz,ite_true] using hex)
    · exact Or.inr (by simpa only [hz,ite_false] using hex)
  apply next_page_zero_of_kernel (E := E) (r := 2) (p := (5,130)) hs2
  intro x hx
  rcases sourcecases x with hx0|hxb
  · exact hx0
  · subst x
    exfalso
    apply targetne
    rw [←hd,ModuleCat.comp_apply,hx,map_zero]

private theorem uPermanentSourceE5Zero :
    Subsingleton (model.classical.sphere.Page 5 (5,130)) := by
  have hs2 : model.classical.sphere.r₀≤2 := by rw [model.classical.firstPage]
  have hz3 := uPermanentSourceE3Zero
  have hz4 : Subsingleton (model.classical.sphere.Page 4 (5,130)) :=
    next_page_zero_of_kernel (E := model.classical.sphere) (r := 3) (p := (5,130))
      (hs2.trans (by decide : (2:ℤ)≤3)) (fun x _=>hz3.elim x 0)
  exact next_page_zero_of_kernel (E := model.classical.sphere) (r := 4) (p := (5,130))
    (hs2.trans (by decide : (2:ℤ)≤4)) (fun x _=>hz4.elim x 0)

private theorem uPermanentLateIncoming (r : ℤ) (hr : 5≤r) :
    model.classical.sphere.d r (((10:ℤ),134)-model.classical.sphere.diffDeg r)=0 := by
  let E := model.classical.sphere
  have hdeg : ((10:ℤ),134)-E.diffDeg r=(10-r,135-r) := by
    simp only [E,ClassicalAdamsFamily.sphere,ClassicalAdamsFamily.obj,
      model.classical.differentialDegree,Prod.mk_sub_mk]
    congr 1; omega
  have hz : Subsingleton (E.Page r (10-r,135-r)) := by
    by_cases h5 : r=5
    · subst r
      exact uPermanentSourceE5Zero
    · by_cases hhigh : 11≤r
      · exact KIP126.AdamsSynthetic.Standard.classical_page_negative .sphere r (10-r) (135-r) (by omega)
      · have hr6 : 6≤r := by omega
        have initial : Subsingleton (E.Page 2 (10-r,135-r)) := by
          interval_cases r <;> exact uPermanentInitialZero _ _ (by decide) (by decide)
        exact uPermanentPageZero E r (by omega) _ initial
  rw [hdeg]
  letI := hz
  ext a
  have ha : a=0 := Subsingleton.elim _ _
  simp only [ha,map_zero]

private theorem uPermanentCycleCandidate : IsPermanentCycle model.classical.sphere (10,134) U := by
  let E := model.classical.sphere
  apply isPermanentCycle_of_reachesPage E 1000
    (by change model.classical.sphere.r₀≤1000; rw [model.classical.firstPage]; omega)
    (10,134) U uPermanentReaches1000
  intro r hr
  have hdeg : (10,134)+E.diffDeg r=(10+r,133+r) := by
    simp only [E,ClassicalAdamsFamily.sphere,ClassicalAdamsFamily.obj,
      model.classical.differentialDegree,Prod.mk_add_mk]
    congr 1; omega
  have h2 : Subsingleton (E.Page 2 ((10,134)+E.diffDeg r)) := by
    rw [hdeg]
    exact KIP126.Literature.Standard.sphereVanishing (10+r) (133+r) (by omega) (by omega)
  letI := uPermanentPageZero E r (by omega) _ h2
  ext a
  exact Subsingleton.elim _ _

private theorem uPermanentCandidate : NonzeroSurvival model.classical.sphere (10,134) U := by
  exact uPermanentNonzeroOfPermanentFinite model.classical.sphere 5
    (by rw [model.classical.firstPage]; omega) (10,134) U
    uPermanentCycleCandidate uPermanentSurvivesFive uPermanentLateIncoming

end ArchiveUPermanenceConstruction

public theorem u_permanent : NonzeroSurvival model.classical.sphere (10,134) U := by
  exact uPermanentCandidate
/-- Exhaustion of the actual E₅ component, with its nonzero continuation. -/
public theorem high_e5 : ∃ y : model.classical.sphere.Page 5 (25,150),
    RepresentsOnPage model.classical.sphere 5 (25,150) highClass y ∧ y ≠ 0 ∧
    ∀ z : model.classical.sphere.Page 5 (25,150), z = 0 ∨ z = y := by
  classical
  let E := model.classical.sphere
  have hs2 : E.r₀≤2 := by
    change model.classical.sphere.r₀≤2
    rw [model.classical.firstPage]
  have hs4 : E.r₀≤4 := le_trans hs2 (by decide)
  have h429 : HasDifferential E 3 (18,145) (21,147) (basis .sphere 18 145 4) (basis .sphere 21 147 2) := by
    have hrow := result ⟨.sphere, .equation, 3, 18, 145, [4], 21, 147, [2], "S0_AdamsE2_ss", 3748⟩ (by
      exact List.mem_of_getElem? (l := Raw.claims) (i := 429) rfl)
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,c,hc,h⟩ := hrow
    change HasDifferential E 3 (18,145) (21,147) a c at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 18 145 [4] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 21 147 [2] = true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hc
    rw [←ha ,←hc] at h
    exact h
  have h430 : HasDifferential E 4 (21,147) (25,150) (basis .sphere 21 147 1) (basis .sphere 25 150 3) := by
    have hrow := result ⟨.sphere, .equation, 4, 21, 147, [1], 25, 150, [3], "S0_AdamsE2_ss", 3749⟩ (by
      exact List.mem_of_getElem? (l := Raw.claims) (i := 430) rfl)
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,c,hc,h⟩ := hrow
    change HasDifferential E 4 (21,147) (25,150) a c at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 21 147 [1] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 25 150 [3] = true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hc
    rw [←ha ,←hc] at h
    exact h
  have h431 : ReachesPage E 4 (21,147) (basis .sphere 21 147 0) := by
    have hrow := result ⟨.sphere, .reaches, 4, 21, 147, [0], 21, 147, [], "S0_AdamsE2_ss", 3750⟩ (by
      exact List.mem_of_getElem? (l := Raw.claims) (i := 431) rfl)
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,h⟩ := hrow
    have vx : Raw.coordinatesValid Raw.degrees .sphere 21 147 [0] = true := rfl
    simp only [decode,vx,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha
    rw [←ha] at h
    exact h
  have h462 : ReachesPage E 1000 (25,150) (basis .sphere 25 150 2) := by
    have hrow := result ⟨.sphere, .reaches, 1000, 25, 150, [2], 25, 150, [], "S0_AdamsE2_ss", 3993⟩ (by
      exact List.mem_of_getElem? (l := Raw.claims) (i := 462) rfl)
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,h⟩ := hrow
    have vx : Raw.coordinatesValid Raw.degrees .sphere 25 150 [2] = true := rfl
    simp only [decode,vx,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha
    rw [←ha] at h
    exact h
  have h463 : ReachesPage E 1000 (25,150) (basis .sphere 25 150 0 + (basis .sphere 25 150 1)) := by
    have hrow := result ⟨.sphere, .reaches, 1000, 25, 150, [0, 1], 25, 150, [], "S0_AdamsE2_ss", 3994⟩ (by
      exact List.mem_of_getElem? (l := Raw.claims) (i := 463) rfl)
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,h⟩ := hrow
    have vx : Raw.coordinatesValid Raw.degrees .sphere 25 150 [0, 1] = true := rfl
    simp only [decode,vx,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha
    rw [←ha] at h
    exact h
  have h464 : HasDifferential E 2 (25,150) (27,151) (basis .sphere 25 150 1) (basis .sphere 27 151 0) := by
    have hrow := result ⟨.sphere, .equation, 2, 25, 150, [1], 27, 151, [0], "S0_AdamsE2_ss", 3995⟩ (by
      exact List.mem_of_getElem? (l := Raw.claims) (i := 464) rfl)
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,c,hc,h⟩ := hrow
    change HasDifferential E 2 (25,150) (27,151) a c at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 25 150 [1] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 27 151 [0] = true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hc
    rw [←ha ,←hc] at h
    exact h
  have h661 : ¬ HasDifferential E 4 (21,147) (25,150) (basis .sphere 21 147 0) (0) := by
    have hrow := result ⟨.sphere, .refutation, 4, 21, 147, [0], 25, 150, [], "proofs.db/log", 154532⟩ (by
      exact List.mem_of_getElem? (l := Raw.claims) (i := 661) rfl)
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,c,hc,h⟩ := hrow
    change ¬ HasDifferential E 4 (21,147) (25,150) a c at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 21 147 [0] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 25 150 [] = true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hc
    rw [←ha ,←hc] at h
    exact h
  have h662 : ¬ HasDifferential E 4 (21,147) (25,150) (basis .sphere 21 147 0) (basis .sphere 25 150 3) := by
    have hrow := result ⟨.sphere, .refutation, 4, 21, 147, [0], 25, 150, [3], "proofs.db/log", 154533⟩ (by
      exact List.mem_of_getElem? (l := Raw.claims) (i := 662) rfl)
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,c,hc,h⟩ := hrow
    change ¬ HasDifferential E 4 (21,147) (25,150) a c at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 21 147 [0] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 25 150 [3] = true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hc
    rw [←ha ,←hc] at h
    exact h
  have h663 : ¬ HasDifferential E 4 (21,147) (25,150) (basis .sphere 21 147 0) (basis .sphere 25 150 2) := by
    have hrow := result ⟨.sphere, .refutation, 4, 21, 147, [0], 25, 150, [2], "proofs.db/log", 154534⟩ (by
      exact List.mem_of_getElem? (l := Raw.claims) (i := 663) rfl)
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,c,hc,h⟩ := hrow
    change ¬ HasDifferential E 4 (21,147) (25,150) a c at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 21 147 [0] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 25 150 [2] = true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hc
    rw [←ha ,←hc] at h
    exact h
  have h664 : ¬ HasDifferential E 4 (21,147) (25,150) (basis .sphere 21 147 0) (basis .sphere 25 150 2 + (basis .sphere 25 150 3)) := by
    have hrow := result ⟨.sphere, .refutation, 4, 21, 147, [0], 25, 150, [2, 3], "proofs.db/log", 154535⟩ (by
      exact List.mem_of_getElem? (l := Raw.claims) (i := 664) rfl)
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,c,hc,h⟩ := hrow
    change ¬ HasDifferential E 4 (21,147) (25,150) a c at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 21 147 [0] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 25 150 [2, 3] = true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hc
    rw [←ha ,←hc] at h
    exact h
  have h665 : ¬ HasDifferential E 4 (21,147) (25,150) (basis .sphere 21 147 0) (basis .sphere 25 150 0 + (basis .sphere 25 150 1)) := by
    have hrow := result ⟨.sphere, .refutation, 4, 21, 147, [0], 25, 150, [0, 1], "proofs.db/log", 154536⟩ (by
      exact List.mem_of_getElem? (l := Raw.claims) (i := 665) rfl)
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,c,hc,h⟩ := hrow
    change ¬ HasDifferential E 4 (21,147) (25,150) a c at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 21 147 [0] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 25 150 [0, 1] = true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hc
    rw [←ha ,←hc] at h
    exact h
  have h666 : ¬ HasDifferential E 4 (21,147) (25,150) (basis .sphere 21 147 0) (basis .sphere 25 150 0 + (basis .sphere 25 150 1 + (basis .sphere 25 150 3))) := by
    have hrow := result ⟨.sphere, .refutation, 4, 21, 147, [0], 25, 150, [0, 1, 3], "proofs.db/log", 154537⟩ (by
      exact List.mem_of_getElem? (l := Raw.claims) (i := 666) rfl)
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,c,hc,h⟩ := hrow
    change ¬ HasDifferential E 4 (21,147) (25,150) a c at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 21 147 [0] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 25 150 [0, 1, 3] = true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hc
    rw [←ha ,←hc] at h
    exact h
  obtain ⟨f,hf⟩ := basis_correct
    ⟨.sphere,25,150,["559,1","558,1","13,4,51,1","8,2,9,1,13,1,80,1"]⟩ (by
      exact List.mem_of_getElem? (l := Raw.degrees) (i := 281) rfl)
  change E.Page 2 (25,150) ≃ₗ[ℤ] (Fin 4 →₀ F2) at f
  change ∀ i : Fin 4, f.symm (Finsupp.single i 1)=basis .sphere 25 150 i.val at hf
  obtain ⟨g,hg⟩ := basis_correct
    ⟨.sphere,27,151,["0,1,557,1","0,2,17,1,260,1"]⟩ (by
      exact List.mem_of_getElem? (l := Raw.degrees) (i := 289) rfl)
  change E.Page 2 (27,151) ≃ₗ[ℤ] (Fin 2 →₀ F2) at g
  change ∀ i : Fin 2, g.symm (Finsupp.single i 1)=basis .sphere 27 151 i.val at hg
  obtain ⟨es,hes⟩ := basis_correct
    ⟨.sphere,21,147,["530,1","1,1,510,1","0,3,500,1"]⟩ (by
      exact List.mem_of_getElem? (l := Raw.degrees) (i := 262) rfl)
  change E.Page 2 (21,147) ≃ₗ[ℤ] (Fin 3 →₀ F2) at es
  change ∀ i : Fin 3, es.symm (Finsupp.single i 1)=basis .sphere 21 147 i.val at hes
  let A := basis .sphere 25 150 0+basis .sphere 25 150 1
  let H := basis .sphere 25 150 2
  let C := basis .sphere 25 150 3
  let δ : E.Page 2 (25,150) ⟶ E.Page 2 (27,151) :=
    E.d 2 (25,150) ≫ eqToHom (congrArg (E.Page 2) h464.target_degree)
  have d1 : δ (basis .sphere 25 150 1)=basis .sphere 27 151 0 := h464.eq_on_page_two.2
  have d1ne : δ (basis .sphere 25 150 1)≠0 := by
    rw [d1]
    have h := hg (0 : Fin 2)
    change g.symm (Finsupp.single (0 : Fin 2) 1)=basis .sphere 27 151 0 at h
    rw [←h]
    exact basis_vector_ne_zero g 0
  have dA : δ A=0 := by
    have h := represents_d_zero_of_later hs2 (by decide : (2:ℤ)<1000)
      (represents_two_self _) h463
    change E.d 2 (25,150) A=0 at h
    simp only [δ,ModuleCat.comp_apply,h,map_zero]
  have dH : δ H=0 := by
    have h := represents_d_zero_of_later hs2 (by decide : (2:ℤ)<1000)
      (represents_two_self _) h462
    change E.d 2 (25,150) H=0 at h
    simp only [δ,ModuleCat.comp_apply,h,map_zero]
  obtain ⟨hdeg4,a1,c4,ha1,hc4,da1⟩ := h430
  have dC : δ C=0 := by
    have h := represents_d_zero_of_later hs2 (by decide : (2:ℤ)<4)
      (represents_two_self _) ⟨c4,hc4⟩
    change E.d 2 (25,150) C=0 at h
    simp only [δ,ModuleCat.comp_apply,h,map_zero]
  have d0ne : δ (basis .sphere 25 150 0)≠0 := by
    intro h
    have hsum : δ (basis .sphere 25 150 0)+δ (basis .sphere 25 150 1)=0 := by
      simpa only [A,map_add] using dA
    rw [h,zero_add] at hsum
    exact d1ne hsum
  have targetgen (r : ℤ) (hr : 3≤r)
      (ar hr' cr : E.Page r (25,150))
      (har : RepresentsOnPage E r (25,150) A ar)
      (hhr : RepresentsOnPage E r (25,150) H hr')
      (hcr : RepresentsOnPage E r (25,150) C cr)
      (z : E.Page r (25,150)) :
      ∃ bits : Fin 3 → F2, z=(if bits 0=0 then 0 else ar)+
        ((if bits 1=0 then 0 else hr')+(if bits 2=0 then 0 else cr)) := by
    obtain ⟨x,hxz⟩ := page_has_initial_representative (by omega) z
    have hx := finite_basis_expansion f x
    simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,hf,add_zero] at hx
    change x=(if f x 0=0 then 0 else basis .sphere 25 150 0)+
      ((if f x 1=0 then 0 else basis .sphere 25 150 1)+
      ((if f x 2=0 then 0 else H)+(if f x 3=0 then 0 else C))) at hx
    have dx : δ x=0 := by
      have h := represents_d_zero_of_later hs2 (by omega : (2:ℤ)<r)
        (represents_two_self _) ⟨z,hxz⟩
      simp only [δ,ModuleCat.comp_apply,h,map_zero]
    have hd := congrArg δ hx
    rw [dx] at hd
    simp only [map_add,apply_ite,map_zero] at hd
    simp only [dH,dC,ite_self,add_zero] at hd
    have h01 : f x 0=0 ↔ f x 1=0 := by
      constructor
      · intro h0
        by_contra h1
        have hh : (0 : E.Page 2 (27,151))=δ (basis .sphere 25 150 1) := by
          simpa only [h0,h1,ite_true,ite_false,zero_add] using hd
        exact d1ne hh.symm
      · intro h1
        by_contra h0
        have hh : (0 : E.Page 2 (27,151))=δ (basis .sphere 25 150 0) := by
          simpa only [h0,h1,ite_true,ite_false,add_zero] using hd
        exact d0ne hh.symm
    have pairrep : RepresentsOnPage E r (25,150)
        ((if f x 0=0 then 0 else basis .sphere 25 150 0)+
         (if f x 1=0 then 0 else basis .sphere 25 150 1))
        (if f x 0=0 then 0 else ar) := by
      by_cases h0 : f x 0=0
      · have h1 := h01.mp h0
        simpa only [h0,h1,ite_true,zero_add] using
          (RepresentsOnPage.zero (E:=E) (p:=(25,150)) (by omega : (2:ℤ)≤r))
      · have h1 : f x 1≠0 := fun h=>h0 (h01.mpr h)
        simpa only [h0,h1,ite_false] using har
    have rep := represents_add_tail pairrep
      (represents_add_tail (represents_bit (f x 2) hhr) (represents_bit (f x 3) hcr))
    simp only [add_assoc] at rep
    rw [←hx] at rep
    have hz := represents_unique hxz rep
    refine ⟨![f x 0,f x 2,f x 3],?_⟩
    change z=(if f x 0=0 then 0 else ar)+
      ((if f x 2=0 then 0 else hr')+(if f x 3=0 then 0 else cr))
    exact hz
  have twice (r : ℤ) (hr : 2≤r) (z : E.Page r (25,150)) : z+z=0 := by
    obtain ⟨x,hx⟩ := page_has_initial_representative hr z
    have hxx : x+x=0 := by
      apply f.injective
      simp only [map_add,map_zero]
      ext i
      simp only [Finsupp.add_apply,Finsupp.zero_apply]
      generalize f x i=t
      fin_cases t <;> decide
    have hh := represents_add_tail hx hx
    rw [hxx] at hh
    exact represents_unique hh (RepresentsOnPage.zero hr)
  obtain ⟨a4,ha4⟩ := reaches_before (by decide : (2:ℤ)≤4) (by decide : (4:ℤ)≤1000) h463
  obtain ⟨h4,hh4⟩ := reaches_before (by decide : (2:ℤ)≤4) (by decide : (4:ℤ)≤1000) h462
  obtain ⟨a5,ha5⟩ := reaches_before (by decide : (2:ℤ)≤5) (by decide : (5:ℤ)≤1000) h463
  obtain ⟨h5,hh5⟩ := reaches_before (by decide : (2:ℤ)≤5) (by decide : (5:ℤ)≤1000) h462
  obtain ⟨a0,ha0⟩ := h431
  have rsrc2 : RepresentsOnPage E 4 (21,147) (basis .sphere 21 147 2) 0 :=
    differential_target_later_zero (le_trans hs2 (by decide)) (by decide) h429
  let Δ : E.Page 4 (21,147) ⟶ E.Page 4 (25,150) :=
    E.d 4 (21,147) ≫ eqToHom (congrArg (E.Page 4) hdeg4)
  let D := Δ a0
  have dc : Δ a1=c4 := da1
  have sourcegen (z : E.Page 4 (21,147)) : z=0 ∨ z=a0 ∨ z=a1 ∨ z=a0+a1 := by
    have hv (i : Fin 3) : RepresentsOnPage E 4 (21,147)
        (es.symm (Finsupp.single i 1)) (![a0,a1,0] i) := by
      rw [hes i]
      fin_cases i
      · exact ha0
      · exact ha1
      · exact rsrc2
    obtain ⟨bits,hbits⟩ := page_generated_from_representatives (by decide : (2:ℤ)≤4)
      es ![a0,a1,0] hv z
    simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,Matrix.cons_val_zero,
      Matrix.cons_val_succ,ite_self,add_zero] at hbits
    change z=(if bits 0=0 then 0 else a0)+(if bits 1=0 then 0 else a1) at hbits
    by_cases h0 : bits 0=0 <;> by_cases h1 : bits 1=0
    · exact Or.inl (by simpa only [h0,h1,ite_true,zero_add] using hbits)
    · exact Or.inr (Or.inr (Or.inl (by simpa only [h0,h1,ite_true,ite_false,zero_add] using hbits)))
    · exact Or.inr (Or.inl (by simpa only [h0,h1,ite_true,ite_false,add_zero] using hbits))
    · exact Or.inr (Or.inr (Or.inr (by simpa only [h0,h1,ite_false] using hbits)))
  have n0 : D≠0 := by
    intro hd
    exact h661 ⟨hdeg4,a0,0,ha0,RepresentsOnPage.zero (by decide),hd⟩
  have nC : D≠c4 := by
    intro hd
    exact h662 ⟨hdeg4,a0,c4,ha0,hc4,hd⟩
  have nH : D≠h4 := by
    intro hd
    exact h663 ⟨hdeg4,a0,h4,ha0,hh4,hd⟩
  have nHC : D≠h4+c4 := by
    intro hd
    exact h664 ⟨hdeg4,a0,h4+c4,ha0,represents_add_tail hh4 hc4,hd⟩
  have nA : D≠a4 := by
    intro hd
    exact h665 ⟨hdeg4,a0,a4,ha0,ha4,hd⟩
  have nAC : D≠a4+c4 := by
    intro hd
    apply h666
    refine ⟨hdeg4,a0,a4+c4,ha0,?_,hd⟩
    simpa only [add_assoc] using represents_add_tail ha4 hc4
  have allowed : D=a4+h4 ∨ D=(a4+h4)+c4 := by
    obtain ⟨bits,hbits⟩ := targetgen 4 (by decide) a4 h4 c4 ha4 hh4 hc4 D
    by_cases h0 : bits 0=0 <;> by_cases h1 : bits 1=0 <;> by_cases h2 : bits 2=0
    · exact False.elim (n0 (by simpa only [h0,h1,h2,ite_true,zero_add] using hbits))
    · exact False.elim (nC (by simpa only [h0,h1,h2,ite_true,ite_false,zero_add] using hbits))
    · exact False.elim (nH (by simpa only [h0,h1,h2,ite_true,ite_false,zero_add,add_zero] using hbits))
    · exact False.elim (nHC (by simpa only [h0,h1,h2,ite_true,ite_false,zero_add] using hbits))
    · exact False.elim (nA (by simpa only [h0,h1,h2,ite_true,ite_false,zero_add,add_zero] using hbits))
    · exact False.elim (nAC (by simpa only [h0,h1,h2,ite_true,ite_false,zero_add] using hbits))
    · exact Or.inl (by simpa only [h0,h1,h2,ite_true,ite_false,add_zero] using hbits)
    · exact Or.inr (by simpa only [h0,h1,h2,ite_false,add_assoc] using hbits)
  have h4ne : h4≠0 := by
    intro hz
    rcases allowed with hd | hd
    · exact nA (by simpa only [hz,add_zero] using hd)
    · exact nAC (by simpa only [hz,add_zero] using hd)
  have h4nc : h4≠c4 := by
    intro hz
    rcases allowed with hd | hd
    · exact nAC (by simpa only [hz] using hd)
    · apply nA
      rw [hz,add_assoc,twice 4 (by decide) c4,add_zero] at hd
      exact hd
  have h5ne : h5≠0 := by
    apply represents_next_nonzero_of_not_incoming_at hdeg4 hs4 (by decide) hh5 hh4
    intro z hz
    rcases sourcegen z with hz0 | hz0 | hz0 | hz0
    · subst z
      rw [map_zero] at hz
      exact h4ne hz.symm
    · subst z
      exact nH hz
    · subst z
      rw [dc] at hz
      exact h4nc hz.symm
    · rw [hz0,map_add,dc] at hz
      apply nHC
      calc
        D=(D+c4)+c4 := by rw [add_assoc,twice 4 (by decide) c4,add_zero]
        _=h4+c4 := congrArg (fun w=>w+c4) hz
  have c5 : RepresentsOnPage E 5 (25,150) C 0 :=
    differential_target_later_zero hs4 (by decide)
      ⟨hdeg4,a1,c4,ha1,hc4,da1⟩
  have ah5 : a5+h5=0 := by
    rcases allowed with hd | hd
    · have dd : HasDifferential E 4 (21,147) (25,150)
          (basis .sphere 21 147 0) (A+H) :=
        ⟨hdeg4,a0,a4+h4,ha0,represents_add_tail ha4 hh4,hd⟩
      have hz := differential_target_later_zero hs4 (by decide : (4:ℤ)<5) dd
      exact represents_unique (represents_add_tail ha5 hh5) hz
    · have dd : HasDifferential E 4 (21,147) (25,150)
          (basis .sphere 21 147 0) ((A+H)+C) :=
        ⟨hdeg4,a0,(a4+h4)+c4,ha0,
          represents_add_tail (represents_add_tail ha4 hh4) hc4,hd⟩
      have hz := differential_target_later_zero hs4 (by decide : (4:ℤ)<5) dd
      have hh := represents_unique (represents_add_tail (represents_add_tail ha5 hh5) c5) hz
      simpa only [add_zero] using hh
  have a5eq : a5=h5 := by
    calc
      a5=(a5+h5)+h5 := by rw [add_assoc,twice 5 (by decide) h5,add_zero]
      _=h5 := by rw [ah5,zero_add]
  have hall (z : E.Page 5 (25,150)) : z=0 ∨ z=h5 := by
    obtain ⟨bits,hbits⟩ := targetgen 5 (by decide) a5 h5 0 ha5 hh5 c5 z
    simp only [a5eq,ite_self,add_zero] at hbits
    by_cases h0 : bits 0=0 <;> by_cases h1 : bits 1=0
    · exact Or.inl (by simpa only [h0,h1,ite_true,zero_add] using hbits)
    · exact Or.inr (by simpa only [h0,h1,ite_true,ite_false,zero_add] using hbits)
    · exact Or.inr (by simpa only [h0,h1,ite_true,ite_false,add_zero] using hbits)
    · exact Or.inl (by simpa only [h0,h1,ite_false,twice 5 (by decide) h5] using hbits)
  have high_value : H=highClass := by
    have hv := basis_value
      ⟨.mul (.mul (.mul (.mul (.named .g) (.named .g)) (.named .g)) (.named .g))
        (.named .delta_h_1_mul_g),2⟩ (by decide)
    change H=product
      (product (r := (16,96))
        (product (r := (12,72)) (product (r := (8,48)) (atom .g) (atom .g)) (atom .g)) (atom .g))
      (atom .delta_h_1_mul_g) at hv
    have ha : product (r := (16,96))
        (product (r := (12,72)) (product (r := (8,48)) (atom .g) (atom .g)) (atom .g)) (atom .g)=
        product (r := (16,96)) (product (r := (8,48)) (atom .g) (atom .g))
          (product (r := (8,48)) (atom .g) (atom .g)) :=
      eq_of_heq (model.sphereAlgebra.assoc (8,48) (4,24) (4,24)
        (product (r := (8,48)) (atom .g) (atom .g)) (atom .g) (atom .g))
    rw [ha] at hv
    exact hv
  change RepresentsOnPage E 5 (25,150) H h5 at hh5
  rw [high_value] at hh5
  exact ⟨h5,hh5,h5ne,hall⟩

private theorem v_incoming_late_zero (r : ℤ) (hr4 : 4≤r) (hr12 : r<12) :
    model.classical.sphere.d r (9-r,133-r)=0 := by
  let E := model.classical.sphere
  have pages0 (p : ℤ×ℤ) (e0 : E.Page 2 p ≃ₗ[ℤ] (Fin 0 →₀ F2))
      (r : ℤ) (hr : 2≤r) : Subsingleton (E.Page r p) := by
    haveI : Subsingleton (E.Page 2 p) := e0.injective.subsingleton
    have hz (y : E.Page r p) : y=0 := by
      obtain ⟨x,hx⟩ := page_has_initial_representative hr y
      rw [Subsingleton.elim x 0] at hx
      exact represents_unique hx (RepresentsOnPage.zero hr)
    exact ⟨fun x y=>(hz x).trans (hz y).symm⟩
  haveI : Subsingleton (E.Page r (9-r,133-r)) := by
    interval_cases r
    · obtain ⟨z,hz⟩ := basis_correct ⟨.sphere, 5, 129, []⟩ (by
        exact List.mem_of_getElem? (i := 125) (by rfl))
      change E.Page 2 (5,129) ≃ₗ[ℤ] (Fin 0 →₀ F2) at z
      exact pages0 (5,129) z 4 (by decide)
    · obtain ⟨z,hz⟩ := basis_correct ⟨.sphere, 4, 128, []⟩ (by
        exact List.mem_of_getElem? (i := 117) (by rfl))
      change E.Page 2 (4,128) ≃ₗ[ℤ] (Fin 0 →₀ F2) at z
      exact pages0 (4,128) z 5 (by decide)
    · obtain ⟨z,hz⟩ := basis_correct ⟨.sphere, 3, 127, []⟩ (by
        exact List.mem_of_getElem? (i := 106) (by rfl))
      change E.Page 2 (3,127) ≃ₗ[ℤ] (Fin 0 →₀ F2) at z
      exact pages0 (3,127) z 6 (by decide)
    · obtain ⟨z,hz⟩ := basis_correct ⟨.sphere, 2, 126, []⟩ (by
        exact List.mem_of_getElem? (i := 98) (by rfl))
      change E.Page 2 (2,126) ≃ₗ[ℤ] (Fin 0 →₀ F2) at z
      exact pages0 (2,126) z 7 (by decide)
    · obtain ⟨z,hz⟩ := basis_correct ⟨.sphere, 1, 125, []⟩ (by
        exact List.mem_of_getElem? (i := 88) (by rfl))
      change E.Page 2 (1,125) ≃ₗ[ℤ] (Fin 0 →₀ F2) at z
      exact pages0 (1,125) z 8 (by decide)
    · obtain ⟨z,hz⟩ := basis_correct ⟨.sphere, 0, 124, []⟩ (by
        exact List.mem_of_getElem? (i := 75) (by rfl))
      change E.Page 2 (0,124) ≃ₗ[ℤ] (Fin 0 →₀ F2) at z
      exact pages0 (0,124) z 9 (by decide)
    · exact KIP126.AdamsSynthetic.Standard.classical_page_negative .sphere 10 (9-10) (133-10) (by decide)
    · exact KIP126.AdamsSynthetic.Standard.classical_page_negative .sphere 11 (9-11) (133-11) (by decide)
  ext x
  change E.d r (9-r,133-r) x=0
  rw [Subsingleton.elim x 0,map_zero]


public theorem v_to_e12 : SurvivesTo model.classical.sphere 12 (9,132) V := by
  classical
  let E := model.classical.sphere
  have hs2 : E.r₀≤2 := by
    change model.classical.sphere.r₀≤2
    rw [model.classical.firstPage]
  have h163 : HasDifferential E 2 (5,130) (7,131)
      (basis .sphere 5 130 0) (basis .sphere 7 131 2) := by
    have hrow := result ⟨.sphere, .equation, 2, 5, 130, [0], 7, 131, [2], "S0_AdamsE2_ss", 2435⟩ (by
      exact List.mem_of_getElem? (i := 163) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 2 (5,130) (7,131) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 5 130 [0]=true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 7 131 [2]=true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    exact h
  have h170 : HasDifferential E 5 (6,130) (11,134)
      (basis .sphere 6 130 0) (basis .sphere 11 134 2) := by
    have hrow := result ⟨.sphere, .equation, 5, 6, 130, [0], 11, 134, [2], "S0_AdamsE2_ss", 2434⟩ (by
      exact List.mem_of_getElem? (i := 170) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 5 (6,130) (11,134) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 6 130 [0]=true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 11 134 [2]=true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    exact h
  have h182 : HasDifferential E 5 (7,131) (12,135)
      (basis .sphere 7 131 1) (basis .sphere 12 135 2) := by
    have hrow := result ⟨.sphere, .equation, 5, 7, 131, [1], 12, 135, [2], "S0_AdamsE2_ss", 2490⟩ (by
      exact List.mem_of_getElem? (i := 182) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 5 (7,131) (12,135) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 7 131 [1]=true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 12 135 [2]=true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    exact h
  have h183 : HasDifferential E 3 (7,131) (10,133)
      (basis .sphere 7 131 0) (basis .sphere 10 133 0 + basis .sphere 10 133 1) := by
    have hrow := result ⟨.sphere, .equation, 3, 7, 131, [0], 10, 133, [0, 1], "S0_AdamsE2_ss", 2491⟩ (by
      exact List.mem_of_getElem? (i := 183) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 3 (7,131) (10,133) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 7 131 [0]=true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 10 133 [0, 1]=true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    exact h
  have h219 : ReachesPage E 12 (9,132) (basis .sphere 9 132 0 + basis .sphere 9 132 1) := by
    have hrow := result ⟨.sphere, .reaches, 12, 9, 132, [0, 1], 9, 132, [], "S0_AdamsE2_ss", 2569⟩ (by
      exact List.mem_of_getElem? (i := 219) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,h⟩ := hrow
    have vx : Raw.coordinatesValid Raw.degrees .sphere 9 132 [0, 1]=true := rfl
    simp only [decode,vx,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      add_zero,Option.some.injEq] at ha
    rw [←ha] at h
    exact h
  obtain ⟨g,hg⟩ := basis_correct ⟨.sphere, 9, 132, ["366,1", "0,1,352,1"]⟩ (by
    exact List.mem_of_getElem? (i := 171) (by rfl))
  change E.Page 2 (9,132) ≃ₗ[ℤ] (Fin 2 →₀ F2) at g
  change ∀ i : Fin 2, g.symm (Finsupp.single i 1)=basis .sphere 9 132 i.val at hg
  obtain ⟨e,he⟩ := basis_correct ⟨.sphere, 7, 131, ["353,1", "69,1,75,1", "0,1,339,1"]⟩ (by
    exact List.mem_of_getElem? (i := 148) (by rfl))
  change E.Page 2 (7,131) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e
  change ∀ i : Fin 3, e.symm (Finsupp.single i 1)=basis .sphere 7 131 i.val at he
  obtain ⟨f,hf⟩ := basis_correct ⟨.sphere, 6, 130, ["339,1"]⟩ (by
    exact List.mem_of_getElem? (i := 136) (by rfl))
  change E.Page 2 (6,130) ≃ₗ[ℤ] (Fin 1 →₀ F2) at f
  change ∀ i : Fin 1, f.symm (Finsupp.single i 1)=basis .sphere 6 130 i.val at hf
  have Vb : V=basis .sphere 9 132 0+basis .sphere 9 132 1 := by
    have v0 := basis_value ⟨.named .x_123_9,0⟩ (by decide)
    change basis .sphere 9 132 0=atom .x_123_9 at v0
    have v1 : basis .sphere 9 132 1=product (r := (9,132)) h0 (atom .x_123_8) := by
      have h := basis_value ⟨.mul (.named .h0) (.named .x_123_8),1⟩ (by decide)
      simpa only [Expression.value,Expression.degree,atom_h0] using h
    dsimp only [V]
    rw [←v0,←v1]
  have Vne : V≠0 := by
    have hg0 : g.symm (Finsupp.single (0 : Fin 2) 1)=basis .sphere 9 132 0 := hg 0
    have hg1 : g.symm (Finsupp.single (1 : Fin 2) 1)=basis .sphere 9 132 1 := hg 1
    rw [Vb,←hg0,←hg1]
    exact basis_pair_sum_ne_zero g 0 1 (by decide)
  have hr12 : ReachesPage E 12 (9,132) V := by rw [Vb];exact h219
  obtain ⟨v12,hv12⟩ := hr12
  have hin2 : E.d 2 (7,131)=0 := by
    obtain ⟨_,a0,_,ha0,_,_⟩ := h183
    obtain ⟨_,a1,_,ha15,_,_⟩ := h182
    obtain ⟨a13,ha13⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤5) ha15
    have ha2 : RepresentsOnPage E 3 (7,131) (basis .sphere 7 131 2) 0 :=
      differential_target_later_zero hs2 (by decide) h163
    apply d_zero_of_complete_representatives (by decide : (2:ℤ)≤2) e
    intro i
    refine ⟨e.symm (Finsupp.single i 1),represents_two_self _,?_⟩
    rw [he i]
    fin_cases i
    · exact represents_d_zero_of_later hs2 (by decide : (2:ℤ)<3) (represents_two_self _) ⟨a0,ha0⟩
    · exact represents_d_zero_of_later hs2 (by decide : (2:ℤ)<3) (represents_two_self _) ⟨a13,ha13⟩
    · exact represents_d_zero_of_later hs2 (by decide : (2:ℤ)<3) (represents_two_self _) ⟨0,ha2⟩
  have hin3 : E.d 3 (6,130)=0 := by
    obtain ⟨_,a,_,ha,_,_⟩ := h170
    obtain ⟨b,hb⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤5) ha
    apply d_zero_of_complete_representatives (by decide : (2:ℤ)≤3) f
    intro i
    have hi : i=0 := Subsingleton.elim _ _
    subst i
    have hf0 : f.symm (Finsupp.single (0 : Fin 1) 1)=basis .sphere 6 130 0 := hf 0
    refine ⟨b,?_,?_⟩
    · rw [hf0]
      exact hb
    · exact represents_d_zero_of_later (hs2.trans (by decide : (2:ℤ)≤3))
        (by decide : (3:ℤ)<5) hb ⟨a,ha⟩
  have hinlate (r : ℤ) (hr4 : 4≤r) (hr12 : r<12) : E.d r (9-r,133-r)=0 :=
    v_incoming_late_zero r hr4 hr12
  have deg (r : ℤ) : (9-r,133-r)+E.diffDeg r=(9,132) := by
    simp only [E,Classical.Adams.ClassicalAdamsFamily.sphere,Classical.Adams.ClassicalAdamsFamily.obj,
      model.classical.differentialDegree,Prod.mk_add_mk,Prod.mk.injEq]
    constructor <;> omega
  obtain ⟨v3,hv3⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤12) hv12
  obtain ⟨v4,hv4⟩ := represents_before (by decide : (2:ℤ)≤4) (by decide : (4:ℤ)≤12) hv12
  obtain ⟨v5,hv5⟩ := represents_before (by decide : (2:ℤ)≤5) (by decide : (5:ℤ)≤12) hv12
  obtain ⟨v6,hv6⟩ := represents_before (by decide : (2:ℤ)≤6) (by decide : (6:ℤ)≤12) hv12
  obtain ⟨v7,hv7⟩ := represents_before (by decide : (2:ℤ)≤7) (by decide : (7:ℤ)≤12) hv12
  obtain ⟨v8,hv8⟩ := represents_before (by decide : (2:ℤ)≤8) (by decide : (8:ℤ)≤12) hv12
  obtain ⟨v9,hv9⟩ := represents_before (by decide : (2:ℤ)≤9) (by decide : (9:ℤ)≤12) hv12
  obtain ⟨v10,hv10⟩ := represents_before (by decide : (2:ℤ)≤10) (by decide : (10:ℤ)≤12) hv12
  obtain ⟨v11,hv11⟩ := represents_before (by decide : (2:ℤ)≤11) (by decide : (11:ℤ)≤12) hv12
  have v3ne : v3≠0 := represents_next_nonzero_of_incoming_zero_at
    (hs2.trans (by decide : (2:ℤ)≤2)) (by decide) hin2 hv3 (represents_two_self V) Vne (deg 2)
  have v4ne : v4≠0 := represents_next_nonzero_of_incoming_zero_at
    (hs2.trans (by decide : (2:ℤ)≤3)) (by decide) hin3 hv4 hv3 v3ne (deg 3)
  have v5ne : v5≠0 := represents_next_nonzero_of_incoming_zero_at
    (hs2.trans (by decide : (2:ℤ)≤4)) (by decide) (hinlate 4 (by decide) (by decide)) hv5 hv4 v4ne (deg 4)
  have v6ne : v6≠0 := represents_next_nonzero_of_incoming_zero_at
    (hs2.trans (by decide : (2:ℤ)≤5)) (by decide) (hinlate 5 (by decide) (by decide)) hv6 hv5 v5ne (deg 5)
  have v7ne : v7≠0 := represents_next_nonzero_of_incoming_zero_at
    (hs2.trans (by decide : (2:ℤ)≤6)) (by decide) (hinlate 6 (by decide) (by decide)) hv7 hv6 v6ne (deg 6)
  have v8ne : v8≠0 := represents_next_nonzero_of_incoming_zero_at
    (hs2.trans (by decide : (2:ℤ)≤7)) (by decide) (hinlate 7 (by decide) (by decide)) hv8 hv7 v7ne (deg 7)
  have v9ne : v9≠0 := represents_next_nonzero_of_incoming_zero_at
    (hs2.trans (by decide : (2:ℤ)≤8)) (by decide) (hinlate 8 (by decide) (by decide)) hv9 hv8 v8ne (deg 8)
  have v10ne : v10≠0 := represents_next_nonzero_of_incoming_zero_at
    (hs2.trans (by decide : (2:ℤ)≤9)) (by decide) (hinlate 9 (by decide) (by decide)) hv10 hv9 v9ne (deg 9)
  have v11ne : v11≠0 := represents_next_nonzero_of_incoming_zero_at
    (hs2.trans (by decide : (2:ℤ)≤10)) (by decide) (hinlate 10 (by decide) (by decide)) hv11 hv10 v10ne (deg 10)
  have v12ne : v12≠0 := represents_next_nonzero_of_incoming_zero_at
    (hs2.trans (by decide : (2:ℤ)≤11)) (by decide) (hinlate 11 (by decide) (by decide)) hv12 hv11 v11ne (deg 11)
  exact ⟨v12,hv12,v12ne⟩


/-- Survival through E₁₂ excludes earlier hits; later sources have negative
Adams filtration and vanish in the fixed sphere Adams system. -/
public theorem v_not_hit : NeverHit model.classical.sphere (9,132) V := by
  intro r hr q hq y hy hne z hd
  by_cases hlt : r<12
  · exact no_earlier_hit_of_survival
      (by rw [model.classical.firstPage]; omega) hr hlt v_to_e12
      ⟨q,hq,z,y,hy,hne,hd⟩
  · have hneg : q.1<0 := by
      have h := congrArg Prod.fst hq
      simp only [ClassicalAdamsFamily.sphere,ClassicalAdamsFamily.obj,
        model.classical.differentialDegree] at h
      change q.1+r=9 at h
      omega
    haveI : Subsingleton (model.classical.sphere.Page r q) :=
      KIP126.AdamsSynthetic.Standard.classical_page_negative .sphere r q.1 q.2 hneg
    have hz : z=0 := Subsingleton.elim _ _
    apply hne
    simpa only [hz,ModuleCat.comp_apply,map_zero] using hd.symm


private theorem actual_h1_h0_zero : product (r := (2,3)) h1 h0=0 := by
  let e := coordinates 2 3 (by decide)
  have hn : archive.basisCount 2 3=0 :=
    (archive_dimension 2 3 (by decide)).trans (by decide)
  haveI : Subsingleton (Fin (archive.basisCount 2 3) →₀ ZMod 2) := by
    rw [hn]
    infer_instance
  apply e.injective
  exact Subsingleton.elim _ _

private theorem actual_h1_h0_x1238_zero :
    product (r := (10,134)) h1 (product (r := (9,132)) h0 (atom .x_123_8))=0 := by
  have ha := model.sphereAlgebra.assoc (1,2) (1,1) (8,131) h1 h0 (atom .x_123_8)
  have he : product (r := (10,134)) (product (r := (2,3)) h1 h0) (atom .x_123_8) =
      product (r := (10,134)) h1 (product (r := (9,132)) h0 (atom .x_123_8)) :=
    eq_of_heq ha
  rw [←he,actual_h1_h0_zero]
  dsimp only [product]
  simp only [map_zero,LinearMap.zero_apply]

private theorem actual_h1_v :
    product (r := (10,134)) h1 V = product (r := (10,134)) h1 (atom .x_123_9) := by
  calc
    _ = product (r := (10,134)) h1 (atom .x_123_9) +
        product (r := (10,134)) h1 (product (r := (9,132)) h0 (atom .x_123_8)) := by
      dsimp only [V,product]
      simp only [map_add,Nat.cast_ofNat]
    _ = _ := by rw [actual_h1_h0_x1238_zero,add_zero]

private theorem actual_x1258_basis : basis .sphere 8 133 1 = atom .x_125_8 := by
  have h := basis_value ⟨.named .x_125_8,1⟩ (by decide)
  exact h

private theorem actual_h1_x1239_basis : basis .sphere 10 134 2 =
    product (r := (10,134)) h1 (atom .x_123_9) := by
  have h := basis_value ⟨.mul (.named .h1) (.named .x_123_9),2⟩ (by decide)
  simpa only [Expression.value,Expression.degree,atom_h1] using h

private theorem actual_d2_target_basis :
    basis .sphere 10 134 2 + basis .sphere 10 134 4 = d2Target := by
  change basis .sphere 10 134 2 + basis .sphere 10 134 4 =
    product (r := (10,134)) h1 V + U
  rw [actual_h1_v,actual_h1_x1239_basis,basis_U]

private theorem actual_d2_x1258_equation :
    HasDifferential model.classical.sphere 2 (8,133) (10,134) (atom .x_125_8) d2Target := by
  have hrow := result
    ⟨.sphere,.equation,2,8,133,[1],10,134,[2,4],"S0_AdamsE2_ss",2630⟩ (by
      exact List.mem_of_getElem? (i := 201) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 133 [1]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 10 134 [2,4]=true := rfl
  simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy,actual_x1258_basis,actual_d2_target_basis] at hd
  exact hd

private theorem basis2_add_basis4_nonzero :
    KIP126.Computation.Table.basis .sphere 10 134 2 +
      KIP126.Computation.Table.basis .sphere 10 134 4 ≠ 0 := by
  obtain ⟨e,he⟩ := KIP126.Computation.Table.basis_correct
    ⟨.sphere,10,134,["389,1", "388,1", "1,1,366,1", "0,1,373,1", "0,2,367,1"]⟩ (by
      exact List.mem_of_getElem? (l := KIP126.Computation.Table.Raw.degrees) (i := 181) rfl)
  change KIP126.Computation.Table.Page .sphere 10 134 ≃ₗ[ℤ] (Fin 5 →₀ ZMod 2) at e
  change ∀ i : Fin 5, e.symm (Finsupp.single i 1) =
    KIP126.Computation.Table.basis .sphere 10 134 i.val at he
  have he2 : e.symm (Finsupp.single (2 : Fin 5) 1) =
      KIP126.Computation.Table.basis .sphere 10 134 2 := he 2
  have he4 : e.symm (Finsupp.single (4 : Fin 5) 1) =
      KIP126.Computation.Table.basis .sphere 10 134 4 := he 4
  have e2 : e (KIP126.Computation.Table.basis .sphere 10 134 2) =
      Finsupp.single (2 : Fin 5) 1 := by
    simpa only [LinearEquiv.apply_symm_apply] using (congrArg e he2).symm
  have e4 : e (KIP126.Computation.Table.basis .sphere 10 134 4) =
      Finsupp.single (4 : Fin 5) 1 := by
    simpa only [LinearEquiv.apply_symm_apply] using (congrArg e he4).symm
  intro hz
  have hh := congrArg (fun a => (e a) (2 : Fin 5)) hz
  simp only [map_add,map_zero,Finsupp.add_apply,Finsupp.zero_apply,e2,e4] at hh
  norm_num [Finsupp.single_apply,Fin.ext_iff] at hh

universe u
private theorem nonzero_page_two_differential
    {R : Type u} [Ring R]
    {E : KIP126.Core.SpectralSequence (ModuleCat.{v} R) (ℤ × ℤ)}
    {p q : ℤ × ℤ} {x : E.Page 2 p} {y : E.Page 2 q}
    (hd : HasDifferential E 2 p q x y) (hne : y ≠ 0) :
    HasNonzeroDifferential E 2 p q x y := by
  obtain ⟨hdeg,heq⟩ := hd.eq_on_page_two
  exact ⟨hdeg,x,y,RepresentsOnPage.self_two x,RepresentsOnPage.self_two y,heq,hne⟩


public theorem d2_x125_8 : HasNonzeroDifferential model.classical.sphere 2 (8,133) (10,134)
    (atom .x_125_8) d2Target := by
  apply nonzero_page_two_differential actual_d2_x1258_equation
  rw [←actual_d2_target_basis]
  exact basis2_add_basis4_nonzero

private theorem sphere_d4_7_133_zero :
    model.classical.sphere.d 4 (7,133) = 0 := by
  classical
  let E := model.classical.sphere
  have hs2 : E.r₀ ≤ 2 := by
    change (model.classical.obj KIP126.StableHomotopy.SphereSpectrum).r₀ ≤ 2
    rw [model.classical.firstPage]
  have h165 : HasDifferential E 2 (5,132) (7,133)
      (KIP126.Computation.Table.basis .sphere 5 132 0)
      (KIP126.Computation.Table.basis .sphere 7 133 1) := by
    have hrow := KIP126.Computation.Table.result
      ⟨.sphere,.equation,2,5,132,[0],7,133,[1],"S0_AdamsE2_ss",2575⟩ (by
        exact List.mem_of_getElem? (l := KIP126.Computation.Table.Raw.claims) (i := 165) rfl)
    dsimp only [KIP126.Computation.Table.Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (5,132) (7,133) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees
      .sphere 5 132 [0] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees
      .sphere 7 133 [1] = true := rfl
    simp only [KIP126.Computation.Table.decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  have h186 : ReachesPage E 18 (7,133)
      (KIP126.Computation.Table.basis .sphere 7 133 0) := by
    have hrow := KIP126.Computation.Table.result
      ⟨.sphere,.reaches,18,7,133,[0],7,133,[],"S0_AdamsE2_ss",2632⟩ (by
        exact List.mem_of_getElem? (l := KIP126.Computation.Table.Raw.claims) (i := 186) rfl)
    dsimp only [KIP126.Computation.Table.Statement] at hrow
    obtain ⟨x,hx,hlate⟩ := hrow
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees
      .sphere 7 133 [0] = true := rfl
    simp only [KIP126.Computation.Table.decode,vx,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
    rw [←hx] at hlate
    exact hlate
  obtain ⟨a18,ha18⟩ := h186
  obtain ⟨a0,ha0⟩ := represents_before (by decide : (2 : ℤ) ≤ 4)
    (by decide : (4 : ℤ) ≤ 18) ha18
  have da0 : E.d 4 (7,133) a0 = 0 :=
    represents_d_zero_of_later (le_trans hs2 (by decide)) (by decide : (4 : ℤ) < 18)
      ha0 ⟨a18,ha18⟩
  have ha1 : RepresentsOnPage E 4 (7,133)
      (KIP126.Computation.Table.basis .sphere 7 133 1) 0 :=
    differential_target_later_zero hs2 (by decide) h165
  obtain ⟨e,he⟩ := KIP126.Computation.Table.basis_correct
    ⟨.sphere,7,133,["1,1,69,1,76,1", "0,5,69,2"]⟩ (by
      exact List.mem_of_getElem? (l := KIP126.Computation.Table.Raw.degrees) (i := 150) rfl)
  change E.Page 2 (7,133) ≃ₗ[ℤ] (Fin 2 →₀ F2) at e
  change ∀ i : Fin 2, e.symm (Finsupp.single i 1) =
    KIP126.Computation.Table.basis .sphere 7 133 i.val at he
  have hv (i : Fin 2) : RepresentsOnPage E 4 (7,133)
      (e.symm (Finsupp.single i 1)) (![a0,0] i) := by
    rw [he i]
    fin_cases i
    · exact ha0
    · exact ha1
  have hz (z : E.Page 4 (7,133)) : E.d 4 (7,133) z = 0 := by
    obtain ⟨c,hc⟩ := page_generated_from_representatives (by decide : (2 : ℤ) ≤ 4)
      e ![a0,0] hv z
    have hform : z = if c 0 = 0 then 0 else a0 := by
      simpa only [Fin.sum_univ_succ,Fin.sum_univ_zero,Matrix.cons_val_zero,
        Matrix.cons_val_succ,ite_self,add_zero] using hc
    rw [hform]
    by_cases hc0 : c 0 = 0
    · simp only [hc0,ite_true,map_zero]
    · simp only [hc0,ite_false,da0]
  ext z
  exact hz z


private theorem labels_equal_at_three_of_zero_incoming_two
    {E : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ×ℤ)}
    (hs : E.r₀≤2) {p q : ℤ×ℤ} (hdeg : p+E.diffDeg 2=q) (hin : E.d 2 p=0)
    {x y : E.Page 2 q} {a : E.Page 3 q}
    (hx : RepresentsOnPage E 3 q x a) (hy : RepresentsOnPage E 3 q y a) : x=y := by
  by_contra hxy
  have hn : x-y≠0 := sub_ne_zero.mpr hxy
  have hr : RepresentsOnPage E 3 q (x-y) 0 := by
    simpa only [sub_self] using represents_sub hx hy
  have hzero : (0 : E.Page 3 q)≠0 :=
    represents_next_nonzero_of_incoming_zero_at hs (by decide) hin hr
      (represents_two_self _) hn hdeg
  exact hzero rfl

private theorem y_survives_five_of_fourth_incoming_zero
    (hin4 : model.classical.sphere.d 4 (7,133)=0) :
    SurvivesTo model.classical.sphere 5 (11,136) Y := by
  classical
  let E := model.classical.sphere
  have hs2 : E.r₀≤2 := by
    change model.classical.sphere.r₀≤2
    rw [model.classical.firstPage]
  have hs3 : E.r₀≤3 := hs2.trans (by decide)
  have hs4 : E.r₀≤4 := hs2.trans (by decide)
  have h190 : HasDifferential E 2 (7,134) (9,135)
      (basis .sphere 7 134 1) (basis .sphere 9 135 4) := by
    have hrow := result ⟨.sphere, .equation, 2, 7, 134, [1], 9, 135, [4], "S0_AdamsE2_ss", 2709⟩ (by
      exact List.mem_of_getElem? (i := 190) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 2 (7,134) (9,135) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 7 134 [1]=true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 9 135 [4]=true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    exact h
  have h191 : HasDifferential E 2 (7,134) (9,135)
      (basis .sphere 7 134 4) (basis .sphere 9 135 5) := by
    have hrow := result ⟨.sphere, .equation, 2, 7, 134, [4], 9, 135, [5], "S0_AdamsE2_ss", 2710⟩ (by
      exact List.mem_of_getElem? (i := 191) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 2 (7,134) (9,135) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 7 134 [4]=true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 9 135 [5]=true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    exact h
  have h231 : HasDifferential E 4 (9,135) (13,138)
      (basis .sphere 9 135 2) (basis .sphere 13 138 0) := by
    have hrow := result ⟨.sphere, .equation, 4, 9, 135, [2], 13, 138, [0], "S0_AdamsE2_ss", 2790⟩ (by
      exact List.mem_of_getElem? (i := 231) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 4 (9,135) (13,138) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 9 135 [2]=true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 13 138 [0]=true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    exact h
  have h232 : HasDifferential E 4 (9,135) (13,138)
      (basis .sphere 9 135 1) (basis .sphere 13 138 2) := by
    have hrow := result ⟨.sphere, .equation, 4, 9, 135, [1], 13, 138, [2], "S0_AdamsE2_ss", 2791⟩ (by
      exact List.mem_of_getElem? (i := 232) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 4 (9,135) (13,138) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 9 135 [1]=true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 13 138 [2]=true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    exact h
  have h233 : HasDifferential E 3 (9,135) (12,137)
      (basis .sphere 9 135 0) (basis .sphere 12 137 3 + basis .sphere 12 137 4) := by
    have hrow := result ⟨.sphere, .equation, 3, 9, 135, [0], 12, 137, [3, 4], "S0_AdamsE2_ss", 2792⟩ (by
      exact List.mem_of_getElem? (i := 233) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 3 (9,135) (12,137) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 9 135 [0]=true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 12 137 [3, 4]=true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    exact h
  have h234 : HasDifferential E 3 (9,135) (12,137)
      (basis .sphere 9 135 3) (basis .sphere 12 137 3) := by
    have hrow := result ⟨.sphere, .equation, 3, 9, 135, [3], 12, 137, [3], "S0_AdamsE2_ss", 2793⟩ (by
      exact List.mem_of_getElem? (i := 234) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 3 (9,135) (12,137) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 9 135 [3]=true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 12 137 [3]=true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    exact h
  have h176 : HasDifferential E 2 (6,133) (8,134)
      (basis .sphere 6 133 1) (basis .sphere 8 134 5) := by
    have hrow := result ⟨.sphere, .equation, 2, 6, 133, [1], 8, 134, [5], "S0_AdamsE2_ss", 2634⟩ (by
      exact List.mem_of_getElem? (i := 176) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 2 (6,133) (8,134) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 6 133 [1]=true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 8 134 [5]=true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    exact h
  have h203 : ReachesPage E 17 (8,134) (basis .sphere 8 134 4) := by
    have hrow := result ⟨.sphere, .reaches, 17, 8, 134, [4], 8, 134, [], "S0_AdamsE2_ss", 2701⟩ (by
      exact List.mem_of_getElem? (i := 203) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,h⟩ := hrow
    have vx : Raw.coordinatesValid Raw.degrees .sphere 8 134 [4]=true := rfl
    simp only [decode,vx,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      add_zero,Option.some.injEq] at ha
    rw [←ha] at h
    exact h
  have h204 : ReachesPage E 6 (8,134) (basis .sphere 8 134 0 + basis .sphere 8 134 3) := by
    have hrow := result ⟨.sphere, .reaches, 6, 8, 134, [0, 3], 8, 134, [], "S0_AdamsE2_ss", 2702⟩ (by
      exact List.mem_of_getElem? (i := 204) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,h⟩ := hrow
    have vx : Raw.coordinatesValid Raw.degrees .sphere 8 134 [0, 3]=true := rfl
    simp only [decode,vx,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      add_zero,Option.some.injEq] at ha
    rw [←ha] at h
    exact h
  have h205 : HasDifferential E 3 (8,134) (11,136)
      (basis .sphere 8 134 3) (basis .sphere 11 136 1) := by
    have hrow := result ⟨.sphere, .equation, 3, 8, 134, [3], 11, 136, [1], "S0_AdamsE2_ss", 2703⟩ (by
      exact List.mem_of_getElem? (i := 205) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 3 (8,134) (11,136) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 8 134 [3]=true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 11 136 [1]=true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    exact h
  have h206 : HasDifferential E 3 (8,134) (11,136)
      (basis .sphere 8 134 2) (basis .sphere 11 136 2) := by
    have hrow := result ⟨.sphere, .equation, 3, 8, 134, [2], 11, 136, [2], "S0_AdamsE2_ss", 2704⟩ (by
      exact List.mem_of_getElem? (i := 206) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 3 (8,134) (11,136) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 8 134 [2]=true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 11 136 [2]=true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    exact h
  have h207 : HasDifferential E 2 (8,134) (10,135)
      (basis .sphere 8 134 1) (basis .sphere 10 135 3) := by
    have hrow := result ⟨.sphere, .equation, 2, 8, 134, [1], 10, 135, [3], "S0_AdamsE2_ss", 2705⟩ (by
      exact List.mem_of_getElem? (i := 207) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 2 (8,134) (10,135) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 8 134 [1]=true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 10 135 [3]=true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    exact h
  have h281 : ReachesPage E 5 (11,136) (basis .sphere 11 136 3) := by
    have hrow := result ⟨.sphere, .reaches, 5, 11, 136, [3], 11, 136, [], "S0_AdamsE2_ss", 2852⟩ (by
      exact List.mem_of_getElem? (i := 281) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,h⟩ := hrow
    have vx : Raw.coordinatesValid Raw.degrees .sphere 11 136 [3]=true := rfl
    simp only [decode,vx,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      add_zero,Option.some.injEq] at ha
    rw [←ha] at h
    exact h
  obtain ⟨e2,he2⟩ := basis_correct ⟨.sphere, 9, 135, ["414,1", "1,1,376,1", "1,1,375,1", "0,1,394,1", "0,1,392,1", "0,7,69,2"]⟩ (by
    exact List.mem_of_getElem? (i := 174) (by rfl))
  change E.Page 2 (9,135) ≃ₗ[ℤ] (Fin 6 →₀ F2) at e2
  change ∀ i : Fin 6, e2.symm (Finsupp.single i 1)=basis .sphere 9 135 i.val at he2
  obtain ⟨e,he⟩ := basis_correct ⟨.sphere, 8, 134, ["395,1", "394,1", "393,1", "392,1", "69,1,85,1", "0,6,69,2"]⟩ (by
    exact List.mem_of_getElem? (i := 162) (by rfl))
  change E.Page 2 (8,134) ≃ₗ[ℤ] (Fin 6 →₀ F2) at e
  change ∀ i : Fin 6, e.symm (Finsupp.single i 1)=basis .sphere 8 134 i.val at he
  obtain ⟨g,hg⟩ := basis_correct ⟨.sphere, 11, 136, ["69,1,89,1", "1,1,389,1", "1,1,388,1", "0,2,391,1", "0,3,375,1"]⟩ (by
    exact List.mem_of_getElem? (i := 192) (by rfl))
  change E.Page 2 (11,136) ≃ₗ[ℤ] (Fin 5 →₀ F2) at g
  change ∀ i : Fin 5, g.symm (Finsupp.single i 1)=basis .sphere 11 136 i.val at hg
  obtain ⟨f,hf⟩ := basis_correct ⟨.sphere, 10, 135, ["413,1", "412,1", "0,1,391,1", "0,1,390,1", "0,2,375,1"]⟩ (by
    exact List.mem_of_getElem? (i := 182) (by rfl))
  change E.Page 2 (10,135) ≃ₗ[ℤ] (Fin 5 →₀ F2) at f
  change ∀ i : Fin 5, f.symm (Finsupp.single i 1)=basis .sphere 10 135 i.val at hf
  have hin2 : E.d 2 (9,135)=0 := by
    obtain ⟨_,a0,_,ha0,_,_⟩ := h233
    obtain ⟨_,a14,_,ha14,_,_⟩ := h232
    obtain ⟨a1,ha1⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤4) ha14
    obtain ⟨_,a24,_,ha24,_,_⟩ := h231
    obtain ⟨a2,ha2⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤4) ha24
    obtain ⟨_,a3,_,ha3,_,_⟩ := h234
    have ha4 : RepresentsOnPage E 3 (9,135) (basis .sphere 9 135 4) 0 :=
      differential_target_later_zero hs2 (by decide) h190
    have ha5 : RepresentsOnPage E 3 (9,135) (basis .sphere 9 135 5) 0 :=
      differential_target_later_zero hs2 (by decide) h191
    have before3 (x : E.Page 2 (9,135)) (hx : ReachesPage E 3 (9,135) x) :
        E.d 2 (9,135) x=0 :=
      represents_d_zero_of_later hs2 (by decide) (represents_two_self _) hx
    apply d_zero_of_complete_representatives (by decide : (2:ℤ)≤2) e2
    intro i
    refine ⟨e2.symm (Finsupp.single i 1),represents_two_self _,?_⟩
    rw [he2 i]
    fin_cases i
    · exact before3 _ ⟨a0,ha0⟩
    · exact before3 _ ⟨a1,ha1⟩
    · exact before3 _ ⟨a2,ha2⟩
    · exact before3 _ ⟨a3,ha3⟩
    · exact before3 _ ⟨0,ha4⟩
    · exact before3 _ ⟨0,ha5⟩
  have bY : basis .sphere 11 136 3=Y := by
    have h := basis_value ⟨.mul (.mul (.named .h0) (.named .h0)) (.named .x_125_9_2),3⟩ (by decide)
    simp only [Expression.value,Expression.degree,atom_h0] at h
    change basis .sphere 11 136 3=Y at h
    exact h
  have gy1 : g (basis .sphere 11 136 1)=Finsupp.single (1 : Fin 5) 1 := by
    have h : g.symm (Finsupp.single (1 : Fin 5) 1)=basis .sphere 11 136 1 := hg 1
    rw [←h,LinearEquiv.apply_symm_apply]
  have gy2 : g (basis .sphere 11 136 2)=Finsupp.single (2 : Fin 5) 1 := by
    have h : g.symm (Finsupp.single (2 : Fin 5) 1)=basis .sphere 11 136 2 := hg 2
    rw [←h,LinearEquiv.apply_symm_apply]
  have gy3 : g (basis .sphere 11 136 3)=Finsupp.single (3 : Fin 5) 1 := by
    have h : g.symm (Finsupp.single (3 : Fin 5) 1)=basis .sphere 11 136 3 := hg 3
    rw [←h,LinearEquiv.apply_symm_apply]
  have coordY : g Y 3=1 := by rw [←bY,gy3];exact Finsupp.single_eq_same
  have coord1 : g (basis .sphere 11 136 1) 3=0 := by
    rw [gy1]
    norm_num [Finsupp.single_apply,Fin.ext_iff]
  have coord2 : g (basis .sphere 11 136 2) 3=0 := by
    rw [gy2]
    norm_num [Finsupp.single_apply,Fin.ext_iff]
  have reachY : ReachesPage E 5 (11,136) Y := by rw [←bY];exact h281
  obtain ⟨y5,hy5⟩ := reachY
  obtain ⟨y3,hy3⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤5) hy5
  obtain ⟨y4,hy4⟩ := represents_before (by decide : (2:ℤ)≤4) (by decide : (4:ℤ)≤5) hy5
  have deg2 : (9,135)+E.diffDeg 2=(11,136) := by
    simp only [E,Classical.Adams.ClassicalAdamsFamily.sphere,Classical.Adams.ClassicalAdamsFamily.obj,
      model.classical.differentialDegree,Prod.mk_add_mk,Int.reduceAdd,Int.reduceSub]
  obtain ⟨deg3,a3,t1,ha3,ht1,hd3⟩ := h205
  obtain ⟨_,a2,t2,ha2,ht2,hd2⟩ := h206
  obtain ⟨aW6,haW6⟩ := h204
  obtain ⟨aW3,haW3⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤6) haW6
  let a0 := aW3-a3
  have ha0 : RepresentsOnPage E 3 (8,134) (basis .sphere 8 134 0) a0 := by
    simpa only [add_sub_cancel_right] using represents_sub haW3 ha3
  obtain ⟨a417,ha417⟩ := h203
  obtain ⟨a4,ha4⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤17) ha417
  have ha5 : RepresentsOnPage E 3 (8,134) (basis .sphere 8 134 5) 0 :=
    differential_target_later_zero hs2 (by decide) h176
  let δ2 : E.Page 2 (8,134) ⟶ E.Page 2 (10,135) :=
    E.d 2 (8,134) ≫ eqToHom (congrArg (E.Page 2) h207.target_degree)
  have before3 (x : E.Page 2 (8,134)) (hx : ReachesPage E 3 (8,134) x) : δ2 x=0 := by
    have hd := represents_d_zero_of_later hs2 (by decide) (represents_two_self _) hx
    change (E.d 2 (8,134) ≫ _) x=0
    rw [ModuleCat.comp_apply,hd,map_zero]
  have d20 : δ2 (basis .sphere 8 134 0)=0 := before3 _ ⟨a0,ha0⟩
  have d21 : δ2 (basis .sphere 8 134 1)=basis .sphere 10 135 3 := h207.eq_on_page_two.2
  have d22 : δ2 (basis .sphere 8 134 2)=0 := before3 _ ⟨a2,ha2⟩
  have d23 : δ2 (basis .sphere 8 134 3)=0 := before3 _ ⟨a3,ha3⟩
  have d24 : δ2 (basis .sphere 8 134 4)=0 := before3 _ ⟨a4,ha4⟩
  have d25 : δ2 (basis .sphere 8 134 5)=0 := before3 _ ⟨0,ha5⟩
  have d2target_ne : basis .sphere 10 135 3≠0 := by
    have hf3 : f.symm (Finsupp.single (3 : Fin 5) 1)=basis .sphere 10 135 3 := hf 3
    rw [←hf3]
    exact basis_vector_ne_zero f 3
  have δ2bit (c : F2) (a : E.Page 2 (8,134)) :
      δ2 (if c=0 then 0 else a)=if c=0 then 0 else δ2 a := by
    by_cases hc : c=0 <;> simp only [hc,ite_true,ite_false,map_zero]
  let δ3 : E.Page 3 (8,134) ⟶ E.Page 3 (11,136) :=
    E.d 3 (8,134) ≫ eqToHom (congrArg (E.Page 3) deg3)
  have d3 : δ3 a3=t1 := hd3
  have d2 : δ3 a2=t2 := hd2
  have dW : δ3 aW3=0 := by
    have hd := represents_d_zero_of_later hs3 (by decide : (3:ℤ)<6) haW3 ⟨aW6,haW6⟩
    change (E.d 3 (8,134) ≫ _) aW3=0
    rw [ModuleCat.comp_apply,hd,map_zero]
  have d0 : δ3 a0= -t1 := by
    change δ3 (aW3-a3)= -t1
    rw [map_sub,dW,d3,zero_sub]
  have d4 : δ3 a4=0 := by
    have hd := represents_d_zero_of_later hs3 (by decide : (3:ℤ)<17) ha4 ⟨a417,ha417⟩
    change (E.d 3 (8,134) ≫ _) a4=0
    rw [ModuleCat.comp_apply,hd,map_zero]
  have δ3bit (c : F2) (a : E.Page 3 (8,134)) :
      δ3 (if c=0 then 0 else a)=if c=0 then 0 else δ3 a := by
    by_cases hc : c=0 <;> simp only [hc,ite_true,ite_false,map_zero]
  have y4ne : y4≠0 := by
    apply represents_next_nonzero_of_not_incoming_at deg3 hs3 (by decide) hy4 hy3
    intro z hhit
    change δ3 z=y3 at hhit
    obtain ⟨x,hxz⟩ := page_has_initial_representative (by decide : (2:ℤ)≤3) z
    have hx := finite_basis_expansion e x
    simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,he,add_zero] at hx
    change x=(if e x 0=0 then 0 else basis .sphere 8 134 0)+
      ((if e x 1=0 then 0 else basis .sphere 8 134 1)+
      ((if e x 2=0 then 0 else basis .sphere 8 134 2)+
      ((if e x 3=0 then 0 else basis .sphere 8 134 3)+
      ((if e x 4=0 then 0 else basis .sphere 8 134 4)+
       (if e x 5=0 then 0 else basis .sphere 8 134 5))))) at hx
    have dx : δ2 x=0 := before3 _ ⟨z,hxz⟩
    have hdx := congrArg δ2 hx
    simp only [map_add,δ2bit,d20,d21,d22,d23,d24,d25,ite_self,zero_add,add_zero] at hdx
    have c1 : e x 1=0 := by
      by_contra hh
      apply d2target_ne
      simpa only [hh,ite_false] using hdx.symm.trans dx
    let zform := (if e x 0=0 then 0 else a0)+
      ((if e x 2=0 then 0 else a2)+((if e x 3=0 then 0 else a3)+
       (if e x 4=0 then 0 else a4)))
    have rsum := represents_add_tail (represents_bit (e x 0) ha0)
      (represents_add_tail (represents_bit (e x 2) ha2)
        (represents_add_tail (represents_bit (e x 3) ha3)
          (represents_add_tail (represents_bit (e x 4) ha4) (represents_bit (e x 5) ha5))))
    have xx : x=(if e x 0=0 then 0 else basis .sphere 8 134 0)+
      ((if e x 2=0 then 0 else basis .sphere 8 134 2)+
      ((if e x 3=0 then 0 else basis .sphere 8 134 3)+
      ((if e x 4=0 then 0 else basis .sphere 8 134 4)+
       (if e x 5=0 then 0 else basis .sphere 8 134 5)))) := by
      simpa only [c1,ite_true,zero_add] using hx
    have rx : RepresentsOnPage E 3 (8,134) x zform := by
      simp only [ite_self,add_zero] at rsum
      rw [←xx] at rsum
      exact rsum
    have z_eq : z=zform := represents_unique hxz rx
    let im2 := (if e x 0=0 then 0 else -basis .sphere 11 136 1)+
      ((if e x 2=0 then 0 else basis .sphere 11 136 2)+
       (if e x 3=0 then 0 else basis .sphere 11 136 1))
    let im3 := (if e x 0=0 then 0 else -t1)+
      ((if e x 2=0 then 0 else t2)+(if e x 3=0 then 0 else t1))
    have hform : δ3 z=im3 := by
      rw [z_eq]
      change δ3 ((if e x 0=0 then 0 else a0)+
        ((if e x 2=0 then 0 else a2)+((if e x 3=0 then 0 else a3)+
         (if e x 4=0 then 0 else a4))))=im3
      simp only [map_add,δ3bit,d0,d2,d3,d4,ite_self,add_zero]
      rfl
    have htneg : RepresentsOnPage E 3 (11,136) (-basis .sphere 11 136 1) (-t1) := by
      simpa only [zero_sub] using represents_sub
        (RepresentsOnPage.zero (E:=E) (p:=(11,136)) (by decide : (2:ℤ)≤3)) ht1
    have rim : RepresentsOnPage E 3 (11,136) im2 im3 :=
      represents_add_tail (represents_bit (e x 0) htneg)
        (represents_add_tail (represents_bit (e x 2) ht2) (represents_bit (e x 3) ht1))
    have him3 : im3=y3 := hform.symm.trans hhit
    rw [him3] at rim
    have labels : Y=im2 := labels_equal_at_three_of_zero_incoming_two hs2 deg2 hin2 hy3 rim
    have coordneg : g (-basis .sphere 11 136 1) 3=0 := by
      rw [map_neg,Finsupp.neg_apply,coord1,neg_zero]
    have gbit (c : F2) (a : E.Page 2 (11,136)) :
        g (if c=0 then 0 else a) 3=if c=0 then 0 else g a 3 := by
      by_cases hc : c=0 <;> simp only [hc,ite_true,ite_false,map_zero,Finsupp.zero_apply]
    have cim : g im2 3=0 := by
      change g ((if e x 0=0 then 0 else -basis .sphere 11 136 1)+
        ((if e x 2=0 then 0 else basis .sphere 11 136 2)+
         (if e x 3=0 then 0 else basis .sphere 11 136 1))) 3=0
      simp only [map_add,Finsupp.add_apply,gbit,coordneg,coord2,coord1,ite_self,zero_add]
    have hc := congrArg (fun a=>g a 3) labels
    exact one_ne_zero (coordY.symm.trans (hc.trans cim))
  have deg4 : (7,133)+E.diffDeg 4=(11,136) := by
    simp only [E,Classical.Adams.ClassicalAdamsFamily.sphere,Classical.Adams.ClassicalAdamsFamily.obj,
      model.classical.differentialDegree,Prod.mk_add_mk,Int.reduceAdd,Int.reduceSub]
  have y5ne : y5≠0 := represents_next_nonzero_of_incoming_zero_at hs4 (by decide)
    hin4 hy5 hy4 y4ne deg4
  exact ⟨y5,hy5,y5ne⟩


public theorem y_to_e5 : SurvivesTo model.classical.sphere 5 (11,136) Y := by
  exact y_survives_five_of_fourth_incoming_zero sphere_d4_7_133_zero

public theorem y_not_hit : NeverHit model.classical.sphere (11,136) Y := by sorry

private theorem d_zero_of_empty_initial_basis
    {E : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ×ℤ)}
    {p : ℤ×ℤ} (r : ℤ) (hr : 2≤r)
    (e : E.Page 2 p ≃ₗ[ℤ] (Fin 0 →₀ F2)) : E.d r p=0 := by
  haveI : Subsingleton (E.Page 2 p) := e.injective.subsingleton
  have hz (y : E.Page r p) : y=0 := by
    obtain ⟨x,hx⟩ := page_has_initial_representative hr y
    rw [Subsingleton.elim x 0] at hx
    exact represents_unique hx (RepresentsOnPage.zero hr)
  ext y
  change E.d r p y=0
  rw [hz y,map_zero]

private theorem third_nonzero_of_zero_incoming_two_at
    {E : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ×ℤ)}
    (hs : E.r₀≤2) {p q s : ℤ×ℤ} {x : E.Page 2 p} {y : E.Page 2 q}
    (hd : HasDifferential E 3 p q x y) (hin : E.d 2 s=0)
    (hy : y≠0) (hdeg : s+E.diffDeg 2=q) : HasNonzeroDifferential E 3 p q x y := by
  obtain ⟨h,a,b,ha,hb,heq⟩ := hd
  have bn : b≠0 := represents_next_nonzero_of_incoming_zero_at hs (by decide)
    hin hb (represents_two_self _) hy hdeg
  exact ⟨h,a,b,ha,hb,heq,bn⟩

public theorem x_to_e6 : SurvivesTo model.classical.sphere 6 (8,130) X := by
  classical
  let E := model.classical.sphere
  have hs2 : E.r₀≤2 := by
    change model.classical.sphere.r₀≤2
    rw [model.classical.firstPage]
  have h197 : ReachesPage E 6 (8,130) (basis .sphere 8 130 0) := by
    have hrow := result ⟨.sphere, .reaches, 6, 8, 130, [0], 8, 130, [], "S0_AdamsE2_ss", 2433⟩ (by
      exact List.mem_of_getElem? (i := 197) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,h⟩ := hrow
    have vx : Raw.coordinatesValid Raw.degrees .sphere 8 130 [0]=true := rfl
    simp only [decode,vx,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      add_zero,Option.some.injEq] at ha
    rw [←ha] at h
    exact h
  obtain ⟨g,hg⟩ := basis_correct ⟨.sphere, 8, 130, ["1,1,323,1"]⟩ (by
    exact List.mem_of_getElem? (i := 158) (by rfl))
  change E.Page 2 (8,130) ≃ₗ[ℤ] (Fin 1 →₀ F2) at g
  change ∀ i : Fin 1, g.symm (Finsupp.single i 1)=basis .sphere 8 130 i.val at hg
  have bX : basis .sphere 8 130 0=X := by
    have h := basis_value ⟨.mul (.named .h1) (.named .x_121_7),0⟩ (by decide)
    simp only [Expression.value,Expression.degree,atom_h1] at h
    change basis .sphere 8 130 0=X at h
    exact h
  have Xne : X≠0 := by
    have hg0 : g.symm (Finsupp.single (0 : Fin 1) 1)=basis .sphere 8 130 0 := hg 0
    rw [←bX,←hg0]
    exact basis_vector_ne_zero g 0
  have hx6 : ReachesPage E 6 (8,130) X := by rw [←bX];exact h197
  obtain ⟨x6,hx6⟩ := hx6
  have hin2 : E.d 2 (6,129)=0 := by
    obtain ⟨e,he⟩ := basis_correct ⟨.sphere, 6, 129, []⟩ (by
      exact List.mem_of_getElem? (i := 135) (by rfl))
    change E.Page 2 (6,129) ≃ₗ[ℤ] (Fin 0 →₀ F2) at e
    exact d_zero_of_empty_initial_basis 2 (by decide) e
  have deg2 : (6,129)+E.diffDeg 2=(8,130) := by
    simp only [E,Classical.Adams.ClassicalAdamsFamily.sphere,Classical.Adams.ClassicalAdamsFamily.obj,
      model.classical.differentialDegree,Prod.mk_add_mk,Int.reduceAdd,Int.reduceSub]
  have hin3 : E.d 3 (5,128)=0 := by
    obtain ⟨e,he⟩ := basis_correct ⟨.sphere, 5, 128, []⟩ (by
      exact List.mem_of_getElem? (i := 124) (by rfl))
    change E.Page 2 (5,128) ≃ₗ[ℤ] (Fin 0 →₀ F2) at e
    exact d_zero_of_empty_initial_basis 3 (by decide) e
  have deg3 : (5,128)+E.diffDeg 3=(8,130) := by
    simp only [E,Classical.Adams.ClassicalAdamsFamily.sphere,Classical.Adams.ClassicalAdamsFamily.obj,
      model.classical.differentialDegree,Prod.mk_add_mk,Int.reduceAdd,Int.reduceSub]
  have hin4 : E.d 4 (4,127)=0 := by
    obtain ⟨e,he⟩ := basis_correct ⟨.sphere, 4, 127, []⟩ (by
      exact List.mem_of_getElem? (i := 116) (by rfl))
    change E.Page 2 (4,127) ≃ₗ[ℤ] (Fin 0 →₀ F2) at e
    exact d_zero_of_empty_initial_basis 4 (by decide) e
  have deg4 : (4,127)+E.diffDeg 4=(8,130) := by
    simp only [E,Classical.Adams.ClassicalAdamsFamily.sphere,Classical.Adams.ClassicalAdamsFamily.obj,
      model.classical.differentialDegree,Prod.mk_add_mk,Int.reduceAdd,Int.reduceSub]
  have hin5 : E.d 5 (3,126)=0 := by
    obtain ⟨e,he⟩ := basis_correct ⟨.sphere, 3, 126, []⟩ (by
      exact List.mem_of_getElem? (i := 105) (by rfl))
    change E.Page 2 (3,126) ≃ₗ[ℤ] (Fin 0 →₀ F2) at e
    exact d_zero_of_empty_initial_basis 5 (by decide) e
  have deg5 : (3,126)+E.diffDeg 5=(8,130) := by
    simp only [E,Classical.Adams.ClassicalAdamsFamily.sphere,Classical.Adams.ClassicalAdamsFamily.obj,
      model.classical.differentialDegree,Prod.mk_add_mk,Int.reduceAdd,Int.reduceSub]
  obtain ⟨x3,hx3⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤6) hx6
  obtain ⟨x4,hx4⟩ := represents_before (by decide : (2:ℤ)≤4) (by decide : (4:ℤ)≤6) hx6
  obtain ⟨x5,hx5⟩ := represents_before (by decide : (2:ℤ)≤5) (by decide : (5:ℤ)≤6) hx6
  have x3ne : x3≠0 := represents_next_nonzero_of_incoming_zero_at
    (hs2.trans (by decide : (2:ℤ)≤2)) (by decide) hin2 hx3 (represents_two_self X) Xne deg2
  have x4ne : x4≠0 := represents_next_nonzero_of_incoming_zero_at
    (hs2.trans (by decide : (2:ℤ)≤3)) (by decide) hin3 hx4 hx3 x3ne deg3
  have x5ne : x5≠0 := represents_next_nonzero_of_incoming_zero_at
    (hs2.trans (by decide : (2:ℤ)≤4)) (by decide) hin4 hx5 hx4 x4ne deg4
  have x6ne : x6≠0 := represents_next_nonzero_of_incoming_zero_at
    (hs2.trans (by decide : (2:ℤ)≤5)) (by decide) hin5 hx6 hx5 x5ne deg5
  exact ⟨x6,hx6,x6ne⟩

/-- The E₆ continuation excludes earlier hits. The three remaining
nonnegative-filtration source components have zero archived E₂ dimension. -/
public theorem x_not_hit : NeverHit model.classical.sphere (8,130) X := by
  intro r hr q hq y hy hne z hd
  by_cases hlt : r<6
  · exact no_earlier_hit_of_survival
      (by rw [model.classical.firstPage]; omega) hr hlt x_to_e6
      ⟨q,hq,z,y,hy,hne,hd⟩
  · have hs : q.1+r=8 := by
      have h := congrArg Prod.fst hq
      simp only [ClassicalAdamsFamily.sphere,ClassicalAdamsFamily.obj,
        model.classical.differentialDegree] at h
      change q.1+r=8 at h
      exact h
    have ht : q.2+(r-1)=130 := by
      have h := congrArg Prod.snd hq
      simp only [ClassicalAdamsFamily.sphere,ClassicalAdamsFamily.obj,
        model.classical.differentialDegree] at h
      change q.2+(r-1)=130 at h
      exact h
    have hzpage : Subsingleton (model.classical.sphere.Page r q) := by
      by_cases hbig : 9≤r
      · exact KIP126.AdamsSynthetic.Standard.classical_page_negative .sphere r q.1 q.2 (by omega)
      · have hsmall : 6≤r ∧ r≤8 := by omega
        interval_cases r
        · have hq' : q=(2,125) := Prod.ext (by omega) (by omega)
          rw [hq']
          exact page_zero_of_initial_zero _ 6 (by decide) _
            (initial_sphere_zero 2 125 (by decide) (by decide))
        · have hq' : q=(1,124) := Prod.ext (by omega) (by omega)
          rw [hq']
          exact page_zero_of_initial_zero _ 7 (by decide) _
            (initial_sphere_zero 1 124 (by decide) (by decide))
        · have hq' : q=(0,123) := Prod.ext (by omega) (by omega)
          rw [hq']
          exact page_zero_of_initial_zero _ 8 (by decide) _
            (initial_sphere_zero 0 123 (by decide) (by decide))
    have hz : z=0 := hzpage.elim _ _
    apply hne
    simpa only [hz,ModuleCat.comp_apply,map_zero] using hd.symm


section NativeRelationCalculationHelpers
set_option maxRecDepth 100000
private theorem nativeCoreSplitOnAuxChar (s : String) (c : Char) (b i : String.Pos.Raw)
    (acc : List String) :
    s.splitOnAux (String.singleton c) b i 0 acc = s.splitAux (· == c) b i acc := by
  have hg : String.Pos.Raw.get (String.singleton c) 0 = c := by
    simp only [String.Pos.Raw.get, String.toList_singleton, String.Pos.Raw.utf8GetAux,
      ↓reduceIte]
  have hn : String.Pos.Raw.next (String.singleton c) 0 = ⟨c.utf8Size⟩ := by
    simp [String.Pos.Raw.next, hg, String.Pos.Raw.ext_iff]
  have he : String.Pos.Raw.atEnd (String.singleton c) ⟨c.utf8Size⟩ = true := by
    simp [String.Pos.Raw.atEnd]
  fun_induction String.splitAux s (· == c) b i acc with
  | case1 b i acc h => rw [String.splitOnAux, if_pos h]
  | case2 b i acc h _ h' i' ih =>
    have hi : String.Pos.Raw.get s i = c := by simpa using h'
    have hu : (String.Pos.Raw.next s i).unoffsetBy ⟨c.utf8Size⟩ = i := by
      apply String.Pos.Raw.ext
      change (i.byteIdx+(String.Pos.Raw.get s i).utf8Size)-c.utf8Size=i.byteIdx
      rw [hi]
      exact Nat.add_sub_cancel _ _
    rw [String.splitOnAux, if_neg h, hg, if_pos h', hn, if_pos he, hu]
    exact ih
  | case3 b i acc h _ h' ih =>
    have hu : i.unoffsetBy 0 = i := String.Pos.Raw.unoffsetBy_zero
    rw [String.splitOnAux, if_neg h, hg, if_neg h', hu]
    exact ih
private theorem nativeCoreSplitOnChar (s : String) (c : Char) :
    s.splitOn (String.singleton c) = (s.toList.splitOn c).map String.ofList := by
  have hc : (String.singleton c == "") = false := by simp
  rw [String.splitOn, hc, if_neg Bool.false_ne_true, nativeCoreSplitOnAuxChar]
  change String.splitToList s (· == c) = _
  rw [String.splitToList_of_valid, List.splitOn_eq_splitOnP]
private theorem nativeCoreMiddleMember (s code : String) (a c b : List Char)
    (hs : s=String.ofList (a++'\n'::(c++'\n'::b)))
    (hc : String.ofList c=code) (hn : '\n'∉c) : code∈s.splitOn "\n" := by
  rw [hs,show "\n"=String.singleton '\n' from rfl,nativeCoreSplitOnChar,String.toList_ofList,
    List.splitOn_append_cons_self,List.splitOn_append_cons_self_of_not_mem hn]
  apply List.mem_map.mpr
  exact ⟨c,List.mem_append.mpr (Or.inr (List.mem_cons_self)),hc⟩

private theorem nativeCoreFromChunk {first : List String} {chunks : Array String}
    {code : String} (i : Fin chunks.size) (h : code ∈ chunks[i].splitOn "\n") :
    code ∈ first ++ chunks.toList.flatMap (fun s=>s.splitOn "\n") := by
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  exact ⟨chunks[i],Array.mem_toList_iff.mpr (Array.getElem_mem i.isLt),h⟩

private theorem nativeCoreA :
    (sourceProduct 1 1 8 70 (sourceAtom .h0) (sourceAtom .b)).val +
      (sourceAtom .h0).val^7 * (sourceAtom .h5).val^2 = 0 := by
  change Ideal.Quotient.mk _
    ((MvPolynomial.X (atomIndex .h0) : MvPolynomial (Fin generators.count) (ZMod 2)) *
      MvPolynomial.X (atomIndex .b) +
      MvPolynomial.X (atomIndex .h0)^7 * MvPolynomial.X (atomIndex .h5)^2) = 0
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply Ideal.subset_span
  refine ⟨"0,1,82,1;0,7,18,2", ?_, ?_⟩
  · apply nativeCoreFromChunk (i := ⟨0,by decide⟩)
    apply nativeCoreMiddleMember _ "0,1,82,1;0,7,18,2" ['0',',','3',',','2',',','1','\n','0',',','1',',','2',',','2','\n','2',',','1',',','3',',','1','\n','2',',','3',';','1',',','2',',','3',',','1','\n','0',',','1',',','4',',','1','\n','0',',','4',',','3',',','1','\n','2',',','1',',','4',',','1','\n','1',',','2',',','4',',','1','\n','0',',','1',',','5',',','1','\n','1',',','1',',','3',',','2','\n','0',',','2',',','3',',','2','\n','2',',','1',',','5',',','1','\n','1',',','1',',','6',',','1','\n','1',',','2',',','5',',','1',';','0',',','2',',','6',',','1','\n','3',',','1',',','4',',','1','\n','0',',','3',',','6',',','1','\n','2',',','1',',','6',',','1',';','0',',','2',',','8',',','1','\n','0',',','3',',','8',',','1','\n','2',',','1',',','8',',','1',';','0',',','1',',','9',',','1','\n','4',',','2',';','3',',','1',',','5',',','1','\n','3',',','1',',','5',',','1',';','1',',','2',',','8',',','1','\n','0',',','1',',','1','1',',','1','\n','1',',','1',',','9',',','1',';','0',',','1',',','1','0',',','1','\n','3',',','1',',','7',',','1','\n','3',',','3',';','2',',','2',',','7',',','1','\n','1',',','1',',','1','1',',','1','\n','1',',','1',',','1','0',',','1','\n','3',',','1',',','6',',','1','\n','0',',','2',',','1','0',',','1','\n','0',',','1',',','1','2',',','1','\n','0',',','8',',','7',',','1','\n','2',',','1',',','9',',','1',';','0',',','1',',','1','3',',','1','\n','4',',','1',',','5',',','1',';','1',',','1',',','1','2',',','1','\n','0',',','4',',','9',',','1','\n','3',',','1',',','8',',','1','\n','2',',','1',',','1','0',',','1',';','1',',','1',',','1','3',',','1','\n','0',',','3',',','1','3',',','1','\n','4',',','1',',','6',',','1','\n','2',',','1',',','1','2',',','1','\n','1',',','2',',','1','2',',','1','\n','0',',','1',',','1','4',',','1','\n','1',',','2',',','1','3',',','1','\n','5',',','2',';','1',',','1',',','1','4',',','1','\n','3',',','1',',','9',',','1',';','1',',','1',',','4',',','1',',','7',',','1','\n','4',',','1',',','8',',','1','\n','3',',','1',',','1','1',',','1','\n','3',',','1',',','1','0',',','1','\n','2',',','2',',','1','1',',','1','\n','5',',','1',',','7',',','1','\n','0',',','2',',','2',',','1',',','1','3',',','1','\n','5',',','1',',','6',',','1','\n','2',',','1',',','1','4',',','1','\n','1',',','1',',','1','5',',','1','\n','1',',','2',',','1','4',',','1',';','0',',','2',',','1','5',',','1','\n','3',',','1',',','1','2',',','1','\n','0',',','3',',','1','5',',','1','\n','3',',','1',',','1','3',',','1','\n','6',',','1',',','7',',','1',';','2',',','2',',','1','3',',','1','\n','4',',','1',',','9',',','1','\n','1',',','1',',','1','7',',','1','\n','5',',','1',',','8',',','1',';','1',',','1',',','1','6',',','1','\n','6',',','2',';','2',',','1',',','1','5',',','1','\n','2',',','1',',','1','5',',','1',';','0',',','2',',','1','6',',','1','\n','4',',','1',',','1','1',',','1','\n','4',',','1',',','1','0',',','1','\n','0',',','3',',','1','6',',','1','\n','7',',','1',',','8',',','1','\n','2',',','1',',','1','7',',','1',';','0',',','1',',','2','0',',','1','\n','6',',','1',',','8',',','1',';','2',',','1',',','1','6',',','1','\n','2',',','1',',','1','6',',','1',';','0',',','1',',','1','9',',','1','\n','4',',','1',',','1','2',',','1',';','3',',','1',',','1','4',',','1','\n','3',',','1',',','1','4',',','1',';','1',',','2',',','1','6',',','1','\n','4',',','1',',','1','3',',','1','\n','1',',','1',',','2','0',',','1','\n','5',',','1',',','9',',','1',';','1',',','1',',','1','9',',','1','\n','1',',','1',',','1','9',',','1',';','0',',','2',',','2','0',',','1','\n','2',',','1',',','7',',','2','\n','1',',','2',',','7',',','2','\n','0',',','4',',','7',',','2','\n','5',',','1',',','1','1',',','1','\n','5',',','1',',','1','0',',','1','\n','3',',','1',',','1','5',',','1','\n','0',',','3',',','2','0',',','1','\n','0',',','1',',','2','1',',','1','\n','0',',','6',',','1','7',',','1','\n','7',',','1',',','9',',','1','\n','0',',','1',',','2','5',',','1','\n','0',',','1',',','2','4',',','1','\n','2',',','1',',','2','0',',','1',';','0',',','1',',','2','2',',','1','\n','6',',','1',',','9',',','1',';','2',',','1',',','1','9',',','1','\n','2',',','1',',','1','9',',','1',';','0',',','1',',','8',',','2','\n','5',',','1',',','1','2',',','1',';','4',',','1',',','1','4',',','1','\n','4',',','1',',','1','4',',','1',';','1',',','1',',','2','1',',','1','\n','0',',','4',',','1','9',',','1','\n','7',',','1',',','1','1',',','1','\n','7',',','1',',','1','0',',','1','\n','1',',','1',',','2','5',',','1',';','0',',','1',',','2','6',',','1','\n','1',',','1',',','2','4',',','1','\n','1',',','1',',','2','3',',','1','\n','6',',','1',',','1','1',',','1','\n','1',',','1',',','2','2',',','1','\n','3',',','1',',','1','7',',','1',';','0',',','2',',','2','3',',','1','\n','6',',','1',',','1','0',',','1',';','5',',','1',',','1','3',',','1','\n','3',',','1',',','1','6',',','1','\n','5',',','1',',','1','3',',','1',';','1',',','1',',','8',',','2','\n','1',',','1',',','8',',','2',';','0',',','2',',','2','2',',','1','\n','1',',','1',',','2','6',',','1','\n','0',',','2',',','2','6',',','1','\n','0',',','1',',','2','8',',','1','\n','7',',','1',',','1','2',',','1','\n','0',',','3',',','2','2',',','1','\n','6',',','1',',','1','2',',','1','\n','4',',','1',',','1','5',',','1','\n','2',',','1',',','2','1',',','1','\n','1',',','2',',','2','1',',','1','\n','0',',','1',',','2','7',',','1','\n','7',',','1',',','1','3',',','1',';','2',',','1',',','2','5',',','1','\n','8',',','1',',','1','1',',','1','\n','2',',','1',',','2','3',',','1',';','1',',','1',',','2','8',',','1','\n','8',',','1',',','1','0',',','1',';','2',',','1',',','2','2',',','1','\n','2',',','1',',','2','2',',','1',';','0',',','1',',','2','9',',','1','\n','6',',','1',',','1','3',',','1',';','0',',','1',',','8',',','1',',','9',',','1','\n','5',',','1',',','1','4',',','1',';','1',',','1',',','2','7',',','1','\n','2',',','1',',','2','6',',','1','\n','3',',','1',',','2','0',',','1','\n','1',',','1',',','2','9',',','1','\n','3',',','1',',','1','9',',','1','\n','4',',','1',',','1','7',',','1',';','0',',','2',',','8',',','1',',','9',',','1','\n','8',',','1',',','1','2',',','1',';','4',',','1',',','1','6',',','1','\n','4',',','1',',','1','6',',','1',';','0',',','5',',','2','3',',','1','\n','2',',','1',',','2','8',',','1','\n','9',',','2',';','8',',','1',',','1','3',',','1','\n','1',',','2',',','2','8',',','1','\n','7',',','1',',','1','4',',','1','\n','0',',','3',',','2','9',',','1','\n','0',',','6',',','2','3',',','1','\n','6',',','1',',','1','4',',','1','\n','5',',','1',',','1','5',',','1','\n','2',',','1',',','2','7',',','1','\n','1',',','1',',','3','0',',','1','\n','1',',','2',',','2','7',',','1',';','0',',','2',',','3','0',',','1','\n','4',',','1',',','7',',','2','\n','0',',','1',',','3','5',',','1','\n','9',',','1',',','1','1',',','1','\n','0',',','1',',','3','3',',','1','\n','9',',','1',',','1','0',',','1',';','2',',','1',',','2','9',',','1','\n','2',',','1',',','2','9',',','1',';','0',',','1',',','3','2',',','1','\n','3',',','1',',','2','1',',','1','\n','0',',','3',',','3','0',',','1','\n','3',',','1',',','2','5',',','1',';','1',',','1',',','3','5',',','1','\n','1','1',',','2',';','3',',','1',',','2','4',',','1','\n','3',',','1',',','2','4',',','1',';','2',',','2',',','2','5',',','1','\n','2',',','2',',','2','5',',','1',';','1',',','1',',','3','4',',','1','\n','1','0',',','1',',','1','1',',','1',';','2',',','2',',','2','4',',','1','\n','2',',','2',',','2','4',',','1',';','1',',','1',',','3','3',',','1','\n','3',',','1',',','2','3',',','1',';','1',',','1',',','3','3',',','1',';','0',',','2',',','3','4',',','1','\n','1','0',',','2','\n','3',',','1',',','2','2',',','1','\n','1',',','1',',','3','2',',','1','\n','1',',','1',',','8',',','1',',','1','3',',','1',';','0',',','2',',','3','2',',','1','\n','7',',','1',',','1','5',',','1',';','4',',','1',',','2','0',',','1','\n','4',',','1',',','2','0',',','1',';','0',',','2',',','8',',','1',',','1','3',',','1','\n','9',',','1',',','1','2',',','1','\n','4',',','1',',','1','9',',','1','\n','5',',','1',',','1','7',',','1','\n','8',',','1',',','1','4',',','1',';','5',',','1',',','1','6',',','1','\n','5',',','1',',','1','6',',','1',';','1',',','1',',','3','1',',','1','\n','6',',','1',',','1','5',',','1',';','2',',','1',',','3','0',',','1','\n','2',',','1',',','3','0',',','1',';','0',',','2',',','3','1',',','1','\n','3',',','1',',','2','6',',','1',';','0',',','1',',','3','7',',','1','\n','1','1',',','1',',','1','2',',','1','\n','0',',','3',',','3','2',',','1','\n','1','0',',','1',',','1','2',',','1','\n','0',',','3',',','3','1',',','1','\n','1',',','1',',','3','8',',','1','\n','2',',','1',',','3','5',',','1',';','1',',','1',',','3','7',',','1','\n','1',',','1',',','3','7',',','1',';','0',',','2',',','3','8',',','1','\n','2',',','1',',','3','4',',','1','\n','1',',','2',',','3','5',',','1',';','0',',','2',',','3','7',',','1','\n','1','1',',','1',',','1','3',',','1',';','3',',','1',',','2','8',',','1','\n','3',',','1',',','2','8',',','1',';','2',',','1',',','3','3',',','1','\n','2',',','1',',','3','3',',','1',';','1',',','1',',','3','6',',','1','\n','1',',','2',',','3','4',',','1','\n','7',',','1',',','1','7',',','1','\n','1','0',',','1',',','1','3',',','1',';','2',',','1',',','3','2',',','1','\n','1',',','2',',','3','3',',','1','\n','2',',','1',',','3','2',',','1',';','0',',','2',',','3','6',',','1','\n','7',',','1',',','1','6',',','1',';','0',',','1',',','9',',','1',',','1','3',',','1','\n','0',',','1',',','9',',','1',',','1','3',',','1',';','0',',','4',',','3','4',',','1','\n','6',',','1',',','1','7',',','1',';','0',',','1',',','4','0',',','1','\n','8',',','1',',','1','5',',','1',';','6',',','1',',','1','6',',','1','\n','6',',','1',',','1','6',',','1',';','2',',','1',',','3','1',',','1','\n','2',',','1',',','3','1',',','1',';','0',',','1',',','3','9',',','1','\n','1','2',',','2',';','4',',','1',',','2','1',',','1','\n','4',',','1',',','2','1',',','1',';','3',',','1',',','2','7',',','1','\n','3',',','1',',','2','7',',','1',';','1',',','2',',','3','1',',','1','\n','0',',','3',',','3','8',',','1','\n','4',',','1',',','2','5',',','1','\n','0',',','3',',','3','7',',','1','\n','4',',','1',',','2','4',',','1','\n','3',',','1',',','2','9',',','1','\n','4',',','1',',','2','3',',','1',';','0',',','3',',','3','6',',','1','\n','4',',','1',',','2','2',',','1',';','0',',','5',',','3','4',',','1','\n','1','2',',','1',',','1','3',',','1','\n','5',',','1',',','2','0',',','1','\n','1',',','1',',','4','0',',','1','\n','9',',','1',',','1','4',',','1',';','5',',','1',',','1','9',',','1','\n','5',',','1',',','1','9',',','1',';','1',',','1',',','3','9',',','1','\n','1',',','1',',','3','9',',','1',';','0',',','2',',','4','0',',','1','\n','7',',','1',',','1','8',',','1','\n','7',',','3',';','3',',','2',',','1','8',',','1','\n','2',',','1',',','3','8',',','1','\n','2',',','1',',','3','7',',','1','\n','4',',','1',',','2','6',',','1','\n','2',',','1',',','3','6',',','1','\n','1',',','2',',','3','6',',','1','\n','0',',','4',',','3','6',',','1','\n','0',',','6',',','3','4',',','1','\n','1','1',',','1',',','1','4',',','1','\n','1','0',',','1',',','1','4',',','1','\n','3',',','1',',','3','0',',','1','\n','0',',','3',',','4','0',',','1','\n','0',',','1',',','4','1',',','1','\n','0',',','1','6',',','1','8',',','1','\n','7',',','1',',','2','0',',','1','\n','7',',','1',',','1','9',',','1','\n','4',',','1',',','2','8',',','1','\n','0',',','1',',','1','3',',','2','\n','0',',','1',',','4','2',',','1','\n','6',',','1',',','2','0',',','1',';','2',',','1',',','4','0',',','1','\n','2',',','1',',','4','0',',','1',';','0',',','1',',','8',',','1',',','1','7',',','1','\n','9',',','1',',','1','5',',','1',';','6',',','1',',','1','9',',','1','\n','6',',','1',',','1','9',',','1',';','2',',','1',',','3','9',',','1','\n','2',',','1',',','3','9',',','1',';','0',',','1',',','8',',','1',',','1','6',',','1','\n','1','2',',','1',',','1','4',',','1',';','5',',','1',',','2','1',',','1','\n','5',',','1',',','2','1',',','1',';','4',',','1',',','2','7',',','1','\n','4',',','1',',','2','7',',','1',';','1',',','1',',','4','1',',','1','\n','0',',','4',',','3','9',',','1','\n','3',',','1',',','3','5',',','1',';','1',',','1',',','4','3',',','1','\n','3',',','1',',','3','4',',','1',';','0',',','2',',','4','3',',','1','\n','3',',','1',',','3','3',',','1','\n','3',',','1',',','3','2',',','1','\n','5',',','1',',','2','5',',','1','\n','1',',','1',',','1','3',',','2','\n','5',',','1',',','2','4',',','1','\n','4',',','1',',','2','9',',','1','\n','5',',','1',',','2','3',',','1','\n','1','1',',','1',',','1','5',',','1','\n','5',',','1',',','2','2',',','1','\n','1','3',',','1',',','1','4',',','1',';','1','0',',','1',',','1','5',',','1','\n','3',',','1',',','3','1',',','1','\n','1','0',',','1',',','1','5',',','1',';','1',',','1',',','8',',','1',',','1','6',',','1','\n','1',',','1',',','8',',','1',',','1','6',',','1',';','0',',','2',',','8',',','1',',','1','7',',','1','\n','0',',','3',',','4','3',',','1','\n','5',',','1',',','2','6',',','1','\n','9',',','1',',','1','7',',','1',';','8',',','1',',','2','0',',','1','\n','9',',','1',',','1','6',',','1',';','8',',','1',',','1','9',',','1','\n','7',',','1',',','2','1',',','1','\n','1','2',',','1',',','1','5',',','1','\n','6',',','1',',','2','1',',','1','\n','4',',','1',',','3','0',',','1','\n','2',',','1',',','4','1',',','1','\n','1',',','2',',','4','1',',','1','\n','0',',','1',',','4','4',',','1','\n','7',',','1',',','2','5',',','1','\n','3',',','1',',','3','7',',','1',';','2',',','1',',','4','3',',','1','\n','7',',','1',',','2','4',',','1','\n','1',',','2',',','4','3',',','1','\n','7',',','1',',','2','3',',','1','\n','3',',','1',',','3','6',',','1',';','0',',','2',',','8',',','1',',','1','8',',','1','\n','7',',','1',',','2','2',',','1','\n','6',',','1',',','2','5',',','1','\n','2',',','1',',','1','3',',','2','\n','1','1',',','1',',','1','7',',','1','\n','6',',','1',',','2','4',',','1','\n','2',',','1',',','4','2',',','1','\n','0',',','1',',','4','6',',','1','\n','1','1',',','1',',','1','6',',','1','\n','1','0',',','1',',','1','7',',','1',';','6',',','1',',','2','3',',','1','\n','6',',','1',',','2','3',',','1',';','5',',','1',',','2','8',',','1','\n','5',',','1',',','2','8',',','1',';','1',',','2',',','4','2',',','1','\n','1',',','2',',','4','2',',','1',';','0',',','1',',','4','5',',','1','\n','1','0',',','1',',','1','6',',','1',';','6',',','1',',','2','2',',','1','\n','6',',','1',',','2','2',',','1',';','0',',','1',',','8',',','1',',','2','0',',','1','\n','1','3',',','1',',','1','5',',','1',';','0',',','1',',','8',',','1',',','1','9',',','1','\n','1','4',',','2',';','5',',','1',',','2','7',',','1','\n','5',',','1',',','2','7',',','1',';','1',',','1',',','4','4',',','1','\n','7',',','1',',','2','6',',','1','\n','0',',','1',',','3',',','1',',','3','8',',','1','\n','4',',','1',',','3','5',',','1','\n','4',',','1',',','3','4',',','1','\n','6',',','1',',','2','6',',','1','\n','4',',','1',',','3','3',',','1','\n','4',',','1',',','3','2',',','1','\n','1',',','1',',','4','6',',','1','\n','1',',','1',',','4','5',',','1','\n','5',',','1',',','2','9',',','1','\n','3',',','1',',','4','0',',','1','\n','0',',','2',',','4','5',',','1','\n','3',',','1',',','3','9',',','1','\n','1','2',',','1',',','1','7',',','1',';','0',',','2',',','8',',','1',',','1','9',',','1','\n','1','2',',','1',',','1','6',',','1','\n','8',',','1',',','2','1',',','1','\n','4',',','1',',','3','1',',','1','\n','7',',','1',',','2','8',',','1',';','1',',','2',',','8',',','1',',','1','8',',','1','\n','0',',','2',',','2',',','1',',','4','3',',','1','\n','8',',','1',',','2','5',',','1','\n','0',',','1',',','4','8',',','1','\n','8',',','1',',','2','4',',','1','\n','1','3',',','1',',','1','7',',','1',';','9',',','1',',','2','0',',','1','\n','9',',','1',',','2','0',',','1',';','8',',','1',',','2','2',',','1','\n','6',',','1',',','2','8',',','1','\n','1','3',',','1',',','1','6',',','1',';','9',',','1',',','1','9',',','1','\n','9',',','1',',','1','9',',','1',';','8',',','3','\n','7',',','1',',','2','7',',','1','\n','1','4',',','1',',','1','5',',','1','\n','6',',','1',',','2','7',',','1','\n','5',',','1',',','3','0',',','1','\n','2',',','1',',','4','4',',','1','\n','1',',','1',',','4','7',',','1','\n','1',',','2',',','4','4',',','1',';','0',',','2',',','4','7',',','1','\n','4',',','1',',','3','8',',','1','\n','4',',','1',',','3','7',',','1','\n','8',',','1',',','2','6',',','1','\n','7',',','1',',','2','9',',','1','\n','4',',','1',',','3','6',',','1','\n','0',',','1',',','5','2',',','1','\n','1','1',',','1',',','2','0',',','1','\n','2',',','1',',','4','6',',','1','\n','0',',','1',',','5','1',',','1','\n','1','1',',','1',',','1','9',',','1','\n','1','0',',','1',',','2','0',',','1','\n','2',',','1',',','4','5',',','1','\n','0',',','1',',','8',',','1',',','2','3',',','1','\n','1','0',',','1',',','1','9',',','1',';','6',',','1',',','2','9',',','1','\n','6',',','1',',','2','9',',','1',';','0',',','1',',','8',',','1',',','2','2',',','1','\n','3',',','1',',','4','1',',','1','\n','0',',','3',',','4','7',',','1','\n','1','3',',','1',',','1','8',',','1',';','3',',','1',',','4','3',',','1','\n','2',',','2',',','4','3',',','1','\n','0',',','3',',','9',',','1',',','1','8',',','1','\n','5',',','1',',','3','5',',','1','\n','1',',','1',',','5','2',',','1','\n','8',',','1',',','2','8',',','1','\n','5',',','1',',','3','4',',','1','\n','3',',','1',',','4','2',',','1','\n','1',',','1',',','5','1',',','1','\n','5',',','1',',','3','3',',','1','\n','5',',','1',',','3','2',',','1','\n','1','2',',','1',',','2','0',',','1',';','7',',','1',',','3','0',',','1','\n','7',',','1',',','3','0',',','1',';','4',',','1',',','4','0',',','1','\n','4',',','1',',','4','0',',','1',';','0',',','2',',','8',',','3','\n','1','2',',','1',',','1','9',',','1','\n','9',',','1',',','2','1',',','1','\n','4',',','1',',','3','9',',','1','\n','1','4',',','1',',','1','7',',','1','\n','1',',','1',',','5','0',',','1','\n','1','4',',','1',',','1','6',',','1',';','8',',','1',',','2','7',',','1','\n','8',',','1',',','2','7',',','1',';','5',',','1',',','3','1',',','1','\n','5',',','1',',','3','1',',','1',';','1',',','1',',','4','9',',','1','\n','1','5',',','2',';','6',',','1',',','3','0',',','1','\n','6',',','1',',','3','0',',','1',';','2',',','1',',','4','7',',','1','\n','2',',','1',',','4','7',',','1',';','0',',','2',',','4','9',',','1','\n','0',',','1',',','5','4',',','1','\n','9',',','1',',','2','5',',','1','\n','2',',','1',',','4','8',',','1','\n','1',',','1',',','5','3',',','1','\n','9',',','1',',','2','4',',','1','\n','1',',','2',',','4','8',',','1',';','0',',','2',',','5','3',',','1','\n','1','3',',','1',',','2','0',',','1',';','9',',','1',',','2','2',',','1','\n','9',',','1',',','2','2',',','1',';','8',',','1',',','2','9',',','1','\n','1','3',',','1',',','1','9',',','1',';','8',',','2',',','9',',','1','\n','1','1',',','1',',','2','1',',','1','\n','1','0',',','1',',','2','1',',','1','\n','0',',','3',',','4','9',',','1','\n','7',',','1',',','3','5',',','1',';','2',',','1',',','1','1',',','1',',','1','8',',','1','\n','7',',','1',',','3','4',',','1','\n','0',',','1',',','5','7',',','1','\n','1','1',',','1',',','2','5',',','1','\n','7',',','1',',','3','3',',','1','\n','1',',','1',',','5','4',',','1','\n','1','1',',','1',',','2','4',',','1','\n','1','0',',','1',',','2','5',',','1','\n','9',',','1',',','2','6',',','1','\n','7',',','1',',','3','2',',','1','\n','5',',','1',',','3','8',',','1','\n','1','1',',','1',',','2','3',',','1','\n','1','0',',','1',',','2','4',',','1','\n','6',',','1',',','3','5',',','1','\n','5',',','1',',','3','7',',','1','\n','2',',','1',',','5','2',',','1','\n','1','4',',','1',',','1','8',',','1','\n','1','1',',','1',',','2','2',',','1','\n','1','0',',','1',',','2','3',',','1','\n','6',',','1',',','3','4',',','1','\n','2',',','1',',','5','1',',','1','\n','0',',','3',',','5','3',',','1','\n','1','0',',','1',',','2','2',',','1','\n','6',',','1',',','3','3',',','1','\n','5',',','1',',','3','6',',','1','\n','0',',','1',',','9',',','1',',','2','3',',','1','\n','6',',','1',',','3','2',',','1','\n','0',',','1',',','8',',','1',',','2','9',',','1','\n','7',',','1',',','3','1',',','1','\n','0',',','1',',','8',',','2',',','9',',','1','\n','1','5',',','1',',','1','7',',','1',';','2',',','1',',','5','0',',','1','\n','2',',','1',',','5','0',',','1',';','0',',','1',',','5','6',',','1','\n','1','5',',','1',',','1','6',',','1',';','8',',','1',',','3','0',',','1','\n','8',',','1',',','3','0',',','1',';','6',',','1',',','3','1',',','1','\n','6',',','1',',','3','1',',','1',';','2',',','1',',','4','9',',','1','\n','2',',','1',',','4','9',',','1',';','0',',','1',',','5','5',',','1','\n','1','2',',','1',',','2','1',',','1',';','4',',','1',',','4','1',',','1','\n','4',',','1',',','4','1',',','1',';','3',',','1',',','4','4',',','1','\n','3',',','1',',','4','4',',','1',';','1',',','2',',','4','9',',','1','\n','1',',','1',',','5','7',',','1','\n','1','1',',','1',',','2','6',',','1','\n','4',',','1',',','4','3',',','1','\n','1','0',',','1',',','2','6',',','1','\n','9',',','1',',','2','8',',','1','\n','3',',','1',',','4','6',',','1','\n','1','2',',','1',',','2','5',',','1','\n','3',',','1',',','4','5',',','1','\n','1','2',',','1',',','2','4',',','1','\n','4',',','1',',','4','2',',','1','\n','1','2',',','1',',','2','3',',','1','\n','1','2',',','1',',','2','2',',','1','\n','1','3',',','1',',','2','1',',','1','\n','1','4',',','1',',','2','0',',','1','\n','5',',','1',',','4','0',',','1','\n','1',',','1',',','5','6',',','1','\n','1','4',',','1',',','1','9',',','1',';','9',',','1',',','2','7',',','1','\n','9',',','1',',','2','7',',','1',';','5',',','1',',','3','9',',','1','\n','5',',','1',',','3','9',',','1',';','1',',','1',',','5','5',',','1','\n','1',',','1',',','5','5',',','1',';','0',',','2',',','5','6',',','1','\n','7',',','1',',','3','8',',','1','\n','7',',','1',',','3','7',',','1','\n','3',',','2',',','3','8',',','1','\n','7',',','1',',','3','6',',','1','\n','8',',','1',',','3','5',',','1','\n','6',',','1',',','3','8',',','1','\n','1','1',',','1',',','2','8',',','1','\n','8',',','1',',','3','4',',','1','\n','6',',','1',',','3','7',',','1','\n','0',',','1',',','2',',','1',',','5','3',',','1','\n','1','5',',','1',',','1','8',',','1','\n','1','0',',','1',',','2','8',',','1','\n','8',',','1',',','3','3',',','1','\n','1','2',',','1',',','2','6',',','1','\n','1','3',',','1',',','2','2',',','1',';','9',',','1',',','2','9',',','1','\n','9',',','1',',','2','9',',','1',';','8',',','1',',','3','2',',','1','\n','6',',','1',',','3','6',',','1','\n','1','1',',','1',',','2','7',',','1','\n','1','6',',','2',';','8',',','1',',','3','1',',','1','\n','1','0',',','1',',','2','7',',','1','\n','3',',','1',',','4','7',',','1','\n','0',',','3',',','5','6',',','1','\n','0',',','1',',','5','8',',','1','\n','0',',','6',',','5','0',',','1','\n','2',',','1',',','5','7',',','1','\n','0',',','1',',','6','1',',','1','\n','1','3',',','1',',','2','6',',','1','\n','3',',','1',',','4','8',',','1','\n','1','1',',','1',',','2','9',',','1','\n','1','0',',','1',',','2','9',',','1','\n','0',',','1',',','1','3',',','1',',','2','3',',','1','\n','7',',','1',',','4','0',',','1','\n','0',',','1',',','8',',','1',',','3','2',',','1','\n','1','2',',','1',',','2','8',',','1','\n','7',',','1',',','3','9',',','1','\n','0',',','1',',','8',',','2',',','1','3',',','1','\n','0',',','1',',','6','0',',','1',';','0',',','1',',','5','9',',','1','\n','1','5',',','1',',','2','0',',','1',';','6',',','1',',','4','0',',','1','\n','6',',','1',',','4','0',',','1',';','2',',','1',',','5','6',',','1','\n','2',',','1',',','5','6',',','1',';','0',',','1',',','1','6',',','1',',','1','7',',','1','\n','1','5',',','1',',','1','9',',','1',';','9',',','1',',','3','0',',','1','\n','9',',','1',',','3','0',',','1',';','6',',','1',',','3','9',',','1','\n','6',',','1',',','3','9',',','1',';','2',',','1',',','5','5',',','1','\n','2',',','1',',','5','5',',','1',';','0',',','1',',','8',',','1',',','3','1',',','1','\n','1','4',',','1',',','2','1',',','1',';','1','2',',','1',',','2','7',',','1','\n','1','2',',','1',',','2','7',',','1',';','5',',','1',',','4','1',',','1','\n','5',',','1',',','4','1',',','1',';','4',',','1',',','4','4',',','1','\n','4',',','1',',','4','4',',','1',';','1',',','1',',','5','8',',','1','\n','0',',','4',',','5','5',',','1','\n','8',',','1',',','3','8',',','1','\n','8',',','1',',','3','7',',','1','\n','5',',','1',',','4','3',',','1','\n','3',',','1',',','5','2',',','1','\n','1','3',',','1',',','2','8',',','1','\n','8',',','1',',','3','6',',','1','\n','3',',','1',',','5','1',',','1','\n','4',',','1',',','4','6',',','1','\n','1','4',',','1',',','2','5',',','1','\n','4',',','1',',','4','5',',','1','\n','1','4',',','1',',','2','4',',','1','\n','1','2',',','1',',','2','9',',','1','\n','1',',','1',',','6','0',',','1','\n','5',',','1',',','4','2',',','1',';','1',',','1',',','5','9',',','1','\n','1','4',',','1',',','2','3',',','1','\n','1','4',',','1',',','2','2',',','1','\n','1','1',',','1',',','3','0',',','1','\n','3',',','1',',','5','0',',','1',';','0',',','2',',','1','7',',','2','\n','1','3',',','1',',','2','7',',','1',';','1','0',',','1',',','3','0',',','1','\n','3',',','1',',','4','9',',','1','\n','1','0',',','1',',','3','0',',','1',';','1',',','1',',','8',',','1',',','3','1',',','1','\n','1',',','1',',','8',',','1',',','3','1',',','1',';','0',',','2',',','1','6',',','1',',','1','7',',','1','\n','9',',','1',',','3','5',',','1','\n','3',',','1',',','5','3',',','1','\n','9',',','1',',','3','4',',','1','\n','2',',','2',',','5','3',',','1','\n','9',',','1',',','3','3',',','1','\n','0',',','1',',','1','6',',','1',',','1','8',',','1','\n','1','3',',','1',',','2','9',',','1',';','9',',','1',',','3','2',',','1','\n','1','4',',','1',',','2','6',',','1','\n','1','7',',','1',',','1','9',',','1',';','1','6',',','1',',','2','0',',','1','\n','1','6',',','1',',','2','0',',','1',';','8',',','1',',','4','0',',','1','\n','1','6',',','1',',','1','9',',','1',';','9',',','1',',','3','1',',','1','\n','9',',','1',',','3','1',',','1',';','8',',','1',',','3','9',',','1','\n','7',',','1',',','4','1',',','1','\n','1','5',',','1',',','2','1',',','1','\n','1','2',',','1',',','3','0',',','1','\n','6',',','1',',','4','1',',','1','\n','4',',','1',',','4','7',',','1','\n','2',',','1',',','5','8',',','1','\n','1',',','2',',','5','8',',','1','\n','0',',','1',',','6','2',',','1','\n','7',',','1',',','4','3',',','1','\n','3',',','2',',','4','3',',','1','\n','1','1',',','1',',','3','5',',','1','\n','3',',','1',',','5','4',',','1','\n','2',',','1',',','6','1',',','1','\n','1','1',',','1',',','3','4',',','1','\n','1','0',',','1',',','3','5',',','1','\n','2',',','2',',','5','4',',','1','\n','1',',','2',',','6','1',',','1','\n','1','1',',','1',',','3','3',',','1','\n','1','0',',','1',',','3','4',',','1','\n','6',',','1',',','4','3',',','1','\n','2',',','1',',','1','3',',','1',',','2','5',',','1','\n','1','1',',','1',',','3','2',',','1','\n','1','0',',','1',',','3','3',',','1','\n','7',',','1',',','4','2',',','1',';','4',',','1',',','4','8',',','1','\n','2',',','1',',','1','3',',','1',',','2','4',',','1','\n','4',',','1',',','4','8',',','1',';','1',',','1',',','1','6',',','1',',','1','8',',','1','\n','1',',','1',',','1','6',',','1',',','1','8',',','1',';','0',',','2',',','1','7',',','1',',','1','8',',','1','\n','1','0',',','1',',','3','2',',','1','\n','0',',','1',',','9',',','1',',','3','2',',','1','\n','1','5',',','1',',','2','5',',','1','\n','1','5',',','1',',','2','4',',','1','\n','6',',','1',',','4','2',',','1','\n','2',',','1',',','6','0',',','1','\n','2',',','1',',','5','9',',','1','\n','0',',','1',',','6','3',',','1','\n','1','5',',','1',',','2','3',',','1',';','1','4',',','1',',','2','8',',','1','\n','1','1',',','1',',','3','1',',','1','\n','1','4',',','1',',','2','8',',','1',';','1',',','2',',','5','9',',','1','\n','1',',','2',',','5','9',',','1',';','0',',','1',',','1','7',',','1',',','2','0',',','1','\n','1','5',',','1',',','2','2',',','1',';','1','0',',','1',',','3','1',',','1','\n','1','0',',','1',',','3','1',',','1',';','0',',','1',',','8',',','1',',','4','0',',','1','\n','1','3',',','1',',','3','0',',','1',';','0',',','1',',','8',',','1',',','3','9',',','1','\n','1','4',',','1',',','2','7',',','1',';','5',',','1',',','4','4',',','1','\n','5',',','1',',','4','4',',','1',';','1',',','1',',','6','2',',','1','\n','3',',','1',',','5','7',',','1','\n','9',',','1',',','3','8',',','1','\n','9',',','1',',','3','7',',','1','\n','9',',','1',',','3','6',',','1','\n','1','2',',','1',',','3','5',',','1','\n','4',',','1',',','5','2',',','1','\n','0',',','3',',','1','7',',','1',',','1','8',',','1','\n','1','2',',','1',',','3','4',',','1','\n','4',',','1',',','5','1',',','1','\n','1','5',',','1',',','2','6',',','1','\n','1','2',',','1',',','3','3',',','1','\n','1','2',',','1',',','3','2',',','1','\n','5',',','1',',','4','6',',','1','\n','1',',','1',',','6','3',',','1','\n','5',',','1',',','4','5',',','1','\n','1','4',',','1',',','2','9',',','1','\n','3',',','1',',','5','6',',','1','\n','0',',','2',',','1','7',',','1',',','2','0',',','1','\n','3',',','1',',','5','5',',','1','\n','1','7',',','1',',','2','1',',','1',';','4',',','1',',','5','0',',','1','\n','4',',','1',',','5','0',',','1',';','0',',','2',',','8',',','1',',','3','9',',','1','\n','1','6',',','1',',','2','1',',','1',';','1','2',',','1',',','3','1',',','1','\n','1','2',',','1',',','3','1',',','1',';','8',',','1',',','4','1',',','1','\n','8',',','1',',','4','1',',','1',';','4',',','1',',','4','9',',','1','\n','4',',','1',',','4','9',',','1',';','0',',','5',',','1','7',',','2','\n','0',',','1',',','7','0',',','1','\n','1','1',',','1',',','3','8',',','1','\n','1','1',',','1',',','3','7',',','1','\n','1','0',',','1',',','3','8',',','1','\n','1',',','1',',','6','8',',','1','\n','1','3',',','1',',','3','5',',','1','\n','1','0',',','1',',','3','7',',','1','\n','8',',','1',',','4','3',',','1','\n','1',',','1',',','6','7',',','1',';','0',',','2',',','6','8',',','1','\n','1','3',',','1',',','3','4',',','1','\n','1','1',',','1',',','3','6',',','1','\n','1','0',',','1',',','3','6',',','1','\n','4',',','1',',','5','3',',','1','\n','0',',','1',',','1','8',',','1',',','1','9',',','1','\n','1','7',',','1',',','2','5',',','1','\n','1',',','1',',','6','6',',','1','\n','1','7',',','1',',','2','4',',','1','\n','1','6',',','1',',','2','5',',','1','\n','1','6',',','1',',','2','4',',','1','\n','1','7',',','1',',','2','3',',','1',';','8',',','1',',','4','2',',','1',';','0',',','3',',','6','4',',','1','\n','2','0',',','2',';','1','7',',','1',',','2','2',',','1','\n','1','7',',','1',',','2','2',',','1',';','1','6',',','1',',','2','3',',','1','\n','1','9',',','1',',','2','0',',','1',';','1','6',',','1',',','2','2',',','1','\n','1','5',',','1',',','2','8',',','1','\n','1','6',',','1',',','2','2',',','1',';','9',',','1',',','4','0',',','1','\n','9',',','1',',','4','0',',','1',';','8',',','2',',','1','7',',','1','\n','1','9',',','2',';','1','3',',','1',',','3','1',',','1','\n','1','3',',','1',',','3','1',',','1',';','9',',','1',',','3','9',',','1','\n','9',',','1',',','3','9',',','1',';','8',',','2',',','1','6',',','1','\n','7',',','1',',','4','4',',','1','\n','1','5',',','1',',','2','7',',','1','\n','1','4',',','1',',','3','0',',','1','\n','6',',','1',',','4','4',',','1','\n','5',',','1',',','4','7',',','1','\n','2',',','1',',','6','2',',','1','\n','1',',','1',',','6','5',',','1','\n','1',',','2',',','6','2',',','1',';','0',',','2',',','6','5',',','1','\n','4',',','1',',','5','4',',','1','\n','0',',','3',',','6','8',',','1','\n','1','2',',','1',',','3','8',',','1','\n','7',',','1',',','4','6',',','1',';','0',',','2',',','1','8',',','1',',','2','0',',','1','\n','0',',','3',',','6','7',',','1','\n','1','7',',','1',',','2','6',',','1','\n','1','2',',','1',',','3','7',',','1','\n','7',',','1',',','4','5',',','1','\n','2',',','1',',','6','4',',','1',';','0',',','1',',','7','2',',','1','\n','1','8',',','1',',','2','1',',','1','\n','1','6',',','1',',','2','6',',','1','\n','5',',','1',',','4','8',',','1',';','1',',','2',',','6','4',',','1','\n','0',',','1',',','1','3',',','1',',','3','2',',','1','\n','1','2',',','1',',','3','6',',','1','\n','1','1',',','1',',','4','0',',','1','\n','6',',','1',',','4','6',',','1','\n','2',',','1',',','6','3',',','1','\n','1','1',',','1',',','3','9',',','1','\n','1','0',',','1',',','4','0',',','1','\n','6',',','1',',','4','5',',','1','\n','0',',','1',',','1','6',',','1',',','2','3',',','1','\n','1','5',',','1',',','2','9',',','1',';','1','0',',','1',',','3','9',',','1','\n','1','0',',','1',',','3','9',',','1',';','0',',','1',',','8',',','2',',','1','7',',','1','\n','3',',','1',',','5','8',',','1','\n','0',',','3',',','6','5',',','1','\n','1','8',',','1',',','2','5',',','1','\n','0',',','1',',','7','6',',','1','\n','1','8',',','1',',','2','3',',','1','\n','1','3',',','1',',','3','8',',','1','\n','3',',','1',',','6','1',',','1','\n','2',',','1',',','6','8',',','1',';','0',',','1',',','7','5',',','1','\n','1','3',',','1',',','3','7',',','1','\n','4',',','1',',','5','7',',','1','\n','1','8',',','1',',','2','2',',','1',';','2',',','1',',','6','7',',','1','\n','2',',','1',',','6','7',',','1',';','0',',','1',',','7','3',',','1','\n','8',',','2',',','1','8',',','1','\n','1','3',',','1',',','3','6',',','1','\n','2',',','1',',','6','6',',','1',';','1',',','1',',','7','2',',','1','\n','1',',','1',',','1','3',',','1',',','3','3',',','1','\n','1','7',',','1',',','2','8',',','1','\n','1','4',',','1',',','3','5',',','1','\n','5',',','1',',','5','2',',','1','\n','1','6',',','1',',','2','8',',','1','\n','1','4',',','1',',','3','4',',','1','\n','5',',','1',',','5','1',',','1','\n','3',',','1',',','6','0',',','1',';','3',',','1',',','5','9',',','1','\n','1',',','1',',','8',',','1',',','4','2',',','1','\n','3',',','1',',','5','9',',','1',';','0',',','4',',','6','6',',','1','\n','1','4',',','1',',','3','3',',','1','\n','1','4',',','1',',','3','2',',','1','\n','2','0',',','1',',','2','1',',','1',';','1','2',',','1',',','4','0',',','1','\n','1','2',',','1',',','4','0',',','1',';','7',',','1',',','4','7',',','1','\n','7',',','1',',','4','7',',','1',';','4',',','1',',','5','6',',','1','\n','4',',','1',',','5','6',',','1',';','0',',','2',',','8',',','2',',','1','6',',','1','\n','1','9',',','1',',','2','1',',','1','\n','1','2',',','1',',','3','9',',','1','\n','9',',','1',',','4','1',',','1','\n','4',',','1',',','5','5',',','1','\n','1','7',',','1',',','2','7',',','1','\n','5',',','1',',','5','0',',','1','\n','1','6',',','1',',','2','7',',','1',';','1','4',',','1',',','3','1',',','1','\n','1','4',',','1',',','3','1',',','1',';','8',',','1',',','4','4',',','1','\n','8',',','1',',','4','4',',','1',';','5',',','1',',','4','9',',','1','\n','5',',','1',',','4','9',',','1',';','1',',','1',',','7','1',',','1','\n','1','5',',','1',',','3','0',',','1',';','6',',','1',',','4','7',',','1','\n','6',',','1',',','4','7',',','1',';','2',',','1',',','6','5',',','1','\n','2',',','1',',','6','5',',','1',';','0',',','2',',','7','1',',','1','\n','1','8',',','1',',','2','6',',','1','\n','1',',','2',',','7','0',',','1','\n','1',',','1',',','7','5',',','1','\n','1',',','1',',','7','4',',','1','\n','9',',','1',',','4','3',',','1','\n','7',',','1',',','4','8',',','1',';','1',',','1',',','7','3',',','1','\n','1',',','1',',','7','3',',','1',';','0',',','2',',','7','5',',','1','\n','0',',','2',',','7','5',',','1',';','0',',','2',',','7','4',',','1','\n','2','0',',','1',',','2','5',',','1','\n','2','0',',','1',',','2','4',',','1','\n','1','9',',','1',',','2','5',',','1','\n','6',',','1',',','4','8',',','1','\n','5',',','1',',','5','3',',','1','\n','1','9',',','1',',','2','4',',','1','\n','2','0',',','1',',','2','3',',','1',';','9',',','1',',','4','2',',','1','\n','9',',','1',',','4','2',',','1',';','8',',','1',',','4','6',',','1',';','0',',','3',',','7','2',',','1','\n','2','0',',','1',',','2','2',',','1',';','1','9',',','1',',','2','3',',','1','\n','1','9',',','1',',','2','3',',','1',';','1','7',',','1',',','2','9',',','1','\n','1','7',',','1',',','2','9',',','1',';','8',',','1',',','4','5',',','1','\n','1','9',',','1',',','2','2',',','1',';','1','6',',','1',',','2','9',',','1','\n','1','6',',','1',',','2','9',',','1',';','1','3',',','1',',','4','0',',','1','\n','1','3',',','1',',','4','0',',','1',';','8',',','2',',','2','0',',','1','\n','1','3',',','1',',','3','9',',','1',';','8',',','2',',','1','9',',','1','\n','1','1',',','1',',','4','1',',','1','\n','1','0',',','1',',','4','1',',','1','\n','0',',','3',',','7','1',',','1','\n','1','8',',','1',',','2','8',',','1','\n','1','1',',','1',',','4','3',',','1','\n','1','0',',','1',',','4','3',',','1','\n','7',',','1',',','5','2',',','1','\n','0',',','3',',','7','4',',','1','\n','7',',','1',',','5','1',',','1','\n','0',',','3',',','7','3',',','1','\n','2','0',',','1',',','2','6',',','1','\n','5',',','1',',','5','4',',','1','\n','2',',','1',',','7','2',',','1',';','0',',','1',',','7','9',',','1','\n','1','9',',','1',',','2','6',',','1','\n','1','4',',','1',',','3','8',',','1','\n','1','1',',','1',',','4','2',',','1','\n','1',',','2',',','7','2',',','1','\n','1','5',',','1',',','3','5',',','1','\n','1','4',',','1',',','3','7',',','1','\n','1','0',',','1',',','4','2',',','1','\n','6',',','1',',','5','2',',','1','\n','1','8',',','1',',','2','7',',','1','\n','1','5',',','1',',','3','4',',','1','\n','6',',','1',',','5','1',',','1','\n','0',',','4',',','7','2',',','1','\n','1','5',',','1',',','3','3',',','1','\n','1','4',',','1',',','3','6',',','1','\n','0',',','1',',','8',',','1',',','4','5',',','1','\n','7',',','1',',','5','0',',','1','\n','1','5',',','1',',','3','2',',','1',';','0',',','1',',','8',',','2',',','2','0',',','1','\n','0',',','1',',','8',',','2',',','2','0',',','1',';','0',',','6',',','6','6',',','1','\n','7',',','1',',','4','9',',','1',';','0',',','1',',','8',',','2',',','1','9',',','1','\n','0',',','1',',','8',',','2',',','1','9',',','1',';','0',',','7',',','6','4',',','1','\n','1','7',',','1',',','3','0',',','1',';','6',',','1',',','5','0',',','1','\n','6',',','1',',','5','0',',','1',';','0',',','1',',','7','8',',','1','\n','1','6',',','1',',','3','0',',','1',';','1','5',',','1',',','3','1',',','1','\n','1','5',',','1',',','3','1',',','1',';','8',',','1',',','4','7',',','1','\n','8',',','1',',','4','7',',','1',';','6',',','1',',','4','9',',','1','\n','6',',','1',',','4','9',',','1',';','2',',','1',',','7','1',',','1','\n','2',',','1',',','7','1',',','1',';','0',',','1',',','7','7',',','1','\n','2','1',',','2',';','1','2',',','1',',','4','1',',','1','\n','1','2',',','1',',','4','1',',','1',';','4',',','1',',','5','8',',','1','\n','4',',','1',',','5','8',',','1',';','3',',','1',',','6','2',',','1','\n','3',',','1',',','6','2',',','1',';','1',',','2',',','7','1',',','1','\n','1',',','2',',','7','6',',','1','\n','2',',','1',',','7','4',',','1',';','0',',','1',',','8','6',',','1','\n','1','8',',','1',',','2','9',',','1',';','7',',','1',',','5','3',',','1','\n','7',',','1',',','5','3',',','1',';','2',',','1',',','7','3',',','1','\n','2',',','1',',','7','3',',','1',';','0',',','1',',','8','5',',','1','\n','0',',','1',',','8','5',',','1',';','0',',','1',',','8','4',',','1','\n','8',',','1',',','9',',','1',',','1','8',',','1','\n','4',',','1',',','6','1',',','1','\n','0',',','1',',','8','3',',','1',';','0',',','1',',','8','2',',','1'] ['0',',','1',',','8','2',',','1',';','0',',','7',',','1','8',',','2'] ['5',',','1',',','5','7',',','1','\n','1',',','1',',','8','0',',','1','\n','1','2',',','1',',','4','3',',','1','\n','8',',','1',',','4','8',',','1',';','1',',','1',',','7','9',',','1','\n','3',',','1',',','6','4',',','1',';','1',',','1',',','7','9',',','1',';','0',',','2',',','8','0',',','1','\n','6',',','1',',','5','3',',','1',';','0',',','2',',','7','9',',','1','\n','2','0',',','1',',','2','8',',','1','\n','1','9',',','1',',','2','8',',','1','\n','3',',','1',',','6','3',',','1','\n','2','1',',','1',',','2','5',',','1','\n','2','1',',','1',',','2','4',',','1','\n','1','2',',','1',',','4','2',',','1','\n','4',',','1',',','6','0',',','1','\n','4',',','1',',','5','9',',','1','\n','2','1',',','1',',','2','3',',','1',';','0',',','7',',','6','6',',','1','\n','2','1',',','1',',','2','2',',','1',';','0',',','8',',','6','4',',','1','\n','1','3',',','1',',','4','1',',','1','\n','2','0',',','1',',','2','7',',','1','\n','1','4',',','1',',','4','0',',','1','\n','5',',','1',',','5','6',',','1','\n','1',',','1',',','7','8',',','1','\n','1','9',',','1',',','2','7',',','1',';','1','4',',','1',',','3','9',',','1','\n','1','4',',','1',',','3','9',',','1',';','9',',','1',',','4','4',',','1','\n','9',',','1',',','4','4',',','1',';','5',',','1',',','5','5',',','1','\n','5',',','1',',','5','5',',','1',';','1',',','1',',','7','7',',','1','\n','1',',','1',',','7','7',',','1',';','0',',','2',',','7','8',',','1','\n','3',',','1',',','1','8',',','2','\n','2',',','2',',','1','8',',','2','\n','7',',','1',',','5','4',',','1',';','2',',','1',',','1','8',',','1',',','2','4',',','1','\n','1',',','1',',','8','6',',','1','\n','2','5',',','2',';','1','3',',','1',',','4','3',',','1','\n','1','3',',','1',',','4','3',',','1',';','1',',','1',',','8','5',',','1',';','1',',','1',',','8','4',',','1','\n','1',',','1',',','8','5',',','1',';','0',',','1',',','2',',','1',',','7','5',',','1','\n','1',',','1',',','8','4',',','1',';','0',',','2',',','8','6',',','1','\n','2','4',',','1',',','2','5',',','1','\n','1',',','1',',','8','3',',','1','\n','2','4',',','2','\n','2','3',',','1',',','2','5',',','1','\n','0',',','8',',','1','8',',','2','\n','2','2',',','1',',','2','5',',','1','\n','1','7',',','1',',','3','5',',','1','\n','6',',','1',',','5','4',',','1','\n','3',',','1',',','6','6',',','1',';','0',',','2',',','8','1',',','1','\n','2','2',',','1',',','2','4',',','1','\n','1','6',',','1',',','3','5',',','1','\n','1','5',',','1',',','3','8',',','1','\n','2','3',',','2',';','1','7',',','1',',','3','4',',','1',';','1','3',',','3','\n','8',',','1',',','5','2',',','1','\n','1','7',',','1',',','3','4',',','1',';','0',',','3',',','8','0',',','1','\n','1','7',',','1',',','3','3',',','1','\n','1','6',',','1',',','3','4',',','1','\n','1','5',',','1',',','3','7',',','1','\n','2','2',',','1',',','2','3',',','1',';','1','3',',','1',',','4','2',',','1','\n','1','3',',','1',',','4','2',',','1',';','9',',','1',',','4','6',',','1','\n','9',',','1',',','4','6',',','1',';','8',',','1',',','5','1',',','1','\n','0',',','3',',','7','9',',','1','\n','2','2',',','2',';','2','0',',','1',',','2','9',',','1','\n','1','8',',','1',',','3','0',',','1','\n','2','0',',','1',',','2','9',',','1',';','1','7',',','1',',','3','2',',','1','\n','1','6',',','1',',','3','3',',','1','\n','1','7',',','1',',','3','2',',','1',';','9',',','1',',','4','5',',','1','\n','9',',','1',',','4','5',',','1',';','8',',','2',',','2','3',',','1','\n','2','1',',','1',',','2','6',',','1','\n','1','9',',','1',',','2','9',',','1',';','1','6',',','1',',','3','2',',','1','\n','1','5',',','1',',','3','6',',','1','\n','1','6',',','1',',','3','2',',','1',';','8',',','2',',','2','2',',','1','\n','0',',','8',',','6','6',',','1','\n','1','7',',','1',',','3','1',',','1',';','8',',','1',',','5','0',',','1','\n','0',',','9',',','6','4',',','1','\n','1','1',',','1',',','4','4',',','1','\n','1','6',',','1',',','3','1',',','1',';','8',',','1',',','4','9',',','1','\n','1','0',',','1',',','4','4',',','1','\n','3',',','1',',','6','5',',','1','\n','0',',','3',',','7','8',',','1','\n','0',',','1',',','8','7',',','1','\n','0',',','1','2',',','5','9',',','1','\n','3',',','1',',','7','0',',','1',';','0',',','1',',','9','4',',','1','\n','7',',','1',',','5','7',',','1',';','2',',','2',',','7','0',',','1','\n','2',',','2',',','7','0',',','1',';','0',',','1',',','9','3',',','1','\n','2','5',',','1',',','2','6',',','1','\n','2','4',',','1',',','2','6',',','1','\n','0',',','3',',','8','6',',','1','\n','2','3',',','1',',','2','6',',','1','\n','6',',','1',',','5','7',',','1','\n','0',',','3',',','8','4',',','1','\n','2','2',',','1',',','2','6',',','1','\n','8',',','1',',','5','3',',','1',';','2',',','1',',','7','9',',','1','\n','2',',','1',',','7','9',',','1',';','0',',','1',',','8','9',',','1','\n','1','1',',','1',',','4','6',',','1','\n','1',',','2',',','7','9',',','1','\n','1','1',',','1',',','4','5',',','1','\n','1','0',',','1',',','4','6',',','1','\n','1','0',',','1',',','4','5',',','1','\n','7',',','1',',','5','6',',','1','\n','0',',','1',',','8',',','2',',','2','2',',','1','\n','2','1',',','1',',','2','8',',','1','\n','7',',','1',',','5','5',',','1','\n','0',',','1',',','8',',','4','\n','0',',','1',',','8','8',',','1','\n','2','0',',','1',',','3','0',',','1',';','1','5',',','1',',','4','0',',','1','\n','1','5',',','1',',','4','0',',','1',';','6',',','1',',','5','6',',','1','\n','6',',','1',',','5','6',',','1',';','2',',','1',',','7','8',',','1','\n','2',',','1',',','7','8',',','1',';','0',',','1',',','8',',','1',',','5','0',',','1','\n','1','9',',','1',',','3','0',',','1',';','1','5',',','1',',','3','9',',','1','\n','1','5',',','1',',','3','9',',','1',';','9',',','1',',','4','7',',','1','\n','9',',','1',',','4','7',',','1',';','6',',','1',',','5','5',',','1','\n','6',',','1',',','5','5',',','1',';','2',',','1',',','7','7',',','1','\n','2',',','1',',','7','7',',','1',';','0',',','1',',','8',',','1',',','4','9',',','1','\n','2','1',',','1',',','2','7',',','1',';','1','4',',','1',',','4','1',',','1','\n','1','4',',','1',',','4','1',',','1',';','1','2',',','1',',','4','4',',','1','\n','1','2',',','1',',','4','4',',','1',';','5',',','1',',','5','8',',','1','\n','5',',','1',',','5','8',',','1',';','4',',','1',',','6','2',',','1','\n','4',',','1',',','6','2',',','1',';','1',',','1',',','8','7',',','1','\n','0',',','4',',','7','7',',','1','\n','1','8',',','1',',','3','5',',','1','\n','1',',','1',',','9','4',',','1','\n','1','8',',','1',',','3','4',',','1','\n','1',',','1',',','9','3',',','1','\n','0',',','2',',','9','4',',','1','\n','1','8',',','1',',','3','3',',','1','\n','1',',','1',',','9','1',',','1','\n','0',',','2',',','9','3',',','1','\n','2',',','1',',','8','6',',','1',';','0',',','2',',','9','2',',','1','\n','2','6',',','2','\n','1','8',',','1',',','3','2',',','1','\n','2',',','1',',','8','4',',','1','\n','2',',','1',',','8','5',',','1',';','0',',','1',',','9','5',',','1','\n','0',',','2',',','9','1',',','1','\n','2',',','1',',','8','3',',','1',';','2',',','1',',','8','2',',','1',';','0',',','2',',','3',',','1',',','6','8',',','1','\n','1','7',',','1',',','3','8',',','1','\n','8',',','1',',','5','4',',','1','\n','2',',','1',',','8','1',',','1','\n','2','5',',','1',',','2','8',',','1',';','1',',','2',',','8','2',',','1','\n','1',',','2',',','8','2',',','1',';','0',',','2',',','3',',','1',',','6','7',',','1','\n','2','4',',','1',',','2','8',',','1','\n','1','7',',','1',',','3','7',',','1','\n','1','6',',','1',',','3','8',',','1','\n','5',',','1',',','6','1',',','1',';','3',',','1',',','7','2',',','1','\n','9',',','1',',','4','8',',','1',';','1',',','1',',','9','0',',','1','\n','1',',','1',',','9','0',',','1',';','1',',','1',',','8','9',',','1','\n','3',',','1',',','7','2',',','1',';','1',',','2',',','8','1',',','1','\n','1',',','1',',','8','9',',','1',';','0',',','1',',','2',',','1',',','8','0',',','1','\n','2','3',',','1',',','2','8',',','1','\n','1','6',',','1',',','3','7',',','1','\n','2','2',',','1',',','2','8',',','1','\n','1','8',',','1',',','3','1',',','1','\n','1','4',',','1',',','4','3',',','1','\n','1','7',',','1',',','3','6',',','1',';','4',',','1',',','6','4',',','1','\n','4',',','1',',','6','4',',','1',';','0',',','4',',','8','1',',','1','\n','1','6',',','1',',','3','6',',','1','\n','1','2',',','1',',','4','6',',','1','\n','4',',','1',',','6','3',',','1','\n','2','5',',','1',',','2','7',',','1','\n','1','2',',','1',',','4','5',',','1','\n','2','4',',','1',',','2','7',',','1','\n','2','1',',','1',',','2','9',',','1','\n','5',',','1',',','6','0',',','1','\n','1','4',',','1',',','4','2',',','1',';','5',',','1',',','5','9',',','1','\n','5',',','1',',','5','9',',','1',';','1',',','1',',','8','8',',','1','\n','2','3',',','1',',','2','7',',','1','\n','2','2',',','1',',','2','7',',','1','\n','1','1',',','1',',','4','7',',','1','\n','1','3',',','1',',','4','4',',','1',';','1','0',',','1',',','4','7',',','1','\n','3',',','1',',','7','1',',','1','\n','1','0',',','1',',','4','7',',','1',';','1',',','1',',','8',',','1',',','4','9',',','1','\n','1',',','1',',','8',',','1',',','4','9',',','1',';','0',',','2',',','8',',','1',',','5','0',',','1','\n','4',',','1',',','1','8',',','2',';','1',',','1',',','9','6',',','1','\n','0',',','1',',','9','9',',','1','\n','3',',','1',',','7','5',',','1',';','2',',','2',',','7','6',',','1','\n','3',',','1',',','7','3',',','1','\n','2',',','2',',','7','5',',','1',';','1',',','1',',','9','5',',','1','\n','0',',','3',',','9','2',',','1','\n','8',',','1',',','5','7',',','1','\n','4',',','1',',','6','8',',','1','\n','0',',','2',',','9','5',',','1','\n','2','6',',','1',',','2','8',',','1','\n','1','1',',','1',',','4','8',',','1','\n','4',',','1',',','6','7',',','1','\n','2','5',',','1',',','2','9',',','1','\n','2','0',',','1',',','3','5',',','1','\n','1','0',',','1',',','4','8',',','1','\n','0',',','1',',','9','8',',','1','\n','2','4',',','1',',','2','9',',','1','\n','2','0',',','1',',','3','4',',','1','\n','1','9',',','1',',','3','5',',','1','\n','9',',','1',',','5','2',',','1','\n','0',',','2',',','2',',','1',',','8','0',',','1','\n','2','0',',','1',',','3','3',',','1','\n','1','9',',','1',',','3','4',',','1','\n','2','3',',','1',',','2','9',',','1',';','1','3',',','1',',','4','6',',','1','\n','1','3',',','1',',','4','6',',','1',';','9',',','1',',','5','1',',','1','\n','4',',','1',',','6','6',',','1','\n','0',',','3',',','8','9',',','1','\n','2','2',',','1',',','2','9',',','1',';','2','0',',','1',',','3','2',',','1','\n','1','9',',','1',',','3','3',',','1','\n','2','0',',','1',',','3','2',',','1',';','1','3',',','1',',','4','5',',','1','\n','1','3',',','1',',','4','5',',','1',';','8',',','1',',','9',',','1',',','2','3',',','1','\n','0',',','5',',','8','1',',','1','\n','1','9',',','1',',','3','2',',','1',';','8',',','2',',','2','9',',','1','\n','0',',','6',',','8','0',',','1','\n','2','6',',','1',',','2','7',',','1','\n','2','0',',','1',',','3','1',',','1',';','1','7',',','1',',','3','9',',','1','\n','1','7',',','1',',','3','9',',','1',';','1','6',',','1',',','4','0',',','1','\n','1','6',',','1',',','4','0',',','1',';','9',',','1',',','5','0',',','1','\n','9',',','1',',','5','0',',','1',';','8',',','1',',','5','6',',','1','\n','1','9',',','1',',','3','1',',','1',';','1','6',',','1',',','3','9',',','1','\n','1','6',',','1',',','3','9',',','1',';','9',',','1',',','4','9',',','1','\n','9',',','1',',','4','9',',','1',';','8',',','1',',','5','5',',','1','\n','7',',','1',',','5','8',',','1','\n','2','1',',','1',',','3','0',',','1','\n','1','5',',','1',',','4','1',',','1','\n','1','2',',','1',',','4','7',',','1','\n','6',',','1',',','5','8',',','1','\n','4',',','1',',','6','5',',','1','\n','2',',','1',',','8','7',',','1','\n','1',',','2',',','8','7',',','1','\n','0',',','1',',','9','7',',','1','\n','1','8',',','1',',','3','8',',','1','\n','1','8',',','1',',','3','7',',','1','\n','2',',','1',',','9','4',',','1',';','1',',','1',',','9','9',',','1','\n','2',',','1',',','9','3',',','1','\n','1','8',',','1',',','3','6',',','1','\n','7',',','1',',','6','1',',','1',';','4',',','1',',','7','0',',','1','\n','2',',','1',',','9','1',',','1','\n','4',',','1',',','7','0',',','1',';','1',',','2',',','9','2',',','1','\n','1',',','2',',','9','2',',','1',';','0',',','3',',','9','6',',','1','\n','2','6',',','1',',','2','9',',','1','\n','1','1',',','1',',','5','2',',','1','\n','6',',','1',',','6','1',',','1','\n','9',',','1',',','5','3',',','1',';','2',',','1',',','9','0',',','1','\n','2',',','1',',','9','0',',','1',';','2',',','1',',','8','9',',','1','\n','2',',','1',',','8','9',',','1',';','0',',','1',',','1','0','1',',','1','\n','2','8',',','2','\n','1','1',',','1',',','5','1',',','1','\n','1','0',',','1',',','5','2',',','1','\n','1','5',',','1',',','4','3',',','1','\n','1','0',',','1',',','5','1',',','1','\n','1','2',',','1',',','4','8',',','1','\n','7',',','1',',','6','0',',','1',';','7',',','1',',','5','9',',','1','\n','7',',','1',',','5','9',',','1',';','0',',','4',',','9','0',',','1','\n','2','5',',','1',',','3','0',',','1','\n','2','4',',','1',',','3','0',',','1','\n','1','5',',','1',',','4','2',',','1','\n','1','1',',','1',',','5','0',',','1','\n','6',',','1',',','6','0',',','1','\n','6',',','1',',','5','9',',','1','\n','2',',','1',',','8','8',',','1','\n','0',',','1',',','1','0','0',',','1','\n','2','7',',','1',',','2','8',',','1',';','2','3',',','1',',','3','0',',','1','\n','1','1',',','1',',','4','9',',','1','\n','2','3',',','1',',','3','0',',','1',';','1','0',',','1',',','5','0',',','1','\n','1','0',',','1',',','5','0',',','1',';','1',',','2',',','8','8',',','1','\n','1',',','2',',','8','8',',','1',';','0',',','1',',','1','7',',','1',',','4','0',',','1','\n','2','2',',','1',',','3','0',',','1',';','1','0',',','1',',','4','9',',','1','\n','1','0',',','1',',','4','9',',','1',';','0',',','1',',','8',',','1',',','5','6',',','1','\n','1','3',',','1',',','4','7',',','1',';','0',',','1',',','8',',','1',',','5','5',',','1','\n','2','7',',','2',';','1','4',',','1',',','4','4',',','1']
    · rfl
    · rfl
    · decide
  · have hs : "0,1,82,1;0,7,18,2".splitOn ";"=["0,1,82,1","0,7,18,2"] := by
      simp +decide [String.splitOn,String.splitOnAux]
    have hm0 : (("0,1,82,1".splitOn ",").map (fun n=>n.toNat?.getD 0))=[0,1,82,1] := by
      have hx : "0,1,82,1".splitOn ","=["0","1","82","1"] := by simp +decide [String.splitOn,String.splitOnAux]
      rw [hx]
      simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
    have hm1 : (("0,7,18,2".splitOn ",").map (fun n=>n.toNat?.getD 0))=[0,7,18,2] := by
      have hx : "0,7,18,2".splitOn ","=["0","7","18","2"] := by simp +decide [String.splitOn,String.splitOnAux]
      rw [hx]
      simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
    change _ = (("0,1,82,1;0,7,18,2".splitOn ";").map _).sum
    rw [hs]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
    change _ = (if "0,1,82,1"="" then 1 else _)+((if "0,7,18,2"="" then 1 else _)+0)
    simp only [if_neg (by decide : "0,1,82,1"≠""),if_neg (by decide : "0,7,18,2"≠"")]
    rw [hm0,hm1]
    change _ = (MvPolynomial.X (atomIndex .h0) : MvPolynomial (Fin generators.count) (ZMod 2))^1 *
      (MvPolynomial.X (atomIndex .b)^1 * 1)+
      (MvPolynomial.X (atomIndex .h0)^7*(MvPolynomial.X (atomIndex .h5)^2*1)+0)
    simp only [pow_one,mul_one,add_zero]

private theorem nativeCoreB1 :
    (sourceProduct 12 134 1 4 (sourceProduct 1 32 11 102 (sourceAtom .h5) (sourceAtom .x_91_11)) (sourceAtom .h2)).val + (sourceAtom .h0).val * (Ideal.Quotient.mk _ (MvPolynomial.X (⟨426,by decide⟩ : Fin generators.count))) + (sourceAtom .h0).val^2 * (sourceAtom .h6).val * (Ideal.Quotient.mk _ (MvPolynomial.X (⟨89,by decide⟩ : Fin generators.count))) = 0 := by
  change Ideal.Quotient.mk _ (((MvPolynomial.X (atomIndex .h5) : MvPolynomial (Fin generators.count) (ZMod 2)) * MvPolynomial.X (atomIndex .x_91_11)) * MvPolynomial.X (atomIndex .h2) + MvPolynomial.X (atomIndex .h0) * MvPolynomial.X (⟨426,by decide⟩ : Fin generators.count) + MvPolynomial.X (atomIndex .h0)^2 * MvPolynomial.X (atomIndex .h6) * MvPolynomial.X (⟨89,by decide⟩ : Fin generators.count)) = 0
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply Ideal.subset_span
  refine ⟨"2,1,18,1,188,1;0,1,426,1;0,2,69,1,89,1",?_,?_⟩
  · apply nativeCoreFromChunk (i := ⟨9,by decide⟩)
    apply nativeCoreMiddleMember _ "2,1,18,1,188,1;0,1,426,1;0,2,69,1,89,1" ['2','4',',','1',',','1','7','4',',','1','\n','1','2',',','1',',','2','3','1',',','1','\n','1','0',',','1',',','2','3','5',',','1','\n','4','8',',','1',',','1','2','2',',','1',';','7',',','1',',','2','6','1',',','1','\n','7',',','1',',','2','6','1',',','1',';','1',',','2',',','3','5','1',',','1','\n','9',',','1',',','2','3','9',',','1',';','0',',','1',',','1','8',',','1',',','1','8','8',',','1','\n','0',',','1',',','1','8',',','1',',','1','8','8',',','1',';','0',',','2',',','3','7','1',',','1','\n','0',',','2',',','3','7','1',',','1',';','0',',','2',',','6','9',',','1',',','7','9',',','1','\n','6','4',',','1',',','9','4',',','1','\n','4','8',',','1',',','1','2','1',',','1','\n','4','6',',','1',',','1','3','1',',','1','\n','4','5',',','1',',','1','3','2',',','1','\n','2','3',',','1',',','1','7','4',',','1','\n','2','0',',','1',',','1','9','1',',','1','\n','1','2',',','1',',','2','3','0',',','1','\n','0',',','3',',','3','6','5',',','1','\n','6','4',',','1',',','9','3',',','1','\n','6','4',',','1',',','9','2',',','1','\n','4','8',',','1',',','1','2','0',',','1','\n','4','6',',','1',',','1','3','0',',','1','\n','4','5',',','1',',','1','3','1',',','1','\n','2','2',',','1',',','1','7','4',',','1','\n','2','0',',','1',',','1','9','0',',','1','\n','1','9',',','1',',','1','9','1',',','1','\n','6',',','1',',','2','6','3',',','1','\n','2',',','1',',','1','3',',','1',',','2','0','9',',','1','\n','1',',','1',',','3','7','0',',','1','\n','0',',','1',',','3','8','5',',','1','\n','0',',','3',',','3','6','3',',','1','\n','6','4',',','1',',','9','1',',','1','\n','6','1',',','1',',','1','0','1',',','1','\n','5','7',',','1',',','1','1','4',',','1','\n','5','4',',','1',',','1','1','5',',','1','\n','4','6',',','1',',','1','2','9',',','1','\n','4','6',',','1',',','1','2','8',',','1','\n','4','5',',','1',',','1','3','0',',','1','\n','3','5',',','1',',','1','5','5',',','1','\n','2','8',',','1',',','1','6','4',',','1','\n','2','6',',','1',',','1','7','0',',','1','\n','1','9',',','1',',','1','9','0',',','1','\n','1','1',',','1',',','2','3','4',',','1','\n','6',',','1',',','2','6','2',',','1','\n','2',',','1',',','3','5','0',',','1','\n','2',',','1',',','3','4','9',',','1','\n','0',',','1',',','3','8','4',',','1','\n','0',',','2',',','3','7','0',',','1','\n','6','3',',','1',',','9','4',',','1','\n','4','5',',','1',',','1','2','9',',','1','\n','4','5',',','1',',','1','2','8',',','1','\n','3','4',',','1',',','1','5','5',',','1','\n','2','6',',','1',',','1','6','9',',','1','\n','2','0',',','1',',','1','8','9',',','1','\n','1','7',',','1',',','2','0','2',',','1','\n','1','4',',','1',',','2','1','6',',','1','\n','1','0',',','1',',','2','3','4',',','1','\n','6',',','1',',','2','6','1',',','1','\n','2',',','1',',','3','4','8',',','1','\n','5',',','1',',','2','7','5',',','1',';','1',',','1',',','3','6','9',',','1','\n','1',',','2',',','3','4','9',',','1','\n','0',',','1',',','8',',','1',',','2','5','0',',','1','\n','6','3',',','1',',','9','3',',','1','\n','6','3',',','1',',','9','2',',','1','\n','5','7',',','1',',','1','1','3',',','1','\n','4','2',',','1',',','1','3','9',',','1','\n','4','1',',','1',',','1','4','3',',','1','\n','3','3',',','1',',','1','5','5',',','1','\n','2','6',',','1',',','1','6','8',',','1','\n','1','9',',','1',',','1','8','9',',','1','\n','1','6',',','1',',','2','0','2',',','1','\n','1','2',',','1',',','2','2','9',',','1','\n','0',',','1',',','3','8','3',',','1','\n','0',',','8',',','3','1','2',',','1','\n','6','3',',','1',',','9','1',',','1','\n','5','7',',','1',',','1','1','2',',','1','\n','4','1',',','1',',','1','4','2',',','1','\n','3','2',',','1',',','1','5','5',',','1','\n','2','6',',','1',',','1','6','7',',','1','\n','2','5',',','1',',','1','7','3',',','1','\n','2','5',',','1',',','1','7','2',',','1','\n','7','2',',','1',',','8','0',',','1',';','2','0',',','1',',','1','8','7',',','1','\n','2','0',',','1',',','1','8','7',',','1',';','1','7',',','1',',','2','0','1',',','1','\n','1','9',',','1',',','1','8','8',',','1',';','1','7',',','1',',','2','0','1',',','1',';','1','5',',','1',',','2','0','9',',','1','\n','1','7',',','1',',','2','0','1',',','1',';','1','5',',','1',',','2','0','9',',','1',';','8',',','1',',','2','5','5',',','1','\n','1','5',',','1',',','2','0','9',',','1',';','2',',','1',',','3','4','7',',','1','\n','1','3',',','1',',','2','2','6',',','1',';','2',',','1',',','3','4','6',',','1','\n','7',',','1',',','2','6','0',',','1',';','2',',','1',',','3','4','7',',','1',';','2',',','1',',','3','4','6',',','1',';','0',',','1',',','3','8','2',',','1','\n','2',',','1',',','3','4','7',',','1',';','0',',','1',',','3','8','2',',','1',';','0',',','3',',','3','5','9',',','1','\n','0',',','1',',','3','8','2',',','1',';','0',',','3',',','3','5','9',',','1',';','0',',','4',',','3','4','9',',','1','\n','7','2',',','1',',','7','9',',','1',';','6','4',',','1',',','8','9',',','1',';','4','8',',','1',',','1','1','9',',','1','\n','3','5',',','1',',','1','5','4',',','1','\n','2','6',',','1',',','1','6','6',',','1','\n','2','4',',','1',',','1','7','3',',','1','\n','2','4',',','1',',','1','7','2',',','1','\n','6','4',',','1',',','8','9',',','1',';','1','9',',','1',',','1','8','7',',','1','\n','4','8',',','1',',','1','1','9',',','1',';','1','9',',','1',',','1','8','7',',','1',';','1','6',',','1',',','2','0','1',',','1','\n','1','6',',','1',',','2','0','1',',','1',';','8',',','1',',','2','5','4',',','1','\n','1','9',',','1',',','1','8','7',',','1',';','8',',','1',',','2','5','4',',','1',';','1',',','2',',','3','4','7',',','1','\n','0',',','1',',','3','8','1',',','1','\n','6','4',',','1',',','9','0',',','1',';','8',',','1',',','2','5','4',',','1',';','1',',','2',',','3','4','7',',','1',';','0',',','3',',','3','5','8',',','1','\n','5','2',',','1',',','1','1','8',',','1','\n','4','3',',','1',',','1','3','8',',','1',';','3','4',',','1',',','1','5','4',',','1','\n','3','4',',','1',',','1','5','4',',','1',';','2','3',',','1',',','1','7','2',',','1','\n','2','1',',','1',',','1','7','9',',','1','\n','1','2',',','1',',','2','2','8',',','1','\n','1','1',',','1',',','2','3','3',',','1','\n','2','3',',','1',',','1','7','3',',','1',';','2','3',',','1',',','1','7','2',',','1',';','8',',','1',',','1','3',',','2',',','8','0',',','1','\n','2','3',',','1',',','1','7','2',',','1',';','0',',','3',',','3','5','5',',','1','\n','0',',','3',',','3','5','5',',','1',';','0',',','3',',','1','7',',','1',',','1','8','8',',','1','\n','5','1',',','1',',','1','1','8',',','1',';','4','6',',','1',',','1','2','7',',','1','\n','4','6',',','1',',','1','2','6',',','1','\n','3','3',',','1',',','1','5','4',',','1','\n','4','6',',','1',',','1','2','7',',','1',';','2','2',',','1',',','1','7','3',',','1','\n','2','2',',','1',',','1','7','2',',','1','\n','2','1',',','1',',','1','7','8',',','1','\n','2','2',',','1',',','1','7','3',',','1',';','2','0',',','1',',','1','8','6',',','1','\n','1','1',',','1',',','2','3','2',',','1','\n','1','0',',','1',',','2','3','3',',','1','\n','2','0',',','1',',','1','8','6',',','1',';','8',',','2',',','1','3',',','1',',','1','0','1',',','1','\n','7',',','1',',','2','5','9',',','1','\n','4','3',',','1',',','1','3','7',',','1',';','0',',','4',',','3','4','7',',','1','\n','6','3',',','1',',','9','0',',','1',';','6','3',',','1',',','8','9',',','1','\n','6','1',',','1',',','1','0','0',',','1','\n','6','3',',','1',',','8','9',',','1',';','6','0',',','1',',','1','0','1',',','1','\n','5','9',',','1',',','1','0','1',',','1','\n','6','0',',','1',',','1','0','1',',','1',';','4','5',',','1',',','1','2','7',',','1','\n','4','5',',','1',',','1','2','6',',','1','\n','4','5',',','1',',','1','2','7',',','1',';','3','2',',','1',',','1','5','4',',','1','\n','3','2',',','1',',','1','5','4',',','1',';','2','9',',','1',',','1','6','2',',','1','\n','2','7',',','1',',','1','6','4',',','1','\n','2','1',',','1',',','1','7','7',',','1','\n','2','9',',','1',',','1','6','2',',','1',';','1','9',',','1',',','1','8','6',',','1','\n','1','0',',','1',',','2','3','2',',','1','\n','1','9',',','1',',','1','8','6',',','1',';','8',',','2',',','1','7','3',',','1','\n','7',',','1',',','2','5','8',',','1','\n','6',',','1',',','2','6','0',',','1',';','0',',','1',',','3','8','0',',','1','\n','6','9',',','1',',','8','7',',','1','\n','3','1',',','1',',','1','5','5',',','1','\n','5',',','1',',','2','7','4',',','1','\n','1','4',',','1',',','2','1','5',',','1',';','1',',','1',',','5',',','1',',','2','6','0',',','1','\n','6','2',',','1',',','9','6',',','1','\n','4','4',',','1',',','1','3','4',',','1','\n','4','3',',','1',',','1','3','6',',','1','\n','4','1',',','1',',','1','4','1',',','1','\n','2','1',',','1',',','1','7','6',',','1','\n','7',',','1',',','2','5','7',',','1',';','0',',','7',',','3','1','7',',','1','\n','5','6',',','1',',','1','1','4',',','1','\n','4','4',',','1',',','1','3','3',',','1','\n','1','5',',','1',',','2','0','8',',','1','\n','4','2',',','1',',','1','3','8',',','1',';','8',',','4',',','6','4',',','1','\n','6',',','1',',','2','5','9',',','1','\n','2',',','1',',','3','4','5',',','1','\n','5','8',',','1',',','1','0','7',',','1','\n','5','5',',','1',',','1','1','4',',','1','\n','6','4',',','1',',','8','8',',','1',';','4','2',',','1',',','1','3','7',',','1','\n','1','5',',','1',',','2','0','7',',','1','\n','6',',','1',',','2','5','8',',','1','\n','2',',','1',',','3','4','4',',','1','\n','0',',','1',',','8',',','1',',','2','4','5',',','1','\n','6','2',',','1',',','9','5',',','1','\n','5','8',',','1',',','1','0','6',',','1','\n','5','8',',','1',',','1','0','5',',','1','\n','5','7',',','1',',','1','1','1',',','1','\n','5','6',',','1',',','1','1','3',',','1',';','5','0',',','1',',','1','1','8',',','1','\n','5','0',',','1',',','1','1','8',',','1',';','4','0',',','1',',','1','4','7',',','1','\n','4','0',',','1',',','1','4','7',',','1',';','3','1',',','1',',','1','5','4',',','1','\n','3','1',',','1',',','1','5','4',',','1',';','2','0',',','1',',','1','8','5',',','1','\n','2','0',',','1',',','1','8','5',',','1',';','8',',','1',',','1','7',',','1',',','1','3','8',',','1','\n','0',',','9',',','2','9','9',',','1','\n','7','2',',','1',',','7','8',',','1',';','7','1',',','1',',','8','0',',','1','\n','6','8',',','1',',','8','7',',','1','\n','5','8',',','1',',','1','0','4',',','1','\n','5','8',',','1',',','1','0','3',',','1','\n','5','7',',','1',',','1','1','0',',','1','\n','7','1',',','1',',','8','0',',','1',';','5','6',',','1',',','1','1','2',',','1','\n','5','5',',','1',',','1','1','3',',','1',';','4','9',',','1',',','1','1','8',',','1','\n','4','7',',','1',',','1','2','4',',','1','\n','5','6',',','1',',','1','1','2',',','1',';','4','0',',','1',',','1','4','6',',','1','\n','4','9',',','1',',','1','1','8',',','1',';','3','9',',','1',',','1','4','7',',','1','\n','4','0',',','1',',','1','4','6',',','1',';','3','9',',','1',',','1','4','7',',','1',';','3','0',',','1',',','1','6','0',',','1','\n','2','5',',','1',',','1','7','1',',','1','\n','3','9',',','1',',','1','4','7',',','1',';','3','0',',','1',',','1','6','0',',','1',';','2','0',',','1',',','1','8','4',',','1','\n','3','0',',','1',',','1','6','0',',','1',';','2','0',',','1',',','1','8','4',',','1',';','1','9',',','1',',','1','8','5',',','1','\n','2','0',',','1',',','1','8','4',',','1',';','1','9',',','1',',','1','8','5',',','1',';','1','5',',','1',',','2','0','6',',','1','\n','1','9',',','1',',','1','8','5',',','1',';','1','3',',','1',',','2','2','5',',','1','\n','1','3',',','1',',','2','2','5',',','1',';','9',',','1',',','2','3','8',',','1','\n','9',',','1',',','2','3','8',',','1',';','8',',','1',',','1','6',',','1',',','1','3','8',',','1','\n','1','5',',','1',',','2','0','6',',','1',';','6',',','1',',','2','5','7',',','1','\n','6',',','1',',','2','5','7',',','1',';','2',',','1',',','3','4','3',',','1','\n','2',',','1',',','3','4','3',',','1',';','0',',','1',',','8',',','1',',','2','4','4',',','1','\n','7','2',',','1',',','7','7',',','1',';','7','1',',','1',',','7','9',',','1','\n','6','7',',','1',',','8','7',',','1','\n','6','3',',','1',',','8','8',',','1',';','6','0',',','1',',','1','0','0',',','1','\n','5','9',',','1',',','1','0','0',',','1','\n','7','1',',','1',',','7','9',',','1',';','5','5',',','1',',','1','1','2',',','1','\n','6','0',',','1',',','1','0','0',',','1',';','4','6',',','1',',','1','2','5',',','1','\n','4','6',',','1',',','1','2','5',',','1',';','4','2',',','1',',','1','3','6',',','1','\n','5','5',',','1',',','1','1','2',',','1',';','3','9',',','1',',','1','4','6',',','1','\n','2','4',',','1',',','1','7','1',',','1','\n','3','9',',','1',',','1','4','6',',','1',';','1','9',',','1',',','1','8','4',',','1','\n','1','9',',','1',',','1','8','4',',','1',';','1','3',',','1',',','2','2','4',',','1','\n','1','3',',','1',',','2','2','4',',','1',';','9',',','1',',','2','3','7',',','1','\n','9',',','1',',','2','3','7',',','1',';','8',',','1',',','1','6',',','1',',','1','3','7',',','1','\n','4','2',',','1',',','1','3','6',',','1',';','8',',','4',',','1','7',',','1',',','2','0',',','1','\n','5','2',',','1',',','1','1','7',',','1','\n','3','5',',','1',',','1','5','3',',','1','\n','4','5',',','1',',','1','2','5',',','1',';','2','3',',','1',',','1','7','1',',','1','\n','2','3',',','1',',','1','7','1',',','1',';','8',',','5',',','4','0',',','1','\n','5','2',',','1',',','1','1','6',',','1','\n','3','5',',','1',',','1','5','2',',','1','\n','3','4',',','1',',','1','5','3',',','1','\n','5','1',',','1',',','1','1','7',',','1',';','2','9',',','1',',','1','6','1',',','1','\n','2','9',',','1',',','1','6','1',',','1',';','2','2',',','1',',','1','7','1',',','1','\n','2','2',',','1',',','1','7','1',',','1',';','8',',','5',',','3','9',',','1','\n','0',',','4',',','3','4','3',',','1','\n','6','6',',','1',',','8','7',',','1','\n','3','4',',','1',',','1','5','2',',','1','\n','3','3',',','1',',','1','5','3',',','1','\n','5','1',',','1',',','1','1','6',',','1',';','1','3',',','1',',','2','2','3',',','1','\n','1','3',',','1',',','2','2','3',',','1',';','8',',','2',',','1','7','1',',','1','\n','3','3',',','1',',','1','5','2',',','1','\n','3','2',',','1',',','1','5','3',',','1',';','8',',','2',',','1','7',',','1',',','7','8',',','1','\n','3','2',',','1',',','1','5','2',',','1',';','8',',','3',',','1','1','7',',','1','\n','2','6',',','1',',','1','6','5',',','1','\n','5','6',',','1',',','1','1','1',',','1',';','5','0',',','1',',','1','1','7',',','1','\n','5','0',',','1',',','1','1','7',',','1',';','2','0',',','1',',','1','8','3',',','1','\n','2','0',',','1',',','1','8','3',',','1',';','1','7',',','1',',','2','0','0',',','1','\n','7','1',',','1',',','7','8',',','1',';','5','6',',','1',',','1','1','0',',','1','\n','5','6',',','1',',','1','1','0',',','1',';','5','5',',','1',',','1','1','1',',','1','\n','5','5',',','1',',','1','1','1',',','1',';','5','0',',','1',',','1','1','6',',','1','\n','5','0',',','1',',','1','1','6',',','1',';','4','9',',','1',',','1','1','7',',','1','\n','4','9',',','1',',','1','1','7',',','1',';','4','0',',','1',',','1','4','5',',','1','\n','4','0',',','1',',','1','4','5',',','1',';','3','1',',','1',',','1','5','3',',','1','\n','3','1',',','1',',','1','5','3',',','1',';','2','0',',','1',',','1','8','2',',','1','\n','2','0',',','1',',','1','8','2',',','1',';','1','9',',','1',',','1','8','3',',','1','\n','1','9',',','1',',','1','8','3',',','1',';','1','7',',','1',',','1','9','9',',','1','\n','1','7',',','1',',','1','9','9',',','1',';','1','6',',','1',',','2','0','0',',','1','\n','1','6',',','1',',','2','0','0',',','1',';','8',',','1',',','2','5','3',',','1','\n','7','1',',','1',',','7','7',',','1',';','5','5',',','1',',','1','1','0',',','1','\n','5','5',',','1',',','1','1','0',',','1',';','4','9',',','1',',','1','1','6',',','1','\n','4','9',',','1',',','1','1','6',',','1',';','3','9',',','1',',','1','4','5',',','1','\n','3','9',',','1',',','1','4','5',',','1',';','3','1',',','1',',','1','5','2',',','1','\n','3','1',',','1',',','1','5','2',',','1',';','1','9',',','1',',','1','8','2',',','1','\n','1','9',',','1',',','1','8','2',',','1',';','1','6',',','1',',','1','9','9',',','1','\n','1','6',',','1',',','1','9','9',',','1',';','9',',','1',',','2','3','6',',','1','\n','9',',','1',',','2','3','6',',','1',';','8',',','1',',','2','5','2',',','1','\n','7',',','1',',','2','5','6',',','1','\n','6','5',',','1',',','8','7',',','1','\n','5','8',',','1',',','1','0','2',',','1','\n','4','7',',','1',',','1','2','3',',','1','\n','4','1',',','1',',','1','4','0',',','1','\n','3','0',',','1',',','1','5','9',',','1','\n','2','1',',','1',',','1','7','5',',','1','\n','1','5',',','1',',','2','0','5',',','1','\n','1','2',',','1',',','2','2','7',',','1','\n','6',',','1',',','2','5','6',',','1','\n','4',',','1',',','2','9','0',',','1','\n','2',',','1',',','3','4','2',',','1','\n','1',',','2',',','3','4','2',',','1','\n','0',',','1',',','3','7','9',',','1','\n','6','9',',','1',',','9','4',',','1','\n','6','9',',','1',',','9','2',',','1','\n','1',',','1',',','4','0','0',',','1','\n','6','9',',','1',',','9','1',',','1','\n','4','3',',','1',',','1','4','3',',','1','\n','7',',','1',',','2','7','3',',','1','\n','1',',','1',',','3','9','9',',','1','\n','1',',','1',',','3','9','8',',','1','\n','4','3',',','1',',','1','4','2',',','1','\n','1','1',',','1',',','2','4','2',',','1','\n','3',',','1',',','3','2','3',',','1','\n','1','8',',','1',',','1','9','8',',','1',';','3',',','1',',','6','8',',','1',',','6','9',',','1','\n','1',',','1',',','3','9','7',',','1','\n','1',',','1',',','3','9','6',',','1','\n','1',',','2',',','3','6','8',',','1','\n','0',',','2',',','3','9','8',',','1','\n','0',',','3',',','3','7','8',',','1','\n','1','1',',','1',',','2','4','1',',','1','\n','1','0',',','1',',','2','4','2',',','1','\n','7',',','1',',','2','7','2',',','1','\n','1','8',',','1',',','1','9','7',',','1',';','3',',','1',',','6','7',',','1',',','6','9',',','1','\n','1',',','1',',','3','9','5',',','1',';','1',',','1',',','3','9','4',',','1','\n','3',',','1',',','6','7',',','1',',','6','9',',','1',';','1',',','1',',','3','9','2',',','1','\n','2',',','1',',','3','6','7',',','1',';','1',',','1',',','3','9','4',',','1',';','1',',','1',',','3','9','3',',','1',';','0',',','1',',','4','1','5',',','1','\n','0',',','2',',','3','9','7',',','1','\n','1',',','1',',','3','9','4',',','1',';','1',',','1',',','3','9','2',',','1',';','0',',','2',',','3','9','6',',','1','\n','0',',','3',',','3','7','7',',','1','\n','1','3',',','1',',','2','3','1',',','1','\n','1','1',',','1',',','2','4','0',',','1','\n','1','0',',','1',',','2','4','1',',','1','\n','7',',','1',',','2','7','1',',','1','\n','7',',','1',',','2','7','0',',','1','\n','6','8',',','1',',','9','4',',','1',';','1',',','1',',','3','9','1',',','1','\n','3',',','1',',','3','2','2',',','1',';','1',',','1',',','3','9','1',',','1',';','1',',','1',',','3','9','0',',','1','\n','1',',','1',',','3','9','1',',','1',';','1',',','1',',','3','9','0',',','1',';','1',',','1',',','6','9',',','1',',','8','2',',','1','\n','1',',','1',',','6','9',',','1',',','8','2',',','1',';','1',',','1',',','1','8',',','1',',','1','9','0',',','1','\n','2',',','1',',','3','6','6',',','1',';','0',',','1',',','4','1','4',',','1','\n','1',',','1',',','3','9','0',',','1',';','1',',','1',',','1','8',',','1',',','1','9','0',',','1',';','0',',','2',',','3','9','4',',','1','\n','1',',','1',',','1','8',',','1',',','1','9','0',',','1',';','0',',','2',',','3','9','2',',','1','\n','6','9',',','1',',','9','0',',','1',';','6','9',',','1',',','8','9',',','1','\n','6','8',',','1',',','9','3',',','1','\n','6','7',',','1',',','9','4',',','1','\n','3','5',',','1',',','1','5','8',',','1','\n','1','8',',','1',',','1','9','6',',','1','\n','1','3',',','1',',','2','3','0',',','1','\n','1','0',',','1',',','2','4','0',',','1','\n','6',',','1',',','2','7','3',',','1','\n','3',',','2',',','2','7','0',',','1','\n','3',',','1',',','3','2','1',',','1',';','1',',','1',',','3','8','9',',','1','\n','7',',','1',',','2','6','9',',','1',';','1',',','1',',','3','8','8',',','1','\n','1',',','2',',','3','6','6',',','1','\n','6','8',',','1',',','9','2',',','1',';','1',',','1',',','3','8','9',',','1',';','1',',','1',',','3','8','8',',','1',';','0',',','1',',','4','1','3',',','1','\n','0',',','1',',','4','1','2',',','1','\n','0',',','1',',','4','1','3',',','1',';','0',',','2',',','3','9','1',',','1','\n','0',',','2',',','3','9','0',',','1','\n','6','8',',','1',',','9','1',',','1',';','6','7',',','1',',','9','3',',','1','\n','4','2',',','1',',','1','4','3',',','1','\n','3','4',',','1',',','1','5','8',',','1','\n','6','7',',','1',',','9','3',',','1',';','2','6',',','1',',','1','7','4',',','1','\n','2','3',',','1',',','2','4',',','1',',','6','9',',','1','\n','1','1',',','1',',','2','3','9',',','1','\n','2','6',',','1',',','1','7','4',',','1',';','2',',','1',',','3','6','5',',','1','\n','6','7',',','1',',','9','2',',','1',';','2',',','1',',','3','6','5',',','1',';','1',',','1',',','3','8','7',',','1','\n','3',',','1',',','3','2','0',',','1',';','1',',','1',',','3','8','6',',','1','\n','1',',','1',',','1','8',',','1',',','1','8','9',',','1','\n','0',',','1',',','4','1','1',',','1','\n','2',',','1',',','3','6','5',',','1',';','0',',','1',',','4','1','0',',','1','\n','1',',','1',',','3','8','6',',','1',';','0',',','2',',','3','8','9',',','1',';','0',',','4',',','3','6','7',',','1','\n','4','2',',','1',',','1','4','2',',','1','\n','3','3',',','1',',','1','5','8',',','1','\n','6','7',',','1',',','9','1',',','1',';','1','8',',','1',',','1','9','5',',','1','\n','1','0',',','1',',','2','3','9',',','1','\n','6',',','1',',','2','7','2',',','1','\n','1','8',',','1',',','1','9','5',',','1',';','3',',','1',',','6','8',',','2','\n','2',',','1',',','3','6','4',',','1','\n','3',',','1',',','6','8',',','2',';','2',',','1',',','3','6','3',',','1','\n','0',',','1',',','4','0','8',',','1','\n','2',',','1',',','3','6','3',',','1',';','0',',','2',',','3','8','6',',','1','\n','0',',','3',',','6','9',',','1',',','8','0',',','1','\n','7','6',',','1',',','8','0',',','1','\n','6','6',',','1',',','9','4',',','1','\n','6','4',',','1',',','9','6',',','1','\n','6','1',',','1',',','1','0','7',',','1','\n','5','2',',','1',',','1','2','2',',','1','\n','4','3',',','1',',','1','4','1',',','1','\n','3','5',',','1',',','1','5','7',',','1','\n','3','2',',','1',',','1','5','8',',','1','\n','2','5',',','1',',','1','7','9',',','1','\n','1','7',',','1',',','2','0','4',',','1','\n','1','7',',','1',',','2','0','3',',','1','\n','7',',','1',',','2','6','8',',','1','\n','6',',','1',',','2','7','1',',','1','\n','6',',','1',',','2','7','0',',','1','\n','5',',','1',',','2','8','2',',','1','\n','3',',','1',',','3','1','9',',','1','\n','3',',','1',',','6','7',',','1',',','6','8',',','1',';','0',',','1',',','4','0','7',',','1','\n','7','6',',','1',',','7','9',',','1','\n','7','5',',','1',',','8','0',',','1','\n','7','4',',','1',',','8','0',',','1','\n','6','6',',','1',',','9','3',',','1','\n','6','6',',','1',',','9','2',',','1','\n','6','1',',','1',',','1','0','6',',','1','\n','6','1',',','1',',','1','0','5',',','1','\n','5','7',',','1',',','1','1','5',',','1','\n','5','2',',','1',',','1','2','1',',','1','\n','5','1',',','1',',','1','2','2',',','1','\n','3','8',',','1',',','1','5','1',',','1','\n','3','4',',','1',',','1','5','7',',','1','\n','2','5',',','1',',','1','7','8',',','1','\n','2','4',',','1',',','1','7','9',',','1','\n','1','6',',','1',',','2','0','4',',','1','\n','1','6',',','1',',','2','0','3',',','1','\n','1','3',',','1',',','2','2','9',',','1','\n','6',',','1',',','2','6','9',',','1','\n','5',',','1',',','2','8','1',',','1','\n','3',',','1',',','6','7',',','2','\n','2',',','1',',','3','6','2',',','1','\n','2',',','1',',','3','6','1',',','1','\n','0',',','1',',','4','0','6',',','1','\n','7','5',',','1',',','7','9',',','1','\n','7','4',',','1',',','7','9',',','1','\n','7','3',',','1',',','8','0',',','1','\n','7','2',',','1',',','8','6',',','1','\n','6','8',',','1',',','8','9',',','1','\n','6','6',',','1',',','9','1',',','1','\n','6','1',',','1',',','1','0','4',',','1','\n','6','1',',','1',',','1','0','3',',','1','\n','5','2',',','1',',','1','2','0',',','1','\n','5','1',',','1',',','1','2','1',',','1','\n','3','8',',','1',',','1','5','0',',','1','\n','3','7',',','1',',','1','5','1',',','1','\n','3','3',',','1',',','1','5','7',',','1','\n','2','5',',','1',',','1','7','7',',','1','\n','2','4',',','1',',','1','7','8',',','1','\n','2','3',',','1',',','1','7','9',',','1','\n','1','5',',','1',',','2','1','4',',','1','\n','1','4',',','1',',','2','2','2',',','1','\n','1','2',',','1',',','2','3','5',',','1','\n','9',',','1',',','2','4','3',',','1','\n','4',',','1',',','2','9','4',',','1','\n','6','8',',','1',',','9','0',',','1',';','3',',','2',',','2','6','7',',','1','\n','2',',','1',',','3','6','0',',','1','\n','1',',','1',',','3','8','4',',','1','\n','1',',','2',',','3','6','1',',','1','\n','7','3',',','1',',','7','9',',','1','\n','7','2',',','1',',','8','5',',','1','\n','7','2',',','1',',','8','4',',','1','\n','6','7',',','1',',','8','9',',','1','\n','6','4',',','1',',','9','5',',','1','\n','6','3',',','1',',','9','6',',','1','\n','5','1',',','1',',','1','2','0',',','1','\n','4','6',',','1',',','1','3','4',',','1','\n','4','0',',','1',',','1','4','8',',','1','\n','3','7',',','1',',','1','5','0',',','1','\n','3','2',',','1',',','1','5','7',',','1','\n','3','0',',','1',',','1','6','3',',','1','\n','2','9',',','1',',','1','6','4',',','1','\n','2','4',',','1',',','1','7','7',',','1','\n','2','3',',','1',',','1','7','8',',','1','\n','2','2',',','1',',','1','7','9',',','1','\n','2','0',',','1',',','1','9','2',',','1','\n','1','8',',','1',',','1','9','4',',','1','\n','3',',','1',',','3','1','8',',','1','\n','6','7',',','1',',','9','0',',','1',';','3',',','2',',','2','6','6',',','1','\n','3',',','2',',','2','6','6',',','1',';','2',',','1',',','3','5','9',',','1','\n','2',',','1',',','1','3',',','1',',','2','1','2',',','1','\n','1',',','1',',','8',',','1',',','2','5','0',',','1','\n','1',',','2',',','3','6','0',',','1','\n','7','2',',','1',',','8','3',',','1','\n','4','5',',','1',',','1','3','4',',','1','\n','3','9',',','1',',','1','4','8',',','1','\n','7','2',',','1',',','8','2',',','1',';','3','6',',','1',',','1','5','1',',','1','\n','3','6',',','1',',','1','5','1',',','1',';','3','5',',','1',',','1','5','6',',','1','\n','3','5',',','1',',','1','5','6',',','1',';','2','8',',','1',',','1','7','0',',','1','\n','2','8',',','1',',','1','7','0',',','1',';','2','5',',','1',',','1','7','6',',','1','\n','2','3',',','1',',','1','7','7',',','1','\n','2','2',',','1',',','1','7','8',',','1','\n','1','9',',','1',',','1','9','2',',','1','\n','6','9',',','1',',','8','8',',','1',';','1','8',',','1',',','1','9','3',',','1','\n','1','5',',','1',',','2','1','3',',','1','\n','2','5',',','1',',','1','7','6',',','1',';','1','3',',','1',',','2','2','8',',','1','\n','4','6',',','1',',','1','3','3',',','1',';','9',',','1',',','1','3',',','2',',','7','5',',','1','\n','6',',','1',',','2','6','8',',','1','\n','1','8',',','1',',','1','9','3',',','1',';','5',',','1',',','2','8','0',',','1','\n','5',',','1',',','2','8','0',',','1',';','4',',','1',',','2','9','3',',','1','\n','2',',','1',',','3','5','8',',','1','\n','1','3',',','1',',','2','2','8',',','1',';','2',',','1',',','3','5','7',',','1','\n','4',',','1',',','2','9','3',',','1',';','1',',','1',',','3','8','3',',','1','\n','2',',','1',',','3','5','7',',','1',';','1',',','2',',','3','5','9',',','1','\n','7','2',',','1',',','8','1',',','1','\n','4','8',',','1',',','1','2','4',',','1','\n','4','5',',','1',',','1','3','3',',','1','\n','4','2',',','1',',','1','4','1',',','1','\n','3','8',',','1',',','1','4','9',',','1','\n','3','6',',','1',',','1','5','0',',','1','\n','3','4',',','1',',','1','5','6',',','1','\n','3','1',',','1',',','1','5','8',',','1','\n','2','8',',','1',',','1','6','9',',','1','\n','2','6',',','1',',','1','7','3',',','1','\n','2','6',',','1',',','1','7','2',',','1','\n','2','4',',','1',',','1','7','6',',','1','\n','2','2',',','1',',','1','7','7',',','1','\n','2','1',',','1',',','1','8','1',',','1','\n','1','4',',','1',',','2','2','1',',','1','\n','3',',','1',',','3','1','6',',','1','\n','6',',','1',',','2','6','7',',','1',';','5',',','1',',','2','7','9',',','1',';','2',',','1',',','3','5','6',',','1','\n','3',',','1',',','3','1','7',',','1',';','2',',','1',',','3','5','5',',','1','\n','5',',','1',',','2','7','9',',','1',';','1',',','1',',','3','8','2',',','1','\n','1',',','2',',','3','5','7',',','1','\n','2',',','1',',','3','5','6',',','1',';','0',',','1',',','4','0','5',',','1','\n','1',',','1',',','3','8','2',',','1',';','0',',','1',',','2','0',',','1',',','1','8','8',',','1','\n','6','3',',','1',',','9','5',',','1','\n','6','6',',','1',',','8','9',',','1',';','5','3',',','1',',','1','1','8',',','1','\n','3','7',',','1',',','1','4','9',',','1','\n','3','3',',','1',',','1','5','6',',','1','\n','2','8',',','1',',','1','6','8',',','1','\n','1','2',',','1',',','2','3','4',',','1','\n','6','6',',','1',',','9','0',',','1',';','8',',','1',',','5','0',',','1',',','6','9',',','1','\n','6',',','1',',','2','6','6',',','1',';','4',',','1',',','2','9','2',',','1','\n','1',',','1',',','3','8','1',',','1','\n','5','3',',','1',',','1','1','8',',','1',';','4',',','1',',','2','9','2',',','1',';','0',',','1',',','8',',','1',',','2','5','5',',','1','\n','4',',','1',',','2','9','2',',','1',';','0',',','1',',','2',',','1',',','3','4','6',',','1','\n','8',',','1',',','5','0',',','1',',','6','9',',','1',';','0',',','1',',','8',',','1',',','2','5','5',',','1',';','0',',','1',',','2',',','1',',','3','4','6',',','1',';','0',',','4',',','3','5','9',',','1','\n','2','3',',','1',',','1','7','6',',','1',';','0',',','4',',','3','5','9',',','1',';','0',',','5',',','3','4','9',',','1','\n','6','0',',','1',',','1','0','7',',','1',';','5','9',',','1',',','1','0','7',',','1','\n','5','2',',','1',',','1','1','9',',','1','\n','5','0',',','1',',','1','2','2',',','1','\n','4','7',',','1',',','1','3','2',',','1','\n','3','2',',','1',',','1','5','6',',','1','\n','2','8',',','1',',','1','6','7',',','1','\n','2','2',',','1',',','1','7','6',',','1','\n','5','9',',','1',',','1','0','7',',','1',';','1','5',',','1',',','2','1','2',',','1','\n','8',',','1',',','4','9',',','1',',','6','9',',','1','\n','1','5',',','1',',','2','1','2',',','1',';','4',',','1',',','2','9','1',',','1','\n','4',',','1',',','2','9','1',',','1',';','0',',','1',',','8',',','1',',','2','5','4',',','1','\n','0',',','1',',','8',',','1',',','2','5','4',',','1',';','0',',','4',',','3','5','8',',','1','\n','6','0',',','1',',','1','0','5',',','1','\n','6','0',',','1',',','1','0','6',',','1',';','5','9',',','1',',','1','0','6',',','1','\n','5','9',',','1',',','1','0','5',',','1','\n','5','1',',','1',',','1','1','9',',','1','\n','5','0',',','1',',','1','2','1',',','1','\n','4','9',',','1',',','1','2','2',',','1','\n','4','7',',','1',',','1','3','1',',','1','\n','5','9',',','1',',','1','0','6',',','1',';','3','6',',','1',',','1','4','9',',','1','\n','3','1',',','1',',','1','5','7',',','1','\n','2','8',',','1',',','1','6','6',',','1','\n','3','6',',','1',',','1','4','9',',','1',';','0',',','4',',','1','7',',','1',',','1','8','8',',','1','\n','6','8',',','1',',','8','8',',','1','\n','6','0',',','1',',','1','0','4',',','1','\n','6','0',',','1',',','1','0','3',',','1','\n','5','9',',','1',',','1','0','4',',','1','\n','5','9',',','1',',','1','0','3',',','1','\n','4','9',',','1',',','1','2','1',',','1','\n','4','7',',','1',',','1','3','0',',','1','\n','5',',','1',',','2','7','8',',','1',';','1',',','1',',','3','8','0',',','1','\n','5','0',',','1',',','1','2','0',',','1',';','1',',','1',',','3','8','0',',','1',';','0',',','1',',','4','0','4',',','1','\n','1',',','1',',','3','8','0',',','1',';','0',',','1',',','4','0','4',',','1',';','0',',','5',',','3','4','7',',','1','\n','7','6',',','1',',','7','8',',','1','\n','6','7',',','1',',','8','8',',','1','\n','4','9',',','1',',','1','2','0',',','1','\n','4','7',',','1',',','1','2','9',',','1','\n','4','7',',','1',',','1','2','8',',','1','\n','7','6',',','1',',','7','7',',','1','\n','7','5',',','1',',','7','8',',','1','\n','7','4',',','1',',','7','8',',','1','\n','6','5',',','1',',','9','4',',','1','\n','6','2',',','1',',','9','9',',','1','\n','5','8',',','1',',','1','0','9',',','1','\n','5','6',',','1',',','1','1','5',',','1','\n','2','7',',','1',',','1','7','0',',','1','\n','1','4',',','1',',','2','2','0',',','1','\n','1','2',',','1',',','2','3','3',',','1','\n','7','5',',','1',',','7','7',',','1','\n','7','4',',','1',',','7','7',',','1','\n','7','3',',','1',',','7','8',',','1','\n','7','1',',','1',',','8','6',',','1','\n','6','5',',','1',',','9','3',',','1','\n','6','5',',','1',',','9','2',',','1','\n','5','5',',','1',',','1','1','5',',','1','\n','3','1',',','1',',','1','5','6',',','1','\n','2','7',',','1',',','1','6','9',',','1','\n','1','4',',','1',',','2','1','9',',','1','\n','1','2',',','1',',','2','3','2',',','1','\n','3',',','1',',','3','1','5',',','1','\n','0',',','1',',','8',',','3',',','1','1','8',',','1','\n','7','3',',','1',',','7','7',',','1','\n','7','1',',','1',',','8','5',',','1','\n','7','1',',','1',',','8','4',',','1','\n','7','0',',','1',',','8','7',',','1','\n','6','6',',','1',',','8','8',',','1','\n','6','5',',','1',',','9','1',',','1','\n','5','8',',','1',',','1','0','8',',','1','\n','4','1',',','1',',','1','4','4',',','1','\n','2','7',',','1',',','1','6','8',',','1','\n','2','1',',','1',',','1','8','0',',','1','\n','1','4',',','1',',','2','1','8',',','1','\n','5',',','1',',','2','7','7',',','1','\n','7','1',',','1',',','8','3',',','1','\n','7','1',',','1',',','8','2',',','1','\n','5','0',',','1',',','1','1','9',',','1','\n','2','7',',','1',',','1','6','7',',','1','\n','1','1',',','1',',','2','3','8',',','1','\n','7','1',',','1',',','8','1',',','1','\n','4','9',',','1',',','1','1','9',',','1',';','3','0',',','1',',','1','6','2',',','1','\n','3','0',',','1',',','1','6','2',',','1',';','2','7',',','1',',','1','6','6',',','1','\n','2','6',',','1',',','1','7','1',',','1','\n','1','1',',','1',',','2','3','7',',','1','\n','2','7',',','1',',','1','6','6',',','1',';','1','0',',','1',',','2','3','8',',','1','\n','1','0',',','1',',','2','3','8',',','1',';','1',',','1',',','8',',','1',',','2','4','4',',','1','\n','1',',','1',',','8',',','1',',','2','4','4',',','1',';','0',',','1',',','8',',','1',',','1','7',',','1',',','1','3','8',',','1','\n','5','3',',','1',',','1','1','7',',','1',';','4','7',',','1',',','1','2','7',',','1','\n','4','7',',','1',',','1','2','7',',','1',';','1','0',',','1',',','2','3','7',',','1','\n','4','7',',','1',',','1','2','6',',','1',';','1','0',',','1',',','2','3','7',',','1',';','0',',','1',',','8',',','1',',','1','6',',','1',',','1','3','8',',','1','\n','1','0',',','1',',','2','3','7',',','1',';','0',',','1',',','8',',','1',',','1','6',',','1',',','1','3','8',',','1',';','0',',','2',',','8',',','1',',','2','4','4',',','1','\n','6','5',',','1',',','9','0',',','1',';','6','5',',','1',',','8','9',',','1','\n','6','2',',','1',',','9','8',',','1','\n','6','1',',','1',',','1','0','2',',','1','\n','6','5',',','1',',','8','9',',','1',';','5','3',',','1',',','1','1','6',',','1','\n','5','3',',','1',',','1','1','6',',','1',';','0',',','1',',','8',',','1',',','1','6',',','1',',','1','3','7',',','1','\n','4','3',',','1',',','1','4','0',',','1','\n','4','8',',','1',',','1','2','3',',','1','\n','7',',','1',',','2','6','5',',','1','\n','2','5',',','1',',','1','7','5',',','1','\n','6','5',',','1',',','8','8',',','1','\n','6','0',',','1',',','1','0','2',',','1','\n','5','9',',','1',',','1','0','2',',','1','\n','4','7',',','1',',','1','2','5',',','1','\n','4','2',',','1',',','1','4','0',',','1','\n','3','0',',','1',',','1','6','1',',','1','\n','2','4',',','1',',','1','7','5',',','1','\n','1','5',',','1',',','2','1','1',',','1','\n','1','5',',','1',',','2','1','0',',','1','\n','6',',','1',',','2','6','5',',','1','\n','2',',','1',',','3','5','4',',','1','\n','0',',','1',',','4','0','1',',','1','\n','2','8',',','1',',','1','6','5',',','1',';','2','3',',','1',',','1','7','5',',','1','\n','1','1',',','1',',','2','3','6',',','1','\n','2','3',',','1',',','1','7','5',',','1',';','1',',','2',',','3','5','4',',','1','\n','1',',','2',',','3','5','4',',','1',';','0',',','1',',','1','7',',','1',',','2','0','0',',','1','\n','2','2',',','1',',','1','7','5',',','1',';','1','0',',','1',',','2','3','6',',','1','\n','1','0',',','1',',','2','3','6',',','1',';','0',',','1',',','8',',','1',',','2','5','3',',','1','\n','1','3',',','1',',','2','2','7',',','1',';','0',',','1',',','8',',','1',',','2','5','2',',','1','\n','6','2',',','1',',','9','7',',','1',';','4','4',',','1',',','1','3','5',',','1','\n','4','4',',','1',',','1','3','5',',','1',';','2','7',',','1',',','1','6','5',',','1','\n','2','7',',','1',',','1','6','5',',','1',';','1','4',',','1',',','2','1','7',',','1','\n','1','4',',','1',',','2','1','7',',','1',';','5',',','1',',','2','7','6',',','1','\n','5',',','1',',','2','7','6',',','1',';','1',',','1',',','3','7','9',',','1','\n','6','9',',','1',',','9','6',',','1','\n','2',',','1',',','3','7','8',',','1','\n','2',',','1',',','3','7','7',',','1','\n','0',',','1',',','6','9',',','1',',','9','3',',','1','\n','7','0',',','1',',','9','4',',','1','\n','7','0',',','1',',','9','3',',','1','\n','2',',','1',',','3','7','5',',','1','\n','7','0',',','1',',','9','2',',','1',';','1',',','1',',','4','1','5',',','1','\n','7','0',',','1',',','9','1',',','1','\n','6','8',',','1',',','9','6',',','1','\n','2',',','1',',','3','7','4',',','1',';','1',',','1',',','4','1','4',',','1','\n','1',',','2',',','3','7','6',',','1','\n','1',',','1',',','4','1','4',',','1',';','0',',','2',',','4','1','5',',','1','\n','0',',','3',',','3','9','6',',','1','\n','7','6',',','1',',','8','6',',','1','\n','6','7',',','1',',','9','6',',','1','\n','4','8',',','1',',','1','3','2',',','1','\n','1','8',',','1',',','2','0','2',',','1','\n','8',',','1',',','2','6','4',',','1',';','2',',','1',',','3','7','2',',','1','\n','2',',','1',',','3','7','2',',','1',';','2',',','1',',','6','9',',','1',',','8','0',',','1','\n','3',',','1',',','3','3','2',',','1',';','1',',','1',',','4','1','3',',','1',';','1',',','1',',','4','1','2',',','1','\n','2',',','1',',','6','9',',','1',',','8','0',',','1',';','0',',','1',',','4','1','9',',','1','\n','0',',','3',',','3','9','4',',','1','\n','0',',','3',',','3','9','2',',','1','\n','7','6',',','1',',','8','5',',','1','\n','7','6',',','1',',','8','4',',','1','\n','7','5',',','1',',','8','6',',','1',';','7','4',',','1',',','8','6',',','1','\n','6','1',',','1',',','1','0','9',',','1','\n','4','8',',','1',',','1','3','1',',','1','\n','2','5',',','1',',','1','8','1',',','1','\n','1','2',',','1',',','2','4','2',',','1','\n','3',',','1',',','3','3','1',',','1','\n','1',',','1',',','4','1','1',',','1','\n','1',',','1',',','4','1','0',',','1','\n','1',',','1',',','4','0','9',',','1','\n','7','4',',','1',',','8','6',',','1',';','2',',','1',',','3','7','1',',','1',';','0',',','1',',','6','9',',','1',',','8','9',',','1','\n','2',',','1',',','3','7','1',',','1',';','0',',','1',',','6','9',',','1',',','8','9',',','1',';','0',',','3',',','3','9','1',',','1','\n','7','6',',','1',',','8','3',',','1',';','7','5',',','1',',','8','5',',','1','\n','7','5',',','1',',','8','4',',','1','\n','7','4',',','1',',','8','5',',','1','\n','7','4',',','1',',','8','4',',','1','\n','7','3',',','1',',','8','6',',','1','\n','7','5',',','1',',','8','5',',','1',';','6','8',',','1',',','9','5',',','1','\n','5','3',',','1',',','1','2','2',',','1','\n','4','8',',','1',',','1','3','0',',','1','\n','6','8',',','1',',','9','5',',','1',';','2','4',',','1',',','1','8','1',',','1','\n','2','4',',','1',',','1','8','1',',','1',';','1','8',',','1',',','2','0','1',',','1','\n','1','8',',','1',',','2','0','1',',','1',';','1','3',',','1',',','2','3','5',',','1','\n','1','2',',','1',',','2','4','1',',','1','\n','1','3',',','1',',','2','3','5',',','1',';','9',',','1',',','2','5','1',',','1','\n','3',',','1',',','3','3','0',',','1','\n','1',',','1',',','4','0','8',',','1','\n','0',',','2',',','4','1','0',',','1','\n','0',',','2',',','4','0','9',',','1','\n','0',',','3',',','3','8','9',',','1',';','0',',','5',',','3','6','7',',','1','\n','7','6',',','1',',','8','1',',','1',';','7','5',',','1',',','8','2',',','1','\n','7','4',',','1',',','8','3',',','1','\n','7','5',',','1',',','8','2',',','1',';','7','4',',','1',',','8','2',',','1','\n','7','3',',','1',',','8','5',',','1','\n','7','3',',','1',',','8','4',',','1','\n','7','4',',','1',',','8','2',',','1',';','7','0',',','1',',','9','0',',','1','\n','7','0',',','1',',','8','9',',','1','\n','7','5',',','1',',','8','3',',','1',';','7','0',',','1',',','9','0',',','1',';','6','7',',','1',',','9','5',',','1','\n','6','6',',','1',',','9','6',',','1','\n','6','4',',','1',',','9','9',',','1','\n','6','1',',','1',',','1','0','8',',','1','\n','5','3',',','1',',','1','2','1',',','1','\n','4','8',',','1',',','1','2','9',',','1','\n','4','8',',','1',',','1','2','8',',','1','\n','7','0',',','1',',','9','0',',','1',';','2','8',',','1',',','1','7','4',',','1','\n','2','8',',','1',',','1','7','4',',','1',';','2','6',',','1',',','1','7','9',',','1','\n','6','7',',','1',',','9','5',',','1',';','2','6',',','1',',','1','7','9',',','1',';','2','3',',','1',',','1','8','1',',','1','\n','2','0',',','1',',','1','9','8',',','1','\n','1','2',',','1',',','2','4','0',',','1','\n','8',',','1',',','2','6','3',',','1','\n','5',',','1',',','2','8','9',',','1','\n','4',',','1',',','3','1','0',',','1','\n','2','6',',','1',',','1','7','9',',','1',';','3',',','1',',','3','2','9',',','1','\n','3',',','1',',','3','2','9',',','1',';','1',',','1',',','4','0','7',',','1','\n','0',',','1',',','4','1','7',',','1','\n','1',',','1',',','4','0','7',',','1',';','0',',','3',',','3','8','6',',','1','\n','7','5',',','1',',','8','1',',','1','\n','7','4',',','1',',','8','1',',','1','\n','7','3',',','1',',','8','3',',','1','\n','7','3',',','1',',','8','2',',','1','\n','5','3',',','1',',','1','2','0',',','1','\n','3','8',',','1',',','1','5','5',',','1','\n','2','6',',','1',',','1','7','8',',','1','\n','2','2',',','1',',','1','8','1',',','1','\n','2','0',',','1',',','1','9','7',',','1','\n','1','9',',','1',',','1','9','8',',','1','\n','1','1',',','1',',','2','4','3',',','1','\n','8',',','1',',','2','6','2',',','1','\n','5',',','1',',','2','8','8',',','1','\n','4',',','1',',','3','0','9',',','1','\n','2',',','1',',','3','7','0',',','1','\n','1',',','1',',','4','0','6',',','1','\n','0',',','2',',','4','0','7',',','1','\n','7','3',',','1',',','8','1',',','1','\n','4','3',',','1',',','1','4','4',',','1','\n','3','7',',','1',',','1','5','5',',','1','\n','2','6',',','1',',','1','7','7',',','1','\n','1','9',',','1',',','1','9','7',',','1','\n','1','2',',','1',',','2','3','9',',','1','\n','1','0',',','1',',','2','4','3',',','1','\n','9',',','1',',','2','5','0',',','1',';','8',',','1',',','2','6','1',',','1','\n','4',',','1',',','3','0','8',',','1','\n','4',',','1',',','3','0','7',',','1','\n','3',',','1',',','3','2','8',',','1','\n','6','3',',','1',',','9','9',',','1','\n','2','0',',','1',',','1','9','6',',','1','\n','1','5',',','1',',','2','1','6',',','1','\n','6','6',',','1',',','9','5',',','1',';','1','3',',','1',',','2','3','4',',','1','\n','6',',','1',',','2','7','5',',','1','\n','4',',','1',',','3','0','6',',','1','\n','2',',','1',',','3','6','9',',','1','\n','1','3',',','1',',','2','3','4',',','1',';','2',',','2',',','3','2','8',',','1','\n','2',',','2',',','3','2','8',',','1',';','0',',','1',',','7',',','1',',','2','6','6',',','1','\n','0',',','1',',','7',',','1',',','2','6','6',',','1',';','0',',','1',',','3',',','2',',','2','6','7',',','1','\n','3','6',',','1',',','1','5','5',',','1',';','2','6',',','1',',','1','7','6',',','1','\n','2','1',',','1',',','1','9','1',',','1','\n','1','9',',','1',',','1','9','6',',','1','\n','9',',','1',',','2','4','9',',','1','\n','5',',','1',',','2','8','7',',','1','\n','4',',','1',',','3','0','5',',','1','\n','4',',','1',',','3','0','4',',','1','\n','1',',','2',',','3','6','9',',','1','\n','2','6',',','1',',','1','7','6',',','1',';','0',',','1',',','2',',','1',',','3','5','9',',','1','\n','6','0',',','1',',','1','0','9',',','1','\n','5','9',',','1',',','1','0','9',',','1','\n','5','4',',','1',',','1','1','8',',','1','\n','3','8',',','1',',','1','5','4',',','1','\n','2','9',',','1',',','1','7','0',',','1','\n','2','1',',','1',',','1','9','0',',','1','\n','2','0',',','1',',','1','9','5',',','1','\n','5',',','1',',','2','8','6',',','1','\n','5',',','1',',','2','8','5',',','1','\n','4',',','1',',','3','0','3',',','1','\n','4',',','1',',','3','0','2',',','1','\n','1',',','1',',','4','0','5',',','1','\n','6','4',',','1',',','9','8',',','1','\n','5','3',',','1',',','1','1','9',',','1','\n','5','2',',','1',',','1','2','4',',','1','\n','4','8',',','1',',','1','2','7',',','1','\n','4','8',',','1',',','1','2','6',',','1','\n','3','7',',','1',',','1','5','4',',','1','\n','3','5',',','1',',','1','6','0',',','1','\n','2','9',',','1',',','1','6','9',',','1','\n','2','5',',','1',',','1','8','0',',','1','\n','1','9',',','1',',','1','9','5',',','1','\n','7',',','1',',','2','7','4',',','1','\n','5',',','1',',','2','8','4',',','1','\n','4',',','1',',','3','0','1',',','1','\n','4',',','1',',','3','0','0',',','1','\n','3',',','1',',','3','2','7',',','1','\n','0',',','1',',','2',',','1',',','3','5','5',',','1','\n','0',',','2',',','4','0','5',',','1','\n','0',',','2',',','2','0',',','1',',','1','8','8',',','1','\n','6','0',',','1',',','1','0','8',',','1','\n','7','0',',','1',',','8','8',',','1',';','5','9',',','1',',','1','0','8',',','1','\n','5','1',',','1',',','1','2','4',',','1','\n','5','9',',','1',',','1','0','8',',','1',';','4','2',',','1',',','1','4','4',',','1','\n','4','2',',','1',',','1','4','4',',','1',';','3','4',',','1',',','1','6','0',',','1','\n','2','9',',','1',',','1','6','8',',','1','\n','2','8',',','1',',','1','7','3',',','1','\n','3','4',',','1',',','1','6','0',',','1',';','2','8',',','1',',','1','7','2',',','1','\n','2','8',',','1',',','1','7','2',',','1',';','2','7',',','1',',','1','7','4',',','1','\n','2','4',',','1',',','1','8','0',',','1','\n','2','1',',','1',',','1','8','9',',','1','\n','0',',','2',',','2',',','1',',','3','4','6',',','1','\n','2','7',',','1',',','1','7','4',',','1',';','0',',','6',',','3','4','9',',','1','\n','3','6',',','1',',','1','5','4',',','1','\n','3','3',',','1',',','1','6','0',',','1','\n','2','9',',','1',',','1','6','7',',','1',';','2','3',',','1',',','1','8','0',',','1','\n','2','1',',','1',',','1','8','8',',','1','\n','2','3',',','1',',','1','8','0',',','1',';','1','3',',','1',',','2','3','3',',','1','\n','1','3',',','1',',','2','3','3',',','1',';','9',',','1',',','2','4','8',',','1','\n','4',',','1',',','2','9','9',',','1','\n','0',',','5',',','3','5','8',',','1','\n','6','3',',','1',',','9','8',',','1','\n','4','0',',','1',',','1','5','1',',','1','\n','3','0',',','1',',','1','6','4',',','1','\n','3','2',',','1',',','1','6','0',',','1',';','2','9',',','1',',','1','6','6',',','1','\n','2','9',',','1',',','1','6','6',',','1',';','2','2',',','1',',','1','8','0',',','1','\n','2','2',',','1',',','1','8','0',',','1',';','2','0',',','1',',','1','9','4',',','1','\n','2','0',',','1',',','1','9','4',',','1',';','1','3',',','1',',','2','3','2',',','1','\n','1','3',',','1',',','2','3','2',',','1',';','8',',','1',',','9',',','1',',','1','6','7',',','1','\n','2','1',',','1',',','1','8','7',',','1',';','1',',','1',',','4','0','4',',','1','\n','1',',','1',',','4','0','4',',','1',';','0',',','5',',','1','7',',','1',',','1','8','8',',','1','\n','4','0',',','1',',','1','5','0',',','1','\n','3','9',',','1',',','1','5','1',',','1','\n','2','0',',','1',',','1','9','3',',','1',';','1','9',',','1',',','1','9','4',',','1','\n','1','9',',','1',',','1','9','4',',','1',';','1','7',',','1',',','2','0','8',',','1','\n','1','5',',','1',',','2','1','5',',','1','\n','1','4',',','1',',','2','2','6',',','1','\n','1','7',',','1',',','2','0','8',',','1',';','8',',','2',',','1','8','0',',','1','\n','6',',','1',',','2','7','4',',','1',';','0',',','2',',','4','0','4',',','1','\n','0',',','2',',','4','0','4',',','1',';','0',',','6',',','3','4','7',',','1','\n','6','5',',','1',',','9','6',',','1','\n','4','7',',','1',',','1','3','4',',','1','\n','3','9',',','1',',','1','5','0',',','1','\n','1','9',',','1',',','1','9','3',',','1',';','1','7',',','1',',','2','0','7',',','1','\n','1','6',',','1',',','2','0','8',',','1',';','9',',','1',',','2','4','7',',','1','\n','1','7',',','1',',','2','0','7',',','1',';','9',',','1',',','2','4','7',',','1',';','9',',','1',',','2','4','6',',','1','\n','9',',','1',',','2','4','7',',','1',';','8',',','1',',','2','5','9',',','1','\n','9',',','1',',','2','4','6',',','1',';','0',',','3',',','3','8','0',',','1','\n','4','7',',','1',',','1','3','3',',','1','\n','4','4',',','1',',','1','3','9',',','1','\n','2','1',',','1',',','1','8','6',',','1','\n','1','6',',','1',',','2','0','7',',','1',';','9',',','1',',','2','4','5',',','1','\n','9',',','1',',','2','4','5',',','1',';','8',',','1',',','2','5','8',',','1','\n','5','0',',','1',',','1','2','4',',','1','\n','4','0',',','1',',','1','4','9',',','1',';','1','7',',','1',',','2','0','6',',','1','\n','6','5',',','1',',','9','5',',','1','\n','4','9',',','1',',','1','2','4',',','1','\n','4','8',',','1',',','1','2','5',',','1',';','3','9',',','1',',','1','4','9',',','1',';','3','1',',','1',',','1','6','0',',','1','\n','2','7',',','1',',','1','7','3',',','1','\n','3','9',',','1',',','1','4','9',',','1',';','3','1',',','1',',','1','6','0',',','1',';','2','7',',','1',',','1','7','2',',','1','\n','3','1',',','1',',','1','6','0',',','1',';','1','6',',','1',',','2','0','6',',','1','\n','2','7',',','1',',','1','7','2',',','1',';','1','6',',','1',',','2','0','6',',','1',';','9',',','1',',','2','4','4',',','1','\n','1','6',',','1',',','2','0','6',',','1',';','8',',','1',',','2','5','7',',','1','\n','9',',','1',',','2','4','4',',','1',';','8',',','1',',','2','5','7',',','1',';','1',',','1',',','4','2',',','1',',','1','3','7',',','1','\n','5','4',',','1',',','1','1','7',',','1','\n','5','8',',','1',',','1','1','4',',','1','\n','5','4',',','1',',','1','1','6',',','1','\n','3','8',',','1',',','1','5','3',',','1','\n','0',',','2',',','8',',','1',',','1','7',',','1',',','1','3','8',',','1','\n','3','8',',','1',',','1','5','2',',','1','\n','3','7',',','1',',','1','5','3',',','1','\n','2','8',',','1',',','1','7','1',',','1','\n','6','2',',','1',',','1','0','1',',','1',';','0',',','2',',','8',',','1',',','1','6',',','1',',','1','3','8',',','1','\n','5','8',',','1',',','1','1','3',',','1',';','4','1',',','1',',','1','4','7',',','1','\n','3','7',',','1',',','1','5','2',',','1','\n','4','1',',','1',',','1','4','7',',','1',';','2','1',',','1',',','1','8','5',',','1','\n','1','8',',','1',',','2','0','0',',','1','\n','2','1',',','1',',','1','8','5',',','1',';','1','2',',','1',',','2','3','8',',','1','\n','1','2',',','1',',','2','3','8',',','1',';','4',',','1',',','2','9','8',',','1','\n','4',',','1',',','2','9','8',',','1',';','0',',','2',',','8',',','1',',','1','6',',','1',',','1','3','7',',','1','\n','7','2',',','1',',','8','7',',','1','\n','5','8',',','1',',','1','1','2',',','1','\n','4','1',',','1',',','1','4','6',',','1','\n','3','6',',','1',',','1','5','3',',','1','\n','2','1',',','1',',','1','8','4',',','1','\n','1','8',',','1',',','1','9','9',',','1','\n','1','2',',','1',',','2','3','7',',','1','\n','4',',','1',',','2','9','7',',','1','\n','4','4',',','1',',','1','3','8',',','1','\n','3','6',',','1',',','1','5','2',',','1','\n','1','4',',','1',',','2','2','5',',','1','\n','1',',','1',',','4','0','3',',','1','\n','5','2',',','1',',','1','2','3',',','1','\n','6','4',',','1',',','9','7',',','1',';','4','4',',','1',',','1','3','7',',','1','\n','3','5',',','1',',','1','5','9',',','1','\n','4','4',',','1',',','1','3','7',',','1',';','1','4',',','1',',','2','2','4',',','1','\n','1','4',',','1',',','2','2','4',',','1',';','1',',','1',',','4','0','2',',','1','\n','5','1',',','1',',','1','2','3',',','1','\n','3','4',',','1',',','1','5','9',',','1','\n','3','3',',','1',',','1','5','9',',','1','\n','2','6',',','1',',','1','7','5',',','1','\n','6','3',',','1',',','9','7',',','1','\n','6','2',',','1',',','1','0','0',',','1','\n','4','6',',','1',',','1','3','5',',','1','\n','4','4',',','1',',','1','3','6',',','1','\n','3','2',',','1',',','1','5','9',',','1','\n','2','7',',','1',',','1','7','1',',','1','\n','1','4',',','1',',','2','2','3',',','1','\n','5',',','1',',','2','8','3',',','1','\n','1',',','1',',','4','0','1',',','1','\n','4','5',',','1',',','1','3','5',',','1','\n','2','9',',','1',',','1','6','5',',','1','\n','3',',','1',',','3','2','6',',','1','\n','0',',','2',',','1','7',',','1',',','2','0','0',',','1','\n','3',',','1',',','3','2','5',',','1','\n','5','8',',','1',',','1','1','1',',','1',';','5','0',',','1',',','1','2','3',',','1','\n','5','0',',','1',',','1','2','3',',','1',';','2','1',',','1',',','1','8','3',',','1','\n','2','1',',','1',',','1','8','3',',','1',';','1','7',',','1',',','2','0','5',',','1','\n','1','7',',','1',',','2','0','5',',','1',';','4',',','1',',','2','9','6',',','1','\n','4',',','1',',','2','9','6',',','1',';','0',',','2',',','8',',','1',',','2','5','2',',','1','\n','7','1',',','1',',','8','7',',','1',';','5','8',',','1',',','1','1','0',',','1','\n','5','8',',','1',',','1','1','0',',','1',';','4','9',',','1',',','1','2','3',',','1','\n','4','9',',','1',',','1','2','3',',','1',';','4','1',',','1',',','1','4','5',',','1','\n','4','1',',','1',',','1','4','5',',','1',';','3','1',',','1',',','1','5','9',',','1','\n','3','1',',','1',',','1','5','9',',','1',';','2','1',',','1',',','1','8','2',',','1','\n','2','1',',','1',',','1','8','2',',','1',';','1','6',',','1',',','2','0','5',',','1','\n','1','6',',','1',',','2','0','5',',','1',';','1','2',',','1',',','2','3','6',',','1','\n','1','2',',','1',',','2','3','6',',','1',';','8',',','1',',','2','5','6',',','1','\n','8',',','1',',','2','5','6',',','1',';','4',',','1',',','2','9','5',',','1','\n','4',',','1',',','2','9','5',',','1',';','0',',','5',',','1','7',',','1',',','1','8','3',',','1','\n','6','9',',','1',',','9','9',',','1','\n','2',',','2',',','3','4','1',',','1','\n','2',',','1',',','3','9','9',',','1','\n','2',',','2',',','3','4','0',',','1','\n','7','0',',','1',',','9','6',',','1','\n','3','5',',','1',',','1','6','3',',','1','\n','1','8',',','1',',','2','0','4',',','1','\n','1','8',',','1',',','2','0','3',',','1','\n','2',',','1',',','3','9','7',',','1','\n','0',',','1',',','4','3','0',',','1','\n','3','4',',','1',',','1','6','3',',','1','\n','1','3',',','1',',','2','4','2',',','1','\n','2',',','1',',','3','9','5',',','1',';','2',',','1',',','3','9','3',',','1','\n','2',',','1',',','3','9','2',',','1','\n','2',',','1',',','3','9','4',',','1',';','2',',','1',',','3','9','3',',','1',';','0',',','1',',','4','2','9',',','1','\n','2',',','1',',','3','9','3',',','1',';','0',',','1',',','6','9',',','1',',','9','5',',','1','\n','6','8',',','1',',','9','9',',','1','\n','3','8',',','1',',','1','5','8',',','1','\n','3','3',',','1',',','1','6','3',',','1','\n','1','3',',','1',',','2','4','1',',','1','\n','8',',','1',',','2','7','3',',','1','\n','3',',','1',',','3','3','8',',','1','\n','2',',','1',',','3','9','1',',','1','\n','7',',','1',',','2','8','2',',','1',';','2',',','1',',','3','9','0',',','1','\n','2',',','1',',','3','9','0',',','1',';','2',',','1',',','6','9',',','1',',','8','2',',','1','\n','1',',','2',',','3','9','3',',','1',';','1',',','2',',','3','9','2',',','1','\n','1',',','2',',','3','9','2',',','1',';','0',',','2',',','3',',','1',',','6','8',',','1',',','6','9',',','1','\n','6','9',',','1',',','9','8',',','1','\n','6','7',',','1',',','9','9',',','1','\n','3','7',',','1',',','1','5','8',',','1','\n','3','2',',','1',',','1','6','3',',','1','\n','7','0',',','1',',','9','5',',','1',';','2','5',',','1',',','1','9','1',',','1','\n','1','3',',','1',',','2','4','0',',','1','\n','2','5',',','1',',','1','9','1',',','1',';','7',',','1',',','2','8','1',',','1','\n','3',',','1',',','3','3','7',',','1','\n','7',',','1',',','2','8','1',',','1',';','2',',','1',',','3','8','9',',','1','\n','2',',','1',',','3','8','8',',','1','\n','2',',','1',',','3','8','9',',','1',';','1',',','1',',','4','1','9',',','1','\n','1',',','1',',','4','1','9',',','1',';','0',',','1',',','2',',','1',',','3','7','3',',','1','\n','0',',','3',',','4','1','5',',','1','\n','5','4',',','1',',','1','2','2',',','1','\n','5','2',',','1',',','1','3','2',',','1','\n','2','6',',','1',',','1','8','1',',','1','\n','2','4',',','1',',','1','9','1',',','1',';','1','1',',','1',',','2','5','1',',','1','\n','8',',','1',',','2','7','2',',','1','\n','1','1',',','1',',','2','5','1',',','1',';','4',',','1',',','3','1','3',',','1','\n','4',',','1',',','3','1','3',',','1',';','2',',','1',',','3','8','7',',','1','\n','4',',','1',',','3','1','4',',','1',';','2',',','1',',','3','8','7',',','1',';','2',',','1',',','3','8','6',',','1','\n','2',',','1',',','3','8','7',',','1',';','2',',','1',',','1','8',',','1',',','1','8','9',',','1','\n','2',',','1',',','1','8',',','1',',','1','8','9',',','1',';','1',',','2',',','3','8','9',',','1','\n','1',',','2',',','3','8','9',',','1',';','1',',','2',',','3','8','8',',','1','\n','1',',','2',',','3','8','8',',','1',';','0',',','1',',','4','2','7',',','1','\n','2',',','1',',','3','8','6',',','1',';','0',',','1',',','4','2','7',',','1',';','0',',','2',',','4','1','9',',','1','\n','0',',','3',',','4','1','4',',','1','\n','5','4',',','1',',','1','2','1',',','1','\n','5','2',',','1',',','1','3','1',',','1','\n','5','1',',','1',',','1','3','2',',','1','\n','3','8',',','1',',','1','5','7',',','1','\n','3','6',',','1',',','1','5','8',',','1','\n','2','3',',','1',',','1','9','1',',','1',';','1','0',',','1',',','2','5','1',',','1','\n','8',',','1',',','2','7','1',',','1','\n','8',',','1',',','2','7','0',',','1','\n','1','3',',','1',',','2','3','9',',','1',';','1','0',',','1',',','2','5','1',',','1',';','4',',','1',',','3','1','2',',','1','\n','4',',','1',',','3','1','1',',','1','\n','1','0',',','1',',','2','5','1',',','1',';','4',',','1',',','3','1','2',',','1',';','2',',','1',',','1','8',',','1',',','1','8','8',',','1','\n','4',',','1',',','3','1','2',',','1',';','2',',','1',',','1','8',',','1',',','1','8','8',',','1',';','1',',','2',',','3','8','7',',','1','\n','1',',','2',',','3','8','7',',','1',';','0',',','1',',','4','2','6',',','1'] ['2',',','1',',','1','8',',','1',',','1','8','8',',','1',';','0',',','1',',','4','2','6',',','1',';','0',',','2',',','6','9',',','1',',','8','9',',','1'] ['0',',','1',',','4','2','6',',','1',';','0',',','4',',','3','9','1',',','1','\n','0',',','2',',','6','9',',','1',',','8','9',',','1',';','0',',','5',',','3','7','5',',','1','\n','7','2',',','1',',','9','4',',','1','\n','6','6',',','1',',','9','9',',','1','\n','5','4',',','1',',','1','2','0',',','1','\n','5','2',',','1',',','1','3','0',',','1','\n','5','1',',','1',',','1','3','1',',','1','\n','3','7',',','1',',','1','5','7',',','1','\n','2','2',',','1',',','1','9','1',',','1','\n','1','7',',','1',',','2','1','4',',','1','\n','8',',','1',',','2','6','9',',','1',';','7',',','1',',','2','8','0',',','1','\n','6',',','1',',','2','8','2',',','1','\n','7',',','1',',','2','8','0',',','1',';','1',',','1',',','4','1','8',',','1','\n','2','5',',','1',',','1','8','9',',','1',';','1',',','1',',','4','1','7',',','1','\n','0',',','1',',','9',',','1',',','2','5','1',',','1','\n','0',',','6',',','3','6','7',',','1','\n','7','2',',','1',',','9','3',',','1','\n','5','2',',','1',',','1','2','9',',','1','\n','5','2',',','1',',','1','2','8',',','1','\n','5','1',',','1',',','1','3','0',',','1','\n','4','8',',','1',',','1','3','4',',','1','\n','2','9',',','1',',','1','7','4',',','1','\n','7','2',',','1',',','9','2',',','1',';','2','5',',','1',',','1','8','8',',','1','\n','2','5',',','1',',','1','8','8',',','1',';','2','4',',','1',',','1','8','9',',','1','\n','2','2',',','1',',','1','9','0',',','1','\n','1','6',',','1',',','2','1','4',',','1','\n','1','4',',','1',',','2','3','1',',','1','\n','1','1',',','1',',','2','5','0',',','1','\n','2','4',',','1',',','1','8','9',',','1',';','7',',','1',',','2','7','9',',','1','\n','6',',','1',',','2','8','1',',','1','\n','2',',','1',',','3','8','5',',','1','\n','0',',','4',',','3','8','6',',','1','\n','7','2',',','1',',','9','1',',','1','\n','6','8',',','1',',','9','8',',','1','\n','5','1',',','1',',','1','2','9',',','1','\n','5','1',',','1',',','1','2','8',',','1','\n','4','8',',','1',',','1','3','3',',','1','\n','3','6',',','1',',','1','5','7',',','1','\n','3','1',',','1',',','1','6','3',',','1','\n','2','8',',','1',',','1','7','9',',','1','\n','2','5',',','1',',','1','8','7',',','1','\n','2','4',',','1',',','1','8','8',',','1',';','2','3',',','1',',','1','8','9',',','1','\n','1','7',',','1',',','2','1','3',',','1','\n','1','5',',','1',',','2','2','2',',','1','\n','1','4',',','1',',','2','3','0',',','1','\n','1','0',',','1',',','2','5','0',',','1','\n','2',',','1',',','3','8','4',',','1','\n','1',',','2',',','3','8','5',',','1',';','0',',','1',',','4','2','4',',','1','\n','0',',','1',',','4','2','3',',','1','\n','6','1',',','1',',','1','1','4',',','1','\n','3','8',',','1',',','1','5','6',',','1','\n','2','8',',','1',',','1','7','8',',','1','\n','2','4',',','1',',','1','8','7',',','1','\n','2','2',',','1',',','1','8','9',',','1','\n','2','0',',','1',',','2','0','2',',','1','\n','1','6',',','1',',','2','1','3',',','1','\n','1','1',',','1',',','2','4','9',',','1','\n','8',',','1',',','2','6','8',',','1','\n','6','7',',','1',',','9','8',',','1',';','0',',','2',',','7',',','1',',','2','6','7',',','1','\n','5','7',',','1',',','1','1','8',',','1','\n','4','6',',','1',',','1','3','9',',','1','\n','3','7',',','1',',','1','5','6',',','1']
    · rfl
    · rfl
    · decide
  · have hs : "2,1,18,1,188,1;0,1,426,1;0,2,69,1,89,1".splitOn ";"=["2,1,18,1,188,1","0,1,426,1","0,2,69,1,89,1"] := by
      simp +decide [String.splitOn,String.splitOnAux]
    have hm0 : (("2,1,18,1,188,1".splitOn ",").map (fun n=>n.toNat?.getD 0))=[2,1,18,1,188,1] := by
      have hx : "2,1,18,1,188,1".splitOn ","=["2","1","18","1","188","1"] := by simp +decide [String.splitOn,String.splitOnAux]
      rw [hx]
      simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
    have hm1 : (("0,1,426,1".splitOn ",").map (fun n=>n.toNat?.getD 0))=[0,1,426,1] := by
      have hx : "0,1,426,1".splitOn ","=["0","1","426","1"] := by simp +decide [String.splitOn,String.splitOnAux]
      rw [hx]
      simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
    have hm2 : (("0,2,69,1,89,1".splitOn ",").map (fun n=>n.toNat?.getD 0))=[0,2,69,1,89,1] := by
      have hx : "0,2,69,1,89,1".splitOn ","=["0","2","69","1","89","1"] := by simp +decide [String.splitOn,String.splitOnAux]
      rw [hx]
      simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
    change _ = (("2,1,18,1,188,1;0,1,426,1;0,2,69,1,89,1".splitOn ";").map _).sum
    rw [hs]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
    change _ = (if "2,1,18,1,188,1"="" then 1 else _) + ((if "0,1,426,1"="" then 1 else _) + ((if "0,2,69,1,89,1"="" then 1 else _) + (0)))
    simp only [if_neg (by decide : "2,1,18,1,188,1"≠""),if_neg (by decide : "0,1,426,1"≠""),if_neg (by decide : "0,2,69,1,89,1"≠"")]
    rw [hm0,hm1,hm2]
    change _ = ((MvPolynomial.X (atomIndex .h2))^1 * ((MvPolynomial.X (atomIndex .h5))^1 * ((MvPolynomial.X (atomIndex .x_91_11))^1 * ((1 : MvPolynomial (Fin generators.count) (ZMod 2)))))) + (((MvPolynomial.X (atomIndex .h0))^1 * ((MvPolynomial.X (⟨426,by decide⟩ : Fin generators.count))^1 * ((1 : MvPolynomial (Fin generators.count) (ZMod 2))))) + (((MvPolynomial.X (atomIndex .h0))^2 * ((MvPolynomial.X (atomIndex .h6))^1 * ((MvPolynomial.X (⟨89,by decide⟩ : Fin generators.count))^1 * ((1 : MvPolynomial (Fin generators.count) (ZMod 2)))))) + ((0 : MvPolynomial (Fin generators.count) (ZMod 2)))))
    ring

private theorem nativeCoreB2 :
    (sourceAtom .h0).val * (Ideal.Quotient.mk _ (MvPolynomial.X (⟨426,by decide⟩ : Fin generators.count))) + (sourceAtom .h0).val^4 * (sourceAtom .x_125_9_2).val = 0 := by
  change Ideal.Quotient.mk _ ((MvPolynomial.X (atomIndex .h0) : MvPolynomial (Fin generators.count) (ZMod 2)) * MvPolynomial.X (⟨426,by decide⟩ : Fin generators.count) + MvPolynomial.X (atomIndex .h0)^4 * MvPolynomial.X (atomIndex .x_125_9_2)) = 0
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply Ideal.subset_span
  refine ⟨"0,1,426,1;0,4,391,1",?_,?_⟩
  · apply nativeCoreFromChunk (i := ⟨9,by decide⟩)
    apply nativeCoreMiddleMember _ "0,1,426,1;0,4,391,1" ['2','4',',','1',',','1','7','4',',','1','\n','1','2',',','1',',','2','3','1',',','1','\n','1','0',',','1',',','2','3','5',',','1','\n','4','8',',','1',',','1','2','2',',','1',';','7',',','1',',','2','6','1',',','1','\n','7',',','1',',','2','6','1',',','1',';','1',',','2',',','3','5','1',',','1','\n','9',',','1',',','2','3','9',',','1',';','0',',','1',',','1','8',',','1',',','1','8','8',',','1','\n','0',',','1',',','1','8',',','1',',','1','8','8',',','1',';','0',',','2',',','3','7','1',',','1','\n','0',',','2',',','3','7','1',',','1',';','0',',','2',',','6','9',',','1',',','7','9',',','1','\n','6','4',',','1',',','9','4',',','1','\n','4','8',',','1',',','1','2','1',',','1','\n','4','6',',','1',',','1','3','1',',','1','\n','4','5',',','1',',','1','3','2',',','1','\n','2','3',',','1',',','1','7','4',',','1','\n','2','0',',','1',',','1','9','1',',','1','\n','1','2',',','1',',','2','3','0',',','1','\n','0',',','3',',','3','6','5',',','1','\n','6','4',',','1',',','9','3',',','1','\n','6','4',',','1',',','9','2',',','1','\n','4','8',',','1',',','1','2','0',',','1','\n','4','6',',','1',',','1','3','0',',','1','\n','4','5',',','1',',','1','3','1',',','1','\n','2','2',',','1',',','1','7','4',',','1','\n','2','0',',','1',',','1','9','0',',','1','\n','1','9',',','1',',','1','9','1',',','1','\n','6',',','1',',','2','6','3',',','1','\n','2',',','1',',','1','3',',','1',',','2','0','9',',','1','\n','1',',','1',',','3','7','0',',','1','\n','0',',','1',',','3','8','5',',','1','\n','0',',','3',',','3','6','3',',','1','\n','6','4',',','1',',','9','1',',','1','\n','6','1',',','1',',','1','0','1',',','1','\n','5','7',',','1',',','1','1','4',',','1','\n','5','4',',','1',',','1','1','5',',','1','\n','4','6',',','1',',','1','2','9',',','1','\n','4','6',',','1',',','1','2','8',',','1','\n','4','5',',','1',',','1','3','0',',','1','\n','3','5',',','1',',','1','5','5',',','1','\n','2','8',',','1',',','1','6','4',',','1','\n','2','6',',','1',',','1','7','0',',','1','\n','1','9',',','1',',','1','9','0',',','1','\n','1','1',',','1',',','2','3','4',',','1','\n','6',',','1',',','2','6','2',',','1','\n','2',',','1',',','3','5','0',',','1','\n','2',',','1',',','3','4','9',',','1','\n','0',',','1',',','3','8','4',',','1','\n','0',',','2',',','3','7','0',',','1','\n','6','3',',','1',',','9','4',',','1','\n','4','5',',','1',',','1','2','9',',','1','\n','4','5',',','1',',','1','2','8',',','1','\n','3','4',',','1',',','1','5','5',',','1','\n','2','6',',','1',',','1','6','9',',','1','\n','2','0',',','1',',','1','8','9',',','1','\n','1','7',',','1',',','2','0','2',',','1','\n','1','4',',','1',',','2','1','6',',','1','\n','1','0',',','1',',','2','3','4',',','1','\n','6',',','1',',','2','6','1',',','1','\n','2',',','1',',','3','4','8',',','1','\n','5',',','1',',','2','7','5',',','1',';','1',',','1',',','3','6','9',',','1','\n','1',',','2',',','3','4','9',',','1','\n','0',',','1',',','8',',','1',',','2','5','0',',','1','\n','6','3',',','1',',','9','3',',','1','\n','6','3',',','1',',','9','2',',','1','\n','5','7',',','1',',','1','1','3',',','1','\n','4','2',',','1',',','1','3','9',',','1','\n','4','1',',','1',',','1','4','3',',','1','\n','3','3',',','1',',','1','5','5',',','1','\n','2','6',',','1',',','1','6','8',',','1','\n','1','9',',','1',',','1','8','9',',','1','\n','1','6',',','1',',','2','0','2',',','1','\n','1','2',',','1',',','2','2','9',',','1','\n','0',',','1',',','3','8','3',',','1','\n','0',',','8',',','3','1','2',',','1','\n','6','3',',','1',',','9','1',',','1','\n','5','7',',','1',',','1','1','2',',','1','\n','4','1',',','1',',','1','4','2',',','1','\n','3','2',',','1',',','1','5','5',',','1','\n','2','6',',','1',',','1','6','7',',','1','\n','2','5',',','1',',','1','7','3',',','1','\n','2','5',',','1',',','1','7','2',',','1','\n','7','2',',','1',',','8','0',',','1',';','2','0',',','1',',','1','8','7',',','1','\n','2','0',',','1',',','1','8','7',',','1',';','1','7',',','1',',','2','0','1',',','1','\n','1','9',',','1',',','1','8','8',',','1',';','1','7',',','1',',','2','0','1',',','1',';','1','5',',','1',',','2','0','9',',','1','\n','1','7',',','1',',','2','0','1',',','1',';','1','5',',','1',',','2','0','9',',','1',';','8',',','1',',','2','5','5',',','1','\n','1','5',',','1',',','2','0','9',',','1',';','2',',','1',',','3','4','7',',','1','\n','1','3',',','1',',','2','2','6',',','1',';','2',',','1',',','3','4','6',',','1','\n','7',',','1',',','2','6','0',',','1',';','2',',','1',',','3','4','7',',','1',';','2',',','1',',','3','4','6',',','1',';','0',',','1',',','3','8','2',',','1','\n','2',',','1',',','3','4','7',',','1',';','0',',','1',',','3','8','2',',','1',';','0',',','3',',','3','5','9',',','1','\n','0',',','1',',','3','8','2',',','1',';','0',',','3',',','3','5','9',',','1',';','0',',','4',',','3','4','9',',','1','\n','7','2',',','1',',','7','9',',','1',';','6','4',',','1',',','8','9',',','1',';','4','8',',','1',',','1','1','9',',','1','\n','3','5',',','1',',','1','5','4',',','1','\n','2','6',',','1',',','1','6','6',',','1','\n','2','4',',','1',',','1','7','3',',','1','\n','2','4',',','1',',','1','7','2',',','1','\n','6','4',',','1',',','8','9',',','1',';','1','9',',','1',',','1','8','7',',','1','\n','4','8',',','1',',','1','1','9',',','1',';','1','9',',','1',',','1','8','7',',','1',';','1','6',',','1',',','2','0','1',',','1','\n','1','6',',','1',',','2','0','1',',','1',';','8',',','1',',','2','5','4',',','1','\n','1','9',',','1',',','1','8','7',',','1',';','8',',','1',',','2','5','4',',','1',';','1',',','2',',','3','4','7',',','1','\n','0',',','1',',','3','8','1',',','1','\n','6','4',',','1',',','9','0',',','1',';','8',',','1',',','2','5','4',',','1',';','1',',','2',',','3','4','7',',','1',';','0',',','3',',','3','5','8',',','1','\n','5','2',',','1',',','1','1','8',',','1','\n','4','3',',','1',',','1','3','8',',','1',';','3','4',',','1',',','1','5','4',',','1','\n','3','4',',','1',',','1','5','4',',','1',';','2','3',',','1',',','1','7','2',',','1','\n','2','1',',','1',',','1','7','9',',','1','\n','1','2',',','1',',','2','2','8',',','1','\n','1','1',',','1',',','2','3','3',',','1','\n','2','3',',','1',',','1','7','3',',','1',';','2','3',',','1',',','1','7','2',',','1',';','8',',','1',',','1','3',',','2',',','8','0',',','1','\n','2','3',',','1',',','1','7','2',',','1',';','0',',','3',',','3','5','5',',','1','\n','0',',','3',',','3','5','5',',','1',';','0',',','3',',','1','7',',','1',',','1','8','8',',','1','\n','5','1',',','1',',','1','1','8',',','1',';','4','6',',','1',',','1','2','7',',','1','\n','4','6',',','1',',','1','2','6',',','1','\n','3','3',',','1',',','1','5','4',',','1','\n','4','6',',','1',',','1','2','7',',','1',';','2','2',',','1',',','1','7','3',',','1','\n','2','2',',','1',',','1','7','2',',','1','\n','2','1',',','1',',','1','7','8',',','1','\n','2','2',',','1',',','1','7','3',',','1',';','2','0',',','1',',','1','8','6',',','1','\n','1','1',',','1',',','2','3','2',',','1','\n','1','0',',','1',',','2','3','3',',','1','\n','2','0',',','1',',','1','8','6',',','1',';','8',',','2',',','1','3',',','1',',','1','0','1',',','1','\n','7',',','1',',','2','5','9',',','1','\n','4','3',',','1',',','1','3','7',',','1',';','0',',','4',',','3','4','7',',','1','\n','6','3',',','1',',','9','0',',','1',';','6','3',',','1',',','8','9',',','1','\n','6','1',',','1',',','1','0','0',',','1','\n','6','3',',','1',',','8','9',',','1',';','6','0',',','1',',','1','0','1',',','1','\n','5','9',',','1',',','1','0','1',',','1','\n','6','0',',','1',',','1','0','1',',','1',';','4','5',',','1',',','1','2','7',',','1','\n','4','5',',','1',',','1','2','6',',','1','\n','4','5',',','1',',','1','2','7',',','1',';','3','2',',','1',',','1','5','4',',','1','\n','3','2',',','1',',','1','5','4',',','1',';','2','9',',','1',',','1','6','2',',','1','\n','2','7',',','1',',','1','6','4',',','1','\n','2','1',',','1',',','1','7','7',',','1','\n','2','9',',','1',',','1','6','2',',','1',';','1','9',',','1',',','1','8','6',',','1','\n','1','0',',','1',',','2','3','2',',','1','\n','1','9',',','1',',','1','8','6',',','1',';','8',',','2',',','1','7','3',',','1','\n','7',',','1',',','2','5','8',',','1','\n','6',',','1',',','2','6','0',',','1',';','0',',','1',',','3','8','0',',','1','\n','6','9',',','1',',','8','7',',','1','\n','3','1',',','1',',','1','5','5',',','1','\n','5',',','1',',','2','7','4',',','1','\n','1','4',',','1',',','2','1','5',',','1',';','1',',','1',',','5',',','1',',','2','6','0',',','1','\n','6','2',',','1',',','9','6',',','1','\n','4','4',',','1',',','1','3','4',',','1','\n','4','3',',','1',',','1','3','6',',','1','\n','4','1',',','1',',','1','4','1',',','1','\n','2','1',',','1',',','1','7','6',',','1','\n','7',',','1',',','2','5','7',',','1',';','0',',','7',',','3','1','7',',','1','\n','5','6',',','1',',','1','1','4',',','1','\n','4','4',',','1',',','1','3','3',',','1','\n','1','5',',','1',',','2','0','8',',','1','\n','4','2',',','1',',','1','3','8',',','1',';','8',',','4',',','6','4',',','1','\n','6',',','1',',','2','5','9',',','1','\n','2',',','1',',','3','4','5',',','1','\n','5','8',',','1',',','1','0','7',',','1','\n','5','5',',','1',',','1','1','4',',','1','\n','6','4',',','1',',','8','8',',','1',';','4','2',',','1',',','1','3','7',',','1','\n','1','5',',','1',',','2','0','7',',','1','\n','6',',','1',',','2','5','8',',','1','\n','2',',','1',',','3','4','4',',','1','\n','0',',','1',',','8',',','1',',','2','4','5',',','1','\n','6','2',',','1',',','9','5',',','1','\n','5','8',',','1',',','1','0','6',',','1','\n','5','8',',','1',',','1','0','5',',','1','\n','5','7',',','1',',','1','1','1',',','1','\n','5','6',',','1',',','1','1','3',',','1',';','5','0',',','1',',','1','1','8',',','1','\n','5','0',',','1',',','1','1','8',',','1',';','4','0',',','1',',','1','4','7',',','1','\n','4','0',',','1',',','1','4','7',',','1',';','3','1',',','1',',','1','5','4',',','1','\n','3','1',',','1',',','1','5','4',',','1',';','2','0',',','1',',','1','8','5',',','1','\n','2','0',',','1',',','1','8','5',',','1',';','8',',','1',',','1','7',',','1',',','1','3','8',',','1','\n','0',',','9',',','2','9','9',',','1','\n','7','2',',','1',',','7','8',',','1',';','7','1',',','1',',','8','0',',','1','\n','6','8',',','1',',','8','7',',','1','\n','5','8',',','1',',','1','0','4',',','1','\n','5','8',',','1',',','1','0','3',',','1','\n','5','7',',','1',',','1','1','0',',','1','\n','7','1',',','1',',','8','0',',','1',';','5','6',',','1',',','1','1','2',',','1','\n','5','5',',','1',',','1','1','3',',','1',';','4','9',',','1',',','1','1','8',',','1','\n','4','7',',','1',',','1','2','4',',','1','\n','5','6',',','1',',','1','1','2',',','1',';','4','0',',','1',',','1','4','6',',','1','\n','4','9',',','1',',','1','1','8',',','1',';','3','9',',','1',',','1','4','7',',','1','\n','4','0',',','1',',','1','4','6',',','1',';','3','9',',','1',',','1','4','7',',','1',';','3','0',',','1',',','1','6','0',',','1','\n','2','5',',','1',',','1','7','1',',','1','\n','3','9',',','1',',','1','4','7',',','1',';','3','0',',','1',',','1','6','0',',','1',';','2','0',',','1',',','1','8','4',',','1','\n','3','0',',','1',',','1','6','0',',','1',';','2','0',',','1',',','1','8','4',',','1',';','1','9',',','1',',','1','8','5',',','1','\n','2','0',',','1',',','1','8','4',',','1',';','1','9',',','1',',','1','8','5',',','1',';','1','5',',','1',',','2','0','6',',','1','\n','1','9',',','1',',','1','8','5',',','1',';','1','3',',','1',',','2','2','5',',','1','\n','1','3',',','1',',','2','2','5',',','1',';','9',',','1',',','2','3','8',',','1','\n','9',',','1',',','2','3','8',',','1',';','8',',','1',',','1','6',',','1',',','1','3','8',',','1','\n','1','5',',','1',',','2','0','6',',','1',';','6',',','1',',','2','5','7',',','1','\n','6',',','1',',','2','5','7',',','1',';','2',',','1',',','3','4','3',',','1','\n','2',',','1',',','3','4','3',',','1',';','0',',','1',',','8',',','1',',','2','4','4',',','1','\n','7','2',',','1',',','7','7',',','1',';','7','1',',','1',',','7','9',',','1','\n','6','7',',','1',',','8','7',',','1','\n','6','3',',','1',',','8','8',',','1',';','6','0',',','1',',','1','0','0',',','1','\n','5','9',',','1',',','1','0','0',',','1','\n','7','1',',','1',',','7','9',',','1',';','5','5',',','1',',','1','1','2',',','1','\n','6','0',',','1',',','1','0','0',',','1',';','4','6',',','1',',','1','2','5',',','1','\n','4','6',',','1',',','1','2','5',',','1',';','4','2',',','1',',','1','3','6',',','1','\n','5','5',',','1',',','1','1','2',',','1',';','3','9',',','1',',','1','4','6',',','1','\n','2','4',',','1',',','1','7','1',',','1','\n','3','9',',','1',',','1','4','6',',','1',';','1','9',',','1',',','1','8','4',',','1','\n','1','9',',','1',',','1','8','4',',','1',';','1','3',',','1',',','2','2','4',',','1','\n','1','3',',','1',',','2','2','4',',','1',';','9',',','1',',','2','3','7',',','1','\n','9',',','1',',','2','3','7',',','1',';','8',',','1',',','1','6',',','1',',','1','3','7',',','1','\n','4','2',',','1',',','1','3','6',',','1',';','8',',','4',',','1','7',',','1',',','2','0',',','1','\n','5','2',',','1',',','1','1','7',',','1','\n','3','5',',','1',',','1','5','3',',','1','\n','4','5',',','1',',','1','2','5',',','1',';','2','3',',','1',',','1','7','1',',','1','\n','2','3',',','1',',','1','7','1',',','1',';','8',',','5',',','4','0',',','1','\n','5','2',',','1',',','1','1','6',',','1','\n','3','5',',','1',',','1','5','2',',','1','\n','3','4',',','1',',','1','5','3',',','1','\n','5','1',',','1',',','1','1','7',',','1',';','2','9',',','1',',','1','6','1',',','1','\n','2','9',',','1',',','1','6','1',',','1',';','2','2',',','1',',','1','7','1',',','1','\n','2','2',',','1',',','1','7','1',',','1',';','8',',','5',',','3','9',',','1','\n','0',',','4',',','3','4','3',',','1','\n','6','6',',','1',',','8','7',',','1','\n','3','4',',','1',',','1','5','2',',','1','\n','3','3',',','1',',','1','5','3',',','1','\n','5','1',',','1',',','1','1','6',',','1',';','1','3',',','1',',','2','2','3',',','1','\n','1','3',',','1',',','2','2','3',',','1',';','8',',','2',',','1','7','1',',','1','\n','3','3',',','1',',','1','5','2',',','1','\n','3','2',',','1',',','1','5','3',',','1',';','8',',','2',',','1','7',',','1',',','7','8',',','1','\n','3','2',',','1',',','1','5','2',',','1',';','8',',','3',',','1','1','7',',','1','\n','2','6',',','1',',','1','6','5',',','1','\n','5','6',',','1',',','1','1','1',',','1',';','5','0',',','1',',','1','1','7',',','1','\n','5','0',',','1',',','1','1','7',',','1',';','2','0',',','1',',','1','8','3',',','1','\n','2','0',',','1',',','1','8','3',',','1',';','1','7',',','1',',','2','0','0',',','1','\n','7','1',',','1',',','7','8',',','1',';','5','6',',','1',',','1','1','0',',','1','\n','5','6',',','1',',','1','1','0',',','1',';','5','5',',','1',',','1','1','1',',','1','\n','5','5',',','1',',','1','1','1',',','1',';','5','0',',','1',',','1','1','6',',','1','\n','5','0',',','1',',','1','1','6',',','1',';','4','9',',','1',',','1','1','7',',','1','\n','4','9',',','1',',','1','1','7',',','1',';','4','0',',','1',',','1','4','5',',','1','\n','4','0',',','1',',','1','4','5',',','1',';','3','1',',','1',',','1','5','3',',','1','\n','3','1',',','1',',','1','5','3',',','1',';','2','0',',','1',',','1','8','2',',','1','\n','2','0',',','1',',','1','8','2',',','1',';','1','9',',','1',',','1','8','3',',','1','\n','1','9',',','1',',','1','8','3',',','1',';','1','7',',','1',',','1','9','9',',','1','\n','1','7',',','1',',','1','9','9',',','1',';','1','6',',','1',',','2','0','0',',','1','\n','1','6',',','1',',','2','0','0',',','1',';','8',',','1',',','2','5','3',',','1','\n','7','1',',','1',',','7','7',',','1',';','5','5',',','1',',','1','1','0',',','1','\n','5','5',',','1',',','1','1','0',',','1',';','4','9',',','1',',','1','1','6',',','1','\n','4','9',',','1',',','1','1','6',',','1',';','3','9',',','1',',','1','4','5',',','1','\n','3','9',',','1',',','1','4','5',',','1',';','3','1',',','1',',','1','5','2',',','1','\n','3','1',',','1',',','1','5','2',',','1',';','1','9',',','1',',','1','8','2',',','1','\n','1','9',',','1',',','1','8','2',',','1',';','1','6',',','1',',','1','9','9',',','1','\n','1','6',',','1',',','1','9','9',',','1',';','9',',','1',',','2','3','6',',','1','\n','9',',','1',',','2','3','6',',','1',';','8',',','1',',','2','5','2',',','1','\n','7',',','1',',','2','5','6',',','1','\n','6','5',',','1',',','8','7',',','1','\n','5','8',',','1',',','1','0','2',',','1','\n','4','7',',','1',',','1','2','3',',','1','\n','4','1',',','1',',','1','4','0',',','1','\n','3','0',',','1',',','1','5','9',',','1','\n','2','1',',','1',',','1','7','5',',','1','\n','1','5',',','1',',','2','0','5',',','1','\n','1','2',',','1',',','2','2','7',',','1','\n','6',',','1',',','2','5','6',',','1','\n','4',',','1',',','2','9','0',',','1','\n','2',',','1',',','3','4','2',',','1','\n','1',',','2',',','3','4','2',',','1','\n','0',',','1',',','3','7','9',',','1','\n','6','9',',','1',',','9','4',',','1','\n','6','9',',','1',',','9','2',',','1','\n','1',',','1',',','4','0','0',',','1','\n','6','9',',','1',',','9','1',',','1','\n','4','3',',','1',',','1','4','3',',','1','\n','7',',','1',',','2','7','3',',','1','\n','1',',','1',',','3','9','9',',','1','\n','1',',','1',',','3','9','8',',','1','\n','4','3',',','1',',','1','4','2',',','1','\n','1','1',',','1',',','2','4','2',',','1','\n','3',',','1',',','3','2','3',',','1','\n','1','8',',','1',',','1','9','8',',','1',';','3',',','1',',','6','8',',','1',',','6','9',',','1','\n','1',',','1',',','3','9','7',',','1','\n','1',',','1',',','3','9','6',',','1','\n','1',',','2',',','3','6','8',',','1','\n','0',',','2',',','3','9','8',',','1','\n','0',',','3',',','3','7','8',',','1','\n','1','1',',','1',',','2','4','1',',','1','\n','1','0',',','1',',','2','4','2',',','1','\n','7',',','1',',','2','7','2',',','1','\n','1','8',',','1',',','1','9','7',',','1',';','3',',','1',',','6','7',',','1',',','6','9',',','1','\n','1',',','1',',','3','9','5',',','1',';','1',',','1',',','3','9','4',',','1','\n','3',',','1',',','6','7',',','1',',','6','9',',','1',';','1',',','1',',','3','9','2',',','1','\n','2',',','1',',','3','6','7',',','1',';','1',',','1',',','3','9','4',',','1',';','1',',','1',',','3','9','3',',','1',';','0',',','1',',','4','1','5',',','1','\n','0',',','2',',','3','9','7',',','1','\n','1',',','1',',','3','9','4',',','1',';','1',',','1',',','3','9','2',',','1',';','0',',','2',',','3','9','6',',','1','\n','0',',','3',',','3','7','7',',','1','\n','1','3',',','1',',','2','3','1',',','1','\n','1','1',',','1',',','2','4','0',',','1','\n','1','0',',','1',',','2','4','1',',','1','\n','7',',','1',',','2','7','1',',','1','\n','7',',','1',',','2','7','0',',','1','\n','6','8',',','1',',','9','4',',','1',';','1',',','1',',','3','9','1',',','1','\n','3',',','1',',','3','2','2',',','1',';','1',',','1',',','3','9','1',',','1',';','1',',','1',',','3','9','0',',','1','\n','1',',','1',',','3','9','1',',','1',';','1',',','1',',','3','9','0',',','1',';','1',',','1',',','6','9',',','1',',','8','2',',','1','\n','1',',','1',',','6','9',',','1',',','8','2',',','1',';','1',',','1',',','1','8',',','1',',','1','9','0',',','1','\n','2',',','1',',','3','6','6',',','1',';','0',',','1',',','4','1','4',',','1','\n','1',',','1',',','3','9','0',',','1',';','1',',','1',',','1','8',',','1',',','1','9','0',',','1',';','0',',','2',',','3','9','4',',','1','\n','1',',','1',',','1','8',',','1',',','1','9','0',',','1',';','0',',','2',',','3','9','2',',','1','\n','6','9',',','1',',','9','0',',','1',';','6','9',',','1',',','8','9',',','1','\n','6','8',',','1',',','9','3',',','1','\n','6','7',',','1',',','9','4',',','1','\n','3','5',',','1',',','1','5','8',',','1','\n','1','8',',','1',',','1','9','6',',','1','\n','1','3',',','1',',','2','3','0',',','1','\n','1','0',',','1',',','2','4','0',',','1','\n','6',',','1',',','2','7','3',',','1','\n','3',',','2',',','2','7','0',',','1','\n','3',',','1',',','3','2','1',',','1',';','1',',','1',',','3','8','9',',','1','\n','7',',','1',',','2','6','9',',','1',';','1',',','1',',','3','8','8',',','1','\n','1',',','2',',','3','6','6',',','1','\n','6','8',',','1',',','9','2',',','1',';','1',',','1',',','3','8','9',',','1',';','1',',','1',',','3','8','8',',','1',';','0',',','1',',','4','1','3',',','1','\n','0',',','1',',','4','1','2',',','1','\n','0',',','1',',','4','1','3',',','1',';','0',',','2',',','3','9','1',',','1','\n','0',',','2',',','3','9','0',',','1','\n','6','8',',','1',',','9','1',',','1',';','6','7',',','1',',','9','3',',','1','\n','4','2',',','1',',','1','4','3',',','1','\n','3','4',',','1',',','1','5','8',',','1','\n','6','7',',','1',',','9','3',',','1',';','2','6',',','1',',','1','7','4',',','1','\n','2','3',',','1',',','2','4',',','1',',','6','9',',','1','\n','1','1',',','1',',','2','3','9',',','1','\n','2','6',',','1',',','1','7','4',',','1',';','2',',','1',',','3','6','5',',','1','\n','6','7',',','1',',','9','2',',','1',';','2',',','1',',','3','6','5',',','1',';','1',',','1',',','3','8','7',',','1','\n','3',',','1',',','3','2','0',',','1',';','1',',','1',',','3','8','6',',','1','\n','1',',','1',',','1','8',',','1',',','1','8','9',',','1','\n','0',',','1',',','4','1','1',',','1','\n','2',',','1',',','3','6','5',',','1',';','0',',','1',',','4','1','0',',','1','\n','1',',','1',',','3','8','6',',','1',';','0',',','2',',','3','8','9',',','1',';','0',',','4',',','3','6','7',',','1','\n','4','2',',','1',',','1','4','2',',','1','\n','3','3',',','1',',','1','5','8',',','1','\n','6','7',',','1',',','9','1',',','1',';','1','8',',','1',',','1','9','5',',','1','\n','1','0',',','1',',','2','3','9',',','1','\n','6',',','1',',','2','7','2',',','1','\n','1','8',',','1',',','1','9','5',',','1',';','3',',','1',',','6','8',',','2','\n','2',',','1',',','3','6','4',',','1','\n','3',',','1',',','6','8',',','2',';','2',',','1',',','3','6','3',',','1','\n','0',',','1',',','4','0','8',',','1','\n','2',',','1',',','3','6','3',',','1',';','0',',','2',',','3','8','6',',','1','\n','0',',','3',',','6','9',',','1',',','8','0',',','1','\n','7','6',',','1',',','8','0',',','1','\n','6','6',',','1',',','9','4',',','1','\n','6','4',',','1',',','9','6',',','1','\n','6','1',',','1',',','1','0','7',',','1','\n','5','2',',','1',',','1','2','2',',','1','\n','4','3',',','1',',','1','4','1',',','1','\n','3','5',',','1',',','1','5','7',',','1','\n','3','2',',','1',',','1','5','8',',','1','\n','2','5',',','1',',','1','7','9',',','1','\n','1','7',',','1',',','2','0','4',',','1','\n','1','7',',','1',',','2','0','3',',','1','\n','7',',','1',',','2','6','8',',','1','\n','6',',','1',',','2','7','1',',','1','\n','6',',','1',',','2','7','0',',','1','\n','5',',','1',',','2','8','2',',','1','\n','3',',','1',',','3','1','9',',','1','\n','3',',','1',',','6','7',',','1',',','6','8',',','1',';','0',',','1',',','4','0','7',',','1','\n','7','6',',','1',',','7','9',',','1','\n','7','5',',','1',',','8','0',',','1','\n','7','4',',','1',',','8','0',',','1','\n','6','6',',','1',',','9','3',',','1','\n','6','6',',','1',',','9','2',',','1','\n','6','1',',','1',',','1','0','6',',','1','\n','6','1',',','1',',','1','0','5',',','1','\n','5','7',',','1',',','1','1','5',',','1','\n','5','2',',','1',',','1','2','1',',','1','\n','5','1',',','1',',','1','2','2',',','1','\n','3','8',',','1',',','1','5','1',',','1','\n','3','4',',','1',',','1','5','7',',','1','\n','2','5',',','1',',','1','7','8',',','1','\n','2','4',',','1',',','1','7','9',',','1','\n','1','6',',','1',',','2','0','4',',','1','\n','1','6',',','1',',','2','0','3',',','1','\n','1','3',',','1',',','2','2','9',',','1','\n','6',',','1',',','2','6','9',',','1','\n','5',',','1',',','2','8','1',',','1','\n','3',',','1',',','6','7',',','2','\n','2',',','1',',','3','6','2',',','1','\n','2',',','1',',','3','6','1',',','1','\n','0',',','1',',','4','0','6',',','1','\n','7','5',',','1',',','7','9',',','1','\n','7','4',',','1',',','7','9',',','1','\n','7','3',',','1',',','8','0',',','1','\n','7','2',',','1',',','8','6',',','1','\n','6','8',',','1',',','8','9',',','1','\n','6','6',',','1',',','9','1',',','1','\n','6','1',',','1',',','1','0','4',',','1','\n','6','1',',','1',',','1','0','3',',','1','\n','5','2',',','1',',','1','2','0',',','1','\n','5','1',',','1',',','1','2','1',',','1','\n','3','8',',','1',',','1','5','0',',','1','\n','3','7',',','1',',','1','5','1',',','1','\n','3','3',',','1',',','1','5','7',',','1','\n','2','5',',','1',',','1','7','7',',','1','\n','2','4',',','1',',','1','7','8',',','1','\n','2','3',',','1',',','1','7','9',',','1','\n','1','5',',','1',',','2','1','4',',','1','\n','1','4',',','1',',','2','2','2',',','1','\n','1','2',',','1',',','2','3','5',',','1','\n','9',',','1',',','2','4','3',',','1','\n','4',',','1',',','2','9','4',',','1','\n','6','8',',','1',',','9','0',',','1',';','3',',','2',',','2','6','7',',','1','\n','2',',','1',',','3','6','0',',','1','\n','1',',','1',',','3','8','4',',','1','\n','1',',','2',',','3','6','1',',','1','\n','7','3',',','1',',','7','9',',','1','\n','7','2',',','1',',','8','5',',','1','\n','7','2',',','1',',','8','4',',','1','\n','6','7',',','1',',','8','9',',','1','\n','6','4',',','1',',','9','5',',','1','\n','6','3',',','1',',','9','6',',','1','\n','5','1',',','1',',','1','2','0',',','1','\n','4','6',',','1',',','1','3','4',',','1','\n','4','0',',','1',',','1','4','8',',','1','\n','3','7',',','1',',','1','5','0',',','1','\n','3','2',',','1',',','1','5','7',',','1','\n','3','0',',','1',',','1','6','3',',','1','\n','2','9',',','1',',','1','6','4',',','1','\n','2','4',',','1',',','1','7','7',',','1','\n','2','3',',','1',',','1','7','8',',','1','\n','2','2',',','1',',','1','7','9',',','1','\n','2','0',',','1',',','1','9','2',',','1','\n','1','8',',','1',',','1','9','4',',','1','\n','3',',','1',',','3','1','8',',','1','\n','6','7',',','1',',','9','0',',','1',';','3',',','2',',','2','6','6',',','1','\n','3',',','2',',','2','6','6',',','1',';','2',',','1',',','3','5','9',',','1','\n','2',',','1',',','1','3',',','1',',','2','1','2',',','1','\n','1',',','1',',','8',',','1',',','2','5','0',',','1','\n','1',',','2',',','3','6','0',',','1','\n','7','2',',','1',',','8','3',',','1','\n','4','5',',','1',',','1','3','4',',','1','\n','3','9',',','1',',','1','4','8',',','1','\n','7','2',',','1',',','8','2',',','1',';','3','6',',','1',',','1','5','1',',','1','\n','3','6',',','1',',','1','5','1',',','1',';','3','5',',','1',',','1','5','6',',','1','\n','3','5',',','1',',','1','5','6',',','1',';','2','8',',','1',',','1','7','0',',','1','\n','2','8',',','1',',','1','7','0',',','1',';','2','5',',','1',',','1','7','6',',','1','\n','2','3',',','1',',','1','7','7',',','1','\n','2','2',',','1',',','1','7','8',',','1','\n','1','9',',','1',',','1','9','2',',','1','\n','6','9',',','1',',','8','8',',','1',';','1','8',',','1',',','1','9','3',',','1','\n','1','5',',','1',',','2','1','3',',','1','\n','2','5',',','1',',','1','7','6',',','1',';','1','3',',','1',',','2','2','8',',','1','\n','4','6',',','1',',','1','3','3',',','1',';','9',',','1',',','1','3',',','2',',','7','5',',','1','\n','6',',','1',',','2','6','8',',','1','\n','1','8',',','1',',','1','9','3',',','1',';','5',',','1',',','2','8','0',',','1','\n','5',',','1',',','2','8','0',',','1',';','4',',','1',',','2','9','3',',','1','\n','2',',','1',',','3','5','8',',','1','\n','1','3',',','1',',','2','2','8',',','1',';','2',',','1',',','3','5','7',',','1','\n','4',',','1',',','2','9','3',',','1',';','1',',','1',',','3','8','3',',','1','\n','2',',','1',',','3','5','7',',','1',';','1',',','2',',','3','5','9',',','1','\n','7','2',',','1',',','8','1',',','1','\n','4','8',',','1',',','1','2','4',',','1','\n','4','5',',','1',',','1','3','3',',','1','\n','4','2',',','1',',','1','4','1',',','1','\n','3','8',',','1',',','1','4','9',',','1','\n','3','6',',','1',',','1','5','0',',','1','\n','3','4',',','1',',','1','5','6',',','1','\n','3','1',',','1',',','1','5','8',',','1','\n','2','8',',','1',',','1','6','9',',','1','\n','2','6',',','1',',','1','7','3',',','1','\n','2','6',',','1',',','1','7','2',',','1','\n','2','4',',','1',',','1','7','6',',','1','\n','2','2',',','1',',','1','7','7',',','1','\n','2','1',',','1',',','1','8','1',',','1','\n','1','4',',','1',',','2','2','1',',','1','\n','3',',','1',',','3','1','6',',','1','\n','6',',','1',',','2','6','7',',','1',';','5',',','1',',','2','7','9',',','1',';','2',',','1',',','3','5','6',',','1','\n','3',',','1',',','3','1','7',',','1',';','2',',','1',',','3','5','5',',','1','\n','5',',','1',',','2','7','9',',','1',';','1',',','1',',','3','8','2',',','1','\n','1',',','2',',','3','5','7',',','1','\n','2',',','1',',','3','5','6',',','1',';','0',',','1',',','4','0','5',',','1','\n','1',',','1',',','3','8','2',',','1',';','0',',','1',',','2','0',',','1',',','1','8','8',',','1','\n','6','3',',','1',',','9','5',',','1','\n','6','6',',','1',',','8','9',',','1',';','5','3',',','1',',','1','1','8',',','1','\n','3','7',',','1',',','1','4','9',',','1','\n','3','3',',','1',',','1','5','6',',','1','\n','2','8',',','1',',','1','6','8',',','1','\n','1','2',',','1',',','2','3','4',',','1','\n','6','6',',','1',',','9','0',',','1',';','8',',','1',',','5','0',',','1',',','6','9',',','1','\n','6',',','1',',','2','6','6',',','1',';','4',',','1',',','2','9','2',',','1','\n','1',',','1',',','3','8','1',',','1','\n','5','3',',','1',',','1','1','8',',','1',';','4',',','1',',','2','9','2',',','1',';','0',',','1',',','8',',','1',',','2','5','5',',','1','\n','4',',','1',',','2','9','2',',','1',';','0',',','1',',','2',',','1',',','3','4','6',',','1','\n','8',',','1',',','5','0',',','1',',','6','9',',','1',';','0',',','1',',','8',',','1',',','2','5','5',',','1',';','0',',','1',',','2',',','1',',','3','4','6',',','1',';','0',',','4',',','3','5','9',',','1','\n','2','3',',','1',',','1','7','6',',','1',';','0',',','4',',','3','5','9',',','1',';','0',',','5',',','3','4','9',',','1','\n','6','0',',','1',',','1','0','7',',','1',';','5','9',',','1',',','1','0','7',',','1','\n','5','2',',','1',',','1','1','9',',','1','\n','5','0',',','1',',','1','2','2',',','1','\n','4','7',',','1',',','1','3','2',',','1','\n','3','2',',','1',',','1','5','6',',','1','\n','2','8',',','1',',','1','6','7',',','1','\n','2','2',',','1',',','1','7','6',',','1','\n','5','9',',','1',',','1','0','7',',','1',';','1','5',',','1',',','2','1','2',',','1','\n','8',',','1',',','4','9',',','1',',','6','9',',','1','\n','1','5',',','1',',','2','1','2',',','1',';','4',',','1',',','2','9','1',',','1','\n','4',',','1',',','2','9','1',',','1',';','0',',','1',',','8',',','1',',','2','5','4',',','1','\n','0',',','1',',','8',',','1',',','2','5','4',',','1',';','0',',','4',',','3','5','8',',','1','\n','6','0',',','1',',','1','0','5',',','1','\n','6','0',',','1',',','1','0','6',',','1',';','5','9',',','1',',','1','0','6',',','1','\n','5','9',',','1',',','1','0','5',',','1','\n','5','1',',','1',',','1','1','9',',','1','\n','5','0',',','1',',','1','2','1',',','1','\n','4','9',',','1',',','1','2','2',',','1','\n','4','7',',','1',',','1','3','1',',','1','\n','5','9',',','1',',','1','0','6',',','1',';','3','6',',','1',',','1','4','9',',','1','\n','3','1',',','1',',','1','5','7',',','1','\n','2','8',',','1',',','1','6','6',',','1','\n','3','6',',','1',',','1','4','9',',','1',';','0',',','4',',','1','7',',','1',',','1','8','8',',','1','\n','6','8',',','1',',','8','8',',','1','\n','6','0',',','1',',','1','0','4',',','1','\n','6','0',',','1',',','1','0','3',',','1','\n','5','9',',','1',',','1','0','4',',','1','\n','5','9',',','1',',','1','0','3',',','1','\n','4','9',',','1',',','1','2','1',',','1','\n','4','7',',','1',',','1','3','0',',','1','\n','5',',','1',',','2','7','8',',','1',';','1',',','1',',','3','8','0',',','1','\n','5','0',',','1',',','1','2','0',',','1',';','1',',','1',',','3','8','0',',','1',';','0',',','1',',','4','0','4',',','1','\n','1',',','1',',','3','8','0',',','1',';','0',',','1',',','4','0','4',',','1',';','0',',','5',',','3','4','7',',','1','\n','7','6',',','1',',','7','8',',','1','\n','6','7',',','1',',','8','8',',','1','\n','4','9',',','1',',','1','2','0',',','1','\n','4','7',',','1',',','1','2','9',',','1','\n','4','7',',','1',',','1','2','8',',','1','\n','7','6',',','1',',','7','7',',','1','\n','7','5',',','1',',','7','8',',','1','\n','7','4',',','1',',','7','8',',','1','\n','6','5',',','1',',','9','4',',','1','\n','6','2',',','1',',','9','9',',','1','\n','5','8',',','1',',','1','0','9',',','1','\n','5','6',',','1',',','1','1','5',',','1','\n','2','7',',','1',',','1','7','0',',','1','\n','1','4',',','1',',','2','2','0',',','1','\n','1','2',',','1',',','2','3','3',',','1','\n','7','5',',','1',',','7','7',',','1','\n','7','4',',','1',',','7','7',',','1','\n','7','3',',','1',',','7','8',',','1','\n','7','1',',','1',',','8','6',',','1','\n','6','5',',','1',',','9','3',',','1','\n','6','5',',','1',',','9','2',',','1','\n','5','5',',','1',',','1','1','5',',','1','\n','3','1',',','1',',','1','5','6',',','1','\n','2','7',',','1',',','1','6','9',',','1','\n','1','4',',','1',',','2','1','9',',','1','\n','1','2',',','1',',','2','3','2',',','1','\n','3',',','1',',','3','1','5',',','1','\n','0',',','1',',','8',',','3',',','1','1','8',',','1','\n','7','3',',','1',',','7','7',',','1','\n','7','1',',','1',',','8','5',',','1','\n','7','1',',','1',',','8','4',',','1','\n','7','0',',','1',',','8','7',',','1','\n','6','6',',','1',',','8','8',',','1','\n','6','5',',','1',',','9','1',',','1','\n','5','8',',','1',',','1','0','8',',','1','\n','4','1',',','1',',','1','4','4',',','1','\n','2','7',',','1',',','1','6','8',',','1','\n','2','1',',','1',',','1','8','0',',','1','\n','1','4',',','1',',','2','1','8',',','1','\n','5',',','1',',','2','7','7',',','1','\n','7','1',',','1',',','8','3',',','1','\n','7','1',',','1',',','8','2',',','1','\n','5','0',',','1',',','1','1','9',',','1','\n','2','7',',','1',',','1','6','7',',','1','\n','1','1',',','1',',','2','3','8',',','1','\n','7','1',',','1',',','8','1',',','1','\n','4','9',',','1',',','1','1','9',',','1',';','3','0',',','1',',','1','6','2',',','1','\n','3','0',',','1',',','1','6','2',',','1',';','2','7',',','1',',','1','6','6',',','1','\n','2','6',',','1',',','1','7','1',',','1','\n','1','1',',','1',',','2','3','7',',','1','\n','2','7',',','1',',','1','6','6',',','1',';','1','0',',','1',',','2','3','8',',','1','\n','1','0',',','1',',','2','3','8',',','1',';','1',',','1',',','8',',','1',',','2','4','4',',','1','\n','1',',','1',',','8',',','1',',','2','4','4',',','1',';','0',',','1',',','8',',','1',',','1','7',',','1',',','1','3','8',',','1','\n','5','3',',','1',',','1','1','7',',','1',';','4','7',',','1',',','1','2','7',',','1','\n','4','7',',','1',',','1','2','7',',','1',';','1','0',',','1',',','2','3','7',',','1','\n','4','7',',','1',',','1','2','6',',','1',';','1','0',',','1',',','2','3','7',',','1',';','0',',','1',',','8',',','1',',','1','6',',','1',',','1','3','8',',','1','\n','1','0',',','1',',','2','3','7',',','1',';','0',',','1',',','8',',','1',',','1','6',',','1',',','1','3','8',',','1',';','0',',','2',',','8',',','1',',','2','4','4',',','1','\n','6','5',',','1',',','9','0',',','1',';','6','5',',','1',',','8','9',',','1','\n','6','2',',','1',',','9','8',',','1','\n','6','1',',','1',',','1','0','2',',','1','\n','6','5',',','1',',','8','9',',','1',';','5','3',',','1',',','1','1','6',',','1','\n','5','3',',','1',',','1','1','6',',','1',';','0',',','1',',','8',',','1',',','1','6',',','1',',','1','3','7',',','1','\n','4','3',',','1',',','1','4','0',',','1','\n','4','8',',','1',',','1','2','3',',','1','\n','7',',','1',',','2','6','5',',','1','\n','2','5',',','1',',','1','7','5',',','1','\n','6','5',',','1',',','8','8',',','1','\n','6','0',',','1',',','1','0','2',',','1','\n','5','9',',','1',',','1','0','2',',','1','\n','4','7',',','1',',','1','2','5',',','1','\n','4','2',',','1',',','1','4','0',',','1','\n','3','0',',','1',',','1','6','1',',','1','\n','2','4',',','1',',','1','7','5',',','1','\n','1','5',',','1',',','2','1','1',',','1','\n','1','5',',','1',',','2','1','0',',','1','\n','6',',','1',',','2','6','5',',','1','\n','2',',','1',',','3','5','4',',','1','\n','0',',','1',',','4','0','1',',','1','\n','2','8',',','1',',','1','6','5',',','1',';','2','3',',','1',',','1','7','5',',','1','\n','1','1',',','1',',','2','3','6',',','1','\n','2','3',',','1',',','1','7','5',',','1',';','1',',','2',',','3','5','4',',','1','\n','1',',','2',',','3','5','4',',','1',';','0',',','1',',','1','7',',','1',',','2','0','0',',','1','\n','2','2',',','1',',','1','7','5',',','1',';','1','0',',','1',',','2','3','6',',','1','\n','1','0',',','1',',','2','3','6',',','1',';','0',',','1',',','8',',','1',',','2','5','3',',','1','\n','1','3',',','1',',','2','2','7',',','1',';','0',',','1',',','8',',','1',',','2','5','2',',','1','\n','6','2',',','1',',','9','7',',','1',';','4','4',',','1',',','1','3','5',',','1','\n','4','4',',','1',',','1','3','5',',','1',';','2','7',',','1',',','1','6','5',',','1','\n','2','7',',','1',',','1','6','5',',','1',';','1','4',',','1',',','2','1','7',',','1','\n','1','4',',','1',',','2','1','7',',','1',';','5',',','1',',','2','7','6',',','1','\n','5',',','1',',','2','7','6',',','1',';','1',',','1',',','3','7','9',',','1','\n','6','9',',','1',',','9','6',',','1','\n','2',',','1',',','3','7','8',',','1','\n','2',',','1',',','3','7','7',',','1','\n','0',',','1',',','6','9',',','1',',','9','3',',','1','\n','7','0',',','1',',','9','4',',','1','\n','7','0',',','1',',','9','3',',','1','\n','2',',','1',',','3','7','5',',','1','\n','7','0',',','1',',','9','2',',','1',';','1',',','1',',','4','1','5',',','1','\n','7','0',',','1',',','9','1',',','1','\n','6','8',',','1',',','9','6',',','1','\n','2',',','1',',','3','7','4',',','1',';','1',',','1',',','4','1','4',',','1','\n','1',',','2',',','3','7','6',',','1','\n','1',',','1',',','4','1','4',',','1',';','0',',','2',',','4','1','5',',','1','\n','0',',','3',',','3','9','6',',','1','\n','7','6',',','1',',','8','6',',','1','\n','6','7',',','1',',','9','6',',','1','\n','4','8',',','1',',','1','3','2',',','1','\n','1','8',',','1',',','2','0','2',',','1','\n','8',',','1',',','2','6','4',',','1',';','2',',','1',',','3','7','2',',','1','\n','2',',','1',',','3','7','2',',','1',';','2',',','1',',','6','9',',','1',',','8','0',',','1','\n','3',',','1',',','3','3','2',',','1',';','1',',','1',',','4','1','3',',','1',';','1',',','1',',','4','1','2',',','1','\n','2',',','1',',','6','9',',','1',',','8','0',',','1',';','0',',','1',',','4','1','9',',','1','\n','0',',','3',',','3','9','4',',','1','\n','0',',','3',',','3','9','2',',','1','\n','7','6',',','1',',','8','5',',','1','\n','7','6',',','1',',','8','4',',','1','\n','7','5',',','1',',','8','6',',','1',';','7','4',',','1',',','8','6',',','1','\n','6','1',',','1',',','1','0','9',',','1','\n','4','8',',','1',',','1','3','1',',','1','\n','2','5',',','1',',','1','8','1',',','1','\n','1','2',',','1',',','2','4','2',',','1','\n','3',',','1',',','3','3','1',',','1','\n','1',',','1',',','4','1','1',',','1','\n','1',',','1',',','4','1','0',',','1','\n','1',',','1',',','4','0','9',',','1','\n','7','4',',','1',',','8','6',',','1',';','2',',','1',',','3','7','1',',','1',';','0',',','1',',','6','9',',','1',',','8','9',',','1','\n','2',',','1',',','3','7','1',',','1',';','0',',','1',',','6','9',',','1',',','8','9',',','1',';','0',',','3',',','3','9','1',',','1','\n','7','6',',','1',',','8','3',',','1',';','7','5',',','1',',','8','5',',','1','\n','7','5',',','1',',','8','4',',','1','\n','7','4',',','1',',','8','5',',','1','\n','7','4',',','1',',','8','4',',','1','\n','7','3',',','1',',','8','6',',','1','\n','7','5',',','1',',','8','5',',','1',';','6','8',',','1',',','9','5',',','1','\n','5','3',',','1',',','1','2','2',',','1','\n','4','8',',','1',',','1','3','0',',','1','\n','6','8',',','1',',','9','5',',','1',';','2','4',',','1',',','1','8','1',',','1','\n','2','4',',','1',',','1','8','1',',','1',';','1','8',',','1',',','2','0','1',',','1','\n','1','8',',','1',',','2','0','1',',','1',';','1','3',',','1',',','2','3','5',',','1','\n','1','2',',','1',',','2','4','1',',','1','\n','1','3',',','1',',','2','3','5',',','1',';','9',',','1',',','2','5','1',',','1','\n','3',',','1',',','3','3','0',',','1','\n','1',',','1',',','4','0','8',',','1','\n','0',',','2',',','4','1','0',',','1','\n','0',',','2',',','4','0','9',',','1','\n','0',',','3',',','3','8','9',',','1',';','0',',','5',',','3','6','7',',','1','\n','7','6',',','1',',','8','1',',','1',';','7','5',',','1',',','8','2',',','1','\n','7','4',',','1',',','8','3',',','1','\n','7','5',',','1',',','8','2',',','1',';','7','4',',','1',',','8','2',',','1','\n','7','3',',','1',',','8','5',',','1','\n','7','3',',','1',',','8','4',',','1','\n','7','4',',','1',',','8','2',',','1',';','7','0',',','1',',','9','0',',','1','\n','7','0',',','1',',','8','9',',','1','\n','7','5',',','1',',','8','3',',','1',';','7','0',',','1',',','9','0',',','1',';','6','7',',','1',',','9','5',',','1','\n','6','6',',','1',',','9','6',',','1','\n','6','4',',','1',',','9','9',',','1','\n','6','1',',','1',',','1','0','8',',','1','\n','5','3',',','1',',','1','2','1',',','1','\n','4','8',',','1',',','1','2','9',',','1','\n','4','8',',','1',',','1','2','8',',','1','\n','7','0',',','1',',','9','0',',','1',';','2','8',',','1',',','1','7','4',',','1','\n','2','8',',','1',',','1','7','4',',','1',';','2','6',',','1',',','1','7','9',',','1','\n','6','7',',','1',',','9','5',',','1',';','2','6',',','1',',','1','7','9',',','1',';','2','3',',','1',',','1','8','1',',','1','\n','2','0',',','1',',','1','9','8',',','1','\n','1','2',',','1',',','2','4','0',',','1','\n','8',',','1',',','2','6','3',',','1','\n','5',',','1',',','2','8','9',',','1','\n','4',',','1',',','3','1','0',',','1','\n','2','6',',','1',',','1','7','9',',','1',';','3',',','1',',','3','2','9',',','1','\n','3',',','1',',','3','2','9',',','1',';','1',',','1',',','4','0','7',',','1','\n','0',',','1',',','4','1','7',',','1','\n','1',',','1',',','4','0','7',',','1',';','0',',','3',',','3','8','6',',','1','\n','7','5',',','1',',','8','1',',','1','\n','7','4',',','1',',','8','1',',','1','\n','7','3',',','1',',','8','3',',','1','\n','7','3',',','1',',','8','2',',','1','\n','5','3',',','1',',','1','2','0',',','1','\n','3','8',',','1',',','1','5','5',',','1','\n','2','6',',','1',',','1','7','8',',','1','\n','2','2',',','1',',','1','8','1',',','1','\n','2','0',',','1',',','1','9','7',',','1','\n','1','9',',','1',',','1','9','8',',','1','\n','1','1',',','1',',','2','4','3',',','1','\n','8',',','1',',','2','6','2',',','1','\n','5',',','1',',','2','8','8',',','1','\n','4',',','1',',','3','0','9',',','1','\n','2',',','1',',','3','7','0',',','1','\n','1',',','1',',','4','0','6',',','1','\n','0',',','2',',','4','0','7',',','1','\n','7','3',',','1',',','8','1',',','1','\n','4','3',',','1',',','1','4','4',',','1','\n','3','7',',','1',',','1','5','5',',','1','\n','2','6',',','1',',','1','7','7',',','1','\n','1','9',',','1',',','1','9','7',',','1','\n','1','2',',','1',',','2','3','9',',','1','\n','1','0',',','1',',','2','4','3',',','1','\n','9',',','1',',','2','5','0',',','1',';','8',',','1',',','2','6','1',',','1','\n','4',',','1',',','3','0','8',',','1','\n','4',',','1',',','3','0','7',',','1','\n','3',',','1',',','3','2','8',',','1','\n','6','3',',','1',',','9','9',',','1','\n','2','0',',','1',',','1','9','6',',','1','\n','1','5',',','1',',','2','1','6',',','1','\n','6','6',',','1',',','9','5',',','1',';','1','3',',','1',',','2','3','4',',','1','\n','6',',','1',',','2','7','5',',','1','\n','4',',','1',',','3','0','6',',','1','\n','2',',','1',',','3','6','9',',','1','\n','1','3',',','1',',','2','3','4',',','1',';','2',',','2',',','3','2','8',',','1','\n','2',',','2',',','3','2','8',',','1',';','0',',','1',',','7',',','1',',','2','6','6',',','1','\n','0',',','1',',','7',',','1',',','2','6','6',',','1',';','0',',','1',',','3',',','2',',','2','6','7',',','1','\n','3','6',',','1',',','1','5','5',',','1',';','2','6',',','1',',','1','7','6',',','1','\n','2','1',',','1',',','1','9','1',',','1','\n','1','9',',','1',',','1','9','6',',','1','\n','9',',','1',',','2','4','9',',','1','\n','5',',','1',',','2','8','7',',','1','\n','4',',','1',',','3','0','5',',','1','\n','4',',','1',',','3','0','4',',','1','\n','1',',','2',',','3','6','9',',','1','\n','2','6',',','1',',','1','7','6',',','1',';','0',',','1',',','2',',','1',',','3','5','9',',','1','\n','6','0',',','1',',','1','0','9',',','1','\n','5','9',',','1',',','1','0','9',',','1','\n','5','4',',','1',',','1','1','8',',','1','\n','3','8',',','1',',','1','5','4',',','1','\n','2','9',',','1',',','1','7','0',',','1','\n','2','1',',','1',',','1','9','0',',','1','\n','2','0',',','1',',','1','9','5',',','1','\n','5',',','1',',','2','8','6',',','1','\n','5',',','1',',','2','8','5',',','1','\n','4',',','1',',','3','0','3',',','1','\n','4',',','1',',','3','0','2',',','1','\n','1',',','1',',','4','0','5',',','1','\n','6','4',',','1',',','9','8',',','1','\n','5','3',',','1',',','1','1','9',',','1','\n','5','2',',','1',',','1','2','4',',','1','\n','4','8',',','1',',','1','2','7',',','1','\n','4','8',',','1',',','1','2','6',',','1','\n','3','7',',','1',',','1','5','4',',','1','\n','3','5',',','1',',','1','6','0',',','1','\n','2','9',',','1',',','1','6','9',',','1','\n','2','5',',','1',',','1','8','0',',','1','\n','1','9',',','1',',','1','9','5',',','1','\n','7',',','1',',','2','7','4',',','1','\n','5',',','1',',','2','8','4',',','1','\n','4',',','1',',','3','0','1',',','1','\n','4',',','1',',','3','0','0',',','1','\n','3',',','1',',','3','2','7',',','1','\n','0',',','1',',','2',',','1',',','3','5','5',',','1','\n','0',',','2',',','4','0','5',',','1','\n','0',',','2',',','2','0',',','1',',','1','8','8',',','1','\n','6','0',',','1',',','1','0','8',',','1','\n','7','0',',','1',',','8','8',',','1',';','5','9',',','1',',','1','0','8',',','1','\n','5','1',',','1',',','1','2','4',',','1','\n','5','9',',','1',',','1','0','8',',','1',';','4','2',',','1',',','1','4','4',',','1','\n','4','2',',','1',',','1','4','4',',','1',';','3','4',',','1',',','1','6','0',',','1','\n','2','9',',','1',',','1','6','8',',','1','\n','2','8',',','1',',','1','7','3',',','1','\n','3','4',',','1',',','1','6','0',',','1',';','2','8',',','1',',','1','7','2',',','1','\n','2','8',',','1',',','1','7','2',',','1',';','2','7',',','1',',','1','7','4',',','1','\n','2','4',',','1',',','1','8','0',',','1','\n','2','1',',','1',',','1','8','9',',','1','\n','0',',','2',',','2',',','1',',','3','4','6',',','1','\n','2','7',',','1',',','1','7','4',',','1',';','0',',','6',',','3','4','9',',','1','\n','3','6',',','1',',','1','5','4',',','1','\n','3','3',',','1',',','1','6','0',',','1','\n','2','9',',','1',',','1','6','7',',','1',';','2','3',',','1',',','1','8','0',',','1','\n','2','1',',','1',',','1','8','8',',','1','\n','2','3',',','1',',','1','8','0',',','1',';','1','3',',','1',',','2','3','3',',','1','\n','1','3',',','1',',','2','3','3',',','1',';','9',',','1',',','2','4','8',',','1','\n','4',',','1',',','2','9','9',',','1','\n','0',',','5',',','3','5','8',',','1','\n','6','3',',','1',',','9','8',',','1','\n','4','0',',','1',',','1','5','1',',','1','\n','3','0',',','1',',','1','6','4',',','1','\n','3','2',',','1',',','1','6','0',',','1',';','2','9',',','1',',','1','6','6',',','1','\n','2','9',',','1',',','1','6','6',',','1',';','2','2',',','1',',','1','8','0',',','1','\n','2','2',',','1',',','1','8','0',',','1',';','2','0',',','1',',','1','9','4',',','1','\n','2','0',',','1',',','1','9','4',',','1',';','1','3',',','1',',','2','3','2',',','1','\n','1','3',',','1',',','2','3','2',',','1',';','8',',','1',',','9',',','1',',','1','6','7',',','1','\n','2','1',',','1',',','1','8','7',',','1',';','1',',','1',',','4','0','4',',','1','\n','1',',','1',',','4','0','4',',','1',';','0',',','5',',','1','7',',','1',',','1','8','8',',','1','\n','4','0',',','1',',','1','5','0',',','1','\n','3','9',',','1',',','1','5','1',',','1','\n','2','0',',','1',',','1','9','3',',','1',';','1','9',',','1',',','1','9','4',',','1','\n','1','9',',','1',',','1','9','4',',','1',';','1','7',',','1',',','2','0','8',',','1','\n','1','5',',','1',',','2','1','5',',','1','\n','1','4',',','1',',','2','2','6',',','1','\n','1','7',',','1',',','2','0','8',',','1',';','8',',','2',',','1','8','0',',','1','\n','6',',','1',',','2','7','4',',','1',';','0',',','2',',','4','0','4',',','1','\n','0',',','2',',','4','0','4',',','1',';','0',',','6',',','3','4','7',',','1','\n','6','5',',','1',',','9','6',',','1','\n','4','7',',','1',',','1','3','4',',','1','\n','3','9',',','1',',','1','5','0',',','1','\n','1','9',',','1',',','1','9','3',',','1',';','1','7',',','1',',','2','0','7',',','1','\n','1','6',',','1',',','2','0','8',',','1',';','9',',','1',',','2','4','7',',','1','\n','1','7',',','1',',','2','0','7',',','1',';','9',',','1',',','2','4','7',',','1',';','9',',','1',',','2','4','6',',','1','\n','9',',','1',',','2','4','7',',','1',';','8',',','1',',','2','5','9',',','1','\n','9',',','1',',','2','4','6',',','1',';','0',',','3',',','3','8','0',',','1','\n','4','7',',','1',',','1','3','3',',','1','\n','4','4',',','1',',','1','3','9',',','1','\n','2','1',',','1',',','1','8','6',',','1','\n','1','6',',','1',',','2','0','7',',','1',';','9',',','1',',','2','4','5',',','1','\n','9',',','1',',','2','4','5',',','1',';','8',',','1',',','2','5','8',',','1','\n','5','0',',','1',',','1','2','4',',','1','\n','4','0',',','1',',','1','4','9',',','1',';','1','7',',','1',',','2','0','6',',','1','\n','6','5',',','1',',','9','5',',','1','\n','4','9',',','1',',','1','2','4',',','1','\n','4','8',',','1',',','1','2','5',',','1',';','3','9',',','1',',','1','4','9',',','1',';','3','1',',','1',',','1','6','0',',','1','\n','2','7',',','1',',','1','7','3',',','1','\n','3','9',',','1',',','1','4','9',',','1',';','3','1',',','1',',','1','6','0',',','1',';','2','7',',','1',',','1','7','2',',','1','\n','3','1',',','1',',','1','6','0',',','1',';','1','6',',','1',',','2','0','6',',','1','\n','2','7',',','1',',','1','7','2',',','1',';','1','6',',','1',',','2','0','6',',','1',';','9',',','1',',','2','4','4',',','1','\n','1','6',',','1',',','2','0','6',',','1',';','8',',','1',',','2','5','7',',','1','\n','9',',','1',',','2','4','4',',','1',';','8',',','1',',','2','5','7',',','1',';','1',',','1',',','4','2',',','1',',','1','3','7',',','1','\n','5','4',',','1',',','1','1','7',',','1','\n','5','8',',','1',',','1','1','4',',','1','\n','5','4',',','1',',','1','1','6',',','1','\n','3','8',',','1',',','1','5','3',',','1','\n','0',',','2',',','8',',','1',',','1','7',',','1',',','1','3','8',',','1','\n','3','8',',','1',',','1','5','2',',','1','\n','3','7',',','1',',','1','5','3',',','1','\n','2','8',',','1',',','1','7','1',',','1','\n','6','2',',','1',',','1','0','1',',','1',';','0',',','2',',','8',',','1',',','1','6',',','1',',','1','3','8',',','1','\n','5','8',',','1',',','1','1','3',',','1',';','4','1',',','1',',','1','4','7',',','1','\n','3','7',',','1',',','1','5','2',',','1','\n','4','1',',','1',',','1','4','7',',','1',';','2','1',',','1',',','1','8','5',',','1','\n','1','8',',','1',',','2','0','0',',','1','\n','2','1',',','1',',','1','8','5',',','1',';','1','2',',','1',',','2','3','8',',','1','\n','1','2',',','1',',','2','3','8',',','1',';','4',',','1',',','2','9','8',',','1','\n','4',',','1',',','2','9','8',',','1',';','0',',','2',',','8',',','1',',','1','6',',','1',',','1','3','7',',','1','\n','7','2',',','1',',','8','7',',','1','\n','5','8',',','1',',','1','1','2',',','1','\n','4','1',',','1',',','1','4','6',',','1','\n','3','6',',','1',',','1','5','3',',','1','\n','2','1',',','1',',','1','8','4',',','1','\n','1','8',',','1',',','1','9','9',',','1','\n','1','2',',','1',',','2','3','7',',','1','\n','4',',','1',',','2','9','7',',','1','\n','4','4',',','1',',','1','3','8',',','1','\n','3','6',',','1',',','1','5','2',',','1','\n','1','4',',','1',',','2','2','5',',','1','\n','1',',','1',',','4','0','3',',','1','\n','5','2',',','1',',','1','2','3',',','1','\n','6','4',',','1',',','9','7',',','1',';','4','4',',','1',',','1','3','7',',','1','\n','3','5',',','1',',','1','5','9',',','1','\n','4','4',',','1',',','1','3','7',',','1',';','1','4',',','1',',','2','2','4',',','1','\n','1','4',',','1',',','2','2','4',',','1',';','1',',','1',',','4','0','2',',','1','\n','5','1',',','1',',','1','2','3',',','1','\n','3','4',',','1',',','1','5','9',',','1','\n','3','3',',','1',',','1','5','9',',','1','\n','2','6',',','1',',','1','7','5',',','1','\n','6','3',',','1',',','9','7',',','1','\n','6','2',',','1',',','1','0','0',',','1','\n','4','6',',','1',',','1','3','5',',','1','\n','4','4',',','1',',','1','3','6',',','1','\n','3','2',',','1',',','1','5','9',',','1','\n','2','7',',','1',',','1','7','1',',','1','\n','1','4',',','1',',','2','2','3',',','1','\n','5',',','1',',','2','8','3',',','1','\n','1',',','1',',','4','0','1',',','1','\n','4','5',',','1',',','1','3','5',',','1','\n','2','9',',','1',',','1','6','5',',','1','\n','3',',','1',',','3','2','6',',','1','\n','0',',','2',',','1','7',',','1',',','2','0','0',',','1','\n','3',',','1',',','3','2','5',',','1','\n','5','8',',','1',',','1','1','1',',','1',';','5','0',',','1',',','1','2','3',',','1','\n','5','0',',','1',',','1','2','3',',','1',';','2','1',',','1',',','1','8','3',',','1','\n','2','1',',','1',',','1','8','3',',','1',';','1','7',',','1',',','2','0','5',',','1','\n','1','7',',','1',',','2','0','5',',','1',';','4',',','1',',','2','9','6',',','1','\n','4',',','1',',','2','9','6',',','1',';','0',',','2',',','8',',','1',',','2','5','2',',','1','\n','7','1',',','1',',','8','7',',','1',';','5','8',',','1',',','1','1','0',',','1','\n','5','8',',','1',',','1','1','0',',','1',';','4','9',',','1',',','1','2','3',',','1','\n','4','9',',','1',',','1','2','3',',','1',';','4','1',',','1',',','1','4','5',',','1','\n','4','1',',','1',',','1','4','5',',','1',';','3','1',',','1',',','1','5','9',',','1','\n','3','1',',','1',',','1','5','9',',','1',';','2','1',',','1',',','1','8','2',',','1','\n','2','1',',','1',',','1','8','2',',','1',';','1','6',',','1',',','2','0','5',',','1','\n','1','6',',','1',',','2','0','5',',','1',';','1','2',',','1',',','2','3','6',',','1','\n','1','2',',','1',',','2','3','6',',','1',';','8',',','1',',','2','5','6',',','1','\n','8',',','1',',','2','5','6',',','1',';','4',',','1',',','2','9','5',',','1','\n','4',',','1',',','2','9','5',',','1',';','0',',','5',',','1','7',',','1',',','1','8','3',',','1','\n','6','9',',','1',',','9','9',',','1','\n','2',',','2',',','3','4','1',',','1','\n','2',',','1',',','3','9','9',',','1','\n','2',',','2',',','3','4','0',',','1','\n','7','0',',','1',',','9','6',',','1','\n','3','5',',','1',',','1','6','3',',','1','\n','1','8',',','1',',','2','0','4',',','1','\n','1','8',',','1',',','2','0','3',',','1','\n','2',',','1',',','3','9','7',',','1','\n','0',',','1',',','4','3','0',',','1','\n','3','4',',','1',',','1','6','3',',','1','\n','1','3',',','1',',','2','4','2',',','1','\n','2',',','1',',','3','9','5',',','1',';','2',',','1',',','3','9','3',',','1','\n','2',',','1',',','3','9','2',',','1','\n','2',',','1',',','3','9','4',',','1',';','2',',','1',',','3','9','3',',','1',';','0',',','1',',','4','2','9',',','1','\n','2',',','1',',','3','9','3',',','1',';','0',',','1',',','6','9',',','1',',','9','5',',','1','\n','6','8',',','1',',','9','9',',','1','\n','3','8',',','1',',','1','5','8',',','1','\n','3','3',',','1',',','1','6','3',',','1','\n','1','3',',','1',',','2','4','1',',','1','\n','8',',','1',',','2','7','3',',','1','\n','3',',','1',',','3','3','8',',','1','\n','2',',','1',',','3','9','1',',','1','\n','7',',','1',',','2','8','2',',','1',';','2',',','1',',','3','9','0',',','1','\n','2',',','1',',','3','9','0',',','1',';','2',',','1',',','6','9',',','1',',','8','2',',','1','\n','1',',','2',',','3','9','3',',','1',';','1',',','2',',','3','9','2',',','1','\n','1',',','2',',','3','9','2',',','1',';','0',',','2',',','3',',','1',',','6','8',',','1',',','6','9',',','1','\n','6','9',',','1',',','9','8',',','1','\n','6','7',',','1',',','9','9',',','1','\n','3','7',',','1',',','1','5','8',',','1','\n','3','2',',','1',',','1','6','3',',','1','\n','7','0',',','1',',','9','5',',','1',';','2','5',',','1',',','1','9','1',',','1','\n','1','3',',','1',',','2','4','0',',','1','\n','2','5',',','1',',','1','9','1',',','1',';','7',',','1',',','2','8','1',',','1','\n','3',',','1',',','3','3','7',',','1','\n','7',',','1',',','2','8','1',',','1',';','2',',','1',',','3','8','9',',','1','\n','2',',','1',',','3','8','8',',','1','\n','2',',','1',',','3','8','9',',','1',';','1',',','1',',','4','1','9',',','1','\n','1',',','1',',','4','1','9',',','1',';','0',',','1',',','2',',','1',',','3','7','3',',','1','\n','0',',','3',',','4','1','5',',','1','\n','5','4',',','1',',','1','2','2',',','1','\n','5','2',',','1',',','1','3','2',',','1','\n','2','6',',','1',',','1','8','1',',','1','\n','2','4',',','1',',','1','9','1',',','1',';','1','1',',','1',',','2','5','1',',','1','\n','8',',','1',',','2','7','2',',','1','\n','1','1',',','1',',','2','5','1',',','1',';','4',',','1',',','3','1','3',',','1','\n','4',',','1',',','3','1','3',',','1',';','2',',','1',',','3','8','7',',','1','\n','4',',','1',',','3','1','4',',','1',';','2',',','1',',','3','8','7',',','1',';','2',',','1',',','3','8','6',',','1','\n','2',',','1',',','3','8','7',',','1',';','2',',','1',',','1','8',',','1',',','1','8','9',',','1','\n','2',',','1',',','1','8',',','1',',','1','8','9',',','1',';','1',',','2',',','3','8','9',',','1','\n','1',',','2',',','3','8','9',',','1',';','1',',','2',',','3','8','8',',','1','\n','1',',','2',',','3','8','8',',','1',';','0',',','1',',','4','2','7',',','1','\n','2',',','1',',','3','8','6',',','1',';','0',',','1',',','4','2','7',',','1',';','0',',','2',',','4','1','9',',','1','\n','0',',','3',',','4','1','4',',','1','\n','5','4',',','1',',','1','2','1',',','1','\n','5','2',',','1',',','1','3','1',',','1','\n','5','1',',','1',',','1','3','2',',','1','\n','3','8',',','1',',','1','5','7',',','1','\n','3','6',',','1',',','1','5','8',',','1','\n','2','3',',','1',',','1','9','1',',','1',';','1','0',',','1',',','2','5','1',',','1','\n','8',',','1',',','2','7','1',',','1','\n','8',',','1',',','2','7','0',',','1','\n','1','3',',','1',',','2','3','9',',','1',';','1','0',',','1',',','2','5','1',',','1',';','4',',','1',',','3','1','2',',','1','\n','4',',','1',',','3','1','1',',','1','\n','1','0',',','1',',','2','5','1',',','1',';','4',',','1',',','3','1','2',',','1',';','2',',','1',',','1','8',',','1',',','1','8','8',',','1','\n','4',',','1',',','3','1','2',',','1',';','2',',','1',',','1','8',',','1',',','1','8','8',',','1',';','1',',','2',',','3','8','7',',','1','\n','1',',','2',',','3','8','7',',','1',';','0',',','1',',','4','2','6',',','1','\n','2',',','1',',','1','8',',','1',',','1','8','8',',','1',';','0',',','1',',','4','2','6',',','1',';','0',',','2',',','6','9',',','1',',','8','9',',','1'] ['0',',','1',',','4','2','6',',','1',';','0',',','4',',','3','9','1',',','1'] ['0',',','2',',','6','9',',','1',',','8','9',',','1',';','0',',','5',',','3','7','5',',','1','\n','7','2',',','1',',','9','4',',','1','\n','6','6',',','1',',','9','9',',','1','\n','5','4',',','1',',','1','2','0',',','1','\n','5','2',',','1',',','1','3','0',',','1','\n','5','1',',','1',',','1','3','1',',','1','\n','3','7',',','1',',','1','5','7',',','1','\n','2','2',',','1',',','1','9','1',',','1','\n','1','7',',','1',',','2','1','4',',','1','\n','8',',','1',',','2','6','9',',','1',';','7',',','1',',','2','8','0',',','1','\n','6',',','1',',','2','8','2',',','1','\n','7',',','1',',','2','8','0',',','1',';','1',',','1',',','4','1','8',',','1','\n','2','5',',','1',',','1','8','9',',','1',';','1',',','1',',','4','1','7',',','1','\n','0',',','1',',','9',',','1',',','2','5','1',',','1','\n','0',',','6',',','3','6','7',',','1','\n','7','2',',','1',',','9','3',',','1','\n','5','2',',','1',',','1','2','9',',','1','\n','5','2',',','1',',','1','2','8',',','1','\n','5','1',',','1',',','1','3','0',',','1','\n','4','8',',','1',',','1','3','4',',','1','\n','2','9',',','1',',','1','7','4',',','1','\n','7','2',',','1',',','9','2',',','1',';','2','5',',','1',',','1','8','8',',','1','\n','2','5',',','1',',','1','8','8',',','1',';','2','4',',','1',',','1','8','9',',','1','\n','2','2',',','1',',','1','9','0',',','1','\n','1','6',',','1',',','2','1','4',',','1','\n','1','4',',','1',',','2','3','1',',','1','\n','1','1',',','1',',','2','5','0',',','1','\n','2','4',',','1',',','1','8','9',',','1',';','7',',','1',',','2','7','9',',','1','\n','6',',','1',',','2','8','1',',','1','\n','2',',','1',',','3','8','5',',','1','\n','0',',','4',',','3','8','6',',','1','\n','7','2',',','1',',','9','1',',','1','\n','6','8',',','1',',','9','8',',','1','\n','5','1',',','1',',','1','2','9',',','1','\n','5','1',',','1',',','1','2','8',',','1','\n','4','8',',','1',',','1','3','3',',','1','\n','3','6',',','1',',','1','5','7',',','1','\n','3','1',',','1',',','1','6','3',',','1','\n','2','8',',','1',',','1','7','9',',','1','\n','2','5',',','1',',','1','8','7',',','1','\n','2','4',',','1',',','1','8','8',',','1',';','2','3',',','1',',','1','8','9',',','1','\n','1','7',',','1',',','2','1','3',',','1','\n','1','5',',','1',',','2','2','2',',','1','\n','1','4',',','1',',','2','3','0',',','1','\n','1','0',',','1',',','2','5','0',',','1','\n','2',',','1',',','3','8','4',',','1','\n','1',',','2',',','3','8','5',',','1',';','0',',','1',',','4','2','4',',','1','\n','0',',','1',',','4','2','3',',','1','\n','6','1',',','1',',','1','1','4',',','1','\n','3','8',',','1',',','1','5','6',',','1','\n','2','8',',','1',',','1','7','8',',','1','\n','2','4',',','1',',','1','8','7',',','1','\n','2','2',',','1',',','1','8','9',',','1','\n','2','0',',','1',',','2','0','2',',','1','\n','1','6',',','1',',','2','1','3',',','1','\n','1','1',',','1',',','2','4','9',',','1','\n','8',',','1',',','2','6','8',',','1','\n','6','7',',','1',',','9','8',',','1',';','0',',','2',',','7',',','1',',','2','6','7',',','1','\n','5','7',',','1',',','1','1','8',',','1','\n','4','6',',','1',',','1','3','9',',','1','\n','3','7',',','1',',','1','5','6',',','1']
    · rfl
    · rfl
    · decide
  · have hs : "0,1,426,1;0,4,391,1".splitOn ";"=["0,1,426,1","0,4,391,1"] := by
      simp +decide [String.splitOn,String.splitOnAux]
    have hm0 : (("0,1,426,1".splitOn ",").map (fun n=>n.toNat?.getD 0))=[0,1,426,1] := by
      have hx : "0,1,426,1".splitOn ","=["0","1","426","1"] := by simp +decide [String.splitOn,String.splitOnAux]
      rw [hx]
      simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
    have hm1 : (("0,4,391,1".splitOn ",").map (fun n=>n.toNat?.getD 0))=[0,4,391,1] := by
      have hx : "0,4,391,1".splitOn ","=["0","4","391","1"] := by simp +decide [String.splitOn,String.splitOnAux]
      rw [hx]
      simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
    change _ = (("0,1,426,1;0,4,391,1".splitOn ";").map _).sum
    rw [hs]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
    change _ = (if "0,1,426,1"="" then 1 else _) + ((if "0,4,391,1"="" then 1 else _) + (0))
    simp only [if_neg (by decide : "0,1,426,1"≠""),if_neg (by decide : "0,4,391,1"≠"")]
    rw [hm0,hm1]
    change _ = ((MvPolynomial.X (atomIndex .h0))^1 * ((MvPolynomial.X (⟨426,by decide⟩ : Fin generators.count))^1 * ((1 : MvPolynomial (Fin generators.count) (ZMod 2))))) + (((MvPolynomial.X (atomIndex .h0))^4 * ((MvPolynomial.X (atomIndex .x_125_9_2))^1 * ((1 : MvPolynomial (Fin generators.count) (ZMod 2))))) + ((0 : MvPolynomial (Fin generators.count) (ZMod 2))))
    ring

private theorem nativeCoreB3 :
    (sourceAtom .h0).val^2 * (sourceAtom .h6).val * (Ideal.Quotient.mk _ (MvPolynomial.X (⟨89,by decide⟩ : Fin generators.count))) + (sourceAtom .h0).val^5 * (sourceAtom .x_125_8).val = 0 := by
  change Ideal.Quotient.mk _ ((MvPolynomial.X (atomIndex .h0) : MvPolynomial (Fin generators.count) (ZMod 2))^2 * MvPolynomial.X (atomIndex .h6) * MvPolynomial.X (⟨89,by decide⟩ : Fin generators.count) + MvPolynomial.X (atomIndex .h0)^5 * MvPolynomial.X (atomIndex .x_125_8)) = 0
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply Ideal.subset_span
  refine ⟨"0,2,69,1,89,1;0,5,375,1",?_,?_⟩
  · apply nativeCoreFromChunk (i := ⟨9,by decide⟩)
    apply nativeCoreMiddleMember _ "0,2,69,1,89,1;0,5,375,1" ['2','4',',','1',',','1','7','4',',','1','\n','1','2',',','1',',','2','3','1',',','1','\n','1','0',',','1',',','2','3','5',',','1','\n','4','8',',','1',',','1','2','2',',','1',';','7',',','1',',','2','6','1',',','1','\n','7',',','1',',','2','6','1',',','1',';','1',',','2',',','3','5','1',',','1','\n','9',',','1',',','2','3','9',',','1',';','0',',','1',',','1','8',',','1',',','1','8','8',',','1','\n','0',',','1',',','1','8',',','1',',','1','8','8',',','1',';','0',',','2',',','3','7','1',',','1','\n','0',',','2',',','3','7','1',',','1',';','0',',','2',',','6','9',',','1',',','7','9',',','1','\n','6','4',',','1',',','9','4',',','1','\n','4','8',',','1',',','1','2','1',',','1','\n','4','6',',','1',',','1','3','1',',','1','\n','4','5',',','1',',','1','3','2',',','1','\n','2','3',',','1',',','1','7','4',',','1','\n','2','0',',','1',',','1','9','1',',','1','\n','1','2',',','1',',','2','3','0',',','1','\n','0',',','3',',','3','6','5',',','1','\n','6','4',',','1',',','9','3',',','1','\n','6','4',',','1',',','9','2',',','1','\n','4','8',',','1',',','1','2','0',',','1','\n','4','6',',','1',',','1','3','0',',','1','\n','4','5',',','1',',','1','3','1',',','1','\n','2','2',',','1',',','1','7','4',',','1','\n','2','0',',','1',',','1','9','0',',','1','\n','1','9',',','1',',','1','9','1',',','1','\n','6',',','1',',','2','6','3',',','1','\n','2',',','1',',','1','3',',','1',',','2','0','9',',','1','\n','1',',','1',',','3','7','0',',','1','\n','0',',','1',',','3','8','5',',','1','\n','0',',','3',',','3','6','3',',','1','\n','6','4',',','1',',','9','1',',','1','\n','6','1',',','1',',','1','0','1',',','1','\n','5','7',',','1',',','1','1','4',',','1','\n','5','4',',','1',',','1','1','5',',','1','\n','4','6',',','1',',','1','2','9',',','1','\n','4','6',',','1',',','1','2','8',',','1','\n','4','5',',','1',',','1','3','0',',','1','\n','3','5',',','1',',','1','5','5',',','1','\n','2','8',',','1',',','1','6','4',',','1','\n','2','6',',','1',',','1','7','0',',','1','\n','1','9',',','1',',','1','9','0',',','1','\n','1','1',',','1',',','2','3','4',',','1','\n','6',',','1',',','2','6','2',',','1','\n','2',',','1',',','3','5','0',',','1','\n','2',',','1',',','3','4','9',',','1','\n','0',',','1',',','3','8','4',',','1','\n','0',',','2',',','3','7','0',',','1','\n','6','3',',','1',',','9','4',',','1','\n','4','5',',','1',',','1','2','9',',','1','\n','4','5',',','1',',','1','2','8',',','1','\n','3','4',',','1',',','1','5','5',',','1','\n','2','6',',','1',',','1','6','9',',','1','\n','2','0',',','1',',','1','8','9',',','1','\n','1','7',',','1',',','2','0','2',',','1','\n','1','4',',','1',',','2','1','6',',','1','\n','1','0',',','1',',','2','3','4',',','1','\n','6',',','1',',','2','6','1',',','1','\n','2',',','1',',','3','4','8',',','1','\n','5',',','1',',','2','7','5',',','1',';','1',',','1',',','3','6','9',',','1','\n','1',',','2',',','3','4','9',',','1','\n','0',',','1',',','8',',','1',',','2','5','0',',','1','\n','6','3',',','1',',','9','3',',','1','\n','6','3',',','1',',','9','2',',','1','\n','5','7',',','1',',','1','1','3',',','1','\n','4','2',',','1',',','1','3','9',',','1','\n','4','1',',','1',',','1','4','3',',','1','\n','3','3',',','1',',','1','5','5',',','1','\n','2','6',',','1',',','1','6','8',',','1','\n','1','9',',','1',',','1','8','9',',','1','\n','1','6',',','1',',','2','0','2',',','1','\n','1','2',',','1',',','2','2','9',',','1','\n','0',',','1',',','3','8','3',',','1','\n','0',',','8',',','3','1','2',',','1','\n','6','3',',','1',',','9','1',',','1','\n','5','7',',','1',',','1','1','2',',','1','\n','4','1',',','1',',','1','4','2',',','1','\n','3','2',',','1',',','1','5','5',',','1','\n','2','6',',','1',',','1','6','7',',','1','\n','2','5',',','1',',','1','7','3',',','1','\n','2','5',',','1',',','1','7','2',',','1','\n','7','2',',','1',',','8','0',',','1',';','2','0',',','1',',','1','8','7',',','1','\n','2','0',',','1',',','1','8','7',',','1',';','1','7',',','1',',','2','0','1',',','1','\n','1','9',',','1',',','1','8','8',',','1',';','1','7',',','1',',','2','0','1',',','1',';','1','5',',','1',',','2','0','9',',','1','\n','1','7',',','1',',','2','0','1',',','1',';','1','5',',','1',',','2','0','9',',','1',';','8',',','1',',','2','5','5',',','1','\n','1','5',',','1',',','2','0','9',',','1',';','2',',','1',',','3','4','7',',','1','\n','1','3',',','1',',','2','2','6',',','1',';','2',',','1',',','3','4','6',',','1','\n','7',',','1',',','2','6','0',',','1',';','2',',','1',',','3','4','7',',','1',';','2',',','1',',','3','4','6',',','1',';','0',',','1',',','3','8','2',',','1','\n','2',',','1',',','3','4','7',',','1',';','0',',','1',',','3','8','2',',','1',';','0',',','3',',','3','5','9',',','1','\n','0',',','1',',','3','8','2',',','1',';','0',',','3',',','3','5','9',',','1',';','0',',','4',',','3','4','9',',','1','\n','7','2',',','1',',','7','9',',','1',';','6','4',',','1',',','8','9',',','1',';','4','8',',','1',',','1','1','9',',','1','\n','3','5',',','1',',','1','5','4',',','1','\n','2','6',',','1',',','1','6','6',',','1','\n','2','4',',','1',',','1','7','3',',','1','\n','2','4',',','1',',','1','7','2',',','1','\n','6','4',',','1',',','8','9',',','1',';','1','9',',','1',',','1','8','7',',','1','\n','4','8',',','1',',','1','1','9',',','1',';','1','9',',','1',',','1','8','7',',','1',';','1','6',',','1',',','2','0','1',',','1','\n','1','6',',','1',',','2','0','1',',','1',';','8',',','1',',','2','5','4',',','1','\n','1','9',',','1',',','1','8','7',',','1',';','8',',','1',',','2','5','4',',','1',';','1',',','2',',','3','4','7',',','1','\n','0',',','1',',','3','8','1',',','1','\n','6','4',',','1',',','9','0',',','1',';','8',',','1',',','2','5','4',',','1',';','1',',','2',',','3','4','7',',','1',';','0',',','3',',','3','5','8',',','1','\n','5','2',',','1',',','1','1','8',',','1','\n','4','3',',','1',',','1','3','8',',','1',';','3','4',',','1',',','1','5','4',',','1','\n','3','4',',','1',',','1','5','4',',','1',';','2','3',',','1',',','1','7','2',',','1','\n','2','1',',','1',',','1','7','9',',','1','\n','1','2',',','1',',','2','2','8',',','1','\n','1','1',',','1',',','2','3','3',',','1','\n','2','3',',','1',',','1','7','3',',','1',';','2','3',',','1',',','1','7','2',',','1',';','8',',','1',',','1','3',',','2',',','8','0',',','1','\n','2','3',',','1',',','1','7','2',',','1',';','0',',','3',',','3','5','5',',','1','\n','0',',','3',',','3','5','5',',','1',';','0',',','3',',','1','7',',','1',',','1','8','8',',','1','\n','5','1',',','1',',','1','1','8',',','1',';','4','6',',','1',',','1','2','7',',','1','\n','4','6',',','1',',','1','2','6',',','1','\n','3','3',',','1',',','1','5','4',',','1','\n','4','6',',','1',',','1','2','7',',','1',';','2','2',',','1',',','1','7','3',',','1','\n','2','2',',','1',',','1','7','2',',','1','\n','2','1',',','1',',','1','7','8',',','1','\n','2','2',',','1',',','1','7','3',',','1',';','2','0',',','1',',','1','8','6',',','1','\n','1','1',',','1',',','2','3','2',',','1','\n','1','0',',','1',',','2','3','3',',','1','\n','2','0',',','1',',','1','8','6',',','1',';','8',',','2',',','1','3',',','1',',','1','0','1',',','1','\n','7',',','1',',','2','5','9',',','1','\n','4','3',',','1',',','1','3','7',',','1',';','0',',','4',',','3','4','7',',','1','\n','6','3',',','1',',','9','0',',','1',';','6','3',',','1',',','8','9',',','1','\n','6','1',',','1',',','1','0','0',',','1','\n','6','3',',','1',',','8','9',',','1',';','6','0',',','1',',','1','0','1',',','1','\n','5','9',',','1',',','1','0','1',',','1','\n','6','0',',','1',',','1','0','1',',','1',';','4','5',',','1',',','1','2','7',',','1','\n','4','5',',','1',',','1','2','6',',','1','\n','4','5',',','1',',','1','2','7',',','1',';','3','2',',','1',',','1','5','4',',','1','\n','3','2',',','1',',','1','5','4',',','1',';','2','9',',','1',',','1','6','2',',','1','\n','2','7',',','1',',','1','6','4',',','1','\n','2','1',',','1',',','1','7','7',',','1','\n','2','9',',','1',',','1','6','2',',','1',';','1','9',',','1',',','1','8','6',',','1','\n','1','0',',','1',',','2','3','2',',','1','\n','1','9',',','1',',','1','8','6',',','1',';','8',',','2',',','1','7','3',',','1','\n','7',',','1',',','2','5','8',',','1','\n','6',',','1',',','2','6','0',',','1',';','0',',','1',',','3','8','0',',','1','\n','6','9',',','1',',','8','7',',','1','\n','3','1',',','1',',','1','5','5',',','1','\n','5',',','1',',','2','7','4',',','1','\n','1','4',',','1',',','2','1','5',',','1',';','1',',','1',',','5',',','1',',','2','6','0',',','1','\n','6','2',',','1',',','9','6',',','1','\n','4','4',',','1',',','1','3','4',',','1','\n','4','3',',','1',',','1','3','6',',','1','\n','4','1',',','1',',','1','4','1',',','1','\n','2','1',',','1',',','1','7','6',',','1','\n','7',',','1',',','2','5','7',',','1',';','0',',','7',',','3','1','7',',','1','\n','5','6',',','1',',','1','1','4',',','1','\n','4','4',',','1',',','1','3','3',',','1','\n','1','5',',','1',',','2','0','8',',','1','\n','4','2',',','1',',','1','3','8',',','1',';','8',',','4',',','6','4',',','1','\n','6',',','1',',','2','5','9',',','1','\n','2',',','1',',','3','4','5',',','1','\n','5','8',',','1',',','1','0','7',',','1','\n','5','5',',','1',',','1','1','4',',','1','\n','6','4',',','1',',','8','8',',','1',';','4','2',',','1',',','1','3','7',',','1','\n','1','5',',','1',',','2','0','7',',','1','\n','6',',','1',',','2','5','8',',','1','\n','2',',','1',',','3','4','4',',','1','\n','0',',','1',',','8',',','1',',','2','4','5',',','1','\n','6','2',',','1',',','9','5',',','1','\n','5','8',',','1',',','1','0','6',',','1','\n','5','8',',','1',',','1','0','5',',','1','\n','5','7',',','1',',','1','1','1',',','1','\n','5','6',',','1',',','1','1','3',',','1',';','5','0',',','1',',','1','1','8',',','1','\n','5','0',',','1',',','1','1','8',',','1',';','4','0',',','1',',','1','4','7',',','1','\n','4','0',',','1',',','1','4','7',',','1',';','3','1',',','1',',','1','5','4',',','1','\n','3','1',',','1',',','1','5','4',',','1',';','2','0',',','1',',','1','8','5',',','1','\n','2','0',',','1',',','1','8','5',',','1',';','8',',','1',',','1','7',',','1',',','1','3','8',',','1','\n','0',',','9',',','2','9','9',',','1','\n','7','2',',','1',',','7','8',',','1',';','7','1',',','1',',','8','0',',','1','\n','6','8',',','1',',','8','7',',','1','\n','5','8',',','1',',','1','0','4',',','1','\n','5','8',',','1',',','1','0','3',',','1','\n','5','7',',','1',',','1','1','0',',','1','\n','7','1',',','1',',','8','0',',','1',';','5','6',',','1',',','1','1','2',',','1','\n','5','5',',','1',',','1','1','3',',','1',';','4','9',',','1',',','1','1','8',',','1','\n','4','7',',','1',',','1','2','4',',','1','\n','5','6',',','1',',','1','1','2',',','1',';','4','0',',','1',',','1','4','6',',','1','\n','4','9',',','1',',','1','1','8',',','1',';','3','9',',','1',',','1','4','7',',','1','\n','4','0',',','1',',','1','4','6',',','1',';','3','9',',','1',',','1','4','7',',','1',';','3','0',',','1',',','1','6','0',',','1','\n','2','5',',','1',',','1','7','1',',','1','\n','3','9',',','1',',','1','4','7',',','1',';','3','0',',','1',',','1','6','0',',','1',';','2','0',',','1',',','1','8','4',',','1','\n','3','0',',','1',',','1','6','0',',','1',';','2','0',',','1',',','1','8','4',',','1',';','1','9',',','1',',','1','8','5',',','1','\n','2','0',',','1',',','1','8','4',',','1',';','1','9',',','1',',','1','8','5',',','1',';','1','5',',','1',',','2','0','6',',','1','\n','1','9',',','1',',','1','8','5',',','1',';','1','3',',','1',',','2','2','5',',','1','\n','1','3',',','1',',','2','2','5',',','1',';','9',',','1',',','2','3','8',',','1','\n','9',',','1',',','2','3','8',',','1',';','8',',','1',',','1','6',',','1',',','1','3','8',',','1','\n','1','5',',','1',',','2','0','6',',','1',';','6',',','1',',','2','5','7',',','1','\n','6',',','1',',','2','5','7',',','1',';','2',',','1',',','3','4','3',',','1','\n','2',',','1',',','3','4','3',',','1',';','0',',','1',',','8',',','1',',','2','4','4',',','1','\n','7','2',',','1',',','7','7',',','1',';','7','1',',','1',',','7','9',',','1','\n','6','7',',','1',',','8','7',',','1','\n','6','3',',','1',',','8','8',',','1',';','6','0',',','1',',','1','0','0',',','1','\n','5','9',',','1',',','1','0','0',',','1','\n','7','1',',','1',',','7','9',',','1',';','5','5',',','1',',','1','1','2',',','1','\n','6','0',',','1',',','1','0','0',',','1',';','4','6',',','1',',','1','2','5',',','1','\n','4','6',',','1',',','1','2','5',',','1',';','4','2',',','1',',','1','3','6',',','1','\n','5','5',',','1',',','1','1','2',',','1',';','3','9',',','1',',','1','4','6',',','1','\n','2','4',',','1',',','1','7','1',',','1','\n','3','9',',','1',',','1','4','6',',','1',';','1','9',',','1',',','1','8','4',',','1','\n','1','9',',','1',',','1','8','4',',','1',';','1','3',',','1',',','2','2','4',',','1','\n','1','3',',','1',',','2','2','4',',','1',';','9',',','1',',','2','3','7',',','1','\n','9',',','1',',','2','3','7',',','1',';','8',',','1',',','1','6',',','1',',','1','3','7',',','1','\n','4','2',',','1',',','1','3','6',',','1',';','8',',','4',',','1','7',',','1',',','2','0',',','1','\n','5','2',',','1',',','1','1','7',',','1','\n','3','5',',','1',',','1','5','3',',','1','\n','4','5',',','1',',','1','2','5',',','1',';','2','3',',','1',',','1','7','1',',','1','\n','2','3',',','1',',','1','7','1',',','1',';','8',',','5',',','4','0',',','1','\n','5','2',',','1',',','1','1','6',',','1','\n','3','5',',','1',',','1','5','2',',','1','\n','3','4',',','1',',','1','5','3',',','1','\n','5','1',',','1',',','1','1','7',',','1',';','2','9',',','1',',','1','6','1',',','1','\n','2','9',',','1',',','1','6','1',',','1',';','2','2',',','1',',','1','7','1',',','1','\n','2','2',',','1',',','1','7','1',',','1',';','8',',','5',',','3','9',',','1','\n','0',',','4',',','3','4','3',',','1','\n','6','6',',','1',',','8','7',',','1','\n','3','4',',','1',',','1','5','2',',','1','\n','3','3',',','1',',','1','5','3',',','1','\n','5','1',',','1',',','1','1','6',',','1',';','1','3',',','1',',','2','2','3',',','1','\n','1','3',',','1',',','2','2','3',',','1',';','8',',','2',',','1','7','1',',','1','\n','3','3',',','1',',','1','5','2',',','1','\n','3','2',',','1',',','1','5','3',',','1',';','8',',','2',',','1','7',',','1',',','7','8',',','1','\n','3','2',',','1',',','1','5','2',',','1',';','8',',','3',',','1','1','7',',','1','\n','2','6',',','1',',','1','6','5',',','1','\n','5','6',',','1',',','1','1','1',',','1',';','5','0',',','1',',','1','1','7',',','1','\n','5','0',',','1',',','1','1','7',',','1',';','2','0',',','1',',','1','8','3',',','1','\n','2','0',',','1',',','1','8','3',',','1',';','1','7',',','1',',','2','0','0',',','1','\n','7','1',',','1',',','7','8',',','1',';','5','6',',','1',',','1','1','0',',','1','\n','5','6',',','1',',','1','1','0',',','1',';','5','5',',','1',',','1','1','1',',','1','\n','5','5',',','1',',','1','1','1',',','1',';','5','0',',','1',',','1','1','6',',','1','\n','5','0',',','1',',','1','1','6',',','1',';','4','9',',','1',',','1','1','7',',','1','\n','4','9',',','1',',','1','1','7',',','1',';','4','0',',','1',',','1','4','5',',','1','\n','4','0',',','1',',','1','4','5',',','1',';','3','1',',','1',',','1','5','3',',','1','\n','3','1',',','1',',','1','5','3',',','1',';','2','0',',','1',',','1','8','2',',','1','\n','2','0',',','1',',','1','8','2',',','1',';','1','9',',','1',',','1','8','3',',','1','\n','1','9',',','1',',','1','8','3',',','1',';','1','7',',','1',',','1','9','9',',','1','\n','1','7',',','1',',','1','9','9',',','1',';','1','6',',','1',',','2','0','0',',','1','\n','1','6',',','1',',','2','0','0',',','1',';','8',',','1',',','2','5','3',',','1','\n','7','1',',','1',',','7','7',',','1',';','5','5',',','1',',','1','1','0',',','1','\n','5','5',',','1',',','1','1','0',',','1',';','4','9',',','1',',','1','1','6',',','1','\n','4','9',',','1',',','1','1','6',',','1',';','3','9',',','1',',','1','4','5',',','1','\n','3','9',',','1',',','1','4','5',',','1',';','3','1',',','1',',','1','5','2',',','1','\n','3','1',',','1',',','1','5','2',',','1',';','1','9',',','1',',','1','8','2',',','1','\n','1','9',',','1',',','1','8','2',',','1',';','1','6',',','1',',','1','9','9',',','1','\n','1','6',',','1',',','1','9','9',',','1',';','9',',','1',',','2','3','6',',','1','\n','9',',','1',',','2','3','6',',','1',';','8',',','1',',','2','5','2',',','1','\n','7',',','1',',','2','5','6',',','1','\n','6','5',',','1',',','8','7',',','1','\n','5','8',',','1',',','1','0','2',',','1','\n','4','7',',','1',',','1','2','3',',','1','\n','4','1',',','1',',','1','4','0',',','1','\n','3','0',',','1',',','1','5','9',',','1','\n','2','1',',','1',',','1','7','5',',','1','\n','1','5',',','1',',','2','0','5',',','1','\n','1','2',',','1',',','2','2','7',',','1','\n','6',',','1',',','2','5','6',',','1','\n','4',',','1',',','2','9','0',',','1','\n','2',',','1',',','3','4','2',',','1','\n','1',',','2',',','3','4','2',',','1','\n','0',',','1',',','3','7','9',',','1','\n','6','9',',','1',',','9','4',',','1','\n','6','9',',','1',',','9','2',',','1','\n','1',',','1',',','4','0','0',',','1','\n','6','9',',','1',',','9','1',',','1','\n','4','3',',','1',',','1','4','3',',','1','\n','7',',','1',',','2','7','3',',','1','\n','1',',','1',',','3','9','9',',','1','\n','1',',','1',',','3','9','8',',','1','\n','4','3',',','1',',','1','4','2',',','1','\n','1','1',',','1',',','2','4','2',',','1','\n','3',',','1',',','3','2','3',',','1','\n','1','8',',','1',',','1','9','8',',','1',';','3',',','1',',','6','8',',','1',',','6','9',',','1','\n','1',',','1',',','3','9','7',',','1','\n','1',',','1',',','3','9','6',',','1','\n','1',',','2',',','3','6','8',',','1','\n','0',',','2',',','3','9','8',',','1','\n','0',',','3',',','3','7','8',',','1','\n','1','1',',','1',',','2','4','1',',','1','\n','1','0',',','1',',','2','4','2',',','1','\n','7',',','1',',','2','7','2',',','1','\n','1','8',',','1',',','1','9','7',',','1',';','3',',','1',',','6','7',',','1',',','6','9',',','1','\n','1',',','1',',','3','9','5',',','1',';','1',',','1',',','3','9','4',',','1','\n','3',',','1',',','6','7',',','1',',','6','9',',','1',';','1',',','1',',','3','9','2',',','1','\n','2',',','1',',','3','6','7',',','1',';','1',',','1',',','3','9','4',',','1',';','1',',','1',',','3','9','3',',','1',';','0',',','1',',','4','1','5',',','1','\n','0',',','2',',','3','9','7',',','1','\n','1',',','1',',','3','9','4',',','1',';','1',',','1',',','3','9','2',',','1',';','0',',','2',',','3','9','6',',','1','\n','0',',','3',',','3','7','7',',','1','\n','1','3',',','1',',','2','3','1',',','1','\n','1','1',',','1',',','2','4','0',',','1','\n','1','0',',','1',',','2','4','1',',','1','\n','7',',','1',',','2','7','1',',','1','\n','7',',','1',',','2','7','0',',','1','\n','6','8',',','1',',','9','4',',','1',';','1',',','1',',','3','9','1',',','1','\n','3',',','1',',','3','2','2',',','1',';','1',',','1',',','3','9','1',',','1',';','1',',','1',',','3','9','0',',','1','\n','1',',','1',',','3','9','1',',','1',';','1',',','1',',','3','9','0',',','1',';','1',',','1',',','6','9',',','1',',','8','2',',','1','\n','1',',','1',',','6','9',',','1',',','8','2',',','1',';','1',',','1',',','1','8',',','1',',','1','9','0',',','1','\n','2',',','1',',','3','6','6',',','1',';','0',',','1',',','4','1','4',',','1','\n','1',',','1',',','3','9','0',',','1',';','1',',','1',',','1','8',',','1',',','1','9','0',',','1',';','0',',','2',',','3','9','4',',','1','\n','1',',','1',',','1','8',',','1',',','1','9','0',',','1',';','0',',','2',',','3','9','2',',','1','\n','6','9',',','1',',','9','0',',','1',';','6','9',',','1',',','8','9',',','1','\n','6','8',',','1',',','9','3',',','1','\n','6','7',',','1',',','9','4',',','1','\n','3','5',',','1',',','1','5','8',',','1','\n','1','8',',','1',',','1','9','6',',','1','\n','1','3',',','1',',','2','3','0',',','1','\n','1','0',',','1',',','2','4','0',',','1','\n','6',',','1',',','2','7','3',',','1','\n','3',',','2',',','2','7','0',',','1','\n','3',',','1',',','3','2','1',',','1',';','1',',','1',',','3','8','9',',','1','\n','7',',','1',',','2','6','9',',','1',';','1',',','1',',','3','8','8',',','1','\n','1',',','2',',','3','6','6',',','1','\n','6','8',',','1',',','9','2',',','1',';','1',',','1',',','3','8','9',',','1',';','1',',','1',',','3','8','8',',','1',';','0',',','1',',','4','1','3',',','1','\n','0',',','1',',','4','1','2',',','1','\n','0',',','1',',','4','1','3',',','1',';','0',',','2',',','3','9','1',',','1','\n','0',',','2',',','3','9','0',',','1','\n','6','8',',','1',',','9','1',',','1',';','6','7',',','1',',','9','3',',','1','\n','4','2',',','1',',','1','4','3',',','1','\n','3','4',',','1',',','1','5','8',',','1','\n','6','7',',','1',',','9','3',',','1',';','2','6',',','1',',','1','7','4',',','1','\n','2','3',',','1',',','2','4',',','1',',','6','9',',','1','\n','1','1',',','1',',','2','3','9',',','1','\n','2','6',',','1',',','1','7','4',',','1',';','2',',','1',',','3','6','5',',','1','\n','6','7',',','1',',','9','2',',','1',';','2',',','1',',','3','6','5',',','1',';','1',',','1',',','3','8','7',',','1','\n','3',',','1',',','3','2','0',',','1',';','1',',','1',',','3','8','6',',','1','\n','1',',','1',',','1','8',',','1',',','1','8','9',',','1','\n','0',',','1',',','4','1','1',',','1','\n','2',',','1',',','3','6','5',',','1',';','0',',','1',',','4','1','0',',','1','\n','1',',','1',',','3','8','6',',','1',';','0',',','2',',','3','8','9',',','1',';','0',',','4',',','3','6','7',',','1','\n','4','2',',','1',',','1','4','2',',','1','\n','3','3',',','1',',','1','5','8',',','1','\n','6','7',',','1',',','9','1',',','1',';','1','8',',','1',',','1','9','5',',','1','\n','1','0',',','1',',','2','3','9',',','1','\n','6',',','1',',','2','7','2',',','1','\n','1','8',',','1',',','1','9','5',',','1',';','3',',','1',',','6','8',',','2','\n','2',',','1',',','3','6','4',',','1','\n','3',',','1',',','6','8',',','2',';','2',',','1',',','3','6','3',',','1','\n','0',',','1',',','4','0','8',',','1','\n','2',',','1',',','3','6','3',',','1',';','0',',','2',',','3','8','6',',','1','\n','0',',','3',',','6','9',',','1',',','8','0',',','1','\n','7','6',',','1',',','8','0',',','1','\n','6','6',',','1',',','9','4',',','1','\n','6','4',',','1',',','9','6',',','1','\n','6','1',',','1',',','1','0','7',',','1','\n','5','2',',','1',',','1','2','2',',','1','\n','4','3',',','1',',','1','4','1',',','1','\n','3','5',',','1',',','1','5','7',',','1','\n','3','2',',','1',',','1','5','8',',','1','\n','2','5',',','1',',','1','7','9',',','1','\n','1','7',',','1',',','2','0','4',',','1','\n','1','7',',','1',',','2','0','3',',','1','\n','7',',','1',',','2','6','8',',','1','\n','6',',','1',',','2','7','1',',','1','\n','6',',','1',',','2','7','0',',','1','\n','5',',','1',',','2','8','2',',','1','\n','3',',','1',',','3','1','9',',','1','\n','3',',','1',',','6','7',',','1',',','6','8',',','1',';','0',',','1',',','4','0','7',',','1','\n','7','6',',','1',',','7','9',',','1','\n','7','5',',','1',',','8','0',',','1','\n','7','4',',','1',',','8','0',',','1','\n','6','6',',','1',',','9','3',',','1','\n','6','6',',','1',',','9','2',',','1','\n','6','1',',','1',',','1','0','6',',','1','\n','6','1',',','1',',','1','0','5',',','1','\n','5','7',',','1',',','1','1','5',',','1','\n','5','2',',','1',',','1','2','1',',','1','\n','5','1',',','1',',','1','2','2',',','1','\n','3','8',',','1',',','1','5','1',',','1','\n','3','4',',','1',',','1','5','7',',','1','\n','2','5',',','1',',','1','7','8',',','1','\n','2','4',',','1',',','1','7','9',',','1','\n','1','6',',','1',',','2','0','4',',','1','\n','1','6',',','1',',','2','0','3',',','1','\n','1','3',',','1',',','2','2','9',',','1','\n','6',',','1',',','2','6','9',',','1','\n','5',',','1',',','2','8','1',',','1','\n','3',',','1',',','6','7',',','2','\n','2',',','1',',','3','6','2',',','1','\n','2',',','1',',','3','6','1',',','1','\n','0',',','1',',','4','0','6',',','1','\n','7','5',',','1',',','7','9',',','1','\n','7','4',',','1',',','7','9',',','1','\n','7','3',',','1',',','8','0',',','1','\n','7','2',',','1',',','8','6',',','1','\n','6','8',',','1',',','8','9',',','1','\n','6','6',',','1',',','9','1',',','1','\n','6','1',',','1',',','1','0','4',',','1','\n','6','1',',','1',',','1','0','3',',','1','\n','5','2',',','1',',','1','2','0',',','1','\n','5','1',',','1',',','1','2','1',',','1','\n','3','8',',','1',',','1','5','0',',','1','\n','3','7',',','1',',','1','5','1',',','1','\n','3','3',',','1',',','1','5','7',',','1','\n','2','5',',','1',',','1','7','7',',','1','\n','2','4',',','1',',','1','7','8',',','1','\n','2','3',',','1',',','1','7','9',',','1','\n','1','5',',','1',',','2','1','4',',','1','\n','1','4',',','1',',','2','2','2',',','1','\n','1','2',',','1',',','2','3','5',',','1','\n','9',',','1',',','2','4','3',',','1','\n','4',',','1',',','2','9','4',',','1','\n','6','8',',','1',',','9','0',',','1',';','3',',','2',',','2','6','7',',','1','\n','2',',','1',',','3','6','0',',','1','\n','1',',','1',',','3','8','4',',','1','\n','1',',','2',',','3','6','1',',','1','\n','7','3',',','1',',','7','9',',','1','\n','7','2',',','1',',','8','5',',','1','\n','7','2',',','1',',','8','4',',','1','\n','6','7',',','1',',','8','9',',','1','\n','6','4',',','1',',','9','5',',','1','\n','6','3',',','1',',','9','6',',','1','\n','5','1',',','1',',','1','2','0',',','1','\n','4','6',',','1',',','1','3','4',',','1','\n','4','0',',','1',',','1','4','8',',','1','\n','3','7',',','1',',','1','5','0',',','1','\n','3','2',',','1',',','1','5','7',',','1','\n','3','0',',','1',',','1','6','3',',','1','\n','2','9',',','1',',','1','6','4',',','1','\n','2','4',',','1',',','1','7','7',',','1','\n','2','3',',','1',',','1','7','8',',','1','\n','2','2',',','1',',','1','7','9',',','1','\n','2','0',',','1',',','1','9','2',',','1','\n','1','8',',','1',',','1','9','4',',','1','\n','3',',','1',',','3','1','8',',','1','\n','6','7',',','1',',','9','0',',','1',';','3',',','2',',','2','6','6',',','1','\n','3',',','2',',','2','6','6',',','1',';','2',',','1',',','3','5','9',',','1','\n','2',',','1',',','1','3',',','1',',','2','1','2',',','1','\n','1',',','1',',','8',',','1',',','2','5','0',',','1','\n','1',',','2',',','3','6','0',',','1','\n','7','2',',','1',',','8','3',',','1','\n','4','5',',','1',',','1','3','4',',','1','\n','3','9',',','1',',','1','4','8',',','1','\n','7','2',',','1',',','8','2',',','1',';','3','6',',','1',',','1','5','1',',','1','\n','3','6',',','1',',','1','5','1',',','1',';','3','5',',','1',',','1','5','6',',','1','\n','3','5',',','1',',','1','5','6',',','1',';','2','8',',','1',',','1','7','0',',','1','\n','2','8',',','1',',','1','7','0',',','1',';','2','5',',','1',',','1','7','6',',','1','\n','2','3',',','1',',','1','7','7',',','1','\n','2','2',',','1',',','1','7','8',',','1','\n','1','9',',','1',',','1','9','2',',','1','\n','6','9',',','1',',','8','8',',','1',';','1','8',',','1',',','1','9','3',',','1','\n','1','5',',','1',',','2','1','3',',','1','\n','2','5',',','1',',','1','7','6',',','1',';','1','3',',','1',',','2','2','8',',','1','\n','4','6',',','1',',','1','3','3',',','1',';','9',',','1',',','1','3',',','2',',','7','5',',','1','\n','6',',','1',',','2','6','8',',','1','\n','1','8',',','1',',','1','9','3',',','1',';','5',',','1',',','2','8','0',',','1','\n','5',',','1',',','2','8','0',',','1',';','4',',','1',',','2','9','3',',','1','\n','2',',','1',',','3','5','8',',','1','\n','1','3',',','1',',','2','2','8',',','1',';','2',',','1',',','3','5','7',',','1','\n','4',',','1',',','2','9','3',',','1',';','1',',','1',',','3','8','3',',','1','\n','2',',','1',',','3','5','7',',','1',';','1',',','2',',','3','5','9',',','1','\n','7','2',',','1',',','8','1',',','1','\n','4','8',',','1',',','1','2','4',',','1','\n','4','5',',','1',',','1','3','3',',','1','\n','4','2',',','1',',','1','4','1',',','1','\n','3','8',',','1',',','1','4','9',',','1','\n','3','6',',','1',',','1','5','0',',','1','\n','3','4',',','1',',','1','5','6',',','1','\n','3','1',',','1',',','1','5','8',',','1','\n','2','8',',','1',',','1','6','9',',','1','\n','2','6',',','1',',','1','7','3',',','1','\n','2','6',',','1',',','1','7','2',',','1','\n','2','4',',','1',',','1','7','6',',','1','\n','2','2',',','1',',','1','7','7',',','1','\n','2','1',',','1',',','1','8','1',',','1','\n','1','4',',','1',',','2','2','1',',','1','\n','3',',','1',',','3','1','6',',','1','\n','6',',','1',',','2','6','7',',','1',';','5',',','1',',','2','7','9',',','1',';','2',',','1',',','3','5','6',',','1','\n','3',',','1',',','3','1','7',',','1',';','2',',','1',',','3','5','5',',','1','\n','5',',','1',',','2','7','9',',','1',';','1',',','1',',','3','8','2',',','1','\n','1',',','2',',','3','5','7',',','1','\n','2',',','1',',','3','5','6',',','1',';','0',',','1',',','4','0','5',',','1','\n','1',',','1',',','3','8','2',',','1',';','0',',','1',',','2','0',',','1',',','1','8','8',',','1','\n','6','3',',','1',',','9','5',',','1','\n','6','6',',','1',',','8','9',',','1',';','5','3',',','1',',','1','1','8',',','1','\n','3','7',',','1',',','1','4','9',',','1','\n','3','3',',','1',',','1','5','6',',','1','\n','2','8',',','1',',','1','6','8',',','1','\n','1','2',',','1',',','2','3','4',',','1','\n','6','6',',','1',',','9','0',',','1',';','8',',','1',',','5','0',',','1',',','6','9',',','1','\n','6',',','1',',','2','6','6',',','1',';','4',',','1',',','2','9','2',',','1','\n','1',',','1',',','3','8','1',',','1','\n','5','3',',','1',',','1','1','8',',','1',';','4',',','1',',','2','9','2',',','1',';','0',',','1',',','8',',','1',',','2','5','5',',','1','\n','4',',','1',',','2','9','2',',','1',';','0',',','1',',','2',',','1',',','3','4','6',',','1','\n','8',',','1',',','5','0',',','1',',','6','9',',','1',';','0',',','1',',','8',',','1',',','2','5','5',',','1',';','0',',','1',',','2',',','1',',','3','4','6',',','1',';','0',',','4',',','3','5','9',',','1','\n','2','3',',','1',',','1','7','6',',','1',';','0',',','4',',','3','5','9',',','1',';','0',',','5',',','3','4','9',',','1','\n','6','0',',','1',',','1','0','7',',','1',';','5','9',',','1',',','1','0','7',',','1','\n','5','2',',','1',',','1','1','9',',','1','\n','5','0',',','1',',','1','2','2',',','1','\n','4','7',',','1',',','1','3','2',',','1','\n','3','2',',','1',',','1','5','6',',','1','\n','2','8',',','1',',','1','6','7',',','1','\n','2','2',',','1',',','1','7','6',',','1','\n','5','9',',','1',',','1','0','7',',','1',';','1','5',',','1',',','2','1','2',',','1','\n','8',',','1',',','4','9',',','1',',','6','9',',','1','\n','1','5',',','1',',','2','1','2',',','1',';','4',',','1',',','2','9','1',',','1','\n','4',',','1',',','2','9','1',',','1',';','0',',','1',',','8',',','1',',','2','5','4',',','1','\n','0',',','1',',','8',',','1',',','2','5','4',',','1',';','0',',','4',',','3','5','8',',','1','\n','6','0',',','1',',','1','0','5',',','1','\n','6','0',',','1',',','1','0','6',',','1',';','5','9',',','1',',','1','0','6',',','1','\n','5','9',',','1',',','1','0','5',',','1','\n','5','1',',','1',',','1','1','9',',','1','\n','5','0',',','1',',','1','2','1',',','1','\n','4','9',',','1',',','1','2','2',',','1','\n','4','7',',','1',',','1','3','1',',','1','\n','5','9',',','1',',','1','0','6',',','1',';','3','6',',','1',',','1','4','9',',','1','\n','3','1',',','1',',','1','5','7',',','1','\n','2','8',',','1',',','1','6','6',',','1','\n','3','6',',','1',',','1','4','9',',','1',';','0',',','4',',','1','7',',','1',',','1','8','8',',','1','\n','6','8',',','1',',','8','8',',','1','\n','6','0',',','1',',','1','0','4',',','1','\n','6','0',',','1',',','1','0','3',',','1','\n','5','9',',','1',',','1','0','4',',','1','\n','5','9',',','1',',','1','0','3',',','1','\n','4','9',',','1',',','1','2','1',',','1','\n','4','7',',','1',',','1','3','0',',','1','\n','5',',','1',',','2','7','8',',','1',';','1',',','1',',','3','8','0',',','1','\n','5','0',',','1',',','1','2','0',',','1',';','1',',','1',',','3','8','0',',','1',';','0',',','1',',','4','0','4',',','1','\n','1',',','1',',','3','8','0',',','1',';','0',',','1',',','4','0','4',',','1',';','0',',','5',',','3','4','7',',','1','\n','7','6',',','1',',','7','8',',','1','\n','6','7',',','1',',','8','8',',','1','\n','4','9',',','1',',','1','2','0',',','1','\n','4','7',',','1',',','1','2','9',',','1','\n','4','7',',','1',',','1','2','8',',','1','\n','7','6',',','1',',','7','7',',','1','\n','7','5',',','1',',','7','8',',','1','\n','7','4',',','1',',','7','8',',','1','\n','6','5',',','1',',','9','4',',','1','\n','6','2',',','1',',','9','9',',','1','\n','5','8',',','1',',','1','0','9',',','1','\n','5','6',',','1',',','1','1','5',',','1','\n','2','7',',','1',',','1','7','0',',','1','\n','1','4',',','1',',','2','2','0',',','1','\n','1','2',',','1',',','2','3','3',',','1','\n','7','5',',','1',',','7','7',',','1','\n','7','4',',','1',',','7','7',',','1','\n','7','3',',','1',',','7','8',',','1','\n','7','1',',','1',',','8','6',',','1','\n','6','5',',','1',',','9','3',',','1','\n','6','5',',','1',',','9','2',',','1','\n','5','5',',','1',',','1','1','5',',','1','\n','3','1',',','1',',','1','5','6',',','1','\n','2','7',',','1',',','1','6','9',',','1','\n','1','4',',','1',',','2','1','9',',','1','\n','1','2',',','1',',','2','3','2',',','1','\n','3',',','1',',','3','1','5',',','1','\n','0',',','1',',','8',',','3',',','1','1','8',',','1','\n','7','3',',','1',',','7','7',',','1','\n','7','1',',','1',',','8','5',',','1','\n','7','1',',','1',',','8','4',',','1','\n','7','0',',','1',',','8','7',',','1','\n','6','6',',','1',',','8','8',',','1','\n','6','5',',','1',',','9','1',',','1','\n','5','8',',','1',',','1','0','8',',','1','\n','4','1',',','1',',','1','4','4',',','1','\n','2','7',',','1',',','1','6','8',',','1','\n','2','1',',','1',',','1','8','0',',','1','\n','1','4',',','1',',','2','1','8',',','1','\n','5',',','1',',','2','7','7',',','1','\n','7','1',',','1',',','8','3',',','1','\n','7','1',',','1',',','8','2',',','1','\n','5','0',',','1',',','1','1','9',',','1','\n','2','7',',','1',',','1','6','7',',','1','\n','1','1',',','1',',','2','3','8',',','1','\n','7','1',',','1',',','8','1',',','1','\n','4','9',',','1',',','1','1','9',',','1',';','3','0',',','1',',','1','6','2',',','1','\n','3','0',',','1',',','1','6','2',',','1',';','2','7',',','1',',','1','6','6',',','1','\n','2','6',',','1',',','1','7','1',',','1','\n','1','1',',','1',',','2','3','7',',','1','\n','2','7',',','1',',','1','6','6',',','1',';','1','0',',','1',',','2','3','8',',','1','\n','1','0',',','1',',','2','3','8',',','1',';','1',',','1',',','8',',','1',',','2','4','4',',','1','\n','1',',','1',',','8',',','1',',','2','4','4',',','1',';','0',',','1',',','8',',','1',',','1','7',',','1',',','1','3','8',',','1','\n','5','3',',','1',',','1','1','7',',','1',';','4','7',',','1',',','1','2','7',',','1','\n','4','7',',','1',',','1','2','7',',','1',';','1','0',',','1',',','2','3','7',',','1','\n','4','7',',','1',',','1','2','6',',','1',';','1','0',',','1',',','2','3','7',',','1',';','0',',','1',',','8',',','1',',','1','6',',','1',',','1','3','8',',','1','\n','1','0',',','1',',','2','3','7',',','1',';','0',',','1',',','8',',','1',',','1','6',',','1',',','1','3','8',',','1',';','0',',','2',',','8',',','1',',','2','4','4',',','1','\n','6','5',',','1',',','9','0',',','1',';','6','5',',','1',',','8','9',',','1','\n','6','2',',','1',',','9','8',',','1','\n','6','1',',','1',',','1','0','2',',','1','\n','6','5',',','1',',','8','9',',','1',';','5','3',',','1',',','1','1','6',',','1','\n','5','3',',','1',',','1','1','6',',','1',';','0',',','1',',','8',',','1',',','1','6',',','1',',','1','3','7',',','1','\n','4','3',',','1',',','1','4','0',',','1','\n','4','8',',','1',',','1','2','3',',','1','\n','7',',','1',',','2','6','5',',','1','\n','2','5',',','1',',','1','7','5',',','1','\n','6','5',',','1',',','8','8',',','1','\n','6','0',',','1',',','1','0','2',',','1','\n','5','9',',','1',',','1','0','2',',','1','\n','4','7',',','1',',','1','2','5',',','1','\n','4','2',',','1',',','1','4','0',',','1','\n','3','0',',','1',',','1','6','1',',','1','\n','2','4',',','1',',','1','7','5',',','1','\n','1','5',',','1',',','2','1','1',',','1','\n','1','5',',','1',',','2','1','0',',','1','\n','6',',','1',',','2','6','5',',','1','\n','2',',','1',',','3','5','4',',','1','\n','0',',','1',',','4','0','1',',','1','\n','2','8',',','1',',','1','6','5',',','1',';','2','3',',','1',',','1','7','5',',','1','\n','1','1',',','1',',','2','3','6',',','1','\n','2','3',',','1',',','1','7','5',',','1',';','1',',','2',',','3','5','4',',','1','\n','1',',','2',',','3','5','4',',','1',';','0',',','1',',','1','7',',','1',',','2','0','0',',','1','\n','2','2',',','1',',','1','7','5',',','1',';','1','0',',','1',',','2','3','6',',','1','\n','1','0',',','1',',','2','3','6',',','1',';','0',',','1',',','8',',','1',',','2','5','3',',','1','\n','1','3',',','1',',','2','2','7',',','1',';','0',',','1',',','8',',','1',',','2','5','2',',','1','\n','6','2',',','1',',','9','7',',','1',';','4','4',',','1',',','1','3','5',',','1','\n','4','4',',','1',',','1','3','5',',','1',';','2','7',',','1',',','1','6','5',',','1','\n','2','7',',','1',',','1','6','5',',','1',';','1','4',',','1',',','2','1','7',',','1','\n','1','4',',','1',',','2','1','7',',','1',';','5',',','1',',','2','7','6',',','1','\n','5',',','1',',','2','7','6',',','1',';','1',',','1',',','3','7','9',',','1','\n','6','9',',','1',',','9','6',',','1','\n','2',',','1',',','3','7','8',',','1','\n','2',',','1',',','3','7','7',',','1','\n','0',',','1',',','6','9',',','1',',','9','3',',','1','\n','7','0',',','1',',','9','4',',','1','\n','7','0',',','1',',','9','3',',','1','\n','2',',','1',',','3','7','5',',','1','\n','7','0',',','1',',','9','2',',','1',';','1',',','1',',','4','1','5',',','1','\n','7','0',',','1',',','9','1',',','1','\n','6','8',',','1',',','9','6',',','1','\n','2',',','1',',','3','7','4',',','1',';','1',',','1',',','4','1','4',',','1','\n','1',',','2',',','3','7','6',',','1','\n','1',',','1',',','4','1','4',',','1',';','0',',','2',',','4','1','5',',','1','\n','0',',','3',',','3','9','6',',','1','\n','7','6',',','1',',','8','6',',','1','\n','6','7',',','1',',','9','6',',','1','\n','4','8',',','1',',','1','3','2',',','1','\n','1','8',',','1',',','2','0','2',',','1','\n','8',',','1',',','2','6','4',',','1',';','2',',','1',',','3','7','2',',','1','\n','2',',','1',',','3','7','2',',','1',';','2',',','1',',','6','9',',','1',',','8','0',',','1','\n','3',',','1',',','3','3','2',',','1',';','1',',','1',',','4','1','3',',','1',';','1',',','1',',','4','1','2',',','1','\n','2',',','1',',','6','9',',','1',',','8','0',',','1',';','0',',','1',',','4','1','9',',','1','\n','0',',','3',',','3','9','4',',','1','\n','0',',','3',',','3','9','2',',','1','\n','7','6',',','1',',','8','5',',','1','\n','7','6',',','1',',','8','4',',','1','\n','7','5',',','1',',','8','6',',','1',';','7','4',',','1',',','8','6',',','1','\n','6','1',',','1',',','1','0','9',',','1','\n','4','8',',','1',',','1','3','1',',','1','\n','2','5',',','1',',','1','8','1',',','1','\n','1','2',',','1',',','2','4','2',',','1','\n','3',',','1',',','3','3','1',',','1','\n','1',',','1',',','4','1','1',',','1','\n','1',',','1',',','4','1','0',',','1','\n','1',',','1',',','4','0','9',',','1','\n','7','4',',','1',',','8','6',',','1',';','2',',','1',',','3','7','1',',','1',';','0',',','1',',','6','9',',','1',',','8','9',',','1','\n','2',',','1',',','3','7','1',',','1',';','0',',','1',',','6','9',',','1',',','8','9',',','1',';','0',',','3',',','3','9','1',',','1','\n','7','6',',','1',',','8','3',',','1',';','7','5',',','1',',','8','5',',','1','\n','7','5',',','1',',','8','4',',','1','\n','7','4',',','1',',','8','5',',','1','\n','7','4',',','1',',','8','4',',','1','\n','7','3',',','1',',','8','6',',','1','\n','7','5',',','1',',','8','5',',','1',';','6','8',',','1',',','9','5',',','1','\n','5','3',',','1',',','1','2','2',',','1','\n','4','8',',','1',',','1','3','0',',','1','\n','6','8',',','1',',','9','5',',','1',';','2','4',',','1',',','1','8','1',',','1','\n','2','4',',','1',',','1','8','1',',','1',';','1','8',',','1',',','2','0','1',',','1','\n','1','8',',','1',',','2','0','1',',','1',';','1','3',',','1',',','2','3','5',',','1','\n','1','2',',','1',',','2','4','1',',','1','\n','1','3',',','1',',','2','3','5',',','1',';','9',',','1',',','2','5','1',',','1','\n','3',',','1',',','3','3','0',',','1','\n','1',',','1',',','4','0','8',',','1','\n','0',',','2',',','4','1','0',',','1','\n','0',',','2',',','4','0','9',',','1','\n','0',',','3',',','3','8','9',',','1',';','0',',','5',',','3','6','7',',','1','\n','7','6',',','1',',','8','1',',','1',';','7','5',',','1',',','8','2',',','1','\n','7','4',',','1',',','8','3',',','1','\n','7','5',',','1',',','8','2',',','1',';','7','4',',','1',',','8','2',',','1','\n','7','3',',','1',',','8','5',',','1','\n','7','3',',','1',',','8','4',',','1','\n','7','4',',','1',',','8','2',',','1',';','7','0',',','1',',','9','0',',','1','\n','7','0',',','1',',','8','9',',','1','\n','7','5',',','1',',','8','3',',','1',';','7','0',',','1',',','9','0',',','1',';','6','7',',','1',',','9','5',',','1','\n','6','6',',','1',',','9','6',',','1','\n','6','4',',','1',',','9','9',',','1','\n','6','1',',','1',',','1','0','8',',','1','\n','5','3',',','1',',','1','2','1',',','1','\n','4','8',',','1',',','1','2','9',',','1','\n','4','8',',','1',',','1','2','8',',','1','\n','7','0',',','1',',','9','0',',','1',';','2','8',',','1',',','1','7','4',',','1','\n','2','8',',','1',',','1','7','4',',','1',';','2','6',',','1',',','1','7','9',',','1','\n','6','7',',','1',',','9','5',',','1',';','2','6',',','1',',','1','7','9',',','1',';','2','3',',','1',',','1','8','1',',','1','\n','2','0',',','1',',','1','9','8',',','1','\n','1','2',',','1',',','2','4','0',',','1','\n','8',',','1',',','2','6','3',',','1','\n','5',',','1',',','2','8','9',',','1','\n','4',',','1',',','3','1','0',',','1','\n','2','6',',','1',',','1','7','9',',','1',';','3',',','1',',','3','2','9',',','1','\n','3',',','1',',','3','2','9',',','1',';','1',',','1',',','4','0','7',',','1','\n','0',',','1',',','4','1','7',',','1','\n','1',',','1',',','4','0','7',',','1',';','0',',','3',',','3','8','6',',','1','\n','7','5',',','1',',','8','1',',','1','\n','7','4',',','1',',','8','1',',','1','\n','7','3',',','1',',','8','3',',','1','\n','7','3',',','1',',','8','2',',','1','\n','5','3',',','1',',','1','2','0',',','1','\n','3','8',',','1',',','1','5','5',',','1','\n','2','6',',','1',',','1','7','8',',','1','\n','2','2',',','1',',','1','8','1',',','1','\n','2','0',',','1',',','1','9','7',',','1','\n','1','9',',','1',',','1','9','8',',','1','\n','1','1',',','1',',','2','4','3',',','1','\n','8',',','1',',','2','6','2',',','1','\n','5',',','1',',','2','8','8',',','1','\n','4',',','1',',','3','0','9',',','1','\n','2',',','1',',','3','7','0',',','1','\n','1',',','1',',','4','0','6',',','1','\n','0',',','2',',','4','0','7',',','1','\n','7','3',',','1',',','8','1',',','1','\n','4','3',',','1',',','1','4','4',',','1','\n','3','7',',','1',',','1','5','5',',','1','\n','2','6',',','1',',','1','7','7',',','1','\n','1','9',',','1',',','1','9','7',',','1','\n','1','2',',','1',',','2','3','9',',','1','\n','1','0',',','1',',','2','4','3',',','1','\n','9',',','1',',','2','5','0',',','1',';','8',',','1',',','2','6','1',',','1','\n','4',',','1',',','3','0','8',',','1','\n','4',',','1',',','3','0','7',',','1','\n','3',',','1',',','3','2','8',',','1','\n','6','3',',','1',',','9','9',',','1','\n','2','0',',','1',',','1','9','6',',','1','\n','1','5',',','1',',','2','1','6',',','1','\n','6','6',',','1',',','9','5',',','1',';','1','3',',','1',',','2','3','4',',','1','\n','6',',','1',',','2','7','5',',','1','\n','4',',','1',',','3','0','6',',','1','\n','2',',','1',',','3','6','9',',','1','\n','1','3',',','1',',','2','3','4',',','1',';','2',',','2',',','3','2','8',',','1','\n','2',',','2',',','3','2','8',',','1',';','0',',','1',',','7',',','1',',','2','6','6',',','1','\n','0',',','1',',','7',',','1',',','2','6','6',',','1',';','0',',','1',',','3',',','2',',','2','6','7',',','1','\n','3','6',',','1',',','1','5','5',',','1',';','2','6',',','1',',','1','7','6',',','1','\n','2','1',',','1',',','1','9','1',',','1','\n','1','9',',','1',',','1','9','6',',','1','\n','9',',','1',',','2','4','9',',','1','\n','5',',','1',',','2','8','7',',','1','\n','4',',','1',',','3','0','5',',','1','\n','4',',','1',',','3','0','4',',','1','\n','1',',','2',',','3','6','9',',','1','\n','2','6',',','1',',','1','7','6',',','1',';','0',',','1',',','2',',','1',',','3','5','9',',','1','\n','6','0',',','1',',','1','0','9',',','1','\n','5','9',',','1',',','1','0','9',',','1','\n','5','4',',','1',',','1','1','8',',','1','\n','3','8',',','1',',','1','5','4',',','1','\n','2','9',',','1',',','1','7','0',',','1','\n','2','1',',','1',',','1','9','0',',','1','\n','2','0',',','1',',','1','9','5',',','1','\n','5',',','1',',','2','8','6',',','1','\n','5',',','1',',','2','8','5',',','1','\n','4',',','1',',','3','0','3',',','1','\n','4',',','1',',','3','0','2',',','1','\n','1',',','1',',','4','0','5',',','1','\n','6','4',',','1',',','9','8',',','1','\n','5','3',',','1',',','1','1','9',',','1','\n','5','2',',','1',',','1','2','4',',','1','\n','4','8',',','1',',','1','2','7',',','1','\n','4','8',',','1',',','1','2','6',',','1','\n','3','7',',','1',',','1','5','4',',','1','\n','3','5',',','1',',','1','6','0',',','1','\n','2','9',',','1',',','1','6','9',',','1','\n','2','5',',','1',',','1','8','0',',','1','\n','1','9',',','1',',','1','9','5',',','1','\n','7',',','1',',','2','7','4',',','1','\n','5',',','1',',','2','8','4',',','1','\n','4',',','1',',','3','0','1',',','1','\n','4',',','1',',','3','0','0',',','1','\n','3',',','1',',','3','2','7',',','1','\n','0',',','1',',','2',',','1',',','3','5','5',',','1','\n','0',',','2',',','4','0','5',',','1','\n','0',',','2',',','2','0',',','1',',','1','8','8',',','1','\n','6','0',',','1',',','1','0','8',',','1','\n','7','0',',','1',',','8','8',',','1',';','5','9',',','1',',','1','0','8',',','1','\n','5','1',',','1',',','1','2','4',',','1','\n','5','9',',','1',',','1','0','8',',','1',';','4','2',',','1',',','1','4','4',',','1','\n','4','2',',','1',',','1','4','4',',','1',';','3','4',',','1',',','1','6','0',',','1','\n','2','9',',','1',',','1','6','8',',','1','\n','2','8',',','1',',','1','7','3',',','1','\n','3','4',',','1',',','1','6','0',',','1',';','2','8',',','1',',','1','7','2',',','1','\n','2','8',',','1',',','1','7','2',',','1',';','2','7',',','1',',','1','7','4',',','1','\n','2','4',',','1',',','1','8','0',',','1','\n','2','1',',','1',',','1','8','9',',','1','\n','0',',','2',',','2',',','1',',','3','4','6',',','1','\n','2','7',',','1',',','1','7','4',',','1',';','0',',','6',',','3','4','9',',','1','\n','3','6',',','1',',','1','5','4',',','1','\n','3','3',',','1',',','1','6','0',',','1','\n','2','9',',','1',',','1','6','7',',','1',';','2','3',',','1',',','1','8','0',',','1','\n','2','1',',','1',',','1','8','8',',','1','\n','2','3',',','1',',','1','8','0',',','1',';','1','3',',','1',',','2','3','3',',','1','\n','1','3',',','1',',','2','3','3',',','1',';','9',',','1',',','2','4','8',',','1','\n','4',',','1',',','2','9','9',',','1','\n','0',',','5',',','3','5','8',',','1','\n','6','3',',','1',',','9','8',',','1','\n','4','0',',','1',',','1','5','1',',','1','\n','3','0',',','1',',','1','6','4',',','1','\n','3','2',',','1',',','1','6','0',',','1',';','2','9',',','1',',','1','6','6',',','1','\n','2','9',',','1',',','1','6','6',',','1',';','2','2',',','1',',','1','8','0',',','1','\n','2','2',',','1',',','1','8','0',',','1',';','2','0',',','1',',','1','9','4',',','1','\n','2','0',',','1',',','1','9','4',',','1',';','1','3',',','1',',','2','3','2',',','1','\n','1','3',',','1',',','2','3','2',',','1',';','8',',','1',',','9',',','1',',','1','6','7',',','1','\n','2','1',',','1',',','1','8','7',',','1',';','1',',','1',',','4','0','4',',','1','\n','1',',','1',',','4','0','4',',','1',';','0',',','5',',','1','7',',','1',',','1','8','8',',','1','\n','4','0',',','1',',','1','5','0',',','1','\n','3','9',',','1',',','1','5','1',',','1','\n','2','0',',','1',',','1','9','3',',','1',';','1','9',',','1',',','1','9','4',',','1','\n','1','9',',','1',',','1','9','4',',','1',';','1','7',',','1',',','2','0','8',',','1','\n','1','5',',','1',',','2','1','5',',','1','\n','1','4',',','1',',','2','2','6',',','1','\n','1','7',',','1',',','2','0','8',',','1',';','8',',','2',',','1','8','0',',','1','\n','6',',','1',',','2','7','4',',','1',';','0',',','2',',','4','0','4',',','1','\n','0',',','2',',','4','0','4',',','1',';','0',',','6',',','3','4','7',',','1','\n','6','5',',','1',',','9','6',',','1','\n','4','7',',','1',',','1','3','4',',','1','\n','3','9',',','1',',','1','5','0',',','1','\n','1','9',',','1',',','1','9','3',',','1',';','1','7',',','1',',','2','0','7',',','1','\n','1','6',',','1',',','2','0','8',',','1',';','9',',','1',',','2','4','7',',','1','\n','1','7',',','1',',','2','0','7',',','1',';','9',',','1',',','2','4','7',',','1',';','9',',','1',',','2','4','6',',','1','\n','9',',','1',',','2','4','7',',','1',';','8',',','1',',','2','5','9',',','1','\n','9',',','1',',','2','4','6',',','1',';','0',',','3',',','3','8','0',',','1','\n','4','7',',','1',',','1','3','3',',','1','\n','4','4',',','1',',','1','3','9',',','1','\n','2','1',',','1',',','1','8','6',',','1','\n','1','6',',','1',',','2','0','7',',','1',';','9',',','1',',','2','4','5',',','1','\n','9',',','1',',','2','4','5',',','1',';','8',',','1',',','2','5','8',',','1','\n','5','0',',','1',',','1','2','4',',','1','\n','4','0',',','1',',','1','4','9',',','1',';','1','7',',','1',',','2','0','6',',','1','\n','6','5',',','1',',','9','5',',','1','\n','4','9',',','1',',','1','2','4',',','1','\n','4','8',',','1',',','1','2','5',',','1',';','3','9',',','1',',','1','4','9',',','1',';','3','1',',','1',',','1','6','0',',','1','\n','2','7',',','1',',','1','7','3',',','1','\n','3','9',',','1',',','1','4','9',',','1',';','3','1',',','1',',','1','6','0',',','1',';','2','7',',','1',',','1','7','2',',','1','\n','3','1',',','1',',','1','6','0',',','1',';','1','6',',','1',',','2','0','6',',','1','\n','2','7',',','1',',','1','7','2',',','1',';','1','6',',','1',',','2','0','6',',','1',';','9',',','1',',','2','4','4',',','1','\n','1','6',',','1',',','2','0','6',',','1',';','8',',','1',',','2','5','7',',','1','\n','9',',','1',',','2','4','4',',','1',';','8',',','1',',','2','5','7',',','1',';','1',',','1',',','4','2',',','1',',','1','3','7',',','1','\n','5','4',',','1',',','1','1','7',',','1','\n','5','8',',','1',',','1','1','4',',','1','\n','5','4',',','1',',','1','1','6',',','1','\n','3','8',',','1',',','1','5','3',',','1','\n','0',',','2',',','8',',','1',',','1','7',',','1',',','1','3','8',',','1','\n','3','8',',','1',',','1','5','2',',','1','\n','3','7',',','1',',','1','5','3',',','1','\n','2','8',',','1',',','1','7','1',',','1','\n','6','2',',','1',',','1','0','1',',','1',';','0',',','2',',','8',',','1',',','1','6',',','1',',','1','3','8',',','1','\n','5','8',',','1',',','1','1','3',',','1',';','4','1',',','1',',','1','4','7',',','1','\n','3','7',',','1',',','1','5','2',',','1','\n','4','1',',','1',',','1','4','7',',','1',';','2','1',',','1',',','1','8','5',',','1','\n','1','8',',','1',',','2','0','0',',','1','\n','2','1',',','1',',','1','8','5',',','1',';','1','2',',','1',',','2','3','8',',','1','\n','1','2',',','1',',','2','3','8',',','1',';','4',',','1',',','2','9','8',',','1','\n','4',',','1',',','2','9','8',',','1',';','0',',','2',',','8',',','1',',','1','6',',','1',',','1','3','7',',','1','\n','7','2',',','1',',','8','7',',','1','\n','5','8',',','1',',','1','1','2',',','1','\n','4','1',',','1',',','1','4','6',',','1','\n','3','6',',','1',',','1','5','3',',','1','\n','2','1',',','1',',','1','8','4',',','1','\n','1','8',',','1',',','1','9','9',',','1','\n','1','2',',','1',',','2','3','7',',','1','\n','4',',','1',',','2','9','7',',','1','\n','4','4',',','1',',','1','3','8',',','1','\n','3','6',',','1',',','1','5','2',',','1','\n','1','4',',','1',',','2','2','5',',','1','\n','1',',','1',',','4','0','3',',','1','\n','5','2',',','1',',','1','2','3',',','1','\n','6','4',',','1',',','9','7',',','1',';','4','4',',','1',',','1','3','7',',','1','\n','3','5',',','1',',','1','5','9',',','1','\n','4','4',',','1',',','1','3','7',',','1',';','1','4',',','1',',','2','2','4',',','1','\n','1','4',',','1',',','2','2','4',',','1',';','1',',','1',',','4','0','2',',','1','\n','5','1',',','1',',','1','2','3',',','1','\n','3','4',',','1',',','1','5','9',',','1','\n','3','3',',','1',',','1','5','9',',','1','\n','2','6',',','1',',','1','7','5',',','1','\n','6','3',',','1',',','9','7',',','1','\n','6','2',',','1',',','1','0','0',',','1','\n','4','6',',','1',',','1','3','5',',','1','\n','4','4',',','1',',','1','3','6',',','1','\n','3','2',',','1',',','1','5','9',',','1','\n','2','7',',','1',',','1','7','1',',','1','\n','1','4',',','1',',','2','2','3',',','1','\n','5',',','1',',','2','8','3',',','1','\n','1',',','1',',','4','0','1',',','1','\n','4','5',',','1',',','1','3','5',',','1','\n','2','9',',','1',',','1','6','5',',','1','\n','3',',','1',',','3','2','6',',','1','\n','0',',','2',',','1','7',',','1',',','2','0','0',',','1','\n','3',',','1',',','3','2','5',',','1','\n','5','8',',','1',',','1','1','1',',','1',';','5','0',',','1',',','1','2','3',',','1','\n','5','0',',','1',',','1','2','3',',','1',';','2','1',',','1',',','1','8','3',',','1','\n','2','1',',','1',',','1','8','3',',','1',';','1','7',',','1',',','2','0','5',',','1','\n','1','7',',','1',',','2','0','5',',','1',';','4',',','1',',','2','9','6',',','1','\n','4',',','1',',','2','9','6',',','1',';','0',',','2',',','8',',','1',',','2','5','2',',','1','\n','7','1',',','1',',','8','7',',','1',';','5','8',',','1',',','1','1','0',',','1','\n','5','8',',','1',',','1','1','0',',','1',';','4','9',',','1',',','1','2','3',',','1','\n','4','9',',','1',',','1','2','3',',','1',';','4','1',',','1',',','1','4','5',',','1','\n','4','1',',','1',',','1','4','5',',','1',';','3','1',',','1',',','1','5','9',',','1','\n','3','1',',','1',',','1','5','9',',','1',';','2','1',',','1',',','1','8','2',',','1','\n','2','1',',','1',',','1','8','2',',','1',';','1','6',',','1',',','2','0','5',',','1','\n','1','6',',','1',',','2','0','5',',','1',';','1','2',',','1',',','2','3','6',',','1','\n','1','2',',','1',',','2','3','6',',','1',';','8',',','1',',','2','5','6',',','1','\n','8',',','1',',','2','5','6',',','1',';','4',',','1',',','2','9','5',',','1','\n','4',',','1',',','2','9','5',',','1',';','0',',','5',',','1','7',',','1',',','1','8','3',',','1','\n','6','9',',','1',',','9','9',',','1','\n','2',',','2',',','3','4','1',',','1','\n','2',',','1',',','3','9','9',',','1','\n','2',',','2',',','3','4','0',',','1','\n','7','0',',','1',',','9','6',',','1','\n','3','5',',','1',',','1','6','3',',','1','\n','1','8',',','1',',','2','0','4',',','1','\n','1','8',',','1',',','2','0','3',',','1','\n','2',',','1',',','3','9','7',',','1','\n','0',',','1',',','4','3','0',',','1','\n','3','4',',','1',',','1','6','3',',','1','\n','1','3',',','1',',','2','4','2',',','1','\n','2',',','1',',','3','9','5',',','1',';','2',',','1',',','3','9','3',',','1','\n','2',',','1',',','3','9','2',',','1','\n','2',',','1',',','3','9','4',',','1',';','2',',','1',',','3','9','3',',','1',';','0',',','1',',','4','2','9',',','1','\n','2',',','1',',','3','9','3',',','1',';','0',',','1',',','6','9',',','1',',','9','5',',','1','\n','6','8',',','1',',','9','9',',','1','\n','3','8',',','1',',','1','5','8',',','1','\n','3','3',',','1',',','1','6','3',',','1','\n','1','3',',','1',',','2','4','1',',','1','\n','8',',','1',',','2','7','3',',','1','\n','3',',','1',',','3','3','8',',','1','\n','2',',','1',',','3','9','1',',','1','\n','7',',','1',',','2','8','2',',','1',';','2',',','1',',','3','9','0',',','1','\n','2',',','1',',','3','9','0',',','1',';','2',',','1',',','6','9',',','1',',','8','2',',','1','\n','1',',','2',',','3','9','3',',','1',';','1',',','2',',','3','9','2',',','1','\n','1',',','2',',','3','9','2',',','1',';','0',',','2',',','3',',','1',',','6','8',',','1',',','6','9',',','1','\n','6','9',',','1',',','9','8',',','1','\n','6','7',',','1',',','9','9',',','1','\n','3','7',',','1',',','1','5','8',',','1','\n','3','2',',','1',',','1','6','3',',','1','\n','7','0',',','1',',','9','5',',','1',';','2','5',',','1',',','1','9','1',',','1','\n','1','3',',','1',',','2','4','0',',','1','\n','2','5',',','1',',','1','9','1',',','1',';','7',',','1',',','2','8','1',',','1','\n','3',',','1',',','3','3','7',',','1','\n','7',',','1',',','2','8','1',',','1',';','2',',','1',',','3','8','9',',','1','\n','2',',','1',',','3','8','8',',','1','\n','2',',','1',',','3','8','9',',','1',';','1',',','1',',','4','1','9',',','1','\n','1',',','1',',','4','1','9',',','1',';','0',',','1',',','2',',','1',',','3','7','3',',','1','\n','0',',','3',',','4','1','5',',','1','\n','5','4',',','1',',','1','2','2',',','1','\n','5','2',',','1',',','1','3','2',',','1','\n','2','6',',','1',',','1','8','1',',','1','\n','2','4',',','1',',','1','9','1',',','1',';','1','1',',','1',',','2','5','1',',','1','\n','8',',','1',',','2','7','2',',','1','\n','1','1',',','1',',','2','5','1',',','1',';','4',',','1',',','3','1','3',',','1','\n','4',',','1',',','3','1','3',',','1',';','2',',','1',',','3','8','7',',','1','\n','4',',','1',',','3','1','4',',','1',';','2',',','1',',','3','8','7',',','1',';','2',',','1',',','3','8','6',',','1','\n','2',',','1',',','3','8','7',',','1',';','2',',','1',',','1','8',',','1',',','1','8','9',',','1','\n','2',',','1',',','1','8',',','1',',','1','8','9',',','1',';','1',',','2',',','3','8','9',',','1','\n','1',',','2',',','3','8','9',',','1',';','1',',','2',',','3','8','8',',','1','\n','1',',','2',',','3','8','8',',','1',';','0',',','1',',','4','2','7',',','1','\n','2',',','1',',','3','8','6',',','1',';','0',',','1',',','4','2','7',',','1',';','0',',','2',',','4','1','9',',','1','\n','0',',','3',',','4','1','4',',','1','\n','5','4',',','1',',','1','2','1',',','1','\n','5','2',',','1',',','1','3','1',',','1','\n','5','1',',','1',',','1','3','2',',','1','\n','3','8',',','1',',','1','5','7',',','1','\n','3','6',',','1',',','1','5','8',',','1','\n','2','3',',','1',',','1','9','1',',','1',';','1','0',',','1',',','2','5','1',',','1','\n','8',',','1',',','2','7','1',',','1','\n','8',',','1',',','2','7','0',',','1','\n','1','3',',','1',',','2','3','9',',','1',';','1','0',',','1',',','2','5','1',',','1',';','4',',','1',',','3','1','2',',','1','\n','4',',','1',',','3','1','1',',','1','\n','1','0',',','1',',','2','5','1',',','1',';','4',',','1',',','3','1','2',',','1',';','2',',','1',',','1','8',',','1',',','1','8','8',',','1','\n','4',',','1',',','3','1','2',',','1',';','2',',','1',',','1','8',',','1',',','1','8','8',',','1',';','1',',','2',',','3','8','7',',','1','\n','1',',','2',',','3','8','7',',','1',';','0',',','1',',','4','2','6',',','1','\n','2',',','1',',','1','8',',','1',',','1','8','8',',','1',';','0',',','1',',','4','2','6',',','1',';','0',',','2',',','6','9',',','1',',','8','9',',','1','\n','0',',','1',',','4','2','6',',','1',';','0',',','4',',','3','9','1',',','1'] ['0',',','2',',','6','9',',','1',',','8','9',',','1',';','0',',','5',',','3','7','5',',','1'] ['7','2',',','1',',','9','4',',','1','\n','6','6',',','1',',','9','9',',','1','\n','5','4',',','1',',','1','2','0',',','1','\n','5','2',',','1',',','1','3','0',',','1','\n','5','1',',','1',',','1','3','1',',','1','\n','3','7',',','1',',','1','5','7',',','1','\n','2','2',',','1',',','1','9','1',',','1','\n','1','7',',','1',',','2','1','4',',','1','\n','8',',','1',',','2','6','9',',','1',';','7',',','1',',','2','8','0',',','1','\n','6',',','1',',','2','8','2',',','1','\n','7',',','1',',','2','8','0',',','1',';','1',',','1',',','4','1','8',',','1','\n','2','5',',','1',',','1','8','9',',','1',';','1',',','1',',','4','1','7',',','1','\n','0',',','1',',','9',',','1',',','2','5','1',',','1','\n','0',',','6',',','3','6','7',',','1','\n','7','2',',','1',',','9','3',',','1','\n','5','2',',','1',',','1','2','9',',','1','\n','5','2',',','1',',','1','2','8',',','1','\n','5','1',',','1',',','1','3','0',',','1','\n','4','8',',','1',',','1','3','4',',','1','\n','2','9',',','1',',','1','7','4',',','1','\n','7','2',',','1',',','9','2',',','1',';','2','5',',','1',',','1','8','8',',','1','\n','2','5',',','1',',','1','8','8',',','1',';','2','4',',','1',',','1','8','9',',','1','\n','2','2',',','1',',','1','9','0',',','1','\n','1','6',',','1',',','2','1','4',',','1','\n','1','4',',','1',',','2','3','1',',','1','\n','1','1',',','1',',','2','5','0',',','1','\n','2','4',',','1',',','1','8','9',',','1',';','7',',','1',',','2','7','9',',','1','\n','6',',','1',',','2','8','1',',','1','\n','2',',','1',',','3','8','5',',','1','\n','0',',','4',',','3','8','6',',','1','\n','7','2',',','1',',','9','1',',','1','\n','6','8',',','1',',','9','8',',','1','\n','5','1',',','1',',','1','2','9',',','1','\n','5','1',',','1',',','1','2','8',',','1','\n','4','8',',','1',',','1','3','3',',','1','\n','3','6',',','1',',','1','5','7',',','1','\n','3','1',',','1',',','1','6','3',',','1','\n','2','8',',','1',',','1','7','9',',','1','\n','2','5',',','1',',','1','8','7',',','1','\n','2','4',',','1',',','1','8','8',',','1',';','2','3',',','1',',','1','8','9',',','1','\n','1','7',',','1',',','2','1','3',',','1','\n','1','5',',','1',',','2','2','2',',','1','\n','1','4',',','1',',','2','3','0',',','1','\n','1','0',',','1',',','2','5','0',',','1','\n','2',',','1',',','3','8','4',',','1','\n','1',',','2',',','3','8','5',',','1',';','0',',','1',',','4','2','4',',','1','\n','0',',','1',',','4','2','3',',','1','\n','6','1',',','1',',','1','1','4',',','1','\n','3','8',',','1',',','1','5','6',',','1','\n','2','8',',','1',',','1','7','8',',','1','\n','2','4',',','1',',','1','8','7',',','1','\n','2','2',',','1',',','1','8','9',',','1','\n','2','0',',','1',',','2','0','2',',','1','\n','1','6',',','1',',','2','1','3',',','1','\n','1','1',',','1',',','2','4','9',',','1','\n','8',',','1',',','2','6','8',',','1','\n','6','7',',','1',',','9','8',',','1',';','0',',','2',',','7',',','1',',','2','6','7',',','1','\n','5','7',',','1',',','1','1','8',',','1','\n','4','6',',','1',',','1','3','9',',','1','\n','3','7',',','1',',','1','5','6',',','1']
    · rfl
    · rfl
    · decide
  · have hs : "0,2,69,1,89,1;0,5,375,1".splitOn ";"=["0,2,69,1,89,1","0,5,375,1"] := by
      simp +decide [String.splitOn,String.splitOnAux]
    have hm0 : (("0,2,69,1,89,1".splitOn ",").map (fun n=>n.toNat?.getD 0))=[0,2,69,1,89,1] := by
      have hx : "0,2,69,1,89,1".splitOn ","=["0","2","69","1","89","1"] := by simp +decide [String.splitOn,String.splitOnAux]
      rw [hx]
      simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
    have hm1 : (("0,5,375,1".splitOn ",").map (fun n=>n.toNat?.getD 0))=[0,5,375,1] := by
      have hx : "0,5,375,1".splitOn ","=["0","5","375","1"] := by simp +decide [String.splitOn,String.splitOnAux]
      rw [hx]
      simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
    change _ = (("0,2,69,1,89,1;0,5,375,1".splitOn ";").map _).sum
    rw [hs]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
    change _ = (if "0,2,69,1,89,1"="" then 1 else _) + ((if "0,5,375,1"="" then 1 else _) + (0))
    simp only [if_neg (by decide : "0,2,69,1,89,1"≠""),if_neg (by decide : "0,5,375,1"≠"")]
    rw [hm0,hm1]
    change _ = ((MvPolynomial.X (atomIndex .h0))^2 * ((MvPolynomial.X (atomIndex .h6))^1 * ((MvPolynomial.X (⟨89,by decide⟩ : Fin generators.count))^1 * ((1 : MvPolynomial (Fin generators.count) (ZMod 2)))))) + (((MvPolynomial.X (atomIndex .h0))^5 * ((MvPolynomial.X (atomIndex .x_125_8))^1 * ((1 : MvPolynomial (Fin generators.count) (ZMod 2))))) + ((0 : MvPolynomial (Fin generators.count) (ZMod 2))))
    ring


private theorem nativeCoreTwo : sourceUnit.val+sourceUnit.val=0 := by
  change Ideal.Quotient.mk _ ((1 : MvPolynomial (Fin generators.count) (ZMod 2))+1)=0
  have ht : (1 : MvPolynomial (Fin generators.count) (ZMod 2))+1=0 := CharTwo.add_self_eq_zero _
  rw [ht,map_zero]

private theorem nativeCoreAddSelf {R : Type} [CommRing R] (ht : (1:R)+1=0) (x : R) : x+x=0 := by
  have h := congrArg (fun z=>z*x) ht
  simpa only [add_mul,one_mul,zero_mul] using h

private theorem nativeCoreEqOfAddZero {R : Type} [CommRing R] (ht : (1:R)+1=0)
    {a b : R} (h : a+b=0) : a=b := by
  have hb : -b=b := neg_eq_iff_add_eq_zero.mpr (nativeCoreAddSelf ht b)
  exact (eq_neg_of_add_eq_zero_left h).trans hb

private theorem nativeCoreB :
    (sourceProduct 12 134 1 4 (sourceProduct 1 32 11 102 (sourceAtom .h5) (sourceAtom .x_91_11)) (sourceAtom .h2)).val =
      (sourceAtom .h0).val^4 * (sourceAtom .x_125_9_2).val +
      (sourceAtom .h0).val^5 * (sourceAtom .x_125_8).val := by
  have h1 := nativeCoreB1
  have h2 := nativeCoreB2
  have h3 := nativeCoreB3
  have hs := congrArg₂ (·+·) (congrArg₂ (·+·) h1 h2) h3
  simp only [add_zero] at hs
  apply nativeCoreEqOfAddZero nativeCoreTwo
  have hc0 := nativeCoreAddSelf nativeCoreTwo ((sourceAtom .h0).val *
    (Ideal.Quotient.mk _ (MvPolynomial.X (⟨426,by decide⟩ : Fin generators.count))))
  have hc1 := nativeCoreAddSelf nativeCoreTwo ((sourceAtom .h0).val^2 * (sourceAtom .h6).val *
    (Ideal.Quotient.mk _ (MvPolynomial.X (⟨89,by decide⟩ : Fin generators.count))))
  calc
    _ = (((sourceProduct 12 134 1 4 (sourceProduct 1 32 11 102 (sourceAtom .h5) (sourceAtom .x_91_11)) (sourceAtom .h2)).val +
        (sourceAtom .h0).val * (Ideal.Quotient.mk _ (MvPolynomial.X (⟨426,by decide⟩ : Fin generators.count))) +
        (sourceAtom .h0).val^2 * (sourceAtom .h6).val * (Ideal.Quotient.mk _ (MvPolynomial.X (⟨89,by decide⟩ : Fin generators.count)))) +
      ((sourceAtom .h0).val * (Ideal.Quotient.mk _ (MvPolynomial.X (⟨426,by decide⟩ : Fin generators.count))) +
        (sourceAtom .h0).val^4 * (sourceAtom .x_125_9_2).val) +
      ((sourceAtom .h0).val^2 * (sourceAtom .h6).val * (Ideal.Quotient.mk _ (MvPolynomial.X (⟨89,by decide⟩ : Fin generators.count))) +
        (sourceAtom .h0).val^5 * (sourceAtom .x_125_8).val)) -
      (((sourceAtom .h0).val * (Ideal.Quotient.mk _ (MvPolynomial.X (⟨426,by decide⟩ : Fin generators.count))) +
        (sourceAtom .h0).val * (Ideal.Quotient.mk _ (MvPolynomial.X (⟨426,by decide⟩ : Fin generators.count)))) +
       ((sourceAtom .h0).val^2 * (sourceAtom .h6).val * (Ideal.Quotient.mk _ (MvPolynomial.X (⟨89,by decide⟩ : Fin generators.count))) +
        (sourceAtom .h0).val^2 * (sourceAtom .h6).val * (Ideal.Quotient.mk _ (MvPolynomial.X (⟨89,by decide⟩ : Fin generators.count))))) := by ring
    _ = 0 := by rw [hs,hc0,hc1,add_zero,sub_zero]

private theorem qRoute_d2_add
    {E : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)}
    {p q : ℤ × ℤ} {x x' : E.Page 2 p} {y y' : E.Page 2 q}
    (h : HasDifferential E 2 p q x y)
    (h' : HasDifferential E 2 p q x' y') :
    HasDifferential E 2 p q (x+x') (y+y') := by
  obtain ⟨hdeg,hd⟩ := h.eq_on_page_two
  obtain ⟨hdeg',hd'⟩ := h'.eq_on_page_two
  let δ : E.Page 2 p ⟶ E.Page 2 q := E.d 2 p ≫ eqToHom (congrArg (E.Page 2) hdeg)
  have hδ : δ x=y := hd
  have hδ' : δ x'=y' := hd'
  refine ⟨hdeg,x+x',y+y',RepresentsOnPage.self_two _,RepresentsOnPage.self_two _,?_⟩
  exact (map_add δ.hom x x').trans (congrArg₂ (·+·) hδ hδ')

private theorem qRoute_raw288 :
    HasDifferential model.classical.sphere 2 (11,137) (13,138)
      (basis .sphere 11 137 0) (basis .sphere 13 138 3) := by
  have hrow := result ⟨.sphere,.equation,2,11,137,[0],13,138,[3],"S0_AdamsE2_ss",2927⟩ (by
    exact List.mem_of_getElem? (i := 288) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,h⟩ := hrow
  change HasDifferential model.classical.sphere 2 (11,137) (13,138) x y at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 11 137 [0]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 13 138 [3]=true := rfl
  delta decode at hx hy
  simp (config := { congrConsts := false }) only [vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at h
  exact h

private theorem qRoute_raw289 :
    HasDifferential model.classical.sphere 2 (11,137) (13,138)
      (basis .sphere 11 137 3) (basis .sphere 13 138 4) := by
  have hrow := result ⟨.sphere,.equation,2,11,137,[3],13,138,[4],"S0_AdamsE2_ss",2928⟩ (by
    exact List.mem_of_getElem? (i := 289) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,h⟩ := hrow
  change HasDifferential model.classical.sphere 2 (11,137) (13,138) x y at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 11 137 [3]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 13 138 [4]=true := rfl
  delta decode at hx hy
  simp (config := { congrConsts := false }) only [vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at h
  exact h

private theorem qRoute_sum_differential :
    HasDifferential model.classical.sphere 2 (11,137) (13,138)
      (basis .sphere 11 137 0+basis .sphere 11 137 3)
      (basis .sphere 13 138 3+basis .sphere 13 138 4) :=
  qRoute_d2_add qRoute_raw288 qRoute_raw289

private theorem qRoute_sum_boundary :
    IsBoundaryBy model.classical.sphere 2 (13,138)
      (basis .sphere 13 138 3+basis .sphere 13 138 4) := by
  have hs : model.classical.sphere.r₀≤2 := by rw [model.classical.firstPage]
  exact pq_rep3zero_boundary
    (differential_target_later_zero hs (by decide : (2:ℤ)<3) qRoute_sum_differential)

/- This explicit actual-page equality is the only missing input to this route.
   It is a parameter of a private conditional helper, not a new responsibility. -/
private theorem qRoute_boundary_of_actual_product
    (hProduct : product (r := (13,138)) Q h2 (h := by rfl) =
      basis .sphere 13 138 3+basis .sphere 13 138 4) :
    IsBoundaryBy model.classical.sphere 2 (13,138) (product Q h2 (h := by rfl)) := by
  rw [hProduct]
  exact qRoute_sum_boundary

private theorem qRoute_value250 :
    basis .sphere 13 138 3 =
      Expression.value (.mul (.mul (.mul (.mul (.named .h0) (.named .h0))
        (.named .h0)) (.named .h0)) (.named .x_125_9_2)) := by
  exact basis_value ⟨.mul (.mul (.mul (.mul (.named .h0) (.named .h0))
    (.named .h0)) (.named .h0)) (.named .x_125_9_2),3⟩ (by
      exact List.mem_of_getElem? (i := 250) (by rfl))

private theorem qRoute_value251 :
    basis .sphere 13 138 4 =
      Expression.value (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0))
        (.named .h0)) (.named .h0)) (.named .h0)) (.named .x_125_8)) := by
  exact basis_value ⟨.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0))
    (.named .h0)) (.named .h0)) (.named .h0)) (.named .x_125_8),4⟩ (by
      exact List.mem_of_getElem? (i := 251) (by rfl))



private noncomputable def qTransportH02 : sourceComponent 2 2 :=
  sourceProduct 1 1 1 1 (sourceAtom .h0) (sourceAtom .h0)
private noncomputable def qTransportH03 : sourceComponent 3 3 :=
  sourceProduct 2 2 1 1 qTransportH02 (sourceAtom .h0)
private noncomputable def qTransportH04 : sourceComponent 4 4 :=
  sourceProduct 3 3 1 1 qTransportH03 (sourceAtom .h0)
private noncomputable def qTransportH05 : sourceComponent 5 5 :=
  sourceProduct 4 4 1 1 qTransportH04 (sourceAtom .h0)

private theorem qTransport_product (s t s' t' : ℕ) (ht : t+t'≤261)
    (x : sourceComponent s t) (y : sourceComponent s' t') :
    comparison (s+s') (t+t') ht (sourceProduct s t s' t' x y) =
      product (r := ((s+s':ℕ),(t+t':ℕ)))
        (comparison s t (by omega) x) (comparison s' t' (by omega) y)
        (by simp only [Prod.mk_add_mk,Nat.cast_add]) := by
  with_unfolding_all
    exact comparison_product s t s' t' ht x y

private theorem qTransport_atom (a : KIP126.Computation.Atom) (ht : a.degree.2≤261) :
    comparison a.degree.1 a.degree.2 ht (sourceAtom a) = atom a := by
  with_unfolding_all
    rfl

private theorem qTransport_comparison_h0 (ht : 1≤261) :
    comparison 1 1 ht (sourceAtom .h0)=h0 := by
  exact comparison_h0

private theorem qTransport_comparison_h2 (ht : 4≤261) :
    comparison 1 4 ht (sourceAtom .h2)=h2 := by
  exact comparison_h2

private theorem qTransport_comparison_h5 (ht : 32≤261) :
    comparison 1 32 ht (sourceAtom .h5)=h5 := by
  exact comparison_h5

private theorem qTransport_h02 :
    comparison 2 2 (by decide) qTransportH02 = product (r := (2,2)) h0 h0 := by
  with_unfolding_all
    dsimp only [qTransportH02]
    rw [qTransport_product 1 1 1 1 (by decide),qTransport_comparison_h0]

private theorem qTransport_h03 :
    comparison 3 3 (by decide) qTransportH03 =
      product (r := (3,3)) (product (r := (2,2)) h0 h0) h0 := by
  with_unfolding_all
    dsimp only [qTransportH03]
    rw [qTransport_product 2 2 1 1 (by decide),qTransport_h02,qTransport_comparison_h0]

private theorem qTransport_h04 :
    comparison 4 4 (by decide) qTransportH04 =
      product (r := (4,4)) (product (r := (3,3)) (product (r := (2,2)) h0 h0) h0) h0 := by
  with_unfolding_all
    dsimp only [qTransportH04]
    rw [qTransport_product 3 3 1 1 (by decide),qTransport_h03,qTransport_comparison_h0]

private theorem qTransport_h05 :
    comparison 5 5 (by decide) qTransportH05 =
      product (r := (5,5))
        (product (r := (4,4)) (product (r := (3,3)) (product (r := (2,2)) h0 h0) h0) h0) h0 := by
  with_unfolding_all
    dsimp only [qTransportH05]
    rw [qTransport_product 4 4 1 1 (by decide),qTransport_h04,qTransport_comparison_h0]

private theorem qTransport_qSource :
    comparison 12 134 (by decide)
      (sourceProduct 1 32 11 102 (sourceAtom .h5) (sourceAtom .x_91_11)) = Q := by
  with_unfolding_all
    rw [qTransport_product 1 32 11 102 (by decide),qTransport_comparison_h5,qTransport_atom .x_91_11]
    rfl

private theorem qTransport_qh2 :
    comparison 13 138 (by decide)
      (sourceProduct 12 134 1 4
        (sourceProduct 1 32 11 102 (sourceAtom .h5) (sourceAtom .x_91_11)) (sourceAtom .h2)) =
      product (r := (13,138)) Q h2 (h := by rfl) := by
  with_unfolding_all
    rw [qTransport_product 12 134 1 4 (by decide),qTransport_qSource,qTransport_comparison_h2]

private theorem qTransport_target3 :
    comparison 13 138 (by decide)
      (sourceProduct 4 4 9 134 qTransportH04 (sourceAtom .x_125_9_2)) =
      basis .sphere 13 138 3 := by
  with_unfolding_all
    rw [qTransport_product 4 4 9 134 (by decide),qTransport_h04,qTransport_atom .x_125_9_2,qRoute_value250]
    dsimp only [Expression.value,Expression.degree]
    rw [atom_h0]

private theorem qTransport_target4 :
    comparison 13 138 (by decide)
      (sourceProduct 5 5 8 133 qTransportH05 (sourceAtom .x_125_8)) =
      basis .sphere 13 138 4 := by
  with_unfolding_all
    rw [qTransport_product 5 5 8 133 (by decide),qTransport_h05,qTransport_atom .x_125_8,qRoute_value251]
    dsimp only [Expression.value,Expression.degree]
    rw [atom_h0]

/- The source equality is an explicit research parameter, not an assumed new
   axiom and not a proof of the original q_h2_boundary on its own. -/
private theorem qTransport_actual_of_source
    (hSource : sourceProduct 12 134 1 4
        (sourceProduct 1 32 11 102 (sourceAtom .h5) (sourceAtom .x_91_11)) (sourceAtom .h2) =
      sourceProduct 4 4 9 134 qTransportH04 (sourceAtom .x_125_9_2) +
      sourceProduct 5 5 8 133 qTransportH05 (sourceAtom .x_125_8)) :
    product (r := (13,138)) Q h2 (h := by rfl) = basis .sphere 13 138 3+basis .sphere 13 138 4 := by
  with_unfolding_all
    have h := congrArg (comparison 13 138 (by decide)) hSource
    rw [map_add,qTransport_qh2,qTransport_target3,qTransport_target4] at h
    exact h

private theorem qTransport_boundary_of_source
    (hSource : sourceProduct 12 134 1 4
        (sourceProduct 1 32 11 102 (sourceAtom .h5) (sourceAtom .x_91_11)) (sourceAtom .h2) =
      sourceProduct 4 4 9 134 qTransportH04 (sourceAtom .x_125_9_2) +
      sourceProduct 5 5 8 133 qTransportH05 (sourceAtom .x_125_8)) :
    IsBoundaryBy model.classical.sphere 2 (13,138) (product Q h2 (h := by rfl)) :=
  qRoute_boundary_of_actual_product (qTransport_actual_of_source hSource)

private theorem h0SixAssembly_left_value :
    h0Six=product (r := (6,6))
      (product (r := (5,5))
        (product (r := (4,4))
          (product (r := (3,3)) (product (r := (2,2)) h0 h0) h0) h0) h0) h0 := by
  have h4 : product (r := (4,4)) h0Square h0Square=
      product (r := (4,4)) (product (r := (3,3)) h0Square h0) h0 :=
    (eq_of_heq (model.sphereAlgebra.assoc (2,2) (1,1) (1,1) h0Square h0 h0)).symm
  have h6 : product (r := (6,6)) (product (r := (4,4)) h0Square h0Square) h0Square=
      product (r := (6,6))
        (product (r := (5,5)) (product (r := (4,4)) h0Square h0Square) h0) h0 :=
    (eq_of_heq (model.sphereAlgebra.assoc (4,4) (1,1) (1,1)
      (product (r := (4,4)) h0Square h0Square) h0 h0)).symm
  change product (r := (6,6)) (product (r := (4,4)) h0Square h0Square) h0Square=_
  rw [h6,h4]
  rfl

private theorem h0SixAssembly_source_basis :
    product (r := (7,70)) h0Six h6 (h := by rfl)=basis .sphere 7 70 2 := by
  have hv := basis_value
    ⟨.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0))
      (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h6),2⟩ (by decide)
  simp only [Expression.value,Expression.degree,atom_h0,atom_h6] at hv
  change basis .sphere 7 70 2=product (r := (7,70))
    (product (r := (6,6)) (product (r := (5,5)) (product (r := (4,4))
      (product (r := (3,3)) (product (r := (2,2)) h0 h0) h0) h0) h0) h0) h6 at hv
  rw [←h0SixAssembly_left_value] at hv
  exact hv.symm

private theorem h0SixAssembly_target_polynomial :
    product (r := (9,71)) (product (r := (7,7)) h0Six h0) h5Square=
      basis .sphere 9 71 0 := by
  have hv := basis_value
    ⟨.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0))
      (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0))
      (.mul (.named .h5) (.named .h5)),0⟩ (by decide)
  simp only [Expression.value,Expression.degree,atom_h0,atom_h5] at hv
  change basis .sphere 9 71 0=product (r := (9,71))
    (product (r := (7,7))
      (product (r := (6,6)) (product (r := (5,5)) (product (r := (4,4))
        (product (r := (3,3)) (product (r := (2,2)) h0 h0) h0) h0) h0) h0) h0)
    h5Square at hv
  rw [←h0SixAssembly_left_value] at hv
  exact hv.symm

private theorem h0SixAssembly_actual_differential :
    HasDifferential model.classical.sphere 2 (7,70) (9,71)
      (product h0Six h6 (h := by rfl)) (basis .sphere 9 71 0) := by
  have hrow := result
    ⟨.sphere,.equation,2,7,70,[2],9,71,[0],"S0_AdamsE2_ss",513⟩ (by
      exact List.mem_of_getElem? (i := 180) rfl)
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  have vx : Raw.coordinatesValid Raw.degrees .sphere 7 70 [2]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 9 71 [0]=true := rfl
  delta decode at hx hy
  simp only [vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,
    List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  rw [h0SixAssembly_source_basis]
  exact hd

private theorem h0SixAssembly_target_nonzero : basis .sphere 9 71 0≠0 := by
  obtain ⟨e,he⟩ := basis_correct ⟨.sphere,9,71,["0,7,18,2"]⟩ (by
    exact List.mem_of_getElem? (i := 167) rfl)
  change model.classical.sphere.Page 2 (9,71) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e
  change ∀ i : Fin 1, e.symm (Finsupp.single i 1)=basis .sphere 9 71 i.val at he
  have he0 : e.symm (Finsupp.single (0 : Fin 1) 1)=basis .sphere 9 71 0 := he 0
  rw [←he0]
  exact basis_vector_ne_zero e 0

/-- Conditional assembly only: the equality is the precise native relation
still owed by the coordinator, not an assumed replacement for the public goal. -/
private theorem h0SixAssembly_of_target_basis
    (htarget : product (r := (9,71)) h0 (atom .b) (h := by rfl)=basis .sphere 9 71 0) :
    HasNonzeroDifferential model.classical.sphere 2 (7,70) (9,71)
      (product h0Six h6 (h := by rfl)) (product h0 (atom .b) (h := by rfl)) := by
  obtain ⟨hdeg,x,y,hx,hy,hd⟩ := h0SixAssembly_actual_differential
  have hy_eq : y=basis .sphere 9 71 0 := hy.eq_on_page_two.symm
  refine ⟨hdeg,x,y,hx,?_,hd,?_⟩
  · rw [htarget]
    exact hy
  · rw [hy_eq]
    exact h0SixAssembly_target_nonzero

private theorem h0SixAssembly_of_target_polynomial
    (htarget : product (r := (9,71)) h0 (atom .b) (h := by rfl)=
      product (r := (9,71)) (product (r := (7,7)) h0Six h0) h5Square) :
    HasNonzeroDifferential model.classical.sphere 2 (7,70) (9,71)
      (product h0Six h6 (h := by rfl)) (product h0 (atom .b) (h := by rfl)) := by
  exact h0SixAssembly_of_target_basis (htarget.trans h0SixAssembly_target_polynomial)



private theorem nativeSourceQ :
    sourceProduct 12 134 1 4
        (sourceProduct 1 32 11 102 (sourceAtom .h5) (sourceAtom .x_91_11)) (sourceAtom .h2) =
      sourceProduct 4 4 9 134 qTransportH04 (sourceAtom .x_125_9_2) +
      sourceProduct 5 5 8 133 qTransportH05 (sourceAtom .x_125_8) := by
  apply Subtype.ext
  change (sourceProduct 12 134 1 4
      (sourceProduct 1 32 11 102 (sourceAtom .h5) (sourceAtom .x_91_11)) (sourceAtom .h2)).val =
    (((sourceAtom .h0).val*(sourceAtom .h0).val)*(sourceAtom .h0).val)*(sourceAtom .h0).val *
      (sourceAtom .x_125_9_2).val +
    ((((sourceAtom .h0).val*(sourceAtom .h0).val)*(sourceAtom .h0).val)*(sourceAtom .h0).val)*(sourceAtom .h0).val *
      (sourceAtom .x_125_8).val
  calc
    _ = (sourceAtom .h0).val^4*(sourceAtom .x_125_9_2).val +
        (sourceAtom .h0).val^5*(sourceAtom .x_125_8).val := nativeCoreB
    _ = _ := by ring

private noncomputable def h0NativeH02 : sourceComponent 2 2 :=
  sourceProduct 1 1 1 1 (sourceAtom .h0) (sourceAtom .h0)
private noncomputable def h0NativeH04 : sourceComponent 4 4 :=
  sourceProduct 2 2 2 2 h0NativeH02 h0NativeH02
private noncomputable def h0NativeH06 : sourceComponent 6 6 :=
  sourceProduct 4 4 2 2 h0NativeH04 h0NativeH02
private noncomputable def h0NativeH07 : sourceComponent 7 7 :=
  sourceProduct 6 6 1 1 h0NativeH06 (sourceAtom .h0)
private noncomputable def h0NativeH5Square : sourceComponent 2 64 :=
  sourceProduct 1 32 1 32 (sourceAtom .h5) (sourceAtom .h5)

private theorem nativeSourceA :
    sourceProduct 1 1 8 70 (sourceAtom .h0) (sourceAtom .b) =
      sourceProduct 7 7 2 64 h0NativeH07 h0NativeH5Square := by
  apply Subtype.ext
  have ht := nativeCoreEqOfAddZero nativeCoreTwo nativeCoreA
  change (sourceProduct 1 1 8 70 (sourceAtom .h0) (sourceAtom .b)).val =
    ((((sourceAtom .h0).val*(sourceAtom .h0).val)*((sourceAtom .h0).val*(sourceAtom .h0).val))*
      ((sourceAtom .h0).val*(sourceAtom .h0).val))*(sourceAtom .h0).val *
      ((sourceAtom .h5).val*(sourceAtom .h5).val)
  calc
    _ = (sourceAtom .h0).val^7*(sourceAtom .h5).val^2 := ht
    _ = _ := by ring

private theorem h0NativeH02Comparison : comparison 2 2 (by decide) h0NativeH02=h0Square := by
  with_unfolding_all
    dsimp only [h0NativeH02]
    rw [qTransport_product 1 1 1 1 (by decide),qTransport_comparison_h0]
    rfl

private theorem h0NativeH04Comparison : comparison 4 4 (by decide) h0NativeH04=
    product (r := (4,4)) h0Square h0Square := by
  with_unfolding_all
    dsimp only [h0NativeH04]
    rw [qTransport_product 2 2 2 2 (by decide),h0NativeH02Comparison]

private theorem h0NativeH06Comparison : comparison 6 6 (by decide) h0NativeH06=h0Six := by
  with_unfolding_all
    dsimp only [h0NativeH06]
    rw [qTransport_product 4 4 2 2 (by decide),h0NativeH04Comparison,h0NativeH02Comparison]
    rfl

private theorem h0NativeH07Comparison : comparison 7 7 (by decide) h0NativeH07=
    product (r := (7,7)) h0Six h0 := by
  with_unfolding_all
    dsimp only [h0NativeH07]
    rw [qTransport_product 6 6 1 1 (by decide),h0NativeH06Comparison,qTransport_comparison_h0]

private theorem h0NativeH5SquareComparison : comparison 2 64 (by decide) h0NativeH5Square=h5Square := by
  with_unfolding_all
    dsimp only [h0NativeH5Square]
    rw [qTransport_product 1 32 1 32 (by decide),qTransport_comparison_h5]
    rfl

private theorem nativeActualA : product (r := (9,71)) h0 (atom .b) (h := by rfl)=
    product (r := (9,71)) (product (r := (7,7)) h0Six h0) h5Square := by
  with_unfolding_all
    have h := congrArg (comparison 9 71 (by decide)) nativeSourceA
    rw [qTransport_product 1 1 8 70 (by decide),qTransport_comparison_h0,qTransport_atom .b,
      qTransport_product 7 7 2 64 (by decide),h0NativeH07Comparison,h0NativeH5SquareComparison] at h
    exact h

end NativeRelationCalculationHelpers

public theorem d2_h0Six_h6 : HasNonzeroDifferential model.classical.sphere 2 (7,70) (9,71)
    (product h0Six h6) (product h0 (atom .b)) := by
  exact h0SixAssembly_of_target_polynomial nativeActualA

public theorem d3_h4_x109_12 : HasNonzeroDifferential model.classical.sphere 3 (13,137) (16,139)
    (product h4 (atom .x_109_12) (h := T._proof_1))
    (product h1 (atom .x_122_15_2)) := by
  classical
  let E := model.classical.sphere
  have hs2 : E.r₀≤2 := by
    change model.classical.sphere.r₀≤2
    rw [model.classical.firstPage]
  have h324 : HasDifferential E 3 (13,137) (16,139)
      (basis .sphere 13 137 2) (basis .sphere 16 139 0) := by
    have hrow := result ⟨.sphere, .equation, 3, 13, 137, [2], 16, 139, [0], "S0_AdamsE2_ss", 2917⟩ (by
      exact List.mem_of_getElem? (i := 324) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 3 (13,137) (16,139) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 13 137 [2]=true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 16 139 [0]=true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    exact h
  have h366 : HasDifferential E 2 (14,138) (16,139)
      (basis .sphere 14 138 1) (basis .sphere 16 139 1 + basis .sphere 16 139 2) := by
    have hrow := result ⟨.sphere, .equation, 2, 14, 138, [1], 16, 139, [1, 2], "S0_AdamsE2_ss", 3072⟩ (by
      exact List.mem_of_getElem? (i := 366) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 2 (14,138) (16,139) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 14 138 [1]=true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 16 139 [1, 2]=true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    exact h
  have h367 : HasDifferential E 2 (14,138) (16,139)
      (basis .sphere 14 138 0 + basis .sphere 14 138 1) (basis .sphere 16 139 2) := by
    have hrow := result ⟨.sphere, .equation, 2, 14, 138, [0, 1], 16, 139, [2], "S0_AdamsE2_ss", 3073⟩ (by
      exact List.mem_of_getElem? (i := 367) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 2 (14,138) (16,139) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 14 138 [0, 1]=true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 16 139 [2]=true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    exact h
  have h308 : HasDifferential E 2 (12,137) (14,138)
      (basis .sphere 12 137 1) (basis .sphere 14 138 4) := by
    have hrow := result ⟨.sphere, .equation, 2, 12, 137, [1], 14, 138, [4], "S0_AdamsE2_ss", 2921⟩ (by
      exact List.mem_of_getElem? (i := 308) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 2 (12,137) (14,138) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 12 137 [1] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 14 138 [4] = true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    exact h
  have h309 : HasDifferential E 2 (12,137) (14,138)
      (basis .sphere 12 137 0) (basis .sphere 14 138 3) := by
    have hrow := result ⟨.sphere, .equation, 2, 12, 137, [0], 14, 138, [3], "S0_AdamsE2_ss", 2922⟩ (by
      exact List.mem_of_getElem? (i := 309) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 2 (12,137) (14,138) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 12 137 [0] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 14 138 [3] = true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    exact h
  have hlate : ReachesPage E 1000 (14,138) (basis .sphere 14 138 2) := by
    have hrow := staircase_result
      ⟨.sphere,.reaches,1000,14,138,[2],14,138,[],"S0_AdamsSS_staircase:23:61",3005⟩ (by
        exact List.mem_of_getElem? (l := staircaseClaims) (i := 0) rfl)
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,h⟩ := hrow
    have vx : Raw.coordinatesValid Raw.degrees .sphere 14 138 [2]=true := rfl
    simp only [decode,vx,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      add_zero,Option.some.injEq] at ha
    rw [←ha] at h
    exact h
  obtain ⟨f,hf⟩ := basis_correct
    ⟨.sphere,14,138,["440,1","439,1","23,1,190,1","1,1,418,1","1,1,417,1"]⟩ (by
      exact List.mem_of_getElem? (l := Raw.degrees) (i := 216) rfl)
  change E.Page 2 (14,138) ≃ₗ[ℤ] (Fin 5 →₀ F2) at f
  change ∀ i : Fin 5, f.symm (Finsupp.single i 1)=basis .sphere 14 138 i.val at hf
  obtain ⟨g,hg⟩ := basis_correct
    ⟨.sphere,16,139,["1,1,424,1","0,1,438,1","0,3,418,1"]⟩ (by
      exact List.mem_of_getElem? (l := Raw.degrees) (i := 230) rfl)
  change E.Page 2 (16,139) ≃ₗ[ℤ] (Fin 3 →₀ F2) at g
  change ∀ i : Fin 3, g.symm (Finsupp.single i 1)=basis .sphere 16 139 i.val at hg
  have gc (i : Fin 3) : g (basis .sphere 16 139 i.val)=Finsupp.single i 1 := by
    rw [←hg i,LinearEquiv.apply_symm_apply]
  have gc0 : g (basis .sphere 16 139 0)=Finsupp.single (0 : Fin 3) 1 := gc 0
  have gc1 : g (basis .sphere 16 139 1)=Finsupp.single (1 : Fin 3) 1 := gc 1
  have gc2 : g (basis .sphere 16 139 2)=Finsupp.single (2 : Fin 3) 1 := gc 2
  let δ : E.Page 2 (14,138) ⟶ E.Page 2 (16,139) :=
    E.d 2 (14,138) ≫ eqToHom (congrArg (E.Page 2) h366.target_degree)
  have db1 : δ (basis .sphere 14 138 1)=
      basis .sphere 16 139 1+basis .sphere 16 139 2 := h366.eq_on_page_two.2
  have db01 : δ (basis .sphere 14 138 0+basis .sphere 14 138 1)=
      basis .sphere 16 139 2 := h367.eq_on_page_two.2
  have before3 (x : E.Page 2 (14,138)) (hx : ReachesPage E 3 (14,138) x) :
      δ x=0 := by
    have hd : E.d 2 (14,138) x=0 :=
      represents_d_zero_of_later hs2 (by decide) (represents_two_self _) hx
    simp only [δ,ModuleCat.comp_apply,hd,map_zero]
  have db2 : δ (basis .sphere 14 138 2)=0 := by
    have hd : E.d 2 (14,138) (basis .sphere 14 138 2)=0 :=
      represents_d_zero_of_later hs2 (by decide) (represents_two_self _) hlate
    simp only [δ,ModuleCat.comp_apply,hd,map_zero]
  have db3 : δ (basis .sphere 14 138 3)=0 :=
    before3 _ ⟨0,differential_target_later_zero hs2 (by decide) h309⟩
  have db4 : δ (basis .sphere 14 138 4)=0 :=
    before3 _ ⟨0,differential_target_later_zero hs2 (by decide) h308⟩
  have coord1 : g (δ (basis .sphere 14 138 1)) 0=0 := by
    rw [db1,map_add,gc1,gc2]
    norm_num [Finsupp.add_apply,Finsupp.single_apply]; decide
  have coord0 : g (δ (basis .sphere 14 138 0)) 0=0 := by
    have h := congrArg (fun w => g w 0) db01
    simpa only [map_add,Finsupp.add_apply,coord1,add_zero,gc2,
      Finsupp.single_apply,Fin.reduceEq,if_false] using h
  have columns (i : Fin 5) : g (δ (f.symm (Finsupp.single i 1))) 0=0 := by
    rw [hf i]
    fin_cases i
    · exact coord0
    · exact coord1
    · simp only [db2,map_zero,Finsupp.zero_apply]
    · simp only [db3,map_zero,Finsupp.zero_apply]
    · simp only [db4,map_zero,Finsupp.zero_apply]
  have image_zero (x : E.Page 2 (14,138)) : g (δ x) 0=0 := by
    have hx := finite_basis_expansion f x
    rw [hx,map_sum,map_sum,Finsupp.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : f x i=0
    · simp only [hi,if_true,map_zero,Finsupp.zero_apply]
    · simp only [hi,if_false,columns i]
  obtain ⟨h3,a3,c3,ha3,hc3,heq3⟩ := h324
  have c3ne : c3≠0 := by
    apply represents_next_nonzero_of_not_incoming_at h366.target_degree hs2 (by decide)
      hc3 (represents_two_self _)
    intro z hz
    have h := congrArg (fun w => g w 0) hz
    rw [image_zero z,gc0,Finsupp.single_eq_same] at h
    exact zero_ne_one h
  have hd : HasNonzeroDifferential E 3 (13,137) (16,139)
      (basis .sphere 13 137 2) (basis .sphere 16 139 0) :=
    ⟨h3,a3,c3,ha3,hc3,heq3,c3ne⟩
  have bs : basis .sphere 13 137 2=
      product h4 (atom .x_109_12) (h := T._proof_1) := basis_h4_x109
  have bt : basis .sphere 16 139 0=product h1 (atom .x_122_15_2) := by
    have h := basis_value ⟨.mul (.named .h1) (.named .x_122_15_2),0⟩ (by decide)
    simpa only [Expression.value,Expression.degree,atom_h1] using h
  rw [bs,bt] at hd
  exact hd

public theorem d3_h0Square_x123_13_2 : HasNonzeroDifferential model.classical.sphere 3 (15,138) (18,140)
    (product h0Square (atom .x_123_13_2))
    (product h0Square (atom .x_122_16)) := by
  classical
  let E := model.classical.sphere
  have hs2 : E.r₀≤2 := by
    change model.classical.sphere.r₀≤2
    rw [model.classical.firstPage]
  have h324 : HasDifferential E 3 (13,137) (16,139)
      (basis .sphere 13 137 2) (basis .sphere 16 139 0) := by
    have hrow := result ⟨.sphere, .equation, 3, 13, 137, [2], 16, 139, [0], "S0_AdamsE2_ss", 2917⟩ (by
      exact List.mem_of_getElem? (i := 324) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 3 (13,137) (16,139) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 13 137 [2]=true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 16 139 [0]=true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    exact h
  have h366 : HasDifferential E 2 (14,138) (16,139)
      (basis .sphere 14 138 1) (basis .sphere 16 139 1 + basis .sphere 16 139 2) := by
    have hrow := result ⟨.sphere, .equation, 2, 14, 138, [1], 16, 139, [1, 2], "S0_AdamsE2_ss", 3072⟩ (by
      exact List.mem_of_getElem? (i := 366) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 2 (14,138) (16,139) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 14 138 [1]=true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 16 139 [1, 2]=true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    exact h
  have h367 : HasDifferential E 2 (14,138) (16,139)
      (basis .sphere 14 138 0 + basis .sphere 14 138 1) (basis .sphere 16 139 2) := by
    have hrow := result ⟨.sphere, .equation, 2, 14, 138, [0, 1], 16, 139, [2], "S0_AdamsE2_ss", 3073⟩ (by
      exact List.mem_of_getElem? (i := 367) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 2 (14,138) (16,139) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 14 138 [0, 1]=true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 16 139 [2]=true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    exact h
  have h353 : HasDifferential E 3 (15,138) (18,140)
      (basis .sphere 15 138 2) (basis .sphere 18 140 2) := by
    have hrow := result ⟨.sphere, .equation, 3, 15, 138, [2], 18, 140, [2], "S0_AdamsE2_ss", 3002⟩ (by
      exact List.mem_of_getElem? (i := 353) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 3 (15,138) (18,140) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 15 138 [2]=true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 18 140 [2]=true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    exact h
  obtain ⟨f,hf⟩ := basis_correct ⟨.sphere, 16, 139, ["1,1,424,1", "0,1,438,1", "0,3,418,1"]⟩ (by
    exact List.mem_of_getElem? (i := 230) (by rfl))
  change E.Page 2 (16,139) ≃ₗ[ℤ] (Fin 3 →₀ F2) at f
  change ∀ i : Fin 3, f.symm (Finsupp.single i 1)=basis .sphere 16 139 i.val at hf
  obtain ⟨g,hg⟩ := basis_correct ⟨.sphere, 18, 140, ["8,1,279,1", "1,1,436,1", "0,2,437,1"]⟩ (by
    exact List.mem_of_getElem? (i := 244) (by rfl))
  change E.Page 2 (18,140) ≃ₗ[ℤ] (Fin 3 →₀ F2) at g
  change ∀ i : Fin 3, g.symm (Finsupp.single i 1)=basis .sphere 18 140 i.val at hg
  have hin : E.d 2 (16,139)=0 := by
    obtain ⟨_,_,a0,_,ha0,_⟩ := h324
    have r12 : RepresentsOnPage E 3 (16,139)
        (basis .sphere 16 139 1+basis .sphere 16 139 2) 0 :=
      differential_target_later_zero hs2 (by decide) h366
    have r2 : RepresentsOnPage E 3 (16,139) (basis .sphere 16 139 2) 0 :=
      differential_target_later_zero hs2 (by decide) h367
    have r1 : RepresentsOnPage E 3 (16,139) (basis .sphere 16 139 1) 0 := by
      simpa only [add_sub_cancel_right,sub_self] using represents_sub r12 r2
    have before3 (x : E.Page 2 (16,139)) (hx : ReachesPage E 3 (16,139) x) :
        E.d 2 (16,139) x=0 :=
      represents_d_zero_of_later hs2 (by decide) (represents_two_self _) hx
    apply d_zero_of_complete_representatives (by decide : (2:ℤ)≤2) f
    intro i
    refine ⟨f.symm (Finsupp.single i 1),represents_two_self _,?_⟩
    rw [hf i]
    fin_cases i
    · exact before3 _ ⟨a0,ha0⟩
    · exact before3 _ ⟨0,r1⟩
    · exact before3 _ ⟨0,r2⟩
  have gn : basis .sphere 18 140 2≠0 := by
    have hg2 : g.symm (Finsupp.single (2 : Fin 3) 1)=basis .sphere 18 140 2 := hg 2
    rw [←hg2]
    exact basis_vector_ne_zero g 2
  have deg2 : (16,139)+E.diffDeg 2=(18,140) := by
    simp only [E,Classical.Adams.ClassicalAdamsFamily.sphere,Classical.Adams.ClassicalAdamsFamily.obj,
      model.classical.differentialDegree,Prod.mk_add_mk,Int.reduceAdd,Int.reduceSub]
  have hd := third_nonzero_of_zero_incoming_two_at hs2 h353 hin gn deg2
  have bs : basis .sphere 15 138 2=product (r := (15,138)) h0Square (atom .x_123_13_2) := by
    have h := basis_value ⟨.mul (.mul (.named .h0) (.named .h0)) (.named .x_123_13_2),2⟩ (by decide)
    simp only [Expression.value,Expression.degree,atom_h0] at h
    change basis .sphere 15 138 2=product h0Square (atom .x_123_13_2) at h
    exact h
  have bt : basis .sphere 18 140 2=product (r := (18,140)) h0Square (atom .x_122_16) := by
    have h := basis_value ⟨.mul (.mul (.named .h0) (.named .h0)) (.named .x_122_16),2⟩ (by decide)
    simp only [Expression.value,Expression.degree,atom_h0] at h
    change basis .sphere 18 140 2=product h0Square (atom .x_122_16) at h
    exact h
  rw [bs,bt] at hd
  exact hd

public theorem d3_x126_4 : HasNonzeroDifferential model.classical.sphere 3 (4,130) (7,132)
    (atom .x_126_4) (product h0Square (atom .x_125_5)) := by
  classical
  let E := model.classical.sphere
  have hs2 : E.r₀≤2 := by
    change model.classical.sphere.r₀≤2
    rw [model.classical.firstPage]
  have h153 : HasDifferential E 2 (3,130) (5,131)
      (basis .sphere 3 130 1) (basis .sphere 5 131 0) := by
    have hrow := result ⟨.sphere, .equation, 2, 3, 130, [1], 5, 131, [0], "S0_AdamsE2_ss", 2439⟩ (by
      exact List.mem_of_getElem? (i := 153) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 2 (3,130) (5,131) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 3 130 [1]=true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 5 131 [0]=true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    exact h
  have h157 : HasDifferential E 3 (4,130) (7,132)
      (basis .sphere 4 130 0) (basis .sphere 7 132 0) := by
    have hrow := result ⟨.sphere, .equation, 3, 4, 130, [0], 7, 132, [0], "S0_AdamsE2_ss", 2437⟩ (by
      exact List.mem_of_getElem? (i := 157) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 3 (4,130) (7,132) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 4 130 [0]=true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 7 132 [0]=true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    exact h
  obtain ⟨f,hf⟩ := basis_correct ⟨.sphere, 5, 131, ["0,3,69,2"]⟩ (by
    exact List.mem_of_getElem? (i := 127) (by rfl))
  change E.Page 2 (5,131) ≃ₗ[ℤ] (Fin 1 →₀ F2) at f
  change ∀ i : Fin 1, f.symm (Finsupp.single i 1)=basis .sphere 5 131 i.val at hf
  obtain ⟨g,hg⟩ := basis_correct ⟨.sphere, 7, 132, ["0,2,340,1"]⟩ (by
    exact List.mem_of_getElem? (i := 149) (by rfl))
  change E.Page 2 (7,132) ≃ₗ[ℤ] (Fin 1 →₀ F2) at g
  change ∀ i : Fin 1, g.symm (Finsupp.single i 1)=basis .sphere 7 132 i.val at hg
  have hin : E.d 2 (5,131)=0 := by
    obtain ⟨a,ha,hda⟩ := differential_target_cycle h153
    rw [←ha.eq_on_page_two] at hda
    apply d_zero_of_complete_representatives (by decide : (2:ℤ)≤2) f
    intro i
    refine ⟨f.symm (Finsupp.single i 1),represents_two_self _,?_⟩
    rw [hf i]
    fin_cases i
    exact hda
  have gn : basis .sphere 7 132 0≠0 := by
    have hg0 : g.symm (Finsupp.single (0 : Fin 1) 1)=basis .sphere 7 132 0 := hg 0
    rw [←hg0]
    exact basis_vector_ne_zero g 0
  have deg2 : (5,131)+E.diffDeg 2=(7,132) := by
    simp only [E,Classical.Adams.ClassicalAdamsFamily.sphere,Classical.Adams.ClassicalAdamsFamily.obj,
      model.classical.differentialDegree,Prod.mk_add_mk,Int.reduceAdd,Int.reduceSub]
  have hd := third_nonzero_of_zero_incoming_two_at hs2 h157 hin gn deg2
  have bs : basis .sphere 4 130 0=atom .x_126_4 := by
    have h := basis_value ⟨.named .x_126_4,0⟩ (by decide)
    exact h
  have bt : basis .sphere 7 132 0=product (r := (7,132)) h0Square (atom .x_125_5) := by
    have h := basis_value ⟨.mul (.mul (.named .h0) (.named .h0)) (.named .x_125_5),0⟩ (by decide)
    simp only [Expression.value,Expression.degree,atom_h0] at h
    change basis .sphere 7 132 0=product h0Square (atom .x_125_5) at h
    exact h
  rw [bs,bt] at hd
  exact hd

private theorem d7MainStart : model.classical.sphere.r₀≤2 := by rw [model.classical.firstPage]

private theorem d7MainRow271 : HasDifferential model.classical.sphere 7 (11,134) (18,140)
    (basis .sphere 11 134 0 + basis .sphere 11 134 1 + basis .sphere 11 134 3) (basis .sphere 18 140 1) := by
  have h := result ⟨.sphere, .equation, 7, 11, 134, [0, 1, 3], 18, 140, [1], "S0_AdamsE2_ss", 2687⟩ (by exact List.mem_of_getElem? (i := 271) rfl)
  dsimp only [Statement] at h
  obtain ⟨a,ha,b,hb,h⟩ := h
  change HasDifferential model.classical.sphere 7 (11,134) (18,140) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 11 134 [0, 1, 3]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 18 140 [1]=true := rfl
  delta decode at ha hb
  simp (config := { congrConsts := false }) only [vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem d7MainRow324 : HasDifferential model.classical.sphere 3 (13,137) (16,139)
    (basis .sphere 13 137 2) (basis .sphere 16 139 0) := by
  have h := result ⟨.sphere, .equation, 3, 13, 137, [2], 16, 139, [0], "S0_AdamsE2_ss", 2917⟩ (by exact List.mem_of_getElem? (i := 324) rfl)
  dsimp only [Statement] at h
  obtain ⟨a,ha,b,hb,h⟩ := h
  change HasDifferential model.classical.sphere 3 (13,137) (16,139) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 13 137 [2]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 16 139 [0]=true := rfl
  delta decode at ha hb
  simp (config := { congrConsts := false }) only [vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  exact h

private theorem d7MainRow366 : HasDifferential model.classical.sphere 2 (14,138) (16,139)
    (basis .sphere 14 138 1) (basis .sphere 16 139 1 + basis .sphere 16 139 2) := by
  have h := result ⟨.sphere, .equation, 2, 14, 138, [1], 16, 139, [1, 2], "S0_AdamsE2_ss", 3072⟩ (by exact List.mem_of_getElem? (i := 366) rfl)
  dsimp only [Statement] at h
  obtain ⟨a,ha,b,hb,h⟩ := h
  change HasDifferential model.classical.sphere 2 (14,138) (16,139) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 14 138 [1]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 16 139 [1, 2]=true := rfl
  delta decode at ha hb
  simp (config := { congrConsts := false }) only [vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  exact h

private theorem d7MainRow367 : HasDifferential model.classical.sphere 2 (14,138) (16,139)
    (basis .sphere 14 138 0 + basis .sphere 14 138 1) (basis .sphere 16 139 2) := by
  have h := result ⟨.sphere, .equation, 2, 14, 138, [0, 1], 16, 139, [2], "S0_AdamsE2_ss", 3073⟩ (by exact List.mem_of_getElem? (i := 367) rfl)
  dsimp only [Statement] at h
  obtain ⟨a,ha,b,hb,h⟩ := h
  change HasDifferential model.classical.sphere 2 (14,138) (16,139) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 14 138 [0, 1]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 16 139 [2]=true := rfl
  delta decode at ha hb
  simp (config := { congrConsts := false }) only [vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  exact h

private theorem d7MainRow297 : HasDifferential model.classical.sphere 3 (9,133) (12,135)
    (basis .sphere 9 133 1 + basis .sphere 9 133 2) (basis .sphere 12 135 0) := by
  have h := result ⟨.sphere, .equation, 3, 9, 133, [1, 2], 12, 135, [0], "S0_AdamsE2_ss", 2775⟩ (by exact List.mem_of_getElem? (i := 297) rfl)
  dsimp only [Statement] at h
  obtain ⟨a,ha,b,hb,h⟩ := h
  change HasDifferential model.classical.sphere 3 (9,133) (12,135) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 133 [1, 2]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 135 [0]=true := rfl
  delta decode at ha hb
  simp (config := { congrConsts := false }) only [vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  exact h

private theorem d7MainRow298 : HasDifferential model.classical.sphere 3 (9,133) (12,135)
    (basis .sphere 9 133 0 + basis .sphere 9 133 2) (basis .sphere 12 135 1 + basis .sphere 12 135 2) := by
  have h := result ⟨.sphere, .equation, 3, 9, 133, [0, 2], 12, 135, [1, 2], "S0_AdamsE2_ss", 2776⟩ (by exact List.mem_of_getElem? (i := 298) rfl)
  dsimp only [Statement] at h
  obtain ⟨a,ha,b,hb,h⟩ := h
  change HasDifferential model.classical.sphere 3 (9,133) (12,135) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 133 [0, 2]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 135 [1, 2]=true := rfl
  delta decode at ha hb
  simp (config := { congrConsts := false }) only [vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  exact h

private theorem d7MainRow299 : HasDifferential model.classical.sphere 5 (7,131) (12,135)
    (basis .sphere 7 131 1) (basis .sphere 12 135 2) := by
  have h := result ⟨.sphere, .equation, 5, 7, 131, [1], 12, 135, [2], "S0_AdamsE2_ss", 2777⟩ (by exact List.mem_of_getElem? (i := 299) rfl)
  dsimp only [Statement] at h
  obtain ⟨a,ha,b,hb,h⟩ := h
  change HasDifferential model.classical.sphere 5 (7,131) (12,135) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 7 131 [1]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 135 [2]=true := rfl
  delta decode at ha hb
  simp (config := { congrConsts := false }) only [vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  exact h

private theorem d7MainRow351 : HasDifferential model.classical.sphere 4 (11,135) (15,138)
    (basis .sphere 11 135 1 + basis .sphere 11 135 2) (basis .sphere 15 138 0) := by
  have h := result ⟨.sphere, .equation, 4, 11, 135, [1, 2], 15, 138, [0], "S0_AdamsE2_ss", 3000⟩ (by exact List.mem_of_getElem? (i := 351) rfl)
  dsimp only [Statement] at h
  obtain ⟨a,ha,b,hb,h⟩ := h
  change HasDifferential model.classical.sphere 4 (11,135) (15,138) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 11 135 [1, 2]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 15 138 [0]=true := rfl
  delta decode at ha hb
  simp (config := { congrConsts := false }) only [vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  exact h

private theorem d7MainRow352 : HasDifferential model.classical.sphere 5 (10,134) (15,138)
    (basis .sphere 10 134 3) (basis .sphere 15 138 1) := by
  have h := result ⟨.sphere, .equation, 5, 10, 134, [3], 15, 138, [1], "S0_AdamsE2_ss", 3001⟩ (by exact List.mem_of_getElem? (i := 352) rfl)
  dsimp only [Statement] at h
  obtain ⟨a,ha,b,hb,h⟩ := h
  change HasDifferential model.classical.sphere 5 (10,134) (15,138) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 134 [3]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 15 138 [1]=true := rfl
  delta decode at ha hb
  simp (config := { congrConsts := false }) only [vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  exact h

private theorem d7MainRow353 : HasDifferential model.classical.sphere 3 (15,138) (18,140)
    (basis .sphere 15 138 2) (basis .sphere 18 140 2) := by
  have h := result ⟨.sphere, .equation, 3, 15, 138, [2], 18, 140, [2], "S0_AdamsE2_ss", 3002⟩ (by exact List.mem_of_getElem? (i := 353) rfl)
  dsimp only [Statement] at h
  obtain ⟨a,ha,b,hb,h⟩ := h
  change HasDifferential model.classical.sphere 3 (15,138) (18,140) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 15 138 [2]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 18 140 [2]=true := rfl
  delta decode at ha hb
  simp (config := { congrConsts := false }) only [vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  exact h

private theorem d7MainBasis244 : ∃ e : model.classical.sphere.Page 2 (18,140) ≃ₗ[ℤ] (Fin 3 →₀ F2),
    ∀ j : Fin 3, e.symm (Finsupp.single j 1)=basis .sphere 18 140 j.val := by
  exact basis_correct ⟨.sphere, 18, 140, ["8,1,279,1", "1,1,436,1", "0,2,437,1"]⟩ (by exact List.mem_of_getElem? (i := 244) rfl)

private theorem d7MainBasis230 : ∃ e : model.classical.sphere.Page 2 (16,139) ≃ₗ[ℤ] (Fin 3 →₀ F2),
    ∀ j : Fin 3, e.symm (Finsupp.single j 1)=basis .sphere 16 139 j.val := by
  exact basis_correct ⟨.sphere, 16, 139, ["1,1,424,1", "0,1,438,1", "0,3,418,1"]⟩ (by exact List.mem_of_getElem? (i := 230) rfl)

private theorem d7MainBasis199 : ∃ e : model.classical.sphere.Page 2 (12,135) ≃ₗ[ℤ] (Fin 3 →₀ F2),
    ∀ j : Fin 3, e.symm (Finsupp.single j 1)=basis .sphere 12 135 j.val := by
  exact basis_correct ⟨.sphere, 12, 135, ["408,1", "0,1,386,1", "0,2,69,1,80,1"]⟩ (by exact List.mem_of_getElem? (i := 199) rfl)

private theorem d7MainBasis222 : ∃ e : model.classical.sphere.Page 2 (15,138) ≃ₗ[ℤ] (Fin 3 →₀ F2),
    ∀ j : Fin 3, e.symm (Finsupp.single j 1)=basis .sphere 15 138 j.val := by
  exact basis_correct ⟨.sphere, 15, 138, ["438,1", "7,1,279,1", "0,2,418,1"]⟩ (by exact List.mem_of_getElem? (i := 222) rfl)

private theorem d7MainZeroOfCompleteZero
    {E : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ×ℤ)}
    {r : ℤ} {p : ℤ×ℤ} {n : ℕ} (hr : 2≤r)
    (e : E.Page 2 p ≃ₗ[ℤ] (Fin n →₀ F2))
    (he : ∀ i : Fin n, RepresentsOnPage E r p (e.symm (Finsupp.single i 1)) 0)
    (z : E.Page r p) : z=0 := by
  obtain ⟨c,hc⟩ := page_generated_from_representatives hr e (fun _ => 0) he z
  simpa only [ite_self,Finset.sum_const_zero] using hc

private theorem d7MainD2ZeroOfThirdReps
    {E : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ×ℤ)}
    {p : ℤ×ℤ} {n : ℕ} (hs : E.r₀≤2)
    (e : E.Page 2 p ≃ₗ[ℤ] (Fin n →₀ F2))
    (he : ∀ i : Fin n, ReachesPage E 3 p (e.symm (Finsupp.single i 1))) : E.d 2 p=0 := by
  apply d_zero_of_complete_representatives (by decide : (2:ℤ)≤2) e
  intro i
  refine ⟨e.symm (Finsupp.single i 1),represents_two_self _,?_⟩
  exact represents_d_zero_of_later hs (by decide : (2:ℤ)<3) (represents_two_self _) (he i)

private theorem d7MainIncomingTwo : model.classical.sphere.d 2 (16,139)=0 := by
  with_unfolding_all
    obtain ⟨e,he⟩ := d7MainBasis230
    obtain ⟨_,_,a0,_,ha0,_⟩ := d7MainRow324
    have h12 : RepresentsOnPage model.classical.sphere 3 (16,139)
        (basis .sphere 16 139 1+basis .sphere 16 139 2) 0 :=
      differential_target_later_zero d7MainStart (by decide : (2:ℤ)<3) d7MainRow366
    have h2 : RepresentsOnPage model.classical.sphere 3 (16,139)
        (basis .sphere 16 139 2) 0 :=
      differential_target_later_zero d7MainStart (by decide : (2:ℤ)<3) d7MainRow367
    have h1 : RepresentsOnPage model.classical.sphere 3 (16,139)
        (basis .sphere 16 139 1) 0 := by
      simpa only [add_sub_cancel_right,sub_self] using represents_sub h12 h2
    apply d7MainD2ZeroOfThirdReps d7MainStart e
    intro i
    rw [he i]
    fin_cases i
    · exact ⟨a0,ha0⟩
    · exact ⟨0,h1⟩
    · exact ⟨0,h2⟩

private theorem d7MainSixSourceZero (z : model.classical.sphere.Page 6 (12,135)) : z=0 := by
  with_unfolding_all
    obtain ⟨e,he⟩ := d7MainBasis199
    have h0 : RepresentsOnPage model.classical.sphere 6 (12,135)
        (basis .sphere 12 135 0) 0 :=
      differential_target_later_zero (by have h:=d7MainStart;omega) (by decide : (3:ℤ)<6) d7MainRow297
    have h12 : RepresentsOnPage model.classical.sphere 6 (12,135)
        (basis .sphere 12 135 1+basis .sphere 12 135 2) 0 :=
      differential_target_later_zero (by have h:=d7MainStart;omega) (by decide : (3:ℤ)<6) d7MainRow298
    have h2 : RepresentsOnPage model.classical.sphere 6 (12,135)
        (basis .sphere 12 135 2) 0 :=
      differential_target_later_zero (by have h:=d7MainStart;omega) (by decide : (5:ℤ)<6) d7MainRow299
    have h1 : RepresentsOnPage model.classical.sphere 6 (12,135)
        (basis .sphere 12 135 1) 0 := by
      simpa only [add_sub_cancel_right,sub_self] using represents_sub h12 h2
    apply d7MainZeroOfCompleteZero (by decide : (2:ℤ)≤6) e ?_ z
    intro i
    rw [he i]
    fin_cases i
    · exact h0
    · exact h1
    · exact h2

private theorem d7MainLabelsEqual
    {E : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ×ℤ)}
    (hs : E.r₀≤2) {p q : ℤ×ℤ} (hdeg : p+E.diffDeg 2=q) (hin : E.d 2 p=0)
    {x y : E.Page 2 q} {a : E.Page 3 q}
    (hx : RepresentsOnPage E 3 q x a) (hy : RepresentsOnPage E 3 q y a) : x=y := by
  by_contra hxy
  have hn : x-y≠0 := sub_ne_zero.mpr hxy
  have hz : RepresentsOnPage E 3 q (x-y) 0 := by
    simpa only [sub_self] using represents_sub hx hy
  have hzero : (0 : E.Page 3 q)≠0 :=
    represents_next_nonzero_of_incoming_zero_at hs (by decide) hin hz
      (represents_two_self _) hn hdeg
  exact hzero rfl

private theorem d7MainSourceBinding :
    basis .sphere 11 134 0+basis .sphere 11 134 1+basis .sphere 11 134 3=d7Source := by
  have v0 : basis .sphere 11 134 0=atom .x_123_11_2 := basis_value ⟨.named .x_123_11_2,0⟩ (by decide)
  have v1 : basis .sphere 11 134 1=atom .x_123_11 := basis_value ⟨.named .x_123_11,1⟩ (by decide)
  have h3 := basis_value ⟨.mul (.named .h0) (.mul (.named .h6) (.named .b4)),3⟩ (by decide)
  change basis .sphere 11 134 3=product (r := (11,134)) (atom .h0)
    (product (r := (10,133)) (atom .h6) (atom .b4)) at h3
  rw [atom_h0,atom_h6] at h3
  have ha : product (r := (11,134)) (product (r := (2,65)) h0 h6) (atom .b4)=
      product (r := (11,134)) h0 (product (r := (10,133)) h6 (atom .b4)) :=
    eq_of_heq (model.sphereAlgebra.assoc (1,1) (1,64) (9,69) h0 h6 (atom .b4))
  rw [v0,v1,h3,←ha]
  rfl

private theorem d7MainTargetBinding : basis .sphere 18 140 1=product h1 (atom .x_121_17) := by
  have h := basis_value ⟨.mul (.named .h1) (.named .x_121_17),1⟩ (by decide)
  simpa only [Expression.value,Expression.degree,atom_h1] using h

private theorem d7MainIncomingDegree (r : ℤ) :
    (18-r,141-r)+model.classical.sphere.diffDeg r=(18,140) := by
  simp only [ClassicalAdamsFamily.sphere,ClassicalAdamsFamily.obj,
    model.classical.differentialDegree,Prod.mk_add_mk,Prod.mk.injEq]
  constructor <;> omega

private theorem d7MainThirdAvoid
    {y : model.classical.sphere.Page 3 (18,140)}
    (hy : RepresentsOnPage model.classical.sphere 3 (18,140) (basis .sphere 18 140 1) y)
    (v : model.classical.sphere.Page 3 (15,138)) :
    (model.classical.sphere.d 3 (15,138) ≫
      eqToHom (congrArg (model.classical.sphere.Page 3) (d7MainIncomingDegree 3))) v≠y := by
  with_unfolding_all
    let E := model.classical.sphere
    obtain ⟨e,he⟩ := d7MainBasis222
    obtain ⟨f,hf⟩ := d7MainBasis244
    obtain ⟨_,_,a04,_,ha04,_⟩ := d7MainRow351
    obtain ⟨_,_,a15,_,ha15,_⟩ := d7MainRow352
    obtain ⟨a0,ha0⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤4) ha04
    obtain ⟨a1,ha1⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤5) ha15
    obtain ⟨deg,a2,b,ha2,hb,hd2⟩ := d7MainRow353
    let δ : E.Page 3 (15,138) ⟶ E.Page 3 (18,140) :=
      E.d 3 (15,138) ≫ eqToHom (congrArg (E.Page 3) (d7MainIncomingDegree 3))
    have d0 : δ a0=0 := by
      have hz := represents_d_zero_of_later (by have h:=d7MainStart;omega)
        (by decide : (3:ℤ)<4) ha0 ⟨a04,ha04⟩
      dsimp only [δ]
      rw [ModuleCat.comp_apply,hz,map_zero]
    have d1 : δ a1=0 := by
      have hz := represents_d_zero_of_later (by have h:=d7MainStart;omega)
        (by decide : (3:ℤ)<5) ha1 ⟨a15,ha15⟩
      dsimp only [δ]
      rw [ModuleCat.comp_apply,hz,map_zero]
    have d2 : δ a2=b := hd2
    have hf1 : f.symm (Finsupp.single (1:Fin 3) 1)=basis .sphere 18 140 1 := hf 1
    have hf2 : f.symm (Finsupp.single (2:Fin 3) 1)=basis .sphere 18 140 2 := hf 2
    have n1 : basis .sphere 18 140 1≠0 := by
      rw [←hf1];exact basis_vector_ne_zero f 1
    have yne : y≠0 := represents_next_nonzero_of_incoming_zero_at
      d7MainStart (by decide : (2:ℤ)≤2) d7MainIncomingTwo hy (represents_two_self _) n1 (d7MainIncomingDegree 2)
    have n12 : basis .sphere 18 140 1≠basis .sphere 18 140 2 := by
      intro hh
      have e1 : f (basis .sphere 18 140 1)=Finsupp.single (1:Fin 3) 1 := by
        rw [←hf1,LinearEquiv.apply_symm_apply]
      have e2 : f (basis .sphere 18 140 2)=Finsupp.single (2:Fin 3) 1 := by
        rw [←hf2,LinearEquiv.apply_symm_apply]
      have hcoord := congrArg (fun x=>f x 1) hh
      rw [e1,e2] at hcoord
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hcoord
    let vv : Fin 3 → E.Page 3 (15,138) := ![a0,a1,a2]
    have reps (i : Fin 3) : RepresentsOnPage E 3 (15,138)
        (e.symm (Finsupp.single i 1)) (vv i) := by
      rw [he i]
      fin_cases i
      · exact ha0
      · exact ha1
      · exact ha2
    obtain ⟨bits,hv⟩ := page_generated_from_representatives (by decide : (2:ℤ)≤3) e vv reps v
    simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero] at hv
    change v=(if bits 0=0 then 0 else a0)+
      ((if bits 1=0 then 0 else a1)+(if bits 2=0 then 0 else a2)) at hv
    have bit (c : F2) (a : E.Page 3 (15,138)) :
        δ (if c=0 then 0 else a)=if c=0 then 0 else δ a := by
      by_cases hc : c=0 <;> simp only [hc,ite_true,ite_false,map_zero]
    have dv := congrArg δ hv
    simp only [map_add,bit,d0,d1,d2,ite_self,zero_add] at dv
    intro hit
    change δ v=y at hit
    by_cases hc : bits 2=0
    · have hz : δ v=0 := by simpa only [hc,ite_true] using dv
      exact yne (hit.symm.trans hz)
    · have hb' : δ v=b := by simpa only [hc,ite_false] using dv
      have eqby : b=y := hb'.symm.trans hit
      rw [eqby] at hb
      exact n12 (d7MainLabelsEqual d7MainStart (d7MainIncomingDegree 2) d7MainIncomingTwo hy hb)


private theorem d7FourteenD351 : HasDifferential model.classical.sphere 4 (11,135) (15,138)
    (basis .sphere 11 135 1 + basis .sphere 11 135 2) (basis .sphere 15 138 0) := by
  have hrow := result ⟨.sphere,.equation,4,11,135,[1, 2],15,138,[0],"S0_AdamsE2_ss",3000⟩ (by
    exact List.mem_of_getElem? (i := 351) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential model.classical.sphere 4 (11,135) (15,138) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 11 135 [1, 2]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 15 138 [0]=true := rfl
  delta decode at ha hb
  simp (config := { congrConsts := false }) only [vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  exact h

private theorem d7FourteenD352 : HasDifferential model.classical.sphere 5 (10,134) (15,138)
    (basis .sphere 10 134 3) (basis .sphere 15 138 1) := by
  have hrow := result ⟨.sphere,.equation,5,10,134,[3],15,138,[1],"S0_AdamsE2_ss",3001⟩ (by
    exact List.mem_of_getElem? (i := 352) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential model.classical.sphere 5 (10,134) (15,138) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 134 [3]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 15 138 [1]=true := rfl
  delta decode at ha hb
  simp (config := { congrConsts := false }) only [vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  exact h

private theorem d7FourteenD353 : HasDifferential model.classical.sphere 3 (15,138) (18,140)
    (basis .sphere 15 138 2) (basis .sphere 18 140 2) := by
  have hrow := result ⟨.sphere,.equation,3,15,138,[2],18,140,[2],"S0_AdamsE2_ss",3002⟩ (by
    exact List.mem_of_getElem? (i := 353) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential model.classical.sphere 3 (15,138) (18,140) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 15 138 [2]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 18 140 [2]=true := rfl
  delta decode at ha hb
  simp (config := { congrConsts := false }) only [vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  exact h

private theorem d7FourteenD338 : HasDifferential model.classical.sphere 2 (12,136) (14,137)
    (basis .sphere 12 136 2) (basis .sphere 14 137 2) := by
  have hrow := result ⟨.sphere,.equation,2,12,136,[2],14,137,[2],"S0_AdamsE2_ss",2911⟩ (by
    exact List.mem_of_getElem? (i := 338) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential model.classical.sphere 2 (12,136) (14,137) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 12 136 [2]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 14 137 [2]=true := rfl
  delta decode at ha hb
  simp (config := { congrConsts := false }) only [vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  exact h

private theorem d7FourteenD339 : HasDifferential model.classical.sphere 3 (14,137) (17,139)
    (basis .sphere 14 137 1) (basis .sphere 17 139 1) := by
  have hrow := result ⟨.sphere,.equation,3,14,137,[1],17,139,[1],"S0_AdamsE2_ss",2912⟩ (by
    exact List.mem_of_getElem? (i := 339) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential model.classical.sphere 3 (14,137) (17,139) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 14 137 [1]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 17 139 [1]=true := rfl
  delta decode at ha hb
  simp (config := { congrConsts := false }) only [vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  exact h

private theorem d7FourteenD340 : HasDifferential model.classical.sphere 3 (14,137) (17,139)
    (basis .sphere 14 137 0) (basis .sphere 17 139 0) := by
  have hrow := result ⟨.sphere,.equation,3,14,137,[0],17,139,[0],"S0_AdamsE2_ss",2913⟩ (by
    exact List.mem_of_getElem? (i := 340) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential model.classical.sphere 3 (14,137) (17,139) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 14 137 [0]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 17 139 [0]=true := rfl
  delta decode at ha hb
  simp (config := { congrConsts := false }) only [vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  exact h

private theorem d7Early_d2_15_138_zero : model.classical.sphere.d 2 (15,138)=0 := by
  with_unfolding_all
    classical
    let E := model.classical.sphere
    have hs2 : E.r₀≤2 := by rw [model.classical.firstPage]
    obtain ⟨e,he⟩ := basis_correct ⟨.sphere,15,138,["438,1","7,1,279,1","0,2,418,1"]⟩ (by
      exact List.mem_of_getElem? (i := 222) (by rfl))
    change E.Page 2 (15,138) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e
    change ∀ i : Fin 3, e.symm (Finsupp.single i 1)=basis .sphere 15 138 i.val at he
    have dz (i : ℕ) {r : ℤ} (hr : 2<r)
        (hx : ReachesPage E r (15,138) (basis .sphere 15 138 i)) :
        E.d 2 (15,138) (basis .sphere 15 138 i)=0 :=
      represents_d_zero_of_later hs2 hr (represents_two_self _) hx
    have d0 : E.d 2 (15,138) (basis .sphere 15 138 0)=0 := by
      obtain ⟨_,a,b,ha,hb,hd⟩ := d7FourteenD351
      exact dz 0 (by decide) ⟨b,hb⟩
    have d1 : E.d 2 (15,138) (basis .sphere 15 138 1)=0 := by
      obtain ⟨_,a,b,ha,hb,hd⟩ := d7FourteenD352
      exact dz 1 (by decide) ⟨b,hb⟩
    have d2 : E.d 2 (15,138) (basis .sphere 15 138 2)=0 := by
      obtain ⟨_,a,b,ha,hb,hd⟩ := d7FourteenD353
      exact dz 2 (by decide) ⟨a,ha⟩
    have cols (i : Fin 3) : E.d 2 (15,138) (e.symm (Finsupp.single i 1))=0 := by
      rw [he]
      fin_cases i
      · exact d0
      · exact d1
      · exact d2
    ext x
    change E.d 2 (15,138) x=0
    have hx := finite_basis_expansion e x
    rw [hx,map_sum]
    apply Finset.sum_eq_zero
    intro i hi
    by_cases hc : e x i=0
    · simp only [hc,ite_true,map_zero]
    · simp only [hc,ite_false,cols]

private theorem d7FourteenFourthAt
    {E : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ×ℤ)} {p q : ℤ×ℤ}
    (hdeg : p+E.diffDeg 3=q) (hstart : E.r₀≤2)
    (e : E.Page 2 p ≃ₗ[ℤ] (Fin 3 →₀ F2))
    (y0 y1 : E.Page 2 q)
    (h0 : HasDifferential E 3 p q (e.symm (Finsupp.single 0 1)) y0)
    (h1 : HasDifferential E 3 p q (e.symm (Finsupp.single 1 1)) y1)
    (hz : RepresentsOnPage E 3 p (e.symm (Finsupp.single 2 1)) 0)
    (hin : E.d 2 (q-E.diffDeg 2)=0)
    (hn0 : y0≠0) (hn1 : y1≠0) (hn01 : y0+y1≠0) : Subsingleton (E.Page 4 p) := by
  subst q
  exact fourth_zero_of_three_basis hstart e y0 y1 h0 h1 hz hin hn0 hn1 hn01

private theorem d7Early_fourteen_four_zero :
    ∀ z : model.classical.sphere.Page 4 (14,137), z=0 := by
  with_unfolding_all
    let E := model.classical.sphere
    have hs2 : E.r₀≤2 := by rw [model.classical.firstPage]
    obtain ⟨e,he⟩ := basis_correct ⟨.sphere,14,137,["23,1,181,1","0,1,418,1","0,3,386,1"]⟩ (by
      exact List.mem_of_getElem? (i := 215) (by rfl))
    change E.Page 2 (14,137) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e
    change ∀ i : Fin 3, e.symm (Finsupp.single i 1)=basis .sphere 14 137 i.val at he
    have he0 : e.symm (Finsupp.single (0:Fin 3) 1)=basis .sphere 14 137 0 := he 0
    have he1 : e.symm (Finsupp.single (1:Fin 3) 1)=basis .sphere 14 137 1 := he 1
    have he2 : e.symm (Finsupp.single (2:Fin 3) 1)=basis .sphere 14 137 2 := he 2
    obtain ⟨g,hg⟩ := basis_correct ⟨.sphere,17,139,["13,3,76,1","0,1,437,1"]⟩ (by
      exact List.mem_of_getElem? (i := 237) (by rfl))
    change E.Page 2 (17,139) ≃ₗ[ℤ] (Fin 2 →₀ F2) at g
    change ∀ i : Fin 2, g.symm (Finsupp.single i 1)=basis .sphere 17 139 i.val at hg
    have hg0 : g.symm (Finsupp.single (0:Fin 2) 1)=basis .sphere 17 139 0 := hg 0
    have hg1 : g.symm (Finsupp.single (1:Fin 2) 1)=basis .sphere 17 139 1 := hg 1
    have n0 : basis .sphere 17 139 0≠0 := by
      rw [←hg0]
      exact basis_vector_ne_zero g 0
    have n1 : basis .sphere 17 139 1≠0 := by
      rw [←hg1]
      exact basis_vector_ne_zero g 1
    have g0 : g (basis .sphere 17 139 0)=Finsupp.single (0:Fin 2) 1 := by
      rw [←hg0,LinearEquiv.apply_symm_apply]
    have g1 : g (basis .sphere 17 139 1)=Finsupp.single (1:Fin 2) 1 := by
      rw [←hg1,LinearEquiv.apply_symm_apply]
    have n01 : basis .sphere 17 139 0+basis .sphere 17 139 1≠0 := by
      intro h
      have hh := congrArg (fun y => g y (0:Fin 2)) h
      norm_num [map_add,g0,g1,map_zero,Finsupp.single_apply,Fin.ext_iff] at hh
    have hd0 : HasDifferential E 3 (14,137) (17,139) (e.symm (Finsupp.single 0 1)) (basis .sphere 17 139 0) := by
      rw [he0]
      exact d7FourteenD340
    have hd1 : HasDifferential E 3 (14,137) (17,139) (e.symm (Finsupp.single 1 1)) (basis .sphere 17 139 1) := by
      rw [he1]
      exact d7FourteenD339
    have hz : RepresentsOnPage E 3 (14,137) (e.symm (Finsupp.single 2 1)) 0 := by
      rw [he2]
      exact differential_target_later_zero hs2 (by decide) d7FourteenD338
    have hpre : (17,139)-E.diffDeg 2=(15,138) := by
      simp only [E,ClassicalAdamsFamily.sphere,ClassicalAdamsFamily.obj,
        model.classical.differentialDegree,Prod.mk_sub_mk,Int.reduceSub]
    have hin : E.d 2 ((17,139)-E.diffDeg 2)=0 := by
      rw [hpre]
      exact d7Early_d2_15_138_zero
    haveI := d7FourteenFourthAt d7FourteenD340.target_degree hs2 e
      (basis .sphere 17 139 0) (basis .sphere 17 139 1) hd0 hd1 hz hin n0 n1 n01
    intro z
    exact Subsingleton.elim _ _


/- These private proofs consume the registered upstream Table.result and
sphere basis/comparison responsibilities; no new mathematical assumptions. -/
private theorem d7Thirteen_equation {r s t ts tt : ℕ} {xs ys : List ℕ}
    {origin : String} {record : ℕ}
    (hc : (⟨.sphere,.equation,r,s,t,xs,ts,tt,ys,origin,record⟩ : Raw.Claim) ∈ Raw.claims)
    (vx : Raw.coordinatesValid Raw.degrees .sphere s t xs=true)
    (vy : Raw.coordinatesValid Raw.degrees .sphere ts tt ys=true) :
    HasDifferential model.classical.sphere r (s,t) (ts,tt)
      ((xs.map (basis .sphere s t)).sum) ((ys.map (basis .sphere ts tt)).sum) := by
  have hrow := result ⟨.sphere,.equation,r,s,t,xs,ts,tt,ys,origin,record⟩ hc
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,h⟩ := hrow
  delta decode at hx hy
  simp (config := { congrConsts := false }) only [vx,vy,if_true,Option.some.injEq] at hx hy
  rw [←hx,←hy] at h
  exact h

private theorem d7Thirteen_raw318 :
    HasDifferential model.classical.sphere 2 (11,135) (13,136)
      (basis .sphere 11 135 2) (basis .sphere 13 136 2) := by
  have h := d7Thirteen_equation (r := 2) (s := 11) (t := 135) (ts := 13) (tt := 136)
    (xs := [2]) (ys := [2])
    (origin := "S0_AdamsE2_ss") (record := 2842)
    (by exact List.mem_of_getElem? (i := 318) (by rfl)) (by rfl) (by rfl)
  simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Nat.cast_ofNat] using h

private theorem d7Thirteen_raw319 :
    HasDifferential model.classical.sphere 3 (13,136) (16,138)
      (basis .sphere 13 136 1) (basis .sphere 16 138 1) := by
  have h := d7Thirteen_equation (r := 3) (s := 13) (t := 136) (ts := 16) (tt := 138)
    (xs := [1]) (ys := [1])
    (origin := "S0_AdamsE2_ss") (record := 2843)
    (by exact List.mem_of_getElem? (i := 319) (by rfl)) (by rfl) (by rfl)
  simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Nat.cast_ofNat] using h

private theorem d7Thirteen_raw320 :
    HasDifferential model.classical.sphere 3 (13,136) (16,138)
      (basis .sphere 13 136 0) (basis .sphere 16 138 0 + basis .sphere 16 138 2) := by
  have h := d7Thirteen_equation (r := 3) (s := 13) (t := 136) (ts := 16) (tt := 138)
    (xs := [0]) (ys := [0,2])
    (origin := "S0_AdamsE2_ss") (record := 2844)
    (by exact List.mem_of_getElem? (i := 320) (by rfl)) (by rfl) (by rfl)
  simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Nat.cast_ofNat] using h

private theorem d7Thirteen_raw338 :
    HasDifferential model.classical.sphere 2 (12,136) (14,137)
      (basis .sphere 12 136 2) (basis .sphere 14 137 2) := by
  have h := d7Thirteen_equation (r := 2) (s := 12) (t := 136) (ts := 14) (tt := 137)
    (xs := [2]) (ys := [2])
    (origin := "S0_AdamsE2_ss") (record := 2911)
    (by exact List.mem_of_getElem? (i := 338) (by rfl)) (by rfl) (by rfl)
  simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Nat.cast_ofNat] using h

private theorem d7Thirteen_raw339 :
    HasDifferential model.classical.sphere 3 (14,137) (17,139)
      (basis .sphere 14 137 1) (basis .sphere 17 139 1) := by
  have h := d7Thirteen_equation (r := 3) (s := 14) (t := 137) (ts := 17) (tt := 139)
    (xs := [1]) (ys := [1])
    (origin := "S0_AdamsE2_ss") (record := 2912)
    (by exact List.mem_of_getElem? (i := 339) (by rfl)) (by rfl) (by rfl)
  simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Nat.cast_ofNat] using h

private theorem d7Thirteen_raw340 :
    HasDifferential model.classical.sphere 3 (14,137) (17,139)
      (basis .sphere 14 137 0) (basis .sphere 17 139 0) := by
  have h := d7Thirteen_equation (r := 3) (s := 14) (t := 137) (ts := 17) (tt := 139)
    (xs := [0]) (ys := [0])
    (origin := "S0_AdamsE2_ss") (record := 2913)
    (by exact List.mem_of_getElem? (i := 340) (by rfl)) (by rfl) (by rfl)
  simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Nat.cast_ofNat] using h

private theorem d7Thirteen_basis14 :
    ∃ e : model.classical.sphere.Page 2 (14,137) ≃ₗ[ℤ] (Fin 3 →₀ F2),
      ∀ i, e.symm (Finsupp.single i 1)=basis .sphere 14 137 i.val := by
  exact basis_correct ⟨.sphere,14,137,["23,1,181,1","0,1,418,1","0,3,386,1"]⟩
    (by exact List.mem_of_getElem? (i := 215) (by rfl))

private theorem d7Thirteen_basis13 :
    ∃ e : model.classical.sphere.Page 2 (13,136) ≃ₗ[ℤ] (Fin 3 →₀ F2),
      ∀ i, e.symm (Finsupp.single i 1)=basis .sphere 13 136 i.val := by
  exact basis_correct ⟨.sphere,13,136,["418,1","417,1","0,2,386,1"]⟩
    (by exact List.mem_of_getElem? (i := 207) (by rfl))

private theorem d7Thirteen_basis16 :
    ∃ e : model.classical.sphere.Page 2 (16,138) ≃ₗ[ℤ] (Fin 3 →₀ F2),
      ∀ i, e.symm (Finsupp.single i 1)=basis .sphere 16 138 i.val := by
  exact basis_correct ⟨.sphere,16,138,["437,1","23,1,189,1","0,1,424,1"]⟩
    (by exact List.mem_of_getElem? (i := 229) (by rfl))

private theorem d7Early_d2_14_137_zero : model.classical.sphere.d 2 (14,137)=0 := by
  classical
  have hs2 : model.classical.sphere.r₀ ≤ 2 := by rw [model.classical.firstPage]
  have d0 : model.classical.sphere.d 2 (14,137) (basis .sphere 14 137 0)=0 := by
    obtain ⟨_,a,b,ha,_,_⟩ := d7Thirteen_raw340
    exact represents_d_zero_of_later hs2 (by decide : (2:ℤ)<3)
      (represents_two_self _) ⟨a,ha⟩
  have d1 : model.classical.sphere.d 2 (14,137) (basis .sphere 14 137 1)=0 := by
    obtain ⟨_,a,b,ha,_,_⟩ := d7Thirteen_raw339
    exact represents_d_zero_of_later hs2 (by decide : (2:ℤ)<3)
      (represents_two_self _) ⟨a,ha⟩
  have d2 : model.classical.sphere.d 2 (14,137) (basis .sphere 14 137 2)=0 := by
    obtain ⟨a,ha,hd⟩ := differential_target_cycle d7Thirteen_raw338
    rwa [←ha.eq_on_page_two] at hd
  obtain ⟨e,he⟩ := d7Thirteen_basis14
  ext x
  change model.classical.sphere.d 2 (14,137) x=0
  have hx := finite_basis_expansion e x
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,he,add_zero] at hx
  change x=(if e x 0=0 then 0 else basis .sphere 14 137 0)+
    ((if e x 1=0 then 0 else basis .sphere 14 137 1)+
      (if e x 2=0 then 0 else basis .sphere 14 137 2)) at hx
  rw [hx]
  simp (config := { congrConsts := false }) only [map_add,apply_ite,map_zero,d0,d1,d2,ite_self,add_zero]

private theorem d7Thirteen_fourth_at
    {E : KIP126.Core.SpectralSequence (ModuleCat ℤ) (ℤ × ℤ)}
    {p q : ℤ × ℤ} (hdeg : p+E.diffDeg 3=q) (hstart : E.r₀ ≤ 2)
    (e : E.Page 2 p ≃ₗ[ℤ] (Fin 3 →₀ F2)) (y0 y1 : E.Page 2 q)
    (h0 : HasDifferential E 3 p q (e.symm (Finsupp.single 0 1)) y0)
    (h1 : HasDifferential E 3 p q (e.symm (Finsupp.single 1 1)) y1)
    (hz : RepresentsOnPage E 3 p (e.symm (Finsupp.single 2 1)) 0)
    (hin : E.d 2 (q-E.diffDeg 2)=0)
    (hn0 : y0≠0) (hn1 : y1≠0) (hn01 : y0+y1≠0) :
    Subsingleton (E.Page 4 p) := by
  subst q
  exact fourth_zero_of_three_basis hstart e y0 y1 h0 h1 hz hin hn0 hn1 hn01

private theorem d7Early_thirteen_four_zero (z : model.classical.sphere.Page 4 (13,136)) : z=0 := by
  classical
  obtain ⟨e,he⟩ := d7Thirteen_basis13
  obtain ⟨f,hf⟩ := d7Thirteen_basis16
  have he0 : e.symm (Finsupp.single (0:Fin 3) 1)=basis .sphere 13 136 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 3) 1)=basis .sphere 13 136 1 := he 1
  have he2 : e.symm (Finsupp.single (2:Fin 3) 1)=basis .sphere 13 136 2 := he 2
  have hf0 : f.symm (Finsupp.single (0:Fin 3) 1)=basis .sphere 16 138 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 3) 1)=basis .sphere 16 138 1 := hf 1
  have hf2 : f.symm (Finsupp.single (2:Fin 3) 1)=basis .sphere 16 138 2 := hf 2
  have f0 : f (basis .sphere 16 138 0)=Finsupp.single (0:Fin 3) 1 := by
    rw [←hf0,LinearEquiv.apply_symm_apply]
  have f1 : f (basis .sphere 16 138 1)=Finsupp.single (1:Fin 3) 1 := by
    rw [←hf1,LinearEquiv.apply_symm_apply]
  have f2 : f (basis .sphere 16 138 2)=Finsupp.single (2:Fin 3) 1 := by
    rw [←hf2,LinearEquiv.apply_symm_apply]
  have n0 : basis .sphere 16 138 0+basis .sphere 16 138 2≠0 := by
    intro h
    have hh := congrArg (fun x => f x (0:Fin 3)) h
    norm_num [map_add,f0,f2,map_zero,Finsupp.single_apply,Fin.ext_iff] at hh
  have n1 : basis .sphere 16 138 1≠0 := by
    intro h
    have hh := congrArg (fun x => f x (1:Fin 3)) h
    norm_num [f1,map_zero,Finsupp.single_apply,Fin.ext_iff] at hh
  have n01 : (basis .sphere 16 138 0+basis .sphere 16 138 2)+basis .sphere 16 138 1≠0 := by
    intro h
    have hh := congrArg (fun x => f x (0:Fin 3)) h
    norm_num [map_add,f0,f1,f2,map_zero,Finsupp.single_apply,Fin.ext_iff] at hh
  have hs2 : model.classical.sphere.r₀≤2 := by rw [model.classical.firstPage]
  have hin : model.classical.sphere.d 2 ((16,138)-model.classical.sphere.diffDeg 2)=0 := by
    have hd : ((16,138):ℤ×ℤ)-model.classical.sphere.diffDeg 2=(14,137) := by
      rw [model.classical.differentialDegree]
      rfl
    rw [hd]
    exact d7Early_d2_14_137_zero
  have h0 : HasDifferential model.classical.sphere 3 (13,136) (16,138)
      (e.symm (Finsupp.single 0 1)) (basis .sphere 16 138 0+basis .sphere 16 138 2) := by
    rw [he0]
    exact d7Thirteen_raw320
  have h1 : HasDifferential model.classical.sphere 3 (13,136) (16,138)
      (e.symm (Finsupp.single 1 1)) (basis .sphere 16 138 1) := by
    rw [he1]
    exact d7Thirteen_raw319
  have hz : RepresentsOnPage model.classical.sphere 3 (13,136)
      (e.symm (Finsupp.single 2 1)) 0 := by
    rw [he2]
    exact differential_target_later_zero hs2 (by decide : (2:ℤ)<3) d7Thirteen_raw318
  letI := d7Thirteen_fourth_at d7Thirteen_raw320.target_degree hs2 e
    (basis .sphere 16 138 0+basis .sphere 16 138 2) (basis .sphere 16 138 1)
    h0 h1 hz hin n0 n1 n01
  exact Subsingleton.elim z 0

private theorem d7Early_thirteen_five_zero (z : model.classical.sphere.Page 5 (13,136)) : z=0 := by
  obtain ⟨x,hx⟩ := page_has_initial_representative (by decide : (2:ℤ)≤5) z
  obtain ⟨a,ha⟩ := represents_before (by decide : (2:ℤ)≤4) (by decide : (4:ℤ)≤5) hx
  have hzero := d7Early_thirteen_four_zero a
  rw [hzero] at ha
  exact represents_later_zero (by decide : (4:ℤ)≤5) ha hx



private theorem d7MainMapZeroOfZeroSource
    {E : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ×ℤ)}
    {r : ℤ} {p : ℤ×ℤ} (hz : ∀ z : E.Page r p, z=0) : E.d r p=0 := by
  ext z
  change E.d r p z=0
  rw [hz z,map_zero]


public theorem d7_source : HasNonzeroDifferential model.classical.sphere 7 (11,134) (18,140)
    d7Source (product h1 (atom .x_121_17)) := by
  with_unfolding_all
    let E := model.classical.sphere
    obtain ⟨deg,x7,y7,hx7,hy7,hd⟩ := d7MainRow271
    obtain ⟨y3,hy3⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤7) hy7
    obtain ⟨y4,hy4⟩ := represents_before (by decide : (2:ℤ)≤4) (by decide : (4:ℤ)≤7) hy7
    obtain ⟨y5,hy5⟩ := represents_before (by decide : (2:ℤ)≤5) (by decide : (5:ℤ)≤7) hy7
    obtain ⟨y6,hy6⟩ := represents_before (by decide : (2:ℤ)≤6) (by decide : (6:ℤ)≤7) hy7
    have y4ne : y4≠0 := represents_next_nonzero_of_not_incoming_at (E := E)
      (d7MainIncomingDegree 3) (d7MainStart.trans (by decide)) (by decide)
      hy4 hy3 (fun v=>d7MainThirdAvoid hy3 v)
    have hin4 : E.d 4 (14,137)=0 := d7MainMapZeroOfZeroSource d7Early_fourteen_four_zero
    have hin5 : E.d 5 (13,136)=0 := d7MainMapZeroOfZeroSource d7Early_thirteen_five_zero
    have hin6 : E.d 6 (12,135)=0 := d7MainMapZeroOfZeroSource d7MainSixSourceZero
    have y5ne : y5≠0 := represents_next_nonzero_of_incoming_zero_at (E := E)
      (d7MainStart.trans (by decide)) (by decide) hin4 hy5 hy4 y4ne (d7MainIncomingDegree 4)
    have y6ne : y6≠0 := represents_next_nonzero_of_incoming_zero_at (E := E)
      (d7MainStart.trans (by decide)) (by decide) hin5 hy6 hy5 y5ne (d7MainIncomingDegree 5)
    have y7ne : y7≠0 := represents_next_nonzero_of_incoming_zero_at (E := E)
      (d7MainStart.trans (by decide)) (by decide) hin6 hy7 hy6 y6ne (d7MainIncomingDegree 6)
    have h : HasNonzeroDifferential E 7 (11,134) (18,140)
        (basis .sphere 11 134 0+basis .sphere 11 134 1+basis .sphere 11 134 3)
        (basis .sphere 18 140 1) := ⟨deg,x7,y7,hx7,hy7,hd,y7ne⟩
    rw [d7MainSourceBinding,d7MainTargetBinding] at h
    exact h

private theorem x126D322 : HasDifferential model.classical.sphere 3 (10,135) (13,137)
    (basis .sphere 10 135 0) (basis .sphere 13 137 0) := by
  have hrow := result ⟨.sphere,.equation,3,10,135,[0],13,137,[0],"S0_AdamsE2_ss",2915⟩ (by
    exact List.mem_of_getElem? (i := 322) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential model.classical.sphere 3 (10,135) (13,137) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 135 [0]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 13 137 [0]=true := rfl
  delta decode at ha hb
  simp (config := { congrConsts := false }) only [vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  exact h


private theorem x126D300 : HasDifferential model.classical.sphere 2 (10,135) (12,136)
    (basis .sphere 10 135 1) (basis .sphere 12 136 1 + basis .sphere 12 136 2) := by
  have hrow := result ⟨.sphere,.equation,2,10,135,[1],12,136,[1, 2],"S0_AdamsE2_ss",2845⟩ (by
    exact List.mem_of_getElem? (i := 300) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential model.classical.sphere 2 (10,135) (12,136) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 135 [1]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 136 [1, 2]=true := rfl
  delta decode at ha hb
  simp (config := { congrConsts := false }) only [vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  exact h


private theorem x126D301 : HasDifferential model.classical.sphere 2 (10,135) (12,136)
    (basis .sphere 10 135 2) (basis .sphere 12 136 3 + basis .sphere 12 136 4) := by
  have hrow := result ⟨.sphere,.equation,2,10,135,[2],12,136,[3, 4],"S0_AdamsE2_ss",2846⟩ (by
    exact List.mem_of_getElem? (i := 301) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential model.classical.sphere 2 (10,135) (12,136) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 135 [2]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 136 [3, 4]=true := rfl
  delta decode at ha hb
  simp (config := { congrConsts := false }) only [vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  exact h


private theorem x126D302 : HasDifferential model.classical.sphere 2 (10,135) (12,136)
    (basis .sphere 10 135 4) (basis .sphere 12 136 4) := by
  have hrow := result ⟨.sphere,.equation,2,10,135,[4],12,136,[4],"S0_AdamsE2_ss",2847⟩ (by
    exact List.mem_of_getElem? (i := 302) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential model.classical.sphere 2 (10,135) (12,136) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 135 [4]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 136 [4]=true := rfl
  delta decode at ha hb
  simp (config := { congrConsts := false }) only [vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  exact h


private theorem x126D251 : HasDifferential model.classical.sphere 2 (8,134) (10,135)
    (basis .sphere 8 134 1) (basis .sphere 10 135 3) := by
  have hrow := result ⟨.sphere,.equation,2,8,134,[1],10,135,[3],"S0_AdamsE2_ss",2783⟩ (by
    exact List.mem_of_getElem? (i := 251) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential model.classical.sphere 2 (8,134) (10,135) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 134 [1]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 10 135 [3]=true := rfl
  delta decode at ha hb
  simp (config := { congrConsts := false }) only [vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  exact h


private theorem x126R224 : ReachesPage model.classical.sphere 1000 (9,134) (basis .sphere 9 134 2) := by
  have hrow := result ⟨.sphere,.reaches,1000,9,134,[2],9,134,[],"S0_AdamsE2_ss",2695⟩ (by
    exact List.mem_of_getElem? (i := 224) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,h⟩ := hrow
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 134 [2]=true := rfl
  delta decode at ha
  simp (config := { congrConsts := false }) only [vx,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha
  rw [←ha] at h
  exact h


private theorem x126R225 : ReachesPage model.classical.sphere 7 (9,134) (basis .sphere 9 134 3) := by
  have hrow := result ⟨.sphere,.reaches,7,9,134,[3],9,134,[],"S0_AdamsE2_ss",2696⟩ (by
    exact List.mem_of_getElem? (i := 225) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,h⟩ := hrow
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 134 [3]=true := rfl
  delta decode at ha
  simp (config := { congrConsts := false }) only [vx,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha
  rw [←ha] at h
  exact h


private theorem x126D226 : HasDifferential model.classical.sphere 3 (9,134) (12,136)
    (basis .sphere 9 134 1) (basis .sphere 12 136 0) := by
  have hrow := result ⟨.sphere,.equation,3,9,134,[1],12,136,[0],"S0_AdamsE2_ss",2697⟩ (by
    exact List.mem_of_getElem? (i := 226) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential model.classical.sphere 3 (9,134) (12,136) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 134 [1]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 136 [0]=true := rfl
  delta decode at ha hb
  simp (config := { congrConsts := false }) only [vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  exact h


private theorem x126D227 : HasDifferential model.classical.sphere 2 (9,134) (11,135)
    (basis .sphere 9 134 0) (basis .sphere 11 135 3 + basis .sphere 11 135 4) := by
  have hrow := result ⟨.sphere,.equation,2,9,134,[0],11,135,[3, 4],"S0_AdamsE2_ss",2698⟩ (by
    exact List.mem_of_getElem? (i := 227) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential model.classical.sphere 2 (9,134) (11,135) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 134 [0]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 11 135 [3, 4]=true := rfl
  delta decode at ha hb
  simp (config := { congrConsts := false }) only [vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  exact h


private theorem x126D228 : HasDifferential model.classical.sphere 2 (9,134) (11,135)
    (basis .sphere 9 134 4) (basis .sphere 11 135 4) := by
  have hrow := result ⟨.sphere,.equation,2,9,134,[4],11,135,[4],"S0_AdamsE2_ss",2699⟩ (by
    exact List.mem_of_getElem? (i := 228) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential model.classical.sphere 2 (9,134) (11,135) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 134 [4]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 11 135 [4]=true := rfl
  delta decode at ha hb
  simp (config := { congrConsts := false }) only [vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  exact h


private theorem x126ImageCoord
    {A B : Type} [AddCommGroup A] [Module ℤ A] [AddCommGroup B] [Module ℤ B]
    {n m : ℕ} (e : A ≃ₗ[ℤ] (Fin n →₀ F2)) (f : B ≃ₗ[ℤ] (Fin m →₀ F2))
    (d : A →ₗ[ℤ] B) (x : A) (j : Fin m) :
    f (d x) j = ∑ i : Fin n, if e x i=0 then 0 else f (d (e.symm (Finsupp.single i 1))) j := by
  classical
  have hx := finite_basis_expansion e x
  calc
    f (d x) j = f (d (∑ i : Fin n, if e x i=0 then 0 else e.symm (Finsupp.single i 1))) j := by
      exact congrArg (fun a => f (d a) j) hx
    _ = _ := by
      rw [map_sum,map_sum,Finsupp.finsetSum_apply]
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hc : e x i=0
      · simp only [hc,ite_true,map_zero,Finsupp.zero_apply]
      · simp only [hc,ite_false]


private theorem x126TenDegree :
    (10,135)+model.classical.sphere.diffDeg 2=(12,136) := by
  simp only [ClassicalAdamsFamily.sphere,ClassicalAdamsFamily.obj,
    model.classical.differentialDegree,Prod.mk_add_mk,Int.reduceAdd,Int.reduceSub]


private noncomputable def x126TenD2 :
    model.classical.sphere.Page 2 (10,135) ⟶ model.classical.sphere.Page 2 (12,136) :=
  model.classical.sphere.d 2 (10,135) ≫
    eqToHom (congrArg (model.classical.sphere.Page 2) x126TenDegree)


private theorem x126TenValues (i : Fin 5) :
    x126TenD2 (basis .sphere 10 135 i.val) =
      ![0, basis .sphere 12 136 1 + basis .sphere 12 136 2,
        basis .sphere 12 136 3 + basis .sphere 12 136 4, 0,
        basis .sphere 12 136 4] i := by
  with_unfolding_all
    let E := model.classical.sphere
    have hs2 : E.r₀≤2 := by rw [model.classical.firstPage]
    fin_cases i
    · obtain ⟨_,a,b,ha,hb,hd⟩ := x126D322
      have hz := represents_d_zero_of_later hs2 (by decide : (2:ℤ)<3)
        (represents_two_self (basis .sphere 10 135 0)) ⟨a,ha⟩
      change (eqToHom (congrArg (E.Page 2) x126TenDegree))
        (E.d 2 (10,135) (basis .sphere 10 135 0))=0
      change E.d 2 (10,135) (basis .sphere 10 135 0)=0 at hz
      rw [hz,map_zero]
    · exact x126D300.eq_on_page_two.choose_spec
    · exact x126D301.eq_on_page_two.choose_spec
    · obtain ⟨z,hz,hdz⟩ := differential_target_cycle x126D251
      rw [←hz.eq_on_page_two] at hdz
      change (eqToHom (congrArg (E.Page 2) x126TenDegree))
        (E.d 2 (10,135) (basis .sphere 10 135 3))=0
      rw [hdz,map_zero]
    · exact x126D302.eq_on_page_two.choose_spec


private theorem x126IncomingTwelveCoordinate
    (g : model.classical.sphere.Page 2 (12,136) ≃ₗ[ℤ] (Fin 5 →₀ F2))
    (hg : ∀ i : Fin 5, g.symm (Finsupp.single i 1)=basis .sphere 12 136 i.val)
    (x : model.classical.sphere.Page 2 (10,135)) :
    g (x126TenD2 x) 0=0 := by
  with_unfolding_all
    obtain ⟨f,hf⟩ := basis_correct ⟨.sphere,10,135,["413,1", "412,1", "0,1,391,1", "0,1,390,1", "0,2,375,1"]⟩ (by
      exact List.mem_of_getElem? (i := 182) (by rfl))
    change model.classical.sphere.Page 2 (10,135) ≃ₗ[ℤ] (Fin 5 →₀ F2) at f
    change ∀ i : Fin 5, f.symm (Finsupp.single i 1)=basis .sphere 10 135 i.val at hf
    have each (i : Fin 5) : g (x126TenD2 (f.symm (Finsupp.single i 1))) 0=0 := by
      rw [hf,x126TenValues]
      have eg (i : Fin 5) : g (basis .sphere 12 136 i.val)=Finsupp.single i 1 := by
        rw [←hg i,LinearEquiv.apply_symm_apply]
      have eg1 : g (basis .sphere 12 136 1)=Finsupp.single (1:Fin 5) 1 := eg 1
      have eg2 : g (basis .sphere 12 136 2)=Finsupp.single (2:Fin 5) 1 := eg 2
      have eg3 : g (basis .sphere 12 136 3)=Finsupp.single (3:Fin 5) 1 := eg 3
      have eg4 : g (basis .sphere 12 136 4)=Finsupp.single (4:Fin 5) 1 := eg 4
      fin_cases i
      · change g 0 0=0
        simp only [map_zero,Finsupp.zero_apply]
      · change g (basis .sphere 12 136 1 + basis .sphere 12 136 2) 0=0
        rw [map_add,Finsupp.add_apply,eg1,eg2]
        norm_num [Finsupp.single_apply] <;> decide
      · change g (basis .sphere 12 136 3 + basis .sphere 12 136 4) 0=0
        rw [map_add,Finsupp.add_apply,eg3,eg4]
        norm_num [Finsupp.single_apply] <;> decide
      · change g 0 0=0
        simp only [map_zero,Finsupp.zero_apply]
      · change g (basis .sphere 12 136 4) 0=0
        rw [eg4]
        norm_num [Finsupp.single_apply] <;> decide
    rw [x126ImageCoord f g x126TenD2.hom x 0]
    apply Finset.sum_eq_zero
    intro i hi
    by_cases hc : f x i=0
    · simp only [hc,ite_true]
    · simp only [hc,ite_false,each]


private theorem x126ImageCoordFive
    {A B : Type} [AddCommGroup A] [Module ℤ A] [AddCommGroup B] [Module ℤ B]
    {m : ℕ} (e : A ≃ₗ[ℤ] (Fin 5 →₀ F2)) (f : B ≃ₗ[ℤ] (Fin m →₀ F2))
    (d : A →ₗ[ℤ] B) (x : A) (j : Fin m) :
    f (d x) j = (if e x 0=0 then 0 else f (d (e.symm (Finsupp.single 0 1))) j) +
      ((if e x 1=0 then 0 else f (d (e.symm (Finsupp.single 1 1))) j) +
      ((if e x 2=0 then 0 else f (d (e.symm (Finsupp.single 2 1))) j) +
      ((if e x 3=0 then 0 else f (d (e.symm (Finsupp.single 3 1))) j) +
       (if e x 4=0 then 0 else f (d (e.symm (Finsupp.single 4 1))) j)))) := by
  have h := x126ImageCoord e f d x j
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero] at h
  delta Fin.succ at h
  exact h


private theorem x126NineDegree :
    (9,134)+model.classical.sphere.diffDeg 2=(11,135) := by
  simp only [ClassicalAdamsFamily.sphere,ClassicalAdamsFamily.obj,
    model.classical.differentialDegree,Prod.mk_add_mk,Int.reduceAdd,Int.reduceSub]


private noncomputable def x126NineD2 :
    model.classical.sphere.Page 2 (9,134) ⟶ model.classical.sphere.Page 2 (11,135) :=
  model.classical.sphere.d 2 (9,134) ≫
    eqToHom (congrArg (model.classical.sphere.Page 2) x126NineDegree)


private theorem x126NineValues (i : Fin 5) :
    x126NineD2 (basis .sphere 9 134 i.val) =
      ![basis .sphere 11 135 3 + basis .sphere 11 135 4,0,0,0,basis .sphere 11 135 4] i := by
  with_unfolding_all
    let E := model.classical.sphere
    have hs2 : E.r₀≤2 := by rw [model.classical.firstPage]
    have hz (i : Fin 5) (h : ReachesPage E 3 (9,134) (basis .sphere 9 134 i.val)) :
        x126NineD2 (basis .sphere 9 134 i.val)=0 := by
      have hd := represents_d_zero_of_later hs2 (by decide : (2:ℤ)<3)
        (represents_two_self (basis .sphere 9 134 i.val)) h
      change (eqToHom (congrArg (E.Page 2) x126NineDegree))
        (E.d 2 (9,134) (basis .sphere 9 134 i.val))=0
      change E.d 2 (9,134) (basis .sphere 9 134 i.val)=0 at hd
      rw [hd,map_zero]
    fin_cases i
    · exact x126D227.eq_on_page_two.choose_spec
    · obtain ⟨_,a,b,ha,hb,hd⟩ := x126D226
      exact hz 1 ⟨a,ha⟩
    · exact hz 2 (reaches_before (by decide) (by decide : (3:ℤ)≤1000) x126R224)
    · exact hz 3 (reaches_before (by decide) (by decide : (3:ℤ)≤7) x126R225)
    · exact x126D228.eq_on_page_two.choose_spec

private theorem x126KernelFrame (v : model.classical.sphere.Page 3 (9,134))
    (hv : model.classical.sphere.d 3 (9,134) v=0) :
    ∃ a2 a3 : model.classical.sphere.Page 3 (9,134),
      RepresentsOnPage model.classical.sphere 3 (9,134) (basis .sphere 9 134 2) a2 ∧
      RepresentsOnPage model.classical.sphere 3 (9,134) (basis .sphere 9 134 3) a3 ∧
      (v=0 ∨ v=a2 ∨ v=a3 ∨ v=a2+a3) := by
  with_unfolding_all
    classical
    let E := model.classical.sphere
    have hs2 : E.r₀≤2 := by rw [model.classical.firstPage]
    obtain ⟨f,hf⟩ := basis_correct ⟨.sphere,9,134,["391,1", "390,1", "69,1,82,1", "18,1,190,1", "0,1,375,1"]⟩ (by
      exact List.mem_of_getElem? (i := 173) (by rfl))
    change E.Page 2 (9,134) ≃ₗ[ℤ] (Fin 5 →₀ F2) at f
    change ∀ i : Fin 5, f.symm (Finsupp.single i 1)=basis .sphere 9 134 i.val at hf
    obtain ⟨g,hg⟩ := basis_correct ⟨.sphere,11,135,["411,1", "410,1", "409,1", "0,1,389,1", "0,3,367,1"]⟩ (by
      exact List.mem_of_getElem? (i := 191) (by rfl))
    change E.Page 2 (11,135) ≃ₗ[ℤ] (Fin 5 →₀ F2) at g
    change ∀ i : Fin 5, g.symm (Finsupp.single i 1)=basis .sphere 11 135 i.val at hg
    obtain ⟨k,hk⟩ := basis_correct ⟨.sphere,12,136,["1,1,387,1", "0,1,410,1", "0,1,409,1", "0,2,389,1", "0,4,367,1"]⟩ (by
      exact List.mem_of_getElem? (i := 200) (by rfl))
    change E.Page 2 (12,136) ≃ₗ[ℤ] (Fin 5 →₀ F2) at k
    change ∀ i : Fin 5, k.symm (Finsupp.single i 1)=basis .sphere 12 136 i.val at hk
    obtain ⟨deg3,a1,b0,ha1,hb0,hd1⟩ := x126D226
    have b0ne : b0≠0 := by
      apply represents_next_nonzero_of_not_incoming_at x126TenDegree hs2 (by decide)
        hb0 (represents_two_self (basis .sphere 12 136 0))
      intro z hz
      change x126TenD2 z=basis .sphere 12 136 0 at hz
      have hc := congrArg (fun y => k y 0) hz
      rw [x126IncomingTwelveCoordinate k hk] at hc
      have ek0 : k (basis .sphere 12 136 0) 0=1 := by
        have hh : k.symm (Finsupp.single (0:Fin 5) 1)=basis .sphere 12 136 0 := hk 0
        rw [←hh,LinearEquiv.apply_symm_apply,Finsupp.single_eq_same]
      rw [ek0] at hc
      exact zero_ne_one hc
    obtain ⟨a2,ha2⟩ := reaches_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤1000) x126R224
    obtain ⟨a3,ha3⟩ := reaches_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤7) x126R225
    let d3 : E.Page 3 (9,134) ⟶ E.Page 3 (12,136) :=
      E.d 3 (9,134) ≫ eqToHom (congrArg (E.Page 3) deg3)
    have hda1 : d3 a1=b0 := hd1
    have hda2 : d3 a2=0 := by
      have hz := represents_d_zero_of_later (hs2.trans (by decide : (2:ℤ)≤3))
        (by decide : (3:ℤ)<4) ha2
        (reaches_before (by decide) (by decide : (4:ℤ)≤1000) x126R224)
      change (eqToHom (congrArg (E.Page 3) deg3)) (E.d 3 (9,134) a2)=0
      rw [hz,map_zero]
    have hda3 : d3 a3=0 := by
      have hz := represents_d_zero_of_later (hs2.trans (by decide : (2:ℤ)≤3))
        (by decide : (3:ℤ)<4) ha3
        (reaches_before (by decide) (by decide : (4:ℤ)≤7) x126R225)
      change (eqToHom (congrArg (E.Page 3) deg3)) (E.d 3 (9,134) a3)=0
      rw [hz,map_zero]
    have hvals (i : Fin 5) : x126NineD2.hom (f.symm (Finsupp.single i 1)) =
        ![g.symm (Finsupp.single 3 1 + Finsupp.single 4 1),0,0,0,g.symm (Finsupp.single 4 1)] i := by
      change x126NineD2 (f.symm (Finsupp.single i 1))=_
      rw [hf,x126NineValues]
      have hg3 : g.symm (Finsupp.single (3:Fin 5) 1)=basis .sphere 11 135 3 := hg 3
      have hg4 : g.symm (Finsupp.single (4:Fin 5) 1)=basis .sphere 11 135 4 := hg 4
      fin_cases i
      · change basis .sphere 11 135 3 + basis .sphere 11 135 4 = g.symm (Finsupp.single 3 1 + Finsupp.single 4 1)
        rw [map_add,hg3,hg4]
      · rfl
      · rfl
      · rfl
      · exact hg4.symm
    obtain ⟨x,hx⟩ := page_has_initial_representative (by decide : (2:ℤ)≤3) v
    have hdx : E.d 2 (9,134) x=0 := represents_d_zero_of_later hs2 (by decide)
      (represents_two_self x) ⟨v,hx⟩
    have hmap : x126NineD2 x=0 := by
      change (eqToHom (congrArg (E.Page 2) x126NineDegree)) (E.d 2 (9,134) x)=0
      rw [hdx,map_zero]
    have hmap' : x126NineD2.hom x=0 := hmap
    have hcoord3 := x126ImageCoordFive f g x126NineD2.hom x 3
    have hcoord4 := x126ImageCoordFive f g x126NineD2.hom x 4
    have hv0 : x126NineD2.hom (f.symm (Finsupp.single (0:Fin 5) 1))=g.symm (Finsupp.single 3 1 + Finsupp.single 4 1) := hvals 0
    have hv1 : x126NineD2.hom (f.symm (Finsupp.single (1:Fin 5) 1))=0 := hvals 1
    have hv2 : x126NineD2.hom (f.symm (Finsupp.single (2:Fin 5) 1))=0 := hvals 2
    have hv3 : x126NineD2.hom (f.symm (Finsupp.single (3:Fin 5) 1))=0 := hvals 3
    have hv4 : x126NineD2.hom (f.symm (Finsupp.single (4:Fin 5) 1))=g.symm (Finsupp.single 4 1) := hvals 4
    erw [hmap',hv0,hv1,hv2,hv3,hv4] at hcoord3 hcoord4
    norm_num only [map_zero,Finsupp.add_apply,Finsupp.zero_apply,LinearEquiv.apply_symm_apply,
      Finsupp.single_apply,Fin.reduceEq,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_succ,
      ite_true,ite_false,ite_self,add_zero,zero_add] at hcoord3 hcoord4
    norm_num [Fin.ext_iff] at hcoord3 hcoord4
    have c0 : f x 0=0 := by
      by_contra hc
      simpa only [hc,ite_false] using hcoord3
    have c4 : f x 4=0 := by
      by_contra hc
      have hh : (0:F2)=1 := by simpa only [c0,ite_true,hc,ite_false,zero_add] using hcoord4
      exact zero_ne_one hh
    have he := finite_basis_expansion f x
    simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero] at he
    delta Fin.succ at he
    change x=(if f x 0=0 then 0 else f.symm (Finsupp.single 0 1)) +
      ((if f x 1=0 then 0 else f.symm (Finsupp.single 1 1)) +
      ((if f x 2=0 then 0 else f.symm (Finsupp.single 2 1)) +
      ((if f x 3=0 then 0 else f.symm (Finsupp.single 3 1)) +
       (if f x 4=0 then 0 else f.symm (Finsupp.single 4 1))))) at he
    simp only [c0,c4,ite_true,zero_add,add_zero] at he
    have h1 : RepresentsOnPage E 3 (9,134) (f.symm (Finsupp.single 1 1)) a1 := by rw [hf]; exact ha1
    have h2 : RepresentsOnPage E 3 (9,134) (f.symm (Finsupp.single 2 1)) a2 := by rw [hf]; exact ha2
    have h3 : RepresentsOnPage E 3 (9,134) (f.symm (Finsupp.single 3 1)) a3 := by rw [hf]; exact ha3
    have hrep := represents_add_tail (represents_bit (f x 1) h1)
      (represents_add_tail (represents_bit (f x 2) h2) (represents_bit (f x 3) h3))
    rw [←he] at hrep
    have heq := represents_unique hx hrep
    have hvzero : d3 v=0 := by
      change (eqToHom (congrArg (E.Page 3) deg3)) (E.d 3 (9,134) v)=0
      rw [hv,map_zero]
    have c1 : f x 1=0 := by
      by_contra hc
      rw [heq] at hvzero
      by_cases hc2 : f x 2=0 <;> by_cases hc3 : f x 3=0
      all_goals simp only [hc,hc2,hc3,ite_true,ite_false,map_add,map_zero,hda1,hda2,hda3,zero_add,add_zero] at hvzero
      all_goals exact b0ne hvzero
    have hform : v=(if f x 2=0 then 0 else a2)+(if f x 3=0 then 0 else a3) := by
      rw [heq]
      simp only [c1,ite_true,zero_add]
    refine ⟨a2,a3,ha2,ha3,?_⟩
    by_cases hc2 : f x 2=0 <;> by_cases hc3 : f x 3=0
    · exact Or.inl (by simpa only [hc2,hc3,ite_true,zero_add] using hform)
    · exact Or.inr (Or.inr (Or.inl (by simpa only [hc2,hc3,ite_true,ite_false,zero_add] using hform)))
    · exact Or.inr (Or.inl (by simpa only [hc2,hc3,ite_true,ite_false,add_zero] using hform))
    · exact Or.inr (Or.inr (Or.inr (by simpa only [hc2,hc3,ite_false] using hform)))

private theorem x126SourceReaches : ReachesPage model.classical.sphere 3 (6,132) (basis .sphere 6 132 0) := by
  have hrow := result ⟨.sphere, .reaches, 3, 6, 132, [0], 6, 132, [], "S0_AdamsE2_ss", 2574⟩ (by
    exact List.mem_of_getElem? (i := 174) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,h⟩ := hrow
  have vx : Raw.coordinatesValid Raw.degrees .sphere 6 132 [0]=true := rfl
  delta decode at ha
  simp (config := { congrConsts := false }) only [vx,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha
  rw [←ha] at h
  exact h


private theorem x126RefuteZero : ¬HasDifferential model.classical.sphere 3 (6,132) (9,134)
    (basis .sphere 6 132 0) 0 := by
  have h := result ⟨.sphere, .refutation, 3, 6, 132, [0], 9, 134, [], "proofs.db/log", 2047477⟩ (by
    exact List.mem_of_getElem? (i := 659) (by rfl))
  dsimp only [Statement] at h
  obtain ⟨x,hx,y,hy,hd⟩ := h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 6 132 [0]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 9 134 []=true := rfl
  simp only [decode,vx,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
  simp only [decode,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hy
  rw [←hx,←hy] at hd
  exact hd

private theorem x126RefuteTwo : ¬HasDifferential model.classical.sphere 3 (6,132) (9,134)
    (basis .sphere 6 132 0) (basis .sphere 9 134 2) := by
  have h := result ⟨.sphere, .refutation, 3, 6, 132, [0], 9, 134, [2], "proofs.db/log", 2047478⟩ (by
    exact List.mem_of_getElem? (i := 660) (by rfl))
  dsimp only [Statement] at h
  obtain ⟨x,hx,y,hy,hd⟩ := h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 6 132 [0]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 9 134 [2]=true := rfl
  simp only [decode,vx,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
  simp only [decode,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hy
  rw [←hx,←hy] at hd
  exact hd

private theorem x126SourceBinding : basis .sphere 6 132 0=atom .x_126_6 := by
  have h := basis_value ⟨.named .x_126_6,0⟩ (by decide)
  exact h

private theorem x126TargetThreeBinding : basis .sphere 9 134 3=d3Candidate := by
  have h := basis_value ⟨.mul (.named .h5) (.named .x_94_8),3⟩ (by decide)
  delta d3Candidate
  simpa only [Expression.value,Expression.degree,atom_h5] using h

private theorem x126TargetTwoBinding : basis .sphere 9 134 2=product (r := (9,134)) h6 (atom .b) := by
  have h := basis_value ⟨.mul (.named .h6) (.named .b),2⟩ (by decide)
  simpa only [Expression.value,Expression.degree,atom_h6] using h

private theorem x126TargetSumBinding : basis .sphere 9 134 2+basis .sphere 9 134 3=d3OtherCandidate := by
  rw [x126TargetTwoBinding,x126TargetThreeBinding]
  exact add_comm _ _

public theorem d3_x126_6_candidates :
    HasNonzeroDifferential model.classical.sphere 3 (6,132) (9,134)
      (atom .x_126_6) d3Candidate ∨
    HasNonzeroDifferential model.classical.sphere 3 (6,132) (9,134)
      (atom .x_126_6) d3OtherCandidate := by
  with_unfolding_all
    let E := model.classical.sphere
    obtain ⟨x3,hx3⟩ := x126SourceReaches
    have deg : (6,132)+E.diffDeg 3=(9,134) := by
      simp only [E,ClassicalAdamsFamily.sphere,ClassicalAdamsFamily.obj,
        model.classical.differentialDegree,Prod.mk_add_mk,Int.reduceAdd,Int.reduceSub]
    let y3 : E.Page 3 (9,134) :=
      (E.d 3 (6,132) ≫ eqToHom (congrArg (E.Page 3) deg)) x3
    have y3ne : y3≠0 := by
      intro hy
      apply x126RefuteZero
      exact ⟨deg,x3,0,hx3,RepresentsOnPage.zero (by decide),hy⟩
    obtain ⟨y2,hy2⟩ := page_has_initial_representative (by decide : (2:ℤ)≤3) y3
    have hd : HasDifferential E 3 (6,132) (9,134) (basis .sphere 6 132 0) y2 :=
      ⟨deg,x3,y3,hx3,hy2,rfl⟩
    obtain ⟨y3',hy3',hcycle⟩ := differential_target_cycle hd
    have hy3'eq : y3'=y3 := represents_unique hy3' hy2
    rw [hy3'eq] at hcycle
    obtain ⟨a2,a3,ha2,ha3,hcases⟩ := x126KernelFrame y3 hcycle
    rcases hcases with hz|htwo|hthree|hsum
    · exact (y3ne hz).elim
    · exact (x126RefuteTwo ⟨deg,x3,a2,hx3,ha2,htwo⟩).elim
    · left
      have h : HasNonzeroDifferential E 3 (6,132) (9,134)
          (basis .sphere 6 132 0) (basis .sphere 9 134 3) :=
        ⟨deg,x3,a3,hx3,ha3,hthree,by intro hz; exact y3ne (hthree.trans hz)⟩
      rw [x126SourceBinding,x126TargetThreeBinding] at h
      exact h
    · right
      have h : HasNonzeroDifferential E 3 (6,132) (9,134)
          (basis .sphere 6 132 0) (basis .sphere 9 134 2+basis .sphere 9 134 3) :=
        ⟨deg,x3,a2+a3,hx3,represents_add_tail ha2 ha3,hsum,
          by intro hz; exact y3ne (hsum.trans hz)⟩
      rw [x126SourceBinding,x126TargetSumBinding] at h
      exact h


private theorem tIn_start : model.classical.sphere.r₀≤2 := by rw [model.classical.firstPage]

private theorem tInRow143 : HasDifferential model.classical.sphere 2 (1,128) (3,129) (basis .sphere 1 128 0) (basis .sphere 3 129 0) := by
  have h := result ⟨.sphere, .equation, 2, 1, 128, [0], 3, 129, [0], "S0_AdamsE2_ss", 2315⟩ (by exact List.mem_of_getElem? (i := 143) rfl)
  dsimp only [Statement] at h
  obtain ⟨a,ha,b,hb,h⟩ := h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 1 128 [0]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 3 129 [0]=true := rfl
  delta decode at ha hb
  simp (config := { congrConsts := false }) only [vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  exact h

private theorem tInRow147 : HasDifferential model.classical.sphere 2 (2,129) (4,130) (basis .sphere 2 129 0) (basis .sphere 4 130 1) := by
  have h := result ⟨.sphere, .equation, 2, 2, 129, [0], 4, 130, [1], "S0_AdamsE2_ss", 2381⟩ (by exact List.mem_of_getElem? (i := 147) rfl)
  dsimp only [Statement] at h
  obtain ⟨a,ha,b,hb,h⟩ := h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 2 129 [0]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 4 130 [1]=true := rfl
  delta decode at ha hb
  simp (config := { congrConsts := false }) only [vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  exact h

private theorem tInRow153 : HasDifferential model.classical.sphere 2 (3,130) (5,131) (basis .sphere 3 130 1) (basis .sphere 5 131 0) := by
  have h := result ⟨.sphere, .equation, 2, 3, 130, [1], 5, 131, [0], "S0_AdamsE2_ss", 2439⟩ (by exact List.mem_of_getElem? (i := 153) rfl)
  dsimp only [Statement] at h
  obtain ⟨a,ha,b,hb,h⟩ := h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 3 130 [1]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 5 131 [0]=true := rfl
  delta decode at ha hb
  simp (config := { congrConsts := false }) only [vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  exact h

private theorem tInRow157 : HasDifferential model.classical.sphere 3 (4,130) (7,132) (basis .sphere 4 130 0) (basis .sphere 7 132 0) := by
  have h := result ⟨.sphere, .equation, 3, 4, 130, [0], 7, 132, [0], "S0_AdamsE2_ss", 2437⟩ (by exact List.mem_of_getElem? (i := 157) rfl)
  dsimp only [Statement] at h
  obtain ⟨a,ha,b,hb,h⟩ := h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 4 130 [0]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 7 132 [0]=true := rfl
  delta decode at ha hb
  simp (config := { congrConsts := false }) only [vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  exact h

private theorem tInRow158 : HasDifferential model.classical.sphere 2 (4,131) (6,132) (basis .sphere 4 131 0) (basis .sphere 6 132 1) := by
  have h := result ⟨.sphere, .equation, 2, 4, 131, [0], 6, 132, [1], "S0_AdamsE2_ss", 2495⟩ (by exact List.mem_of_getElem? (i := 158) rfl)
  dsimp only [Statement] at h
  obtain ⟨a,ha,b,hb,h⟩ := h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 4 131 [0]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 6 132 [1]=true := rfl
  delta decode at ha hb
  simp (config := { congrConsts := false }) only [vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  exact h

private theorem tInRow165 : HasDifferential model.classical.sphere 2 (5,132) (7,133) (basis .sphere 5 132 0) (basis .sphere 7 133 1) := by
  have h := result ⟨.sphere, .equation, 2, 5, 132, [0], 7, 133, [1], "S0_AdamsE2_ss", 2575⟩ (by exact List.mem_of_getElem? (i := 165) rfl)
  dsimp only [Statement] at h
  obtain ⟨a,ha,b,hb,h⟩ := h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 5 132 [0]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 7 133 [1]=true := rfl
  delta decode at ha hb
  simp (config := { congrConsts := false }) only [vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  exact h

private theorem tInRow186 : ReachesPage model.classical.sphere 18 (7,133) (basis .sphere 7 133 0) := by
  have h := result ⟨.sphere, .reaches, 18, 7, 133, [0], 7, 133, [], "S0_AdamsE2_ss", 2632⟩ (by exact List.mem_of_getElem? (i := 186) rfl)
  dsimp only [Statement] at h
  obtain ⟨a,ha,h⟩ := h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 7 133 [0]=true := rfl
  delta decode at ha
  simp (config := { congrConsts := false }) only [vx,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha
  rw [←ha] at h
  exact h

private theorem tInRow264 : HasDifferential model.classical.sphere 2 (10,137) (12,138) (basis .sphere 10 137 0) (basis .sphere 12 138 0) := by
  have h := result ⟨.sphere, .equation, 2, 10, 137, [0], 12, 138, [0], "S0_AdamsE2_ss", 2932⟩ (by exact List.mem_of_getElem? (i := 264) rfl)
  dsimp only [Statement] at h
  obtain ⟨a,ha,b,hb,h⟩ := h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 137 [0]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 138 [0]=true := rfl
  delta decode at ha hb
  simp (config := { congrConsts := false }) only [vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  exact h

private theorem tInRow265 : HasDifferential model.classical.sphere 2 (10,137) (12,138) (basis .sphere 10 137 1) (basis .sphere 12 138 2) := by
  have h := result ⟨.sphere, .equation, 2, 10, 137, [1], 12, 138, [2], "S0_AdamsE2_ss", 2933⟩ (by exact List.mem_of_getElem? (i := 265) rfl)
  dsimp only [Statement] at h
  obtain ⟨a,ha,b,hb,h⟩ := h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 137 [1]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 138 [2]=true := rfl
  delta decode at ha hb
  simp (config := { congrConsts := false }) only [vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  exact h

private theorem tInRow266 : HasDifferential model.classical.sphere 2 (10,137) (12,138) (basis .sphere 10 137 5) (basis .sphere 12 138 4) := by
  have h := result ⟨.sphere, .equation, 2, 10, 137, [5], 12, 138, [4], "S0_AdamsE2_ss", 2934⟩ (by exact List.mem_of_getElem? (i := 266) rfl)
  dsimp only [Statement] at h
  obtain ⟨a,ha,b,hb,h⟩ := h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 137 [5]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 138 [4]=true := rfl
  delta decode at ha hb
  simp (config := { congrConsts := false }) only [vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  exact h

private theorem tInRow313 : HasDifferential model.classical.sphere 4 (12,138) (16,141) (basis .sphere 12 138 3) (basis .sphere 16 141 1) := by
  have h := result ⟨.sphere, .equation, 4, 12, 138, [3], 16, 141, [1], "S0_AdamsE2_ss", 3016⟩ (by exact List.mem_of_getElem? (i := 313) rfl)
  dsimp only [Statement] at h
  obtain ⟨a,ha,b,hb,h⟩ := h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 12 138 [3]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 16 141 [1]=true := rfl
  delta decode at ha hb
  simp (config := { congrConsts := false }) only [vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  exact h

private theorem tInRow314 : HasDifferential model.classical.sphere 2 (12,138) (14,139) (basis .sphere 12 138 1) (basis .sphere 14 139 2) := by
  have h := result ⟨.sphere, .equation, 2, 12, 138, [1], 14, 139, [2], "S0_AdamsE2_ss", 3017⟩ (by exact List.mem_of_getElem? (i := 314) rfl)
  dsimp only [Statement] at h
  obtain ⟨a,ha,b,hb,h⟩ := h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 12 138 [1]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 14 139 [2]=true := rfl
  delta decode at ha hb
  simp (config := { congrConsts := false }) only [vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  exact h

private theorem tInBasis202 : ∃ e : model.classical.sphere.Page 2 (12,138) ≃ₗ[ℤ] (Fin 5 →₀ F2),
    ∀ j : Fin 5, e.symm (Finsupp.single j 1)=basis .sphere 12 138 j.val := by
  exact basis_correct ⟨.sphere, 12, 138, ["25,1,190,1", "3,1,336,1", "0,1,427,1", "0,2,419,1", "0,10,69,2"]⟩ (by exact List.mem_of_getElem? (i := 202) rfl)

private theorem tInBasis217 : ∃ e : model.classical.sphere.Page 2 (14,139) ≃ₗ[ℤ] (Fin 3 →₀ F2),
    ∀ j : Fin 3, e.symm (Finsupp.single j 1)=basis .sphere 14 139 j.val := by
  exact basis_correct ⟨.sphere, 14, 139, ["449,1", "1,1,7,1,275,1", "0,2,425,1"]⟩ (by exact List.mem_of_getElem? (i := 217) rfl)

private theorem tInBasis150 : ∃ e : model.classical.sphere.Page 2 (7,133) ≃ₗ[ℤ] (Fin 2 →₀ F2),
    ∀ j : Fin 2, e.symm (Finsupp.single j 1)=basis .sphere 7 133 j.val := by
  exact basis_correct ⟨.sphere, 7, 133, ["1,1,69,1,76,1", "0,5,69,2"]⟩ (by exact List.mem_of_getElem? (i := 150) rfl)

private theorem tInBasis138 : ∃ e : model.classical.sphere.Page 2 (6,132) ≃ₗ[ℤ] (Fin 2 →₀ F2),
    ∀ j : Fin 2, e.symm (Finsupp.single j 1)=basis .sphere 6 132 j.val := by
  exact basis_correct ⟨.sphere, 6, 132, ["368,1", "0,4,69,2"]⟩ (by exact List.mem_of_getElem? (i := 138) rfl)

private theorem tInBasis127 : ∃ e : model.classical.sphere.Page 2 (5,131) ≃ₗ[ℤ] (Fin 1 →₀ F2),
    ∀ j : Fin 1, e.symm (Finsupp.single j 1)=basis .sphere 5 131 j.val := by
  exact basis_correct ⟨.sphere, 5, 131, ["0,3,69,2"]⟩ (by exact List.mem_of_getElem? (i := 127) rfl)

private theorem tInBasis119 : ∃ e : model.classical.sphere.Page 2 (4,130) ≃ₗ[ℤ] (Fin 2 →₀ F2),
    ∀ j : Fin 2, e.symm (Finsupp.single j 1)=basis .sphere 4 130 j.val := by
  exact basis_correct ⟨.sphere, 4, 130, ["341,1", "0,2,69,2"]⟩ (by exact List.mem_of_getElem? (i := 119) rfl)

private theorem tInBasis149 : ∃ e : model.classical.sphere.Page 2 (7,132) ≃ₗ[ℤ] (Fin 1 →₀ F2),
    ∀ j : Fin 1, e.symm (Finsupp.single j 1)=basis .sphere 7 132 j.val := by
  exact basis_correct ⟨.sphere, 7, 132, ["0,2,340,1"]⟩ (by exact List.mem_of_getElem? (i := 149) rfl)

private theorem tInBasis108 : ∃ e : model.classical.sphere.Page 2 (3,129) ≃ₗ[ℤ] (Fin 1 →₀ F2),
    ∀ j : Fin 1, e.symm (Finsupp.single j 1)=basis .sphere 3 129 j.val := by
  exact basis_correct ⟨.sphere, 3, 129, ["0,1,69,2"]⟩ (by exact List.mem_of_getElem? (i := 108) rfl)

private theorem tInBasis90 : ∃ e : model.classical.sphere.Page 2 (1,127) ≃ₗ[ℤ] (Fin 0 →₀ F2),
    ∀ j : Fin 0, e.symm (Finsupp.single j 1)=basis .sphere 1 127 j.val := by
  exact basis_correct ⟨.sphere, 1, 127, []⟩ (by exact List.mem_of_getElem? (i := 90) rfl)

private theorem tInBasis77 : ∃ e : model.classical.sphere.Page 2 (0,126) ≃ₗ[ℤ] (Fin 0 →₀ F2),
    ∀ j : Fin 0, e.symm (Finsupp.single j 1)=basis .sphere 0 126 j.val := by
  exact basis_correct ⟨.sphere, 0, 126, []⟩ (by exact List.mem_of_getElem? (i := 77) rfl)

private theorem tIn_zero_of_complete_zero
    {E : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ×ℤ)}
    {r : ℤ} {p : ℤ×ℤ} {n : ℕ} (hr : 2≤r)
    (e : E.Page 2 p ≃ₗ[ℤ] (Fin n →₀ F2))
    (he : ∀ i : Fin n, RepresentsOnPage E r p (e.symm (Finsupp.single i 1)) 0)
    (z : E.Page r p) : z=0 := by
  obtain ⟨c,hc⟩ := page_generated_from_representatives hr e (fun _ => 0) he z
  simpa only [ite_self,Finset.sum_const_zero] using hc

private theorem tIn_zero_two_after_nonzero
    {E : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ×ℤ)}
    {r : ℤ} {p q : ℤ×ℤ} {b : E.Page 2 q} (hs : E.r₀≤3) (hr : 4≤r)
    (e : E.Page 2 p ≃ₗ[ℤ] (Fin 2 →₀ F2))
    (h0 : HasNonzeroDifferential E 3 p q (e.symm (Finsupp.single 0 1)) b)
    (h1 : RepresentsOnPage E 3 p (e.symm (Finsupp.single 1 1)) 0)
    (z : E.Page r p) : z=0 := by
  obtain ⟨hd,a,y,ha,hy,day,yne⟩ := h0
  obtain ⟨x,hx⟩ := page_has_initial_representative (by omega : 2≤r) z
  obtain ⟨z3,hz3⟩ := represents_before (by decide : (2:ℤ)≤3) (by omega : 3≤r) hx
  have dz : E.d 3 p z3=0 := represents_d_zero_of_later hs (by omega : 3<r) hz3 ⟨z,hx⟩
  have za : z3=a → False := by
    intro h
    rw [h] at dz
    rw [ModuleCat.comp_apply,dz,map_zero] at day
    exact yne day.symm
  have zz : z3=0 := by
    rcases generated_two (by decide : (2:ℤ)≤3) e a 0 ha h1 z3 with h|h|h|h
    · exact h
    · exact (za h).elim
    · exact h
    · exact (za (by simpa only [add_zero] using h)).elim
  rw [zz] at hz3
  exact represents_later_zero (by omega : 3≤r) hz3 hx

private theorem tIn_ninth_zero (r : ℤ) (hr : 3≤r)
    (z : model.classical.sphere.Page r (5,131)) : z=0 := by
  obtain ⟨e,he⟩ := tInBasis127
  apply tIn_zero_of_complete_zero (by omega : 2≤r) e ?_ z
  intro i
  rw [he i]
  fin_cases i
  exact differential_target_later_zero tIn_start (by omega : (2:ℤ)<r) tInRow153

private theorem tIn_eleventh_zero (r : ℤ) (hr : 3≤r)
    (z : model.classical.sphere.Page r (3,129)) : z=0 := by
  obtain ⟨e,he⟩ := tInBasis108
  apply tIn_zero_of_complete_zero (by omega : 2≤r) e ?_ z
  intro i
  rw [he i]
  fin_cases i
  exact differential_target_later_zero tIn_start (by omega : (2:ℤ)<r) tInRow143

private theorem tIn_seventh_map_zero : model.classical.sphere.d 7 (7,133)=0 := by
  obtain ⟨e,he⟩ := tInBasis150
  obtain ⟨a,ha⟩ := reaches_before (by decide : (2:ℤ)≤7) (by decide : (7:ℤ)≤18) tInRow186
  apply d_zero_of_complete_representatives (by decide : (2:ℤ)≤7) e
  intro i
  rw [he i]
  fin_cases i
  · refine ⟨a,ha,?_⟩
    · exact represents_d_zero_of_later (by have h:=tIn_start;omega)
        (by decide : (7:ℤ)<18) ha tInRow186
  · refine ⟨0,?_,map_zero _⟩
    exact differential_target_later_zero tIn_start (by decide : (2:ℤ)<7) tInRow165

private theorem tIn_five_d2_zero : model.classical.sphere.d 2 (5,131)=0 := by
  obtain ⟨e,he⟩ := tInBasis127
  obtain ⟨a,ha,hz⟩ := differential_target_cycle tInRow153
  rw [←ha.eq_on_page_two] at hz
  apply d_zero_of_complete_representatives (by decide : (2:ℤ)≤2) e
  intro i
  rw [he i]
  fin_cases i
  refine ⟨basis .sphere 5 131 0,?_,hz⟩
  exact represents_two_self _

private theorem tIn_four_source_nonzero_d3 :
    HasNonzeroDifferential model.classical.sphere 3 (4,130) (7,132)
      (basis .sphere 4 130 0) (basis .sphere 7 132 0) := by
  obtain ⟨e,he⟩ := tInBasis149
  obtain ⟨hd,a,b,ha,hb,dab⟩ := tInRow157
  refine ⟨hd,a,b,ha,hb,dab,?_⟩
  have hin : (5,131)+model.classical.sphere.diffDeg 2=(7,132) := by
    simp only [model.classical.differentialDegree,Prod.mk_add_mk,Int.reduceSub,Int.reduceAdd]
  apply represents_next_nonzero_of_not_incoming_at hin tIn_start (by decide : (2:ℤ)≤2)
    hb (represents_two_self _)
  intro z hz
  have hn : basis .sphere 7 132 0≠0 := by
    have he0 : e.symm (Finsupp.single (0:Fin 1) 1)=basis .sphere 7 132 0 := he 0
    rw [←he0]
    exact basis_vector_ne_zero e 0
  have hdz : model.classical.sphere.d 2 (5,131) z=0 := by rw [tIn_five_d2_zero];rfl
  rw [ModuleCat.comp_apply,hdz,map_zero] at hz
  exact hn hz.symm

private theorem tIn_tenth_zero (r : ℤ) (hr : 4≤r)
    (z : model.classical.sphere.Page r (4,130)) : z=0 := by
  obtain ⟨e,he⟩ := tInBasis119
  apply tIn_zero_two_after_nonzero (E := model.classical.sphere) (q := (7,132)) (b := basis .sphere 7 132 0)
    (by have h:=tIn_start;omega) hr e ?_ ?_ z
  · rw [he 0]
    exact tIn_four_source_nonzero_d3
  · rw [he 1]
    exact differential_target_later_zero tIn_start (by decide : (2:ℤ)<3) tInRow147

private theorem tIn_empty_later {p : ℤ×ℤ} {r : ℤ} (hr : 2≤r)
    (e : model.classical.sphere.Page 2 p ≃ₗ[ℤ] (Fin 0 →₀ F2))
    (z : model.classical.sphere.Page r p) : z=0 := by
  haveI : Subsingleton (model.classical.sphere.Page 2 p) := e.injective.subsingleton
  obtain ⟨x,hx⟩ := page_has_initial_representative hr z
  rw [Subsingleton.elim x 0] at hx
  exact represents_unique hx (RepresentsOnPage.zero hr)

private theorem tIn_second_avoid (x : model.classical.sphere.Page 2 (12,138)) :
    (model.classical.sphere.d 2 (12,138) ≫
      eqToHom (congrArg (model.classical.sphere.Page 2) tInRow314.target_degree)) x≠T := by
  classical
  let E := model.classical.sphere
  obtain ⟨f,hf⟩ := tInBasis202
  obtain ⟨g,hg⟩ := tInBasis217
  let δ : E.Page 2 (12,138) ⟶ E.Page 2 (14,139) :=
    E.d 2 (12,138) ≫ eqToHom (congrArg (E.Page 2) tInRow314.target_degree)
  have zero_column {b : E.Page 2 (12,138)}
      (h : E.d 2 (12,138) b=0) : δ b=0 := by
    dsimp only [δ]
    rw [ModuleCat.comp_apply,h,map_zero]
  have d0 : δ (basis .sphere 12 138 0)=0 := by
    obtain ⟨a,ha,hz⟩ := differential_target_cycle tInRow264
    rw [←ha.eq_on_page_two] at hz
    exact zero_column hz
  have d1 : δ (basis .sphere 12 138 1)=basis .sphere 14 139 2 := tInRow314.eq_on_page_two.2
  have d2 : δ (basis .sphere 12 138 2)=0 := by
    obtain ⟨a,ha,hz⟩ := differential_target_cycle tInRow265
    rw [←ha.eq_on_page_two] at hz
    exact zero_column hz
  have d3 : δ (basis .sphere 12 138 3)=0 := by
    obtain ⟨_,a,b,ha,hb,hd⟩ := tInRow313
    exact zero_column (represents_d_zero_of_later tIn_start (by decide : (2:ℤ)<4)
      (represents_two_self _) ⟨a,ha⟩)
  have d4 : δ (basis .sphere 12 138 4)=0 := by
    obtain ⟨a,ha,hz⟩ := differential_target_cycle tInRow266
    rw [←ha.eq_on_page_two] at hz
    exact zero_column hz
  have bit (b : F2) (a : E.Page 2 (12,138)) :
      δ (if b=0 then 0 else a)=if b=0 then 0 else δ a := by
    by_cases h : b=0 <;> simp only [h,ite_true,ite_false,map_zero]
  have hx := finite_basis_expansion f x
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,hf,add_zero] at hx
  change x=(if f x 0=0 then 0 else basis .sphere 12 138 0)+
    ((if f x 1=0 then 0 else basis .sphere 12 138 1)+
    ((if f x 2=0 then 0 else basis .sphere 12 138 2)+
    ((if f x 3=0 then 0 else basis .sphere 12 138 3)+
      (if f x 4=0 then 0 else basis .sphere 12 138 4)))) at hx
  have dx := congrArg δ hx
  simp only [map_add,bit,d0,d1,d2,d3,d4,ite_self,add_zero,zero_add] at dx
  have hg1 : g (basis .sphere 14 139 1)=Finsupp.single (1:Fin 3) 1 := by
    have h : g.symm (Finsupp.single (1:Fin 3) 1)=basis .sphere 14 139 1 := hg 1
    rw [←h,LinearEquiv.apply_symm_apply]
  have hg2 : g (basis .sphere 14 139 2)=Finsupp.single (2:Fin 3) 1 := by
    have h : g.symm (Finsupp.single (2:Fin 3) 1)=basis .sphere 14 139 2 := hg 2
    rw [←h,LinearEquiv.apply_symm_apply]
  have coord : g (δ x) 1=0 := by
    rw [dx]
    by_cases h : f x 1=0
    · simp only [h,ite_true,map_zero,Finsupp.zero_apply]
    · simp only [h,ite_false,hg2]
      norm_num [Finsupp.single_apply,Fin.ext_iff]
  intro hit
  change δ x=T at hit
  rw [←basis_T] at hit
  have h := congrArg (fun y=>g y 1) hit
  rw [coord,hg1,Finsupp.single_eq_same] at h
  exact zero_ne_one h

private theorem tIn_eighth_zero (r : ℤ) (hr : 4≤r)
    (z : model.classical.sphere.Page r (6,132)) : z=0 := by
  obtain ⟨e,he⟩ := tInBasis138
  have he0 : e.symm (Finsupp.single (0:Fin 2) 1)=atom .x_126_6 := by
    have hb : basis .sphere 6 132 0=atom .x_126_6 := basis_value ⟨.named .x_126_6,0⟩ (by decide)
    exact (he 0).trans hb
  have he1 : e.symm (Finsupp.single (1:Fin 2) 1)=basis .sphere 6 132 1 := he 1
  have go {b : model.classical.sphere.Page 2 (9,134)}
      (h : HasNonzeroDifferential model.classical.sphere 3 (6,132) (9,134) (atom .x_126_6) b) : z=0 := by
    apply tIn_zero_two_after_nonzero (E := model.classical.sphere) (q := (9,134)) (b := b)
      (by have h:=tIn_start;omega) hr e ?_ ?_ z
    · rw [he0];exact h
    · rw [he1]
      exact differential_target_later_zero tIn_start (by decide : (2:ℤ)<3) tInRow158
  rcases d3_x126_6_candidates with h|h
  · exact go h
  · exact go h

private theorem r5TenD256 : HasDifferential model.classical.sphere 2 (8,135) (10,136)
    (basis .sphere 8 135 0) (basis .sphere 10 136 1) := by
  have hrow := result ⟨.sphere,.equation,2,8,135,[0],10,136,[1],"S0_AdamsE2_ss",2855⟩ (by
    exact List.mem_of_getElem? (i := 256) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential model.classical.sphere 2 (8,135) (10,136) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 135 [0]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 10 136 [1]=true := rfl
  delta decode at ha hb
  simp (config := { congrConsts := false }) only [vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  exact h

private theorem r5TenD257 : HasDifferential model.classical.sphere 2 (8,135) (10,136)
    (basis .sphere 8 135 4) (basis .sphere 10 136 3) := by
  have hrow := result ⟨.sphere,.equation,2,8,135,[4],10,136,[3],"S0_AdamsE2_ss",2856⟩ (by
    exact List.mem_of_getElem? (i := 257) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential model.classical.sphere 2 (8,135) (10,136) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 135 [4]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 10 136 [3]=true := rfl
  delta decode at ha hb
  simp (config := { congrConsts := false }) only [vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  exact h

private theorem r5TenD258 : HasDifferential model.classical.sphere 2 (8,135) (10,136)
    (basis .sphere 8 135 6) (basis .sphere 10 136 4) := by
  have hrow := result ⟨.sphere,.equation,2,8,135,[6],10,136,[4],"S0_AdamsE2_ss",2857⟩ (by
    exact List.mem_of_getElem? (i := 258) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential model.classical.sphere 2 (8,135) (10,136) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 135 [6]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 10 136 [4]=true := rfl
  delta decode at ha hb
  simp (config := { congrConsts := false }) only [vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  exact h

private theorem r5TenD260 : HasDifferential model.classical.sphere 2 (10,136) (12,137)
    (basis .sphere 10 136 0) (basis .sphere 12 137 2) := by
  have hrow := result ⟨.sphere,.equation,2,10,136,[0],12,137,[2],"S0_AdamsE2_ss",2859⟩ (by
    exact List.mem_of_getElem? (i := 260) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential model.classical.sphere 2 (10,136) (12,137) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 136 [0]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 137 [2]=true := rfl
  delta decode at ha hb
  simp (config := { congrConsts := false }) only [vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  exact h

private theorem r5TenR259 : ReachesPage model.classical.sphere 1000 (10,136)
    (basis .sphere 10 136 2) := by
  have hrow := result ⟨.sphere,.reaches,1000,10,136,[2],10,136,[],"S0_AdamsE2_ss",2858⟩ (by
    exact List.mem_of_getElem? (i := 259) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,h⟩ := hrow
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 136 [2]=true := rfl
  delta decode at ha
  simp (config := { congrConsts := false }) only [vx,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha
  rw [←ha] at h
  exact h

private theorem r5TenBasis10 :
    ∃ e : model.classical.sphere.Page 2 (10,136) ≃ₗ[ℤ] (Fin 5 →₀ F2),
      ∀ i, e.symm (Finsupp.single i 1)=basis .sphere 10 136 i.val := by
  exact basis_correct ⟨.sphere,10,136,["419,1","0,1,414,1","0,2,394,1","0,2,392,1","0,8,69,2"]⟩
    (by exact List.mem_of_getElem? (i := 183) (by rfl))

private theorem r5TenBasis12 :
    ∃ e : model.classical.sphere.Page 2 (12,137) ≃ₗ[ℤ] (Fin 5 →₀ F2),
      ∀ i, e.symm (Finsupp.single i 1)=basis .sphere 12 137 i.val := by
  exact basis_correct ⟨.sphere,12,137,["426,1","425,1","0,1,69,1,89,1","0,3,391,1","0,4,375,1"]⟩
    (by exact List.mem_of_getElem? (i := 201) (by rfl))

private noncomputable def r5TenE10 : model.classical.sphere.Page 2 (10,136) ≃ₗ[ℤ] (Fin 5 →₀ F2) :=
  Classical.choose r5TenBasis10
private theorem r5TenE10_basis (i : Fin 5) :
    r5TenE10.symm (Finsupp.single i 1)=basis .sphere 10 136 i.val :=
  Classical.choose_spec r5TenBasis10 i
private noncomputable def r5TenE12 : model.classical.sphere.Page 2 (12,137) ≃ₗ[ℤ] (Fin 5 →₀ F2) :=
  Classical.choose r5TenBasis12
private theorem r5TenE12_basis (i : Fin 5) :
    r5TenE12.symm (Finsupp.single i 1)=basis .sphere 12 137 i.val :=
  Classical.choose_spec r5TenBasis12 i

private noncomputable def r5TenDelta : model.classical.sphere.Page 2 (10,136) →ₗ[ℤ]
    model.classical.sphere.Page 2 (12,137) :=
  (model.classical.sphere.d 2 (10,136) ≫
    eqToHom (congrArg (model.classical.sphere.Page 2) r5TenD260.target_degree)).hom

private theorem r5Ten_matrix (i : Fin 5) :
    r5TenDelta (basis .sphere 10 136 i.val)=
      if i=0 then basis .sphere 12 137 2 else 0 := by
  have hs2 : model.classical.sphere.r₀≤2 := by rw [model.classical.firstPage]
  have d0 : r5TenDelta (basis .sphere 10 136 0)=basis .sphere 12 137 2 :=
    r5TenD260.eq_on_page_two.2
  have d1 : model.classical.sphere.d 2 (10,136) (basis .sphere 10 136 1)=0 := by
    obtain ⟨a,ha,hd⟩ := differential_target_cycle r5TenD256
    rwa [←ha.eq_on_page_two] at hd
  have d2 : model.classical.sphere.d 2 (10,136) (basis .sphere 10 136 2)=0 :=
    represents_d_zero_of_later hs2 (by decide : (2:ℤ)<1000) (represents_two_self _) r5TenR259
  have d3 : model.classical.sphere.d 2 (10,136) (basis .sphere 10 136 3)=0 := by
    obtain ⟨a,ha,hd⟩ := differential_target_cycle r5TenD257
    rwa [←ha.eq_on_page_two] at hd
  have d4 : model.classical.sphere.d 2 (10,136) (basis .sphere 10 136 4)=0 := by
    obtain ⟨a,ha,hd⟩ := differential_target_cycle r5TenD258
    rwa [←ha.eq_on_page_two] at hd
  fin_cases i
  · exact d0
  all_goals simp only [r5TenDelta,ModuleCat.hom_comp,LinearMap.comp_apply,d1,d2,d3,d4,map_zero]
  all_goals norm_num

private theorem r5Ten_delta_formula (x : model.classical.sphere.Page 2 (10,136)) :
    r5TenDelta x=if r5TenE10 x 0=0 then 0 else basis .sphere 12 137 2 := by
  with_unfolding_all
    classical
    have hx := finite_basis_expansion r5TenE10 x
    simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,r5TenE10_basis,add_zero] at hx
    change x=(if r5TenE10 x 0=0 then 0 else basis .sphere 10 136 0)+
      ((if r5TenE10 x 1=0 then 0 else basis .sphere 10 136 1)+
      ((if r5TenE10 x 2=0 then 0 else basis .sphere 10 136 2)+
      ((if r5TenE10 x 3=0 then 0 else basis .sphere 10 136 3)+
        (if r5TenE10 x 4=0 then 0 else basis .sphere 10 136 4)))) at hx
    have d0 : r5TenDelta (basis .sphere 10 136 0)=basis .sphere 12 137 2 := by
      exact r5Ten_matrix (0 : Fin 5)
    have d1 : r5TenDelta (basis .sphere 10 136 1)=0 := by
      have h := r5Ten_matrix (1 : Fin 5)
      exact h
    have d2 : r5TenDelta (basis .sphere 10 136 2)=0 := by
      have h := r5Ten_matrix (2 : Fin 5)
      exact h
    have d3 : r5TenDelta (basis .sphere 10 136 3)=0 := by
      have h := r5Ten_matrix (3 : Fin 5)
      exact h
    have d4 : r5TenDelta (basis .sphere 10 136 4)=0 := by
      have h := r5Ten_matrix (4 : Fin 5)
      exact h
    have hd := congrArg r5TenDelta hx
    by_cases h0 : r5TenE10 x 0=0 <;> by_cases h1 : r5TenE10 x 1=0 <;>
      by_cases h2 : r5TenE10 x 2=0 <;> by_cases h3 : r5TenE10 x 3=0 <;>
      by_cases h4 : r5TenE10 x 4=0 <;>
      simpa only [map_add,h0,h1,h2,h3,h4,ite_true,ite_false,map_zero,
        d0,d1,d2,d3,d4,add_zero,zero_add] using hd

private theorem r5Ten_image_coord (x : model.classical.sphere.Page 2 (10,136))
    (j : Fin 5) (hj : j=3 ∨ j=4) : r5TenE12 (r5TenDelta x) j=0 := by
  have he2 : r5TenE12.symm (Finsupp.single (2 : Fin 5) 1)=basis .sphere 12 137 2 :=
    r5TenE12_basis 2
  have e2 : r5TenE12 (basis .sphere 12 137 2)=Finsupp.single (2 : Fin 5) 1 := by
    rw [←he2,LinearEquiv.apply_symm_apply]
  rw [r5Ten_delta_formula]
  rcases hj with rfl|rfl
  · split
    · simp only [map_zero,Finsupp.zero_apply]
    · rw [e2,Finsupp.single_eq_of_ne (by decide : (3 : Fin 5)≠2)]
  · split
    · simp only [map_zero,Finsupp.zero_apply]
    · rw [e2,Finsupp.single_eq_of_ne (by decide : (4 : Fin 5)≠2)]

private theorem r5_ten_zero (r : ℤ) (hr3 : 3≤r) (hr1000 : r<1000) :
    model.classical.sphere.d r (10,136)=0 := by
  classical
  have hs2 : model.classical.sphere.r₀≤2 := by rw [model.classical.firstPage]
  apply d_zero_of_second_kernel_extends hs2 hr3
  intro x hx
  have hδ : r5TenDelta x=0 := by
    dsimp only [r5TenDelta]
    rw [ModuleCat.hom_comp,LinearMap.comp_apply,hx,map_zero]
  have h0 : r5TenE10 x 0=0 := by
    by_contra hn
    have ht : basis .sphere 12 137 2=0 := by
      simpa only [r5Ten_delta_formula,hn,ite_false] using hδ
    have he2 : r5TenE12.symm (Finsupp.single (2 : Fin 5) 1)=basis .sphere 12 137 2 :=
      r5TenE12_basis 2
    exact basis_vector_ne_zero r5TenE12 2 (he2.trans ht)
  apply reaches_from_support (by omega : (2:ℤ)≤r+1) r5TenE10 x
  intro i hi
  rw [r5TenE10_basis]
  fin_cases i
  · exact (hi h0).elim
  · exact ⟨0,differential_target_later_zero hs2 (by omega) r5TenD256⟩
  · exact reaches_before (by omega) (by omega) r5TenR259
  · exact ⟨0,differential_target_later_zero hs2 (by omega) r5TenD257⟩
  · exact ⟨0,differential_target_later_zero hs2 (by omega) r5TenD258⟩



private theorem r5Equation {r s t ts tt : ℕ} {xs ys : List ℕ} {origin : String} {record : ℕ}
    (hc : (⟨.sphere,.equation,r,s,t,xs,ts,tt,ys,origin,record⟩ : Raw.Claim) ∈ Raw.claims)
    (vx : Raw.coordinatesValid Raw.degrees .sphere s t xs=true)
    (vy : Raw.coordinatesValid Raw.degrees .sphere ts tt ys=true) :
    HasDifferential model.classical.sphere r (s,t) (ts,tt)
      ((xs.map (basis .sphere s t)).sum) ((ys.map (basis .sphere ts tt)).sum) := by
  with_unfolding_all
    have hrow := result ⟨.sphere,.equation,r,s,t,xs,ts,tt,ys,origin,record⟩ hc
    dsimp only [Statement] at hrow
    obtain ⟨x,hx,y,hy,h⟩ := hrow
    simp only [decode,vx,vy,if_true,Option.some.injEq] at hx hy
    rw [←hx,←hy] at h
    exact h

private theorem r5Reach {r s t : ℕ} {xs : List ℕ} {origin : String} {record : ℕ}
    (hc : (⟨.sphere,.reaches,r,s,t,xs,s,t,[],origin,record⟩ : Raw.Claim) ∈ Raw.claims)
    (vx : Raw.coordinatesValid Raw.degrees .sphere s t xs=true) :
    ReachesPage model.classical.sphere r (s,t) ((xs.map (basis .sphere s t)).sum) := by
  with_unfolding_all
    have hrow := result ⟨.sphere,.reaches,r,s,t,xs,s,t,[],origin,record⟩ hc
    dsimp only [Statement] at hrow
    obtain ⟨x,hx,h⟩ := hrow
    simp only [decode,vx,if_true,Option.some.injEq] at hx
    rw [←hx] at h
    exact h

private theorem r5D229 : HasDifferential model.classical.sphere 2 (7,134) (9,135)
    (basis .sphere 7 134 1) (basis .sphere 9 135 4) := by
  with_unfolding_all
    have h := r5Equation (by exact List.mem_of_getElem? (i := 229) (by rfl)) (by rfl) (by rfl)
    simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Nat.cast_ofNat] using h

private theorem r5D230 : HasDifferential model.classical.sphere 2 (7,134) (9,135)
    (basis .sphere 7 134 4) (basis .sphere 9 135 5) := by
  with_unfolding_all
    have h := r5Equation (by exact List.mem_of_getElem? (i := 230) (by rfl)) (by rfl) (by rfl)
    simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Nat.cast_ofNat] using h

private theorem r5D231 : HasDifferential model.classical.sphere 4 (9,135) (13,138)
    (basis .sphere 9 135 2) (basis .sphere 13 138 0) := by
  with_unfolding_all
    have h := r5Equation (by exact List.mem_of_getElem? (i := 231) (by rfl)) (by rfl) (by rfl)
    simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Nat.cast_ofNat] using h

private theorem r5D232 : HasDifferential model.classical.sphere 4 (9,135) (13,138)
    (basis .sphere 9 135 1) (basis .sphere 13 138 2) := by
  with_unfolding_all
    have h := r5Equation (by exact List.mem_of_getElem? (i := 232) (by rfl)) (by rfl) (by rfl)
    simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Nat.cast_ofNat] using h

private theorem r5D233 : HasDifferential model.classical.sphere 3 (9,135) (12,137)
    (basis .sphere 9 135 0) (basis .sphere 12 137 3 + basis .sphere 12 137 4) := by
  with_unfolding_all
    have h := r5Equation (by exact List.mem_of_getElem? (i := 233) (by rfl)) (by rfl) (by rfl)
    simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Nat.cast_ofNat] using h

private theorem r5D234 : HasDifferential model.classical.sphere 3 (9,135) (12,137)
    (basis .sphere 9 135 3) (basis .sphere 12 137 3) := by
  with_unfolding_all
    have h := r5Equation (by exact List.mem_of_getElem? (i := 234) (by rfl)) (by rfl) (by rfl)
    simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Nat.cast_ofNat] using h

private theorem r5D284 : HasDifferential model.classical.sphere 2 (9,136) (11,137)
    (basis .sphere 9 136 2) (basis .sphere 11 137 4) := by
  with_unfolding_all
    have h := r5Equation (by exact List.mem_of_getElem? (i := 284) (by rfl)) (by rfl) (by rfl)
    simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Nat.cast_ofNat] using h

private theorem r5D285 : HasDifferential model.classical.sphere 2 (9,136) (11,137)
    (basis .sphere 9 136 4) (basis .sphere 11 137 5) := by
  with_unfolding_all
    have h := r5Equation (by exact List.mem_of_getElem? (i := 285) (by rfl)) (by rfl) (by rfl)
    simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Nat.cast_ofNat] using h

private theorem r5D286 : ReachesPage model.classical.sphere 1000 (11,137) (basis .sphere 11 137 1 + basis .sphere 11 137 2) := by
  with_unfolding_all
    have h := r5Reach (by exact List.mem_of_getElem? (i := 286) (by rfl)) (by rfl)
    simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Nat.cast_ofNat] using h

private theorem r5D287 : HasDifferential model.classical.sphere 4 (11,137) (15,140)
    (basis .sphere 11 137 2) (basis .sphere 15 140 1) := by
  with_unfolding_all
    have h := r5Equation (by exact List.mem_of_getElem? (i := 287) (by rfl)) (by rfl) (by rfl)
    simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Nat.cast_ofNat] using h

private theorem r5D288 : HasDifferential model.classical.sphere 2 (11,137) (13,138)
    (basis .sphere 11 137 0) (basis .sphere 13 138 3) := by
  with_unfolding_all
    have h := r5Equation (by exact List.mem_of_getElem? (i := 288) (by rfl)) (by rfl) (by rfl)
    simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Nat.cast_ofNat] using h

private theorem r5D289 : HasDifferential model.classical.sphere 2 (11,137) (13,138)
    (basis .sphere 11 137 3) (basis .sphere 13 138 4) := by
  with_unfolding_all
    have h := r5Equation (by exact List.mem_of_getElem? (i := 289) (by rfl)) (by rfl) (by rfl)
    simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Nat.cast_ofNat] using h

private noncomputable def r5e11 : model.classical.sphere.Page 2 (11,137) ≃ₗ[ℤ] (Fin 6 →₀ F2) :=
  (basis_correct ⟨.sphere,11,137,["427,1", "1,1,413,1", "1,1,412,1", "0,1,419,1", "0,2,414,1", "0,9,69,2"]⟩ (by exact List.mem_of_getElem? (i := 193) (by rfl))).choose
private theorem r5he11 (i : Fin 6) :
    r5e11.symm (Finsupp.single i 1)=basis .sphere 11 137 i.val :=
  (basis_correct ⟨.sphere,11,137,["427,1", "1,1,413,1", "1,1,412,1", "0,1,419,1", "0,2,414,1", "0,9,69,2"]⟩ (by exact List.mem_of_getElem? (i := 193) (by rfl))).choose_spec i
private theorem r5ec11_0 : r5e11 (basis .sphere 11 137 0)=Finsupp.single (0:Fin 6) 1 := by
  with_unfolding_all
    have hh : r5e11.symm (Finsupp.single (0:Fin 6) 1)=basis .sphere 11 137 0 := r5he11 0
    rw [←hh,LinearEquiv.apply_symm_apply]
private theorem r5ec11_1 : r5e11 (basis .sphere 11 137 1)=Finsupp.single (1:Fin 6) 1 := by
  with_unfolding_all
    have hh : r5e11.symm (Finsupp.single (1:Fin 6) 1)=basis .sphere 11 137 1 := r5he11 1
    rw [←hh,LinearEquiv.apply_symm_apply]
private theorem r5ec11_2 : r5e11 (basis .sphere 11 137 2)=Finsupp.single (2:Fin 6) 1 := by
  with_unfolding_all
    have hh : r5e11.symm (Finsupp.single (2:Fin 6) 1)=basis .sphere 11 137 2 := r5he11 2
    rw [←hh,LinearEquiv.apply_symm_apply]
private theorem r5ec11_3 : r5e11 (basis .sphere 11 137 3)=Finsupp.single (3:Fin 6) 1 := by
  with_unfolding_all
    have hh : r5e11.symm (Finsupp.single (3:Fin 6) 1)=basis .sphere 11 137 3 := r5he11 3
    rw [←hh,LinearEquiv.apply_symm_apply]
private theorem r5ec11_4 : r5e11 (basis .sphere 11 137 4)=Finsupp.single (4:Fin 6) 1 := by
  with_unfolding_all
    have hh : r5e11.symm (Finsupp.single (4:Fin 6) 1)=basis .sphere 11 137 4 := r5he11 4
    rw [←hh,LinearEquiv.apply_symm_apply]
private theorem r5ec11_5 : r5e11 (basis .sphere 11 137 5)=Finsupp.single (5:Fin 6) 1 := by
  with_unfolding_all
    have hh : r5e11.symm (Finsupp.single (5:Fin 6) 1)=basis .sphere 11 137 5 := r5he11 5
    rw [←hh,LinearEquiv.apply_symm_apply]

private noncomputable def r5e13 : model.classical.sphere.Page 2 (13,138) ≃ₗ[ℤ] (Fin 5 →₀ F2) :=
  (basis_correct ⟨.sphere,13,138,["24,1,190,1", "3,1,335,1", "0,1,425,1", "0,4,391,1", "0,5,375,1"]⟩ (by exact List.mem_of_getElem? (i := 209) (by rfl))).choose
private theorem r5he13 (i : Fin 5) :
    r5e13.symm (Finsupp.single i 1)=basis .sphere 13 138 i.val :=
  (basis_correct ⟨.sphere,13,138,["24,1,190,1", "3,1,335,1", "0,1,425,1", "0,4,391,1", "0,5,375,1"]⟩ (by exact List.mem_of_getElem? (i := 209) (by rfl))).choose_spec i
private theorem r5ec13_0 : r5e13 (basis .sphere 13 138 0)=Finsupp.single (0:Fin 5) 1 := by
  with_unfolding_all
    have hh : r5e13.symm (Finsupp.single (0:Fin 5) 1)=basis .sphere 13 138 0 := r5he13 0
    rw [←hh,LinearEquiv.apply_symm_apply]
private theorem r5ec13_1 : r5e13 (basis .sphere 13 138 1)=Finsupp.single (1:Fin 5) 1 := by
  with_unfolding_all
    have hh : r5e13.symm (Finsupp.single (1:Fin 5) 1)=basis .sphere 13 138 1 := r5he13 1
    rw [←hh,LinearEquiv.apply_symm_apply]
private theorem r5ec13_2 : r5e13 (basis .sphere 13 138 2)=Finsupp.single (2:Fin 5) 1 := by
  with_unfolding_all
    have hh : r5e13.symm (Finsupp.single (2:Fin 5) 1)=basis .sphere 13 138 2 := r5he13 2
    rw [←hh,LinearEquiv.apply_symm_apply]
private theorem r5ec13_3 : r5e13 (basis .sphere 13 138 3)=Finsupp.single (3:Fin 5) 1 := by
  with_unfolding_all
    have hh : r5e13.symm (Finsupp.single (3:Fin 5) 1)=basis .sphere 13 138 3 := r5he13 3
    rw [←hh,LinearEquiv.apply_symm_apply]
private theorem r5ec13_4 : r5e13 (basis .sphere 13 138 4)=Finsupp.single (4:Fin 5) 1 := by
  with_unfolding_all
    have hh : r5e13.symm (Finsupp.single (4:Fin 5) 1)=basis .sphere 13 138 4 := r5he13 4
    rw [←hh,LinearEquiv.apply_symm_apply]

private noncomputable def r5e9 : model.classical.sphere.Page 2 (9,135) ≃ₗ[ℤ] (Fin 6 →₀ F2) :=
  (basis_correct ⟨.sphere,9,135,["414,1", "1,1,376,1", "1,1,375,1", "0,1,394,1", "0,1,392,1", "0,7,69,2"]⟩ (by exact List.mem_of_getElem? (i := 174) (by rfl))).choose
private theorem r5he9 (i : Fin 6) :
    r5e9.symm (Finsupp.single i 1)=basis .sphere 9 135 i.val :=
  (basis_correct ⟨.sphere,9,135,["414,1", "1,1,376,1", "1,1,375,1", "0,1,394,1", "0,1,392,1", "0,7,69,2"]⟩ (by exact List.mem_of_getElem? (i := 174) (by rfl))).choose_spec i
private theorem r5ec9_0 : r5e9 (basis .sphere 9 135 0)=Finsupp.single (0:Fin 6) 1 := by
  with_unfolding_all
    have hh : r5e9.symm (Finsupp.single (0:Fin 6) 1)=basis .sphere 9 135 0 := r5he9 0
    rw [←hh,LinearEquiv.apply_symm_apply]
private theorem r5ec9_1 : r5e9 (basis .sphere 9 135 1)=Finsupp.single (1:Fin 6) 1 := by
  with_unfolding_all
    have hh : r5e9.symm (Finsupp.single (1:Fin 6) 1)=basis .sphere 9 135 1 := r5he9 1
    rw [←hh,LinearEquiv.apply_symm_apply]
private theorem r5ec9_2 : r5e9 (basis .sphere 9 135 2)=Finsupp.single (2:Fin 6) 1 := by
  with_unfolding_all
    have hh : r5e9.symm (Finsupp.single (2:Fin 6) 1)=basis .sphere 9 135 2 := r5he9 2
    rw [←hh,LinearEquiv.apply_symm_apply]
private theorem r5ec9_3 : r5e9 (basis .sphere 9 135 3)=Finsupp.single (3:Fin 6) 1 := by
  with_unfolding_all
    have hh : r5e9.symm (Finsupp.single (3:Fin 6) 1)=basis .sphere 9 135 3 := r5he9 3
    rw [←hh,LinearEquiv.apply_symm_apply]
private theorem r5ec9_4 : r5e9 (basis .sphere 9 135 4)=Finsupp.single (4:Fin 6) 1 := by
  with_unfolding_all
    have hh : r5e9.symm (Finsupp.single (4:Fin 6) 1)=basis .sphere 9 135 4 := r5he9 4
    rw [←hh,LinearEquiv.apply_symm_apply]
private theorem r5ec9_5 : r5e9 (basis .sphere 9 135 5)=Finsupp.single (5:Fin 6) 1 := by
  with_unfolding_all
    have hh : r5e9.symm (Finsupp.single (5:Fin 6) 1)=basis .sphere 9 135 5 := r5he9 5
    rw [←hh,LinearEquiv.apply_symm_apply]

private theorem r5ImageCoord
    {A B : Type} [AddCommGroup A] [Module ℤ A] [AddCommGroup B] [Module ℤ B]
    {n m : ℕ} (e : A ≃ₗ[ℤ] (Fin n →₀ F2)) (f : B ≃ₗ[ℤ] (Fin m →₀ F2))
    (d : A →ₗ[ℤ] B) (x : A) (j : Fin m) :
    f (d x) j = ∑ i : Fin n, if e x i=0 then 0 else f (d (e.symm (Finsupp.single i 1))) j := by
  classical
  have hx := finite_basis_expansion e x
  calc
    f (d x) j = f (d (∑ i : Fin n, if e x i=0 then 0 else e.symm (Finsupp.single i 1))) j := by
      exact congrArg (fun a => f (d a) j) hx
    _ = _ := by
      rw [map_sum,map_sum,Finsupp.finsetSum_apply]
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hc : e x i=0
      · simp only [hc,ite_true,map_zero,Finsupp.zero_apply]
      · simp only [hc,ite_false]

private noncomputable def r5ElevenDelta : model.classical.sphere.Page 2 (11,137) ⟶ model.classical.sphere.Page 2 (13,138) :=
  model.classical.sphere.d 2 (11,137) ≫ eqToHom (congrArg (model.classical.sphere.Page 2) r5D288.target_degree)

private theorem r5ElevenValues (i : Fin 6) :
    r5ElevenDelta (basis .sphere 11 137 i.val) =
      ![basis .sphere 13 138 3,0,0,basis .sphere 13 138 4,0,0] i := by
  with_unfolding_all
    have hs2 : model.classical.sphere.r₀≤2 := by rw [model.classical.firstPage]
    have dz {x : model.classical.sphere.Page 2 (11,137)} {r : ℤ} (hr : 2<r)
        (hx : ReachesPage model.classical.sphere r (11,137) x) : r5ElevenDelta x=0 := by
      have h := represents_d_zero_of_later hs2 hr (represents_two_self x) hx
      change (eqToHom (congrArg (model.classical.sphere.Page 2) r5D288.target_degree)) (model.classical.sphere.d 2 (11,137) x)=0
      rw [h,map_zero]
    have d0 : r5ElevenDelta (basis .sphere 11 137 0)=basis .sphere 13 138 3 :=
      r5D288.eq_on_page_two.choose_spec
    have d3 : r5ElevenDelta (basis .sphere 11 137 3)=basis .sphere 13 138 4 :=
      r5D289.eq_on_page_two.choose_spec
    have d2 : r5ElevenDelta (basis .sphere 11 137 2)=0 := by
      obtain ⟨_,a,b,ha,hb,hd⟩ := r5D287
      exact dz (by decide) ⟨a,ha⟩
    have d12 : r5ElevenDelta (basis .sphere 11 137 1 + basis .sphere 11 137 2)=0 :=
      dz (by decide) r5D286
    have d1 : r5ElevenDelta (basis .sphere 11 137 1)=0 := by
      rw [map_add,d2,add_zero] at d12
      exact d12
    have d4 : r5ElevenDelta (basis .sphere 11 137 4)=0 := by
      obtain ⟨a,ha,hd⟩ := differential_target_cycle r5D284
      rw [←ha.eq_on_page_two] at hd
      change (eqToHom (congrArg (model.classical.sphere.Page 2) r5D288.target_degree)) (model.classical.sphere.d 2 (11,137) (basis .sphere 11 137 4))=0
      rw [hd,map_zero]
    have d5 : r5ElevenDelta (basis .sphere 11 137 5)=0 := by
      obtain ⟨a,ha,hd⟩ := differential_target_cycle r5D285
      rw [←ha.eq_on_page_two] at hd
      change (eqToHom (congrArg (model.classical.sphere.Page 2) r5D288.target_degree)) (model.classical.sphere.d 2 (11,137) (basis .sphere 11 137 5))=0
      rw [hd,map_zero]
    fin_cases i
    · exact d0
    · exact d1
    · exact d2
    · exact d3
    · exact d4
    · exact d5

private theorem r5Eleven_image_coord (x : model.classical.sphere.Page 2 (11,137)) (j : Fin 5)
    (hj : j=0 ∨ j=2) : r5e13 (r5ElevenDelta x) j=0 := by
  with_unfolding_all
    have cols (i : Fin 6) : r5e13 (r5ElevenDelta (r5e11.symm (Finsupp.single i 1))) j=0 := by
      rw [r5he11,r5ElevenValues]
      rcases hj with rfl|rfl <;> fin_cases i <;>
        simp [r5ec13_3,r5ec13_4]
    rw [r5ImageCoord r5e11 r5e13 r5ElevenDelta.hom x j]
    apply Finset.sum_eq_zero
    intro i hi
    by_cases hc : r5e11 x i=0
    · simp only [hc,ite_true]
    · simp only [hc,ite_false,cols]


private theorem r5TwelveNE {x : model.classical.sphere.Page 2 (12,137)}
    {a : model.classical.sphere.Page 3 (12,137)}
    (ha : RepresentsOnPage model.classical.sphere 3 (12,137) x a)
    (j : Fin 5) (hj : j=3 ∨ j=4) (hx : r5TenE12 x j≠0) : a≠0 := by
  with_unfolding_all
    have hs2 : model.classical.sphere.r₀≤2 := by rw [model.classical.firstPage]
    apply represents_next_nonzero_of_not_incoming_at r5TenD260.target_degree hs2 (by decide)
      ha (represents_two_self x)
    intro v hv
    have hh := congrArg (fun y => r5TenE12 y j) hv
    change r5TenE12 (r5TenDelta v) j=r5TenE12 x j at hh
    rw [r5Ten_image_coord v j hj] at hh
    exact hx hh.symm

private theorem r5TenThirdDegree :
    (10,136)+model.classical.sphere.diffDeg 3=(13,138) := by
  simp only [ClassicalAdamsFamily.sphere,ClassicalAdamsFamily.obj,
    model.classical.differentialDegree,Prod.mk_add_mk,Int.reduceAdd,Int.reduceSub]

private theorem r5ThirteenNE {x : model.classical.sphere.Page 2 (13,138)}
    {a : model.classical.sphere.Page 4 (13,138)}
    (ha : RepresentsOnPage model.classical.sphere 4 (13,138) x a)
    (j : Fin 5) (hj : j=0 ∨ j=2) (hx : r5e13 x j≠0) : a≠0 := by
  with_unfolding_all
    have hs2 : model.classical.sphere.r₀≤2 := by rw [model.classical.firstPage]
    obtain ⟨b,hb⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤4) ha
    have bne : b≠0 := by
      apply represents_next_nonzero_of_not_incoming_at r5D288.target_degree hs2 (by decide)
        hb (represents_two_self x)
      intro v hv
      have hh := congrArg (fun y => r5e13 y j) hv
      change r5e13 (r5ElevenDelta v) j=r5e13 x j at hh
      rw [r5Eleven_image_coord v j hj] at hh
      exact hx hh.symm
    exact represents_next_nonzero_of_incoming_zero_at (hs2.trans (by decide : (2:ℤ)≤3))
      (by decide) (r5_ten_zero 3 (by decide) (by decide)) ha hb bne r5TenThirdDegree

private theorem tIncoming_r5_zero :
    ∀ z : model.classical.sphere.Page 5 (9,135), z=0 := by
  with_unfolding_all
    classical
    let E := model.classical.sphere
    have hs2 : E.r₀≤2 := by rw [model.classical.firstPage]
    obtain ⟨deg3,a0,t34,ha0,ht34,hd0⟩ := r5D233
    obtain ⟨_,a3,t3,ha3,ht3,hd3⟩ := r5D234
    obtain ⟨deg4,a1,s2,ha1,hs2rep,hd1⟩ := r5D232
    obtain ⟨_,a2,s0,ha2,hs0rep,hd2⟩ := r5D231
    obtain ⟨a1three,ha1three⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤4) ha1
    obtain ⟨a2three,ha2three⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤4) ha2
    have b4zero (r : ℤ) (hr : 3≤r) : RepresentsOnPage E r (9,135) (basis .sphere 9 135 4) 0 :=
      differential_target_later_zero hs2 (by omega) r5D229
    have b5zero (r : ℤ) (hr : 3≤r) : RepresentsOnPage E r (9,135) (basis .sphere 9 135 5) 0 :=
      differential_target_later_zero hs2 (by omega) r5D230
    let δ3 : E.Page 3 (9,135) ⟶ E.Page 3 (12,137) :=
      E.d 3 (9,135) ≫ eqToHom (congrArg (E.Page 3) deg3)
    have d0 : δ3 a0=t34 := hd0
    have d3 : δ3 a3=t3 := hd3
    have d1 : δ3 a1three=0 := by
      have h := represents_d_zero_of_later (hs2.trans (by decide : (2:ℤ)≤3))
        (by decide : (3:ℤ)<4) ha1three ⟨a1,ha1⟩
      change (eqToHom (congrArg (E.Page 3) deg3)) (E.d 3 (9,135) a1three)=0
      rw [h,map_zero]
    have d2 : δ3 a2three=0 := by
      have h := represents_d_zero_of_later (hs2.trans (by decide : (2:ℤ)≤3))
        (by decide : (3:ℤ)<4) ha2three ⟨a2,ha2⟩
      change (eqToHom (congrArg (E.Page 3) deg3)) (E.d 3 (9,135) a2three)=0
      rw [h,map_zero]
    have ec123 : r5TenE12 (basis .sphere 12 137 3)=Finsupp.single (3:Fin 5) 1 := by
      have hh : r5TenE12.symm (Finsupp.single (3:Fin 5) 1)=basis .sphere 12 137 3 := r5TenE12_basis 3
      rw [←hh,LinearEquiv.apply_symm_apply]
    have ec124 : r5TenE12 (basis .sphere 12 137 4)=Finsupp.single (4:Fin 5) 1 := by
      have hh : r5TenE12.symm (Finsupp.single (4:Fin 5) 1)=basis .sphere 12 137 4 := r5TenE12_basis 4
      rw [←hh,LinearEquiv.apply_symm_apply]
    have n34 : t34≠0 := r5TwelveNE ht34 4 (Or.inr rfl) (by
      rw [map_add,Finsupp.add_apply,ec123,ec124]
      norm_num [Finsupp.single_apply,Fin.ext_iff])
    have n3 : t3≠0 := r5TwelveNE ht3 3 (Or.inl rfl) (by
      rw [ec123,Finsupp.single_eq_same]; exact one_ne_zero)
    have n343 : t34+t3≠0 := r5TwelveNE (represents_add_tail ht34 ht3) 4 (Or.inr rfl) (by
      rw [map_add,Finsupp.add_apply,map_add,Finsupp.add_apply,ec123,ec124]
      norm_num [Finsupp.single_apply,Fin.ext_iff])
    have ns2 : s2≠0 := r5ThirteenNE hs2rep 2 (Or.inr rfl) (by
      rw [r5ec13_2,Finsupp.single_eq_same]; exact one_ne_zero)
    have ns0 : s0≠0 := r5ThirteenNE hs0rep 0 (Or.inl rfl) (by
      rw [r5ec13_0,Finsupp.single_eq_same]; exact one_ne_zero)
    have ns20 : s2+s0≠0 := r5ThirteenNE (represents_add_tail hs2rep hs0rep) 2 (Or.inr rfl) (by
      rw [map_add,Finsupp.add_apply,r5ec13_2,r5ec13_0]
      norm_num [Finsupp.single_apply,Fin.ext_iff])
    intro z
    obtain ⟨x,hx5⟩ := page_has_initial_representative (by decide : (2:ℤ)≤5) z
    have hex := finite_basis_expansion r5e9 x
    simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,r5he9,add_zero] at hex
    change x=(if r5e9 x 0=0 then 0 else basis .sphere 9 135 0)+
      ((if r5e9 x 1=0 then 0 else basis .sphere 9 135 1)+
      ((if r5e9 x 2=0 then 0 else basis .sphere 9 135 2)+
      ((if r5e9 x 3=0 then 0 else basis .sphere 9 135 3)+
      ((if r5e9 x 4=0 then 0 else basis .sphere 9 135 4)+
        (if r5e9 x 5=0 then 0 else basis .sphere 9 135 5))))) at hex
    have hx3 := represents_add_tail (represents_bit (r5e9 x 0) ha0)
      (represents_add_tail (represents_bit (r5e9 x 1) ha1three)
      (represents_add_tail (represents_bit (r5e9 x 2) ha2three)
      (represents_add_tail (represents_bit (r5e9 x 3) ha3)
      (represents_add_tail (represents_bit (r5e9 x 4) (b4zero 3 (by decide)))
        (represents_bit (r5e9 x 5) (b5zero 3 (by decide)))))))
    rw [←hex] at hx3
    have hz3 := represents_d_zero_of_later (hs2.trans (by decide : (2:ℤ)≤3))
      (by decide : (3:ℤ)<5) hx3 ⟨z,hx5⟩
    have hz3' : δ3 ((if r5e9 x 0=0 then 0 else a0)+
      ((if r5e9 x 1=0 then 0 else a1three)+
      ((if r5e9 x 2=0 then 0 else a2three)+
      ((if r5e9 x 3=0 then 0 else a3)+
      ((if r5e9 x 4=0 then 0 else 0)+(if r5e9 x 5=0 then 0 else 0))))))=0 := by
      exact (congrArg (fun w => (eqToHom (congrArg (E.Page 3) deg3)) w) hz3).trans (map_zero _)
    have h03 : r5e9 x 0=0 ∧ r5e9 x 3=0 := by
      by_cases h0 : r5e9 x 0=0 <;> by_cases h3 : r5e9 x 3=0
      · exact ⟨h0,h3⟩
      · have hh : t3=0 := by
          simpa only [h0,h3,ite_true,ite_false,ite_self,apply_ite,map_add,map_zero,d0,d1,d2,d3,add_zero,zero_add] using hz3'
        exact (n3 hh).elim
      · have hh : t34=0 := by
          simpa only [h0,h3,ite_true,ite_false,ite_self,apply_ite,map_add,map_zero,d0,d1,d2,d3,add_zero,zero_add] using hz3'
        exact (n34 hh).elim
      · have hh : t34+t3=0 := by
          simpa only [h0,h3,ite_true,ite_false,ite_self,apply_ite,map_add,map_zero,d0,d1,d2,d3,add_zero,zero_add] using hz3'
        exact (n343 hh).elim
    have h0 := h03.1
    have h3 := h03.2
    simp only [h0,h3,ite_true,zero_add] at hex
    have hx4 := represents_add_tail (represents_bit (r5e9 x 1) ha1)
      (represents_add_tail (represents_bit (r5e9 x 2) ha2)
      (represents_add_tail (represents_bit (r5e9 x 4) (b4zero 4 (by decide)))
        (represents_bit (r5e9 x 5) (b5zero 4 (by decide)))))
    rw [←hex] at hx4
    have hz4 := represents_d_zero_of_later (hs2.trans (by decide : (2:ℤ)≤4))
      (by decide : (4:ℤ)<5) hx4 ⟨z,hx5⟩
    let δ4 : E.Page 4 (9,135) ⟶ E.Page 4 (13,138) :=
      E.d 4 (9,135) ≫ eqToHom (congrArg (E.Page 4) deg4)
    have d41 : δ4 a1=s2 := hd1
    have d42 : δ4 a2=s0 := hd2
    have hz4' : δ4 ((if r5e9 x 1=0 then 0 else a1)+
      ((if r5e9 x 2=0 then 0 else a2)+
      ((if r5e9 x 4=0 then 0 else 0)+(if r5e9 x 5=0 then 0 else 0))))=0 := by
      exact (congrArg (fun w => (eqToHom (congrArg (E.Page 4) deg4)) w) hz4).trans (map_zero _)
    have h12 : r5e9 x 1=0 ∧ r5e9 x 2=0 := by
      by_cases h1 : r5e9 x 1=0 <;> by_cases h2 : r5e9 x 2=0
      · exact ⟨h1,h2⟩
      · have hh : s0=0 := by
          simpa only [h1,h2,ite_true,ite_false,ite_self,apply_ite,map_add,map_zero,d41,d42,add_zero,zero_add] using hz4'
        exact (ns0 hh).elim
      · have hh : s2=0 := by
          simpa only [h1,h2,ite_true,ite_false,ite_self,apply_ite,map_add,map_zero,d41,d42,add_zero,zero_add] using hz4'
        exact (ns2 hh).elim
      · have hh : s2+s0=0 := by
          simpa only [h1,h2,ite_true,ite_false,ite_self,apply_ite,map_add,map_zero,d41,d42,add_zero,zero_add] using hz4'
        exact (ns20 hh).elim
    simp only [h12.1,h12.2,ite_true,zero_add] at hex
    have hxzero := represents_add_tail (represents_bit (r5e9 x 4) (b4zero 5 (by decide)))
      (represents_bit (r5e9 x 5) (b5zero 5 (by decide)))
    rw [←hex] at hxzero
    have hz := represents_unique hx5 hxzero
    simpa only [ite_self,zero_add] using hz


private theorem tIn_third_map_zero : model.classical.sphere.d 3 (11,137)=0 := by
  with_unfolding_all
    apply d_zero_of_second_kernel_extends tIn_start (by decide : (3:ℤ)≤3)
    intro x hdx
    let E := model.classical.sphere
    let δ := r5ElevenDelta
    have hδ : δ x=0 := by
      change (E.d 2 (11,137) ≫ _) x=0
      rw [ModuleCat.comp_apply,hdx,map_zero]
    have d0 := r5ElevenValues 0
    have d1 := r5ElevenValues 1
    have d2 := r5ElevenValues 2
    have d3 := r5ElevenValues 3
    have d4 := r5ElevenValues 4
    have d5 := r5ElevenValues 5
    change δ (basis .sphere 11 137 0)=basis .sphere 13 138 3 at d0
    change δ (basis .sphere 11 137 1)=0 at d1
    change δ (basis .sphere 11 137 2)=0 at d2
    change δ (basis .sphere 11 137 3)=basis .sphere 13 138 4 at d3
    change δ (basis .sphere 11 137 4)=0 at d4
    change δ (basis .sphere 11 137 5)=0 at d5
    have bit (b : F2) (a : E.Page 2 (11,137)) :
        δ (if b=0 then 0 else a)=if b=0 then 0 else δ a := by
      by_cases hb : b=0 <;> simp only [hb,ite_true,ite_false,map_zero]
    have hx := finite_basis_expansion r5e11 x
    simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,r5he11,add_zero] at hx
    change x=(if r5e11 x 0=0 then 0 else basis .sphere 11 137 0)+
      ((if r5e11 x 1=0 then 0 else basis .sphere 11 137 1)+
      ((if r5e11 x 2=0 then 0 else basis .sphere 11 137 2)+
      ((if r5e11 x 3=0 then 0 else basis .sphere 11 137 3)+
      ((if r5e11 x 4=0 then 0 else basis .sphere 11 137 4)+
       (if r5e11 x 5=0 then 0 else basis .sphere 11 137 5))))) at hx
    have dh := congrArg δ hx
    simp only [map_add,bit,d0,d1,d2,d3,d4,d5,ite_self,add_zero,zero_add,hδ] at dh
    have c0 : r5e11 x 0=0 := by
      by_contra hc0
      have hh := congrArg (fun y=>r5e13 y 3) dh
      by_cases hc3 : r5e11 x 3=0 <;>
        simp only [hc0,hc3,ite_false,ite_true,map_zero,map_add,Finsupp.zero_apply,
          Finsupp.add_apply,r5ec13_3,r5ec13_4] at hh <;>
        norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    have c3 : r5e11 x 3=0 := by
      by_contra hc3
      have hh := congrArg (fun y=>r5e13 y 4) dh
      simp only [c0,hc3,ite_false,ite_true,map_zero,map_add,Finsupp.zero_apply,
        Finsupp.add_apply,r5ec13_4] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    obtain ⟨a12,ha12⟩ := reaches_before (by decide : (2:ℤ)≤4)
      (by decide : (4:ℤ)≤1000) r5D286
    obtain ⟨_,a2,_,ha2,_,_⟩ := r5D287
    have ha1 : RepresentsOnPage E 4 (11,137) (basis .sphere 11 137 1) (a12-a2) := by
      simpa only [add_sub_cancel_right] using represents_sub ha12 ha2
    have hb4 : RepresentsOnPage E 4 (11,137) (basis .sphere 11 137 4) 0 :=
      differential_target_later_zero tIn_start (by decide : (2:ℤ)<4) r5D284
    have hb5 : RepresentsOnPage E 4 (11,137) (basis .sphere 11 137 5) 0 :=
      differential_target_later_zero tIn_start (by decide : (2:ℤ)<4) r5D285
    have hxsmall : x=(if r5e11 x 1=0 then 0 else basis .sphere 11 137 1)+
      ((if r5e11 x 2=0 then 0 else basis .sphere 11 137 2)+
      ((if r5e11 x 4=0 then 0 else basis .sphere 11 137 4)+
       (if r5e11 x 5=0 then 0 else basis .sphere 11 137 5))) := by
      simpa only [c0,c3,ite_true,zero_add] using hx
    have hrep := represents_add_tail (represents_bit (r5e11 x 1) ha1)
      (represents_add_tail (represents_bit (r5e11 x 2) ha2)
      (represents_add_tail (represents_bit (r5e11 x 4) hb4) (represents_bit (r5e11 x 5) hb5)))
    rw [←hxsmall] at hrep
    exact ⟨_,hrep⟩

private theorem tIncoming_r6_labels_equal
    {E : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ×ℤ)}
    (hs : E.r₀≤2) {p q : ℤ×ℤ} (hdeg : p+E.diffDeg 2=q) (hin : E.d 2 p=0)
    {x y : E.Page 2 q} {a : E.Page 3 q}
    (hx : RepresentsOnPage E 3 q x a) (hy : RepresentsOnPage E 3 q y a) : x=y := by
  by_contra hxy
  have hn : x-y≠0 := sub_ne_zero.mpr hxy
  have hr : RepresentsOnPage E 3 q (x-y) 0 := by
    simpa only [sub_self] using represents_sub hx hy
  have hzero : (0 : E.Page 3 q)≠0 :=
    represents_next_nonzero_of_incoming_zero_at hs (by decide) hin hr
      (represents_two_self _) hn hdeg
  exact hzero rfl

private theorem tIncoming_r6_frame :
    ∃ w b : model.classical.sphere.Page 6 (8,134),
      RepresentsOnPage model.classical.sphere 6 (8,134) W w ∧
      RepresentsOnPage model.classical.sphere 6 (8,134) (basis .sphere 8 134 4) b ∧
      model.classical.sphere.d 6 (8,134) b=0 ∧
      ∀ z : model.classical.sphere.Page 6 (8,134), z=0 ∨ z=w ∨ z=b ∨ z=w+b := by
  classical
  let E := model.classical.sphere
  have hs2 : E.r₀≤2 := by
    change model.classical.sphere.r₀≤2
    rw [model.classical.firstPage]
  have hs3 : E.r₀≤3 := hs2.trans (by decide)
  have hs4 : E.r₀≤4 := hs2.trans (by decide)
  have h190 : HasDifferential E 2 (7,134) (9,135)
      (basis .sphere 7 134 1) (basis .sphere 9 135 4) := by
    have hrow := result ⟨.sphere, .equation, 2, 7, 134, [1], 9, 135, [4], "S0_AdamsE2_ss", 2709⟩ (by
      exact List.mem_of_getElem? (i := 190) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 2 (7,134) (9,135) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 7 134 [1]=true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 9 135 [4]=true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    exact h
  have h191 : HasDifferential E 2 (7,134) (9,135)
      (basis .sphere 7 134 4) (basis .sphere 9 135 5) := by
    have hrow := result ⟨.sphere, .equation, 2, 7, 134, [4], 9, 135, [5], "S0_AdamsE2_ss", 2710⟩ (by
      exact List.mem_of_getElem? (i := 191) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 2 (7,134) (9,135) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 7 134 [4]=true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 9 135 [5]=true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    exact h
  have h231 : HasDifferential E 4 (9,135) (13,138)
      (basis .sphere 9 135 2) (basis .sphere 13 138 0) := by
    have hrow := result ⟨.sphere, .equation, 4, 9, 135, [2], 13, 138, [0], "S0_AdamsE2_ss", 2790⟩ (by
      exact List.mem_of_getElem? (i := 231) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 4 (9,135) (13,138) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 9 135 [2]=true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 13 138 [0]=true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    exact h
  have h232 : HasDifferential E 4 (9,135) (13,138)
      (basis .sphere 9 135 1) (basis .sphere 13 138 2) := by
    have hrow := result ⟨.sphere, .equation, 4, 9, 135, [1], 13, 138, [2], "S0_AdamsE2_ss", 2791⟩ (by
      exact List.mem_of_getElem? (i := 232) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 4 (9,135) (13,138) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 9 135 [1]=true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 13 138 [2]=true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    exact h
  have h233 : HasDifferential E 3 (9,135) (12,137)
      (basis .sphere 9 135 0) (basis .sphere 12 137 3 + basis .sphere 12 137 4) := by
    have hrow := result ⟨.sphere, .equation, 3, 9, 135, [0], 12, 137, [3, 4], "S0_AdamsE2_ss", 2792⟩ (by
      exact List.mem_of_getElem? (i := 233) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 3 (9,135) (12,137) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 9 135 [0]=true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 12 137 [3, 4]=true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    exact h
  have h234 : HasDifferential E 3 (9,135) (12,137)
      (basis .sphere 9 135 3) (basis .sphere 12 137 3) := by
    have hrow := result ⟨.sphere, .equation, 3, 9, 135, [3], 12, 137, [3], "S0_AdamsE2_ss", 2793⟩ (by
      exact List.mem_of_getElem? (i := 234) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 3 (9,135) (12,137) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 9 135 [3]=true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 12 137 [3]=true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    exact h
  have h176 : HasDifferential E 2 (6,133) (8,134)
      (basis .sphere 6 133 1) (basis .sphere 8 134 5) := by
    have hrow := result ⟨.sphere, .equation, 2, 6, 133, [1], 8, 134, [5], "S0_AdamsE2_ss", 2634⟩ (by
      exact List.mem_of_getElem? (i := 176) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 2 (6,133) (8,134) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 6 133 [1]=true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 8 134 [5]=true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    exact h
  have h203 : ReachesPage E 17 (8,134) (basis .sphere 8 134 4) := by
    have hrow := result ⟨.sphere, .reaches, 17, 8, 134, [4], 8, 134, [], "S0_AdamsE2_ss", 2701⟩ (by
      exact List.mem_of_getElem? (i := 203) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,h⟩ := hrow
    have vx : Raw.coordinatesValid Raw.degrees .sphere 8 134 [4]=true := rfl
    simp only [decode,vx,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      add_zero,Option.some.injEq] at ha
    rw [←ha] at h
    exact h
  have h204 : ReachesPage E 6 (8,134) (basis .sphere 8 134 0 + basis .sphere 8 134 3) := by
    have hrow := result ⟨.sphere, .reaches, 6, 8, 134, [0, 3], 8, 134, [], "S0_AdamsE2_ss", 2702⟩ (by
      exact List.mem_of_getElem? (i := 204) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,h⟩ := hrow
    have vx : Raw.coordinatesValid Raw.degrees .sphere 8 134 [0, 3]=true := rfl
    simp only [decode,vx,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      add_zero,Option.some.injEq] at ha
    rw [←ha] at h
    exact h
  have h205 : HasDifferential E 3 (8,134) (11,136)
      (basis .sphere 8 134 3) (basis .sphere 11 136 1) := by
    have hrow := result ⟨.sphere, .equation, 3, 8, 134, [3], 11, 136, [1], "S0_AdamsE2_ss", 2703⟩ (by
      exact List.mem_of_getElem? (i := 205) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 3 (8,134) (11,136) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 8 134 [3]=true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 11 136 [1]=true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    exact h
  have h206 : HasDifferential E 3 (8,134) (11,136)
      (basis .sphere 8 134 2) (basis .sphere 11 136 2) := by
    have hrow := result ⟨.sphere, .equation, 3, 8, 134, [2], 11, 136, [2], "S0_AdamsE2_ss", 2704⟩ (by
      exact List.mem_of_getElem? (i := 206) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 3 (8,134) (11,136) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 8 134 [2]=true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 11 136 [2]=true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    exact h
  have h207 : HasDifferential E 2 (8,134) (10,135)
      (basis .sphere 8 134 1) (basis .sphere 10 135 3) := by
    have hrow := result ⟨.sphere, .equation, 2, 8, 134, [1], 10, 135, [3], "S0_AdamsE2_ss", 2705⟩ (by
      exact List.mem_of_getElem? (i := 207) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 2 (8,134) (10,135) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 8 134 [1]=true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 10 135 [3]=true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    exact h
  obtain ⟨e2,he2⟩ := basis_correct ⟨.sphere, 9, 135, ["414,1", "1,1,376,1", "1,1,375,1", "0,1,394,1", "0,1,392,1", "0,7,69,2"]⟩ (by
    exact List.mem_of_getElem? (i := 174) (by rfl))
  change E.Page 2 (9,135) ≃ₗ[ℤ] (Fin 6 →₀ F2) at e2
  change ∀ i : Fin 6, e2.symm (Finsupp.single i 1)=basis .sphere 9 135 i.val at he2
  obtain ⟨e,he⟩ := basis_correct ⟨.sphere, 8, 134, ["395,1", "394,1", "393,1", "392,1", "69,1,85,1", "0,6,69,2"]⟩ (by
    exact List.mem_of_getElem? (i := 162) (by rfl))
  change E.Page 2 (8,134) ≃ₗ[ℤ] (Fin 6 →₀ F2) at e
  change ∀ i : Fin 6, e.symm (Finsupp.single i 1)=basis .sphere 8 134 i.val at he
  obtain ⟨g,hg⟩ := basis_correct ⟨.sphere, 11, 136, ["69,1,89,1", "1,1,389,1", "1,1,388,1", "0,2,391,1", "0,3,375,1"]⟩ (by
    exact List.mem_of_getElem? (i := 192) (by rfl))
  change E.Page 2 (11,136) ≃ₗ[ℤ] (Fin 5 →₀ F2) at g
  change ∀ i : Fin 5, g.symm (Finsupp.single i 1)=basis .sphere 11 136 i.val at hg
  obtain ⟨f,hf⟩ := basis_correct ⟨.sphere, 10, 135, ["413,1", "412,1", "0,1,391,1", "0,1,390,1", "0,2,375,1"]⟩ (by
    exact List.mem_of_getElem? (i := 182) (by rfl))
  change E.Page 2 (10,135) ≃ₗ[ℤ] (Fin 5 →₀ F2) at f
  change ∀ i : Fin 5, f.symm (Finsupp.single i 1)=basis .sphere 10 135 i.val at hf
  have hin2 : E.d 2 (9,135)=0 := by
    obtain ⟨_,a0,_,ha0,_,_⟩ := h233
    obtain ⟨_,a14,_,ha14,_,_⟩ := h232
    obtain ⟨a1,ha1⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤4) ha14
    obtain ⟨_,a24,_,ha24,_,_⟩ := h231
    obtain ⟨a2,ha2⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤4) ha24
    obtain ⟨_,a3,_,ha3,_,_⟩ := h234
    have ha4 : RepresentsOnPage E 3 (9,135) (basis .sphere 9 135 4) 0 :=
      differential_target_later_zero hs2 (by decide) h190
    have ha5 : RepresentsOnPage E 3 (9,135) (basis .sphere 9 135 5) 0 :=
      differential_target_later_zero hs2 (by decide) h191
    have before3 (x : E.Page 2 (9,135)) (hx : ReachesPage E 3 (9,135) x) :
        E.d 2 (9,135) x=0 :=
      represents_d_zero_of_later hs2 (by decide) (represents_two_self _) hx
    apply d_zero_of_complete_representatives (by decide : (2:ℤ)≤2) e2
    intro i
    refine ⟨e2.symm (Finsupp.single i 1),represents_two_self _,?_⟩
    rw [he2 i]
    fin_cases i
    · exact before3 _ ⟨a0,ha0⟩
    · exact before3 _ ⟨a1,ha1⟩
    · exact before3 _ ⟨a2,ha2⟩
    · exact before3 _ ⟨a3,ha3⟩
    · exact before3 _ ⟨0,ha4⟩
    · exact before3 _ ⟨0,ha5⟩
  have deg2 : (9,135)+E.diffDeg 2=(11,136) := by
    simp only [E,Classical.Adams.ClassicalAdamsFamily.sphere,Classical.Adams.ClassicalAdamsFamily.obj,
      model.classical.differentialDegree,Prod.mk_add_mk,Int.reduceAdd,Int.reduceSub]
  obtain ⟨deg3,a3,t1,ha3,ht1,hd3⟩ := h205
  obtain ⟨_,a2,t2,ha2,ht2,hd2⟩ := h206
  obtain ⟨aW6,haW6⟩ := h204
  obtain ⟨aW3,haW3⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤6) haW6
  let a0 := aW3-a3
  have ha0 : RepresentsOnPage E 3 (8,134) (basis .sphere 8 134 0) a0 := by
    simpa only [add_sub_cancel_right] using represents_sub haW3 ha3
  obtain ⟨a417,ha417⟩ := h203
  obtain ⟨a4,ha4⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤17) ha417
  have ha5 : RepresentsOnPage E 3 (8,134) (basis .sphere 8 134 5) 0 :=
    differential_target_later_zero hs2 (by decide) h176
  let δ2 : E.Page 2 (8,134) ⟶ E.Page 2 (10,135) :=
    E.d 2 (8,134) ≫ eqToHom (congrArg (E.Page 2) h207.target_degree)
  have before3 (x : E.Page 2 (8,134)) (hx : ReachesPage E 3 (8,134) x) : δ2 x=0 := by
    have hd := represents_d_zero_of_later hs2 (by decide) (represents_two_self _) hx
    change (E.d 2 (8,134) ≫ _) x=0
    rw [ModuleCat.comp_apply,hd,map_zero]
  have d20 : δ2 (basis .sphere 8 134 0)=0 := before3 _ ⟨a0,ha0⟩
  have d21 : δ2 (basis .sphere 8 134 1)=basis .sphere 10 135 3 := h207.eq_on_page_two.2
  have d22 : δ2 (basis .sphere 8 134 2)=0 := before3 _ ⟨a2,ha2⟩
  have d23 : δ2 (basis .sphere 8 134 3)=0 := before3 _ ⟨a3,ha3⟩
  have d24 : δ2 (basis .sphere 8 134 4)=0 := before3 _ ⟨a4,ha4⟩
  have d25 : δ2 (basis .sphere 8 134 5)=0 := before3 _ ⟨0,ha5⟩
  have d2target_ne : basis .sphere 10 135 3≠0 := by
    have hf3 : f.symm (Finsupp.single (3 : Fin 5) 1)=basis .sphere 10 135 3 := hf 3
    rw [←hf3]
    exact basis_vector_ne_zero f 3
  have δ2bit (c : F2) (a : E.Page 2 (8,134)) :
      δ2 (if c=0 then 0 else a)=if c=0 then 0 else δ2 a := by
    by_cases hc : c=0 <;> simp only [hc,ite_true,ite_false,map_zero]
  let δ3 : E.Page 3 (8,134) ⟶ E.Page 3 (11,136) :=
    E.d 3 (8,134) ≫ eqToHom (congrArg (E.Page 3) deg3)
  have d3 : δ3 a3=t1 := hd3
  have d2 : δ3 a2=t2 := hd2
  have dW : δ3 aW3=0 := by
    have hd := represents_d_zero_of_later hs3 (by decide : (3:ℤ)<6) haW3 ⟨aW6,haW6⟩
    change (E.d 3 (8,134) ≫ _) aW3=0
    rw [ModuleCat.comp_apply,hd,map_zero]
  have d0 : δ3 a0= -t1 := by
    change δ3 (aW3-a3)= -t1
    rw [map_sub,dW,d3,zero_sub]
  have d4 : δ3 a4=0 := by
    have hd := represents_d_zero_of_later hs3 (by decide : (3:ℤ)<17) ha4 ⟨a417,ha417⟩
    change (E.d 3 (8,134) ≫ _) a4=0
    rw [ModuleCat.comp_apply,hd,map_zero]
  have δ3bit (c : F2) (a : E.Page 3 (8,134)) :
      δ3 (if c=0 then 0 else a)=if c=0 then 0 else δ3 a := by
    by_cases hc : c=0 <;> simp only [hc,ite_true,ite_false,map_zero]
  obtain ⟨b6,hb6⟩ := represents_before (by decide : (2:ℤ)≤6) (by decide : (6:ℤ)≤17) ha417
  have db6 : E.d 6 (8,134) b6=0 :=
    represents_d_zero_of_later (hs2.trans (by decide)) (by decide : (6:ℤ)<17)
      hb6 ⟨a417,ha417⟩
  have Wb : W=basis .sphere 8 134 0+basis .sphere 8 134 3 := by
    have v0 := basis_value ⟨.named .x_126_8_4,0⟩ (by decide)
    have v3 := basis_value ⟨.named .x_126_8,3⟩ (by decide)
    change basis .sphere 8 134 0=atom .x_126_8_4 at v0
    change basis .sphere 8 134 3=atom .x_126_8 at v3
    dsimp only [W]
    rw [←v0,←v3]
  have hw6 : RepresentsOnPage E 6 (8,134) W aW6 := by rw [Wb]; exact haW6
  refine ⟨aW6,b6,hw6,hb6,db6,?_⟩
  intro z6
  obtain ⟨x,hxz6⟩ := page_has_initial_representative (by decide : (2:ℤ)≤6) z6
  obtain ⟨z3,hxz3⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤6) hxz6
  have hx := finite_basis_expansion e x
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,he,add_zero] at hx
  change x=(if e x 0=0 then 0 else basis .sphere 8 134 0)+
    ((if e x 1=0 then 0 else basis .sphere 8 134 1)+
    ((if e x 2=0 then 0 else basis .sphere 8 134 2)+
    ((if e x 3=0 then 0 else basis .sphere 8 134 3)+
    ((if e x 4=0 then 0 else basis .sphere 8 134 4)+
     (if e x 5=0 then 0 else basis .sphere 8 134 5))))) at hx
  have dx : δ2 x=0 := before3 _ ⟨z3,hxz3⟩
  have hdx := congrArg δ2 hx
  simp only [map_add,δ2bit,d20,d21,d22,d23,d24,d25,ite_self,zero_add,add_zero] at hdx
  have c1 : e x 1=0 := by
    by_contra hh
    apply d2target_ne
    simpa only [hh,ite_false] using hdx.symm.trans dx
  let zform := (if e x 0=0 then 0 else a0)+
    ((if e x 2=0 then 0 else a2)+((if e x 3=0 then 0 else a3)+
     (if e x 4=0 then 0 else a4)))
  have rsum := represents_add_tail (represents_bit (e x 0) ha0)
    (represents_add_tail (represents_bit (e x 2) ha2)
      (represents_add_tail (represents_bit (e x 3) ha3)
        (represents_add_tail (represents_bit (e x 4) ha4) (represents_bit (e x 5) ha5))))
  have xx : x=(if e x 0=0 then 0 else basis .sphere 8 134 0)+
    ((if e x 2=0 then 0 else basis .sphere 8 134 2)+
    ((if e x 3=0 then 0 else basis .sphere 8 134 3)+
    ((if e x 4=0 then 0 else basis .sphere 8 134 4)+
     (if e x 5=0 then 0 else basis .sphere 8 134 5)))) := by
    simpa only [c1,ite_true,zero_add] using hx
  have rx : RepresentsOnPage E 3 (8,134) x zform := by
    simp only [ite_self,add_zero] at rsum
    rw [←xx] at rsum
    exact rsum
  have z_eq : z3=zform := represents_unique hxz3 rx
  let im2 := (if e x 0=0 then 0 else -basis .sphere 11 136 1)+
    ((if e x 2=0 then 0 else basis .sphere 11 136 2)+
     (if e x 3=0 then 0 else basis .sphere 11 136 1))
  let im3 := (if e x 0=0 then 0 else -t1)+
    ((if e x 2=0 then 0 else t2)+(if e x 3=0 then 0 else t1))
  have hform : δ3 z3=im3 := by
    rw [z_eq]
    change δ3 ((if e x 0=0 then 0 else a0)+
      ((if e x 2=0 then 0 else a2)+((if e x 3=0 then 0 else a3)+
       (if e x 4=0 then 0 else a4))))=im3
    simp only [map_add,δ3bit,d0,d2,d3,d4,ite_self,add_zero]
    rfl
  have htneg : RepresentsOnPage E 3 (11,136) (-basis .sphere 11 136 1) (-t1) := by
    simpa only [zero_sub] using represents_sub
      (RepresentsOnPage.zero (E:=E) (p:=(11,136)) (by decide : (2:ℤ)≤3)) ht1
  have rim : RepresentsOnPage E 3 (11,136) im2 im3 :=
    represents_add_tail (represents_bit (e x 0) htneg)
      (represents_add_tail (represents_bit (e x 2) ht2) (represents_bit (e x 3) ht1))
  have dz3 : δ3 z3=0 := by
    have hd := represents_d_zero_of_later hs3 (by decide : (3:ℤ)<6) hxz3 ⟨z6,hxz6⟩
    change (E.d 3 (8,134) ≫ _) z3=0
    rw [ModuleCat.comp_apply,hd,map_zero]
  have im3zero : im3=0 := hform.symm.trans dz3
  rw [im3zero] at rim
  have im2zero : im2=0 := tIncoming_r6_labels_equal hs2 deg2 hin2 rim
    (RepresentsOnPage.zero (by decide : (2:ℤ)≤3))
  have gb (i : Fin 5) : g (basis .sphere 11 136 i.val)=Finsupp.single i 1 := by
    rw [←hg i,LinearEquiv.apply_symm_apply]
  have gb1 : g (basis .sphere 11 136 1)=Finsupp.single (1:Fin 5) 1 := gb 1
  have gb2 : g (basis .sphere 11 136 2)=Finsupp.single (2:Fin 5) 1 := gb 2
  have gbit (c : F2) (a : E.Page 2 (11,136)) (i : Fin 5) :
      g (if c=0 then 0 else a) i=if c=0 then 0 else g a i := by
    by_cases hc : c=0 <;> simp only [hc,ite_true,ite_false,map_zero,Finsupp.zero_apply]
  have coord2 := congrArg (fun a=>g a 2) im2zero
  have coord1 := congrArg (fun a=>g a 1) im2zero
  dsimp only [im2] at coord1 coord2
  simp only [map_add,Finsupp.add_apply,gbit,map_neg,gb1,gb2,
    Finsupp.neg_apply] at coord1 coord2
  norm_num [Finsupp.single_apply,Fin.ext_iff] at coord1 coord2
  have c2 : e x 2=0 := by
    by_contra hh
    simp only [hh] at coord2
  have c03 : e x 0=0 ↔ e x 3=0 := by
    by_cases h0 : e x 0=0 <;> by_cases h3 : e x 3=0
    · exact ⟨fun _=>h3,fun _=>h0⟩
    · have hh := coord1
      simp only [h0,h3,ite_true,ite_false,zero_add,one_ne_zero] at hh
    · have hh := coord1
      simp only [h0,h3,ite_true,ite_false,add_zero,one_ne_zero] at hh
    · exact ⟨fun hh=>(h0 hh).elim,fun hh=>(h3 hh).elim⟩
  have xxx : x=(if e x 0=0 then 0 else basis .sphere 8 134 0+basis .sphere 8 134 3)+
    ((if e x 4=0 then 0 else basis .sphere 8 134 4)+
     (if e x 5=0 then 0 else basis .sphere 8 134 5)) := by
    by_cases h0 : e x 0=0
    · have h3 := c03.mp h0
      simpa only [c2,h0,h3,ite_true,zero_add] using xx
    · have h3 : ¬e x 3=0 := fun h=>(h0 (c03.mpr h))
      simpa only [c2,h0,h3,ite_true,ite_false,zero_add,add_assoc] using xx
  have hb56 : RepresentsOnPage E 6 (8,134) (basis .sphere 8 134 5) 0 :=
    differential_target_later_zero hs2 (by decide) h176
  have rz6 := represents_add_tail (represents_bit (e x 0) haW6)
    (represents_add_tail (represents_bit (e x 4) hb6) (represents_bit (e x 5) hb56))
  rw [←xxx] at rz6
  simp only [ite_self,add_zero] at rz6
  have z6form := represents_unique hxz6 rz6
  by_cases h0 : e x 0=0 <;> by_cases h4 : e x 4=0
  · exact Or.inl (by simpa only [h0,h4,ite_true,add_zero] using z6form)
  · exact Or.inr (Or.inr (Or.inl (by simpa only [h0,h4,ite_true,ite_false,zero_add] using z6form)))
  · exact Or.inr (Or.inl (by simpa only [h0,h4,ite_true,ite_false,add_zero] using z6form))
  · exact Or.inr (Or.inr (Or.inr (by simpa only [h0,h4,ite_false] using z6form)))



/-- Complete incoming-page classification; it identifies actual differentials,
not an arbitrary choice of an E₂ lift. -/
public theorem t_only_incoming (r : ℤ) (h : HitOnPage model.classical.sphere r (14,139) T) :
    (r = 6 ∧ HasNonzeroDifferential model.classical.sphere 6 (8,134) (14,139) W T) ∨
    (r = 12 ∧ HasNonzeroDifferential model.classical.sphere 12 (2,128) (14,139) h6Square T) := by
  with_unfolding_all
    rcases h with ⟨⟨s,t⟩,hdeg,z,y,hy,yne,hd⟩
    have hr : 2≤r := hy.1
    have hs : s=14-r := by
      have hh := congrArg Prod.fst hdeg
      simp only [KIP126.Classical.Adams.ClassicalAdamsFamily.sphere,
        KIP126.Classical.Adams.ClassicalAdamsFamily.obj,model.classical.differentialDegree,
        Prod.mk_add_mk] at hh
      omega
    have ht : t=140-r := by
      have hh := congrArg Prod.snd hdeg
      simp only [KIP126.Classical.Adams.ClassicalAdamsFamily.sphere,
        KIP126.Classical.Adams.ClassicalAdamsFamily.obj,model.classical.differentialDegree,
        Prod.mk_add_mk] at hh
      omega
    subst s
    subst t
    have zero_contra (hz : z=0) : False := by
      rw [hz,ModuleCat.comp_apply,map_zero,map_zero] at hd
      exact yne hd.symm
    have map_contra (hm : model.classical.sphere.d r (14-r,140-r)=0) : False := by
      have hz : model.classical.sphere.d r (14-r,140-r) z=0 := by rw [hm];rfl
      rw [ModuleCat.comp_apply,hz,map_zero] at hd
      exact yne hd.symm
    by_cases hlate : 15≤r
    · haveI : Subsingleton (model.classical.sphere.Page r (14-r,140-r)) :=
        KIP126.AdamsSynthetic.Standard.classical_page_negative .sphere r (14-r) (140-r) (by omega)
      exact (zero_contra (Subsingleton.elim _ _)).elim
    have hle : r≤14 := by omega
    interval_cases r
    · exact (tIn_second_avoid z (hd.trans hy.eq_on_page_two.symm)).elim
    · exact (map_contra tIn_third_map_zero).elim
    · exact (map_contra (r5_ten_zero 4 (by decide) (by decide))).elim
    · exact (zero_contra (tIncoming_r5_zero z)).elim
    · obtain ⟨w,b,hw,hb,hdb,frame⟩ := tIncoming_r6_frame
      let δ := model.classical.sphere.d 6 (8,134) ≫
        eqToHom (congrArg (model.classical.sphere.Page 6) hdeg)
      have db : δ b=0 := by
        dsimp only [δ]
        rw [ModuleCat.comp_apply,hdb,map_zero]
      have dw : δ w=y := by
        rcases frame z with hz|hz|hz|hz
        · exact (zero_contra hz).elim
        · rw [hz] at hd;exact hd
        · rw [hz] at hd
          change δ b=y at hd
          exact (yne (db.symm.trans hd).symm).elim
        · change δ z=y at hd
          rw [hz,map_add,db,add_zero] at hd
          exact hd
      exact Or.inl ⟨rfl,hdeg,w,y,hw,hy,dw,yne⟩
    · exact (map_contra tIn_seventh_map_zero).elim
    · exact (zero_contra (tIn_eighth_zero 8 (by decide) z)).elim
    · exact (zero_contra (tIn_ninth_zero 9 (by decide) z)).elim
    · exact (zero_contra (tIn_tenth_zero 10 (by decide) z)).elim
    · exact (zero_contra (tIn_eleventh_zero 11 (by decide) z)).elim
    · obtain ⟨x,hx⟩ := page_has_initial_representative (by decide : (2:ℤ)≤12) z
      rcases square_exhaustive x with hz|hxSquare
      · rw [hz] at hx
        have zz : z=0 := represents_unique hx (RepresentsOnPage.zero (by decide))
        exact (zero_contra zz).elim
      · rw [hxSquare] at hx
        exact Or.inr ⟨rfl,hdeg,z,y,hx,hy,hd,yne⟩
    · obtain ⟨e,he⟩ := tInBasis90
      exact (zero_contra (tIn_empty_later (by decide) e z)).elim
    · obtain ⟨e,he⟩ := tInBasis77
      exact (zero_contra (tIn_empty_later (by decide) e z)).elim

private theorem differential_targets_of_complete_frame
    {E : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ×ℤ)}
    {r : ℤ} {p q : ℤ×ℤ} {x : E.Page 2 p} {y : E.Page 2 q}
    {y' : E.Page 2 (p+E.diffDeg r)}
    (h : p+E.diffDeg r=q) (hlabel : HEq y' y)
    (hf : ∃ a : E.Page r q, RepresentsOnPage E r q y a ∧
      ∀ b : E.Page r q, b=0 ∨ b=a) :
    DifferentialTargets E r p x y' := by
  subst q
  cases hlabel
  intro xr _
  obtain ⟨a,ha,hall⟩ := hf
  rcases hall (E.d r p xr) with hz | heq
  · exact Or.inl hz
  · exact Or.inr ⟨a,ha,heq⟩

private theorem sphere_six_T_frame :
    ∃ a : model.classical.sphere.Page 6 (14,139),
      RepresentsOnPage model.classical.sphere 6 (14,139) T a ∧
      ∀ b : model.classical.sphere.Page 6 (14,139), b=0 ∨ b=a := by
  classical
  let E := model.classical.sphere
  have hs2 : E.r₀≤2 := by
    change model.classical.sphere.r₀≤2
    rw [model.classical.firstPage]
  have h341 : HasDifferential E 2 (12,138) (14,139)
      (basis .sphere 12 138 1)
      (basis .sphere 14 139 2) := by
    have hrow := result ⟨.sphere, .equation, 2, 12, 138, [1], 14, 139, [2], "S0_AdamsE2_ss", 3079⟩ (by
      exact List.mem_of_getElem? (l := Raw.claims) (i := 341) rfl)
    dsimp only [Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (12,138) (14,139) x y at hd
    have vx : Raw.coordinatesValid Raw.degrees
      .sphere 12 138 [1] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees
      .sphere 14 139 [2] = true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  have h343 : HasDifferential E 2 (14,139) (16,140)
      (basis .sphere 14 139 0)
      (basis .sphere 16 140 2) := by
    have hrow := result ⟨.sphere, .equation, 2, 14, 139, [0], 16, 140, [2], "S0_AdamsE2_ss", 3081⟩ (by
      exact List.mem_of_getElem? (l := Raw.claims) (i := 343) rfl)
    dsimp only [Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (14,139) (16,140) x y at hd
    have vx : Raw.coordinatesValid Raw.degrees
      .sphere 14 139 [0] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees
      .sphere 16 140 [2] = true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  have h342 : ReachesPage E 1000 (14,139)
      (basis .sphere 14 139 1) := by
    have hrow := result ⟨.sphere, .reaches, 1000, 14, 139, [1], 14, 139, [], "S0_AdamsE2_ss", 3080⟩ (by
      exact List.mem_of_getElem? (l := Raw.claims) (i := 342) rfl)
    dsimp only [Statement] at hrow
    obtain ⟨x,hx,hxlate⟩ := hrow
    have vx : Raw.coordinatesValid Raw.degrees
      .sphere 14 139 [1] = true := rfl
    simp only [decode,vx,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
    rw [←hx] at hxlate
    exact hxlate
  obtain ⟨f,hf⟩ := basis_correct
    ⟨.sphere, 14, 139, ["449,1", "1,1,7,1,275,1", "0,2,425,1"]⟩ (by
      exact List.mem_of_getElem? (l := Raw.degrees) (i := 217) rfl)
  change E.Page 2 (14,139) ≃ₗ[ℤ] (Fin 3 →₀ F2) at f
  change ∀ i : Fin 3, f.symm (Finsupp.single i 1) =
    basis .sphere 14 139 i.val at hf
  obtain ⟨g,hg⟩ := basis_correct
    ⟨.sphere, 16, 140, ["9,1,261,1", "1,1,438,1", "0,1,448,1", "0,2,440,1", "0,2,439,1"]⟩ (by
      exact List.mem_of_getElem? (l := Raw.degrees) (i := 231) rfl)
  change E.Page 2 (16,140) ≃ₗ[ℤ] (Fin 5 →₀ F2) at g
  change ∀ i : Fin 5, g.symm (Finsupp.single i 1) =
    basis .sphere 16 140 i.val at hg
  let δ : E.Page 2 (14,139) ⟶ E.Page 2 (16,140) :=
    E.d 2 (14,139) ≫ eqToHom (congrArg (E.Page 2) h343.target_degree)
  have d0 : δ (basis .sphere 14 139 0)=basis .sphere 16 140 2 := h343.eq_on_page_two.2
  have d1 : δ (basis .sphere 14 139 1)=0 := by
    have hd := represents_d_zero_of_later hs2 (by decide : (2:ℤ)<1000)
      (represents_two_self _) h342
    simp only [δ,ModuleCat.comp_apply,hd,map_zero]
  have r2 : RepresentsOnPage E 6 (14,139) (basis .sphere 14 139 2) 0 :=
    differential_target_later_zero hs2 (by decide) h341
  have d2 : δ (basis .sphere 14 139 2)=0 := by
    have hd := represents_d_zero_of_later hs2 (by decide : (2:ℤ)<6)
      (represents_two_self _) ⟨0,r2⟩
    simp only [δ,ModuleCat.comp_apply,hd,map_zero]
  have targetne : basis .sphere 16 140 2≠0 := by
    have hg2 : g.symm (Finsupp.single (2 : Fin 5) 1)=basis .sphere 16 140 2 := hg 2
    rw [←hg2]
    exact basis_vector_ne_zero g 2
  obtain ⟨a,ha⟩ := reaches_before (by decide : (2:ℤ)≤6) (by decide : (6:ℤ)≤1000) h342
  refine ⟨a,?_,?_⟩
  · rw [basis_T] at ha
    exact ha
  · intro b
    obtain ⟨x,hxb⟩ := page_has_initial_representative (by decide : (2:ℤ)≤6) b
    have hx := finite_basis_expansion f x
    simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,hf,add_zero] at hx
    change x=(if f x 0=0 then 0 else basis .sphere 14 139 0)+
      ((if f x 1=0 then 0 else basis .sphere 14 139 1)+
       (if f x 2=0 then 0 else basis .sphere 14 139 2)) at hx
    have dx : δ x=0 := by
      have hd := represents_d_zero_of_later hs2 (by decide : (2:ℤ)<6)
        (represents_two_self _) ⟨b,hxb⟩
      simp only [δ,ModuleCat.comp_apply,hd,map_zero]
    have hd := congrArg δ hx
    rw [dx] at hd
    simp only [map_add,apply_ite,map_zero] at hd
    simp only [d0,d1,d2,ite_self,add_zero] at hd
    have hc0 : f x 0=0 := by
      by_contra h
      have heq : (0 : E.Page 2 (16,140))=basis .sphere 16 140 2 := by
        simpa only [h,ite_false] using hd
      exact targetne heq.symm
    have rep : RepresentsOnPage E 6 (14,139) x (if f x 1=0 then 0 else a) := by
      have hr := represents_add_tail (represents_bit (f x 1) ha) (represents_bit (f x 2) r2)
      simp only [ite_self,add_zero] at hr
      have hx' := hx
      simp only [hc0,ite_true,zero_add] at hx'
      rw [←hx'] at hr
      exact hr
    have hb := represents_unique hxb rep
    by_cases h : f x 1=0
    · exact Or.inl (by simpa only [h,ite_true] using hb)
    · exact Or.inr (by simpa only [h,ite_false] using hb)

public theorem w_d6_targets : DifferentialTargets model.classical.sphere 6 (8,134) W
    (by simpa only [ClassicalAdamsFamily.sphere, ClassicalAdamsFamily.obj, model.classical.differentialDegree,
      Prod.mk_add_mk, Int.reduceSub, Int.reduceAdd] using T) := by
  have hdeg : (8,134)+model.classical.sphere.diffDeg 6=(14,139) := by
    simp only [model.classical.differentialDegree,Prod.mk_add_mk,Int.reduceSub,Int.reduceAdd]
  exact differential_targets_of_complete_frame hdeg (cast_heq _ _) sphere_six_T_frame

private theorem correctionPermanentPageZero
    (E : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ×ℤ))
    (r : ℤ) (hr : 2 ≤ r) (p : ℤ×ℤ) (h2 : Subsingleton (E.Page 2 p)) :
    Subsingleton (E.Page r p) := by
  have hz (a : E.Page r p) : a=0 := by
    obtain ⟨x,hx⟩ := page_has_initial_representative hr a
    rw [h2.elim x 0] at hx
    exact represents_unique hx (RepresentsOnPage.zero hr)
  exact ⟨fun a b=>(hz a).trans (hz b).symm⟩

private theorem correctionPermanentInitialZero (s t : ℕ) (ht : t ≤ 261)
    (hdim : basisDimension s t=0) :
    Subsingleton (model.classical.sphere.Page 2 (s,t)) := by
  let e := coordinates s t ht
  have hn : archive.basisCount s t=0 := (archive_dimension s t ht).trans hdim
  haveI : Subsingleton (Fin (archive.basisCount s t) →₀ ZMod 2) := by
    rw [hn]
    infer_instance
  exact e.injective.subsingleton

private theorem correctionPermanentNonzeroOfPermanentFinite
    (E : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ))
    (N : ℤ) (hN : E.r₀ ≤ N) (p : ℤ × ℤ) (x : E.Page 2 p)
    (hperm : IsPermanentCycle E p x) (hsurv : SurvivesTo E N p x)
    (hin : ∀ r : ℤ, N ≤ r → E.d r (p-E.diffDeg r)=0) :
    NonzeroSurvival E p x := by
  let D := E.ssData p
  let n₂ : WithTop ℕ := ↑(2-E.r₀).toNat
  let n : WithTop ℕ := ↑(N-E.r₀).toNat
  obtain ⟨z,hz⟩ := hperm
  obtain ⟨a,ha,hane⟩ := hsurv
  let zN := Subobject.ofLE (D.Z ⊤) (D.Z n) (D.Z_anti le_top) z
  have hrep : RepresentsOnPage E N p x (D.pageπ n zN) := by
    refine ⟨ha.1,zN,?_,rfl⟩
    dsimp only [zN]
    rw [← CategoryTheory.comp_apply, ← Category.assoc, Subobject.ofLE_comp_ofLE]
    exact hz
  refine ⟨z,hz,?_⟩
  intro hz0
  apply hane
  rw [represents_unique ha hrep]
  have hB : D.B ⊤ = D.B n := boundaries_top_eq_of_d_eq_zero E N hN p hin
  have hb := (subobject_cokernel_π_eq_zero_iff (D.B ⊤) (D.Z ⊤) (D.B_le_Z ⊤) z).mp hz0
  apply (subobject_cokernel_π_eq_zero_iff (D.B n) (D.Z n) (D.B_le_Z n) zN).mpr
  change (Subobject.ofLE (D.Z ⊤) (D.Z n) (D.Z_anti le_top) ≫ (D.Z n).arrow) z ∈ _
  rw [Subobject.ofLE_arrow]
  rwa [← hB]

private theorem correctionPermanentD279 : HasDifferential model.classical.sphere 3 (8,134) (11,136)
    (basis .sphere 8 134 3) (basis .sphere 11 136 1) := by
  have hrow := result ⟨.sphere,.equation,3,8,134,[3],11,136,[1],"S0_AdamsE2_ss",2850⟩ (by
    exact List.mem_of_getElem? (i := 279) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential model.classical.sphere 3 (8,134) (11,136) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 134 [3]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 11 136 [1]=true := rfl
  delta decode at ha hb
  simp (config := { congrConsts := false }) only [vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  exact h

private theorem correctionPermanentD280 : HasDifferential model.classical.sphere 3 (8,134) (11,136)
    (basis .sphere 8 134 2) (basis .sphere 11 136 2) := by
  have hrow := result ⟨.sphere,.equation,3,8,134,[2],11,136,[2],"S0_AdamsE2_ss",2851⟩ (by
    exact List.mem_of_getElem? (i := 280) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential model.classical.sphere 3 (8,134) (11,136) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 134 [2]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 11 136 [2]=true := rfl
  delta decode at ha hb
  simp (config := { congrConsts := false }) only [vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  exact h

private theorem correctionPermanentR281 : ReachesPage model.classical.sphere 5 (11,136) (basis .sphere 11 136 3) := by
  have hrow := result ⟨.sphere,.reaches,5,11,136,[3],11,136,[],"S0_AdamsE2_ss",2852⟩ (by
    exact List.mem_of_getElem? (i := 281) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,h⟩ := hrow
  have vx : Raw.coordinatesValid Raw.degrees .sphere 11 136 [3]=true := rfl
  delta decode at ha
  simp (config := { congrConsts := false }) only [vx,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha
  rw [←ha] at h
  exact h

private theorem correctionPermanentD282 : HasDifferential model.classical.sphere 4 (11,136) (15,139)
    (basis .sphere 11 136 0) (basis .sphere 15 139 0) := by
  have hrow := result ⟨.sphere,.equation,4,11,136,[0],15,139,[0],"S0_AdamsE2_ss",2853⟩ (by
    exact List.mem_of_getElem? (i := 282) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential model.classical.sphere 4 (11,136) (15,139) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 11 136 [0]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 15 139 [0]=true := rfl
  delta decode at ha hb
  simp (config := { congrConsts := false }) only [vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  exact h

private theorem correctionPermanentD321 : HasDifferential model.classical.sphere 2 (11,136) (13,137)
    (basis .sphere 11 136 4) (basis .sphere 13 137 3) := by
  have hrow := result ⟨.sphere,.equation,2,11,136,[4],13,137,[3],"S0_AdamsE2_ss",2914⟩ (by
    exact List.mem_of_getElem? (i := 321) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential model.classical.sphere 2 (11,136) (13,137) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 11 136 [4]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 13 137 [3]=true := rfl
  delta decode at ha hb
  simp (config := { congrConsts := false }) only [vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  exact h

private theorem correctionPermanentD322 : HasDifferential model.classical.sphere 3 (10,135) (13,137)
    (basis .sphere 10 135 0) (basis .sphere 13 137 0) := by
  have hrow := result ⟨.sphere,.equation,3,10,135,[0],13,137,[0],"S0_AdamsE2_ss",2915⟩ (by
    exact List.mem_of_getElem? (i := 322) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential model.classical.sphere 3 (10,135) (13,137) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 135 [0]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 13 137 [0]=true := rfl
  delta decode at ha hb
  simp (config := { congrConsts := false }) only [vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  exact h

private theorem correctionPermanentR323 : ReachesPage model.classical.sphere 1000 (13,137) (basis .sphere 13 137 1) := by
  have hrow := result ⟨.sphere,.reaches,1000,13,137,[1],13,137,[],"S0_AdamsE2_ss",2916⟩ (by
    exact List.mem_of_getElem? (i := 323) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,h⟩ := hrow
  have vx : Raw.coordinatesValid Raw.degrees .sphere 13 137 [1]=true := rfl
  delta decode at ha
  simp (config := { congrConsts := false }) only [vx,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha
  rw [←ha] at h
  exact h

private theorem correctionPermanentD324 : HasDifferential model.classical.sphere 3 (13,137) (16,139)
    (basis .sphere 13 137 2) (basis .sphere 16 139 0) := by
  have hrow := result ⟨.sphere,.equation,3,13,137,[2],16,139,[0],"S0_AdamsE2_ss",2917⟩ (by
    exact List.mem_of_getElem? (i := 324) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential model.classical.sphere 3 (13,137) (16,139) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 13 137 [2]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 16 139 [0]=true := rfl
  delta decode at ha hb
  simp (config := { congrConsts := false }) only [vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  exact h

private theorem correctionPermanentD300 : HasDifferential model.classical.sphere 2 (10,135) (12,136)
    (basis .sphere 10 135 1) (basis .sphere 12 136 1 + basis .sphere 12 136 2) := by
  have hrow := result ⟨.sphere,.equation,2,10,135,[1],12,136,[1, 2],"S0_AdamsE2_ss",2845⟩ (by
    exact List.mem_of_getElem? (i := 300) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential model.classical.sphere 2 (10,135) (12,136) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 135 [1]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 136 [1, 2]=true := rfl
  delta decode at ha hb
  simp (config := { congrConsts := false }) only [vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  exact h

private theorem correctionPermanentD301 : HasDifferential model.classical.sphere 2 (10,135) (12,136)
    (basis .sphere 10 135 2) (basis .sphere 12 136 3 + basis .sphere 12 136 4) := by
  have hrow := result ⟨.sphere,.equation,2,10,135,[2],12,136,[3, 4],"S0_AdamsE2_ss",2846⟩ (by
    exact List.mem_of_getElem? (i := 301) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential model.classical.sphere 2 (10,135) (12,136) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 135 [2]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 136 [3, 4]=true := rfl
  delta decode at ha hb
  simp (config := { congrConsts := false }) only [vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  exact h

private theorem correctionPermanentD302 : HasDifferential model.classical.sphere 2 (10,135) (12,136)
    (basis .sphere 10 135 4) (basis .sphere 12 136 4) := by
  have hrow := result ⟨.sphere,.equation,2,10,135,[4],12,136,[4],"S0_AdamsE2_ss",2847⟩ (by
    exact List.mem_of_getElem? (i := 302) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential model.classical.sphere 2 (10,135) (12,136) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 135 [4]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 136 [4]=true := rfl
  delta decode at ha hb
  simp (config := { congrConsts := false }) only [vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  exact h

private theorem correctionPermanentD251 : HasDifferential model.classical.sphere 2 (8,134) (10,135)
    (basis .sphere 8 134 1) (basis .sphere 10 135 3) := by
  have hrow := result ⟨.sphere,.equation,2,8,134,[1],10,135,[3],"S0_AdamsE2_ss",2783⟩ (by
    exact List.mem_of_getElem? (i := 251) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential model.classical.sphere 2 (8,134) (10,135) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 134 [1]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 10 135 [3]=true := rfl
  delta decode at ha hb
  simp (config := { congrConsts := false }) only [vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  exact h

private theorem correctionPermanentR224 : ReachesPage model.classical.sphere 1000 (9,134) (basis .sphere 9 134 2) := by
  have hrow := result ⟨.sphere,.reaches,1000,9,134,[2],9,134,[],"S0_AdamsE2_ss",2695⟩ (by
    exact List.mem_of_getElem? (i := 224) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,h⟩ := hrow
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 134 [2]=true := rfl
  delta decode at ha
  simp (config := { congrConsts := false }) only [vx,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha
  rw [←ha] at h
  exact h

private theorem correctionPermanentR225 : ReachesPage model.classical.sphere 7 (9,134) (basis .sphere 9 134 3) := by
  have hrow := result ⟨.sphere,.reaches,7,9,134,[3],9,134,[],"S0_AdamsE2_ss",2696⟩ (by
    exact List.mem_of_getElem? (i := 225) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,h⟩ := hrow
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 134 [3]=true := rfl
  delta decode at ha
  simp (config := { congrConsts := false }) only [vx,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha
  rw [←ha] at h
  exact h

private theorem correctionPermanentD226 : HasDifferential model.classical.sphere 3 (9,134) (12,136)
    (basis .sphere 9 134 1) (basis .sphere 12 136 0) := by
  have hrow := result ⟨.sphere,.equation,3,9,134,[1],12,136,[0],"S0_AdamsE2_ss",2697⟩ (by
    exact List.mem_of_getElem? (i := 226) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential model.classical.sphere 3 (9,134) (12,136) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 134 [1]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 136 [0]=true := rfl
  delta decode at ha hb
  simp (config := { congrConsts := false }) only [vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  exact h

private theorem correctionPermanentD227 : HasDifferential model.classical.sphere 2 (9,134) (11,135)
    (basis .sphere 9 134 0) (basis .sphere 11 135 3 + basis .sphere 11 135 4) := by
  have hrow := result ⟨.sphere,.equation,2,9,134,[0],11,135,[3, 4],"S0_AdamsE2_ss",2698⟩ (by
    exact List.mem_of_getElem? (i := 227) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential model.classical.sphere 2 (9,134) (11,135) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 134 [0]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 11 135 [3, 4]=true := rfl
  delta decode at ha hb
  simp (config := { congrConsts := false }) only [vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  exact h

private theorem correctionPermanentD228 : HasDifferential model.classical.sphere 2 (9,134) (11,135)
    (basis .sphere 9 134 4) (basis .sphere 11 135 4) := by
  have hrow := result ⟨.sphere,.equation,2,9,134,[4],11,135,[4],"S0_AdamsE2_ss",2699⟩ (by
    exact List.mem_of_getElem? (i := 228) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential model.classical.sphere 2 (9,134) (11,135) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 134 [4]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 11 135 [4]=true := rfl
  delta decode at ha hb
  simp (config := { congrConsts := false }) only [vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  exact h

private theorem correctionPermanentImageCoord
    {A B : Type} [AddCommGroup A] [Module ℤ A] [AddCommGroup B] [Module ℤ B]
    {n m : ℕ} (e : A ≃ₗ[ℤ] (Fin n →₀ F2)) (f : B ≃ₗ[ℤ] (Fin m →₀ F2))
    (d : A →ₗ[ℤ] B) (x : A) (j : Fin m) :
    f (d x) j = ∑ i : Fin n, if e x i=0 then 0 else f (d (e.symm (Finsupp.single i 1))) j := by
  classical
  have hx := finite_basis_expansion e x
  calc
    f (d x) j = f (d (∑ i : Fin n, if e x i=0 then 0 else e.symm (Finsupp.single i 1))) j := by
      exact congrArg (fun a => f (d a) j) hx
    _ = _ := by
      rw [map_sum,map_sum,Finsupp.finsetSum_apply]
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hc : e x i=0
      · simp only [hc,ite_true,map_zero,Finsupp.zero_apply]
      · simp only [hc,ite_false]

private theorem correctionPermanentKernelFive
    {A B : Type} [AddCommGroup A] [Module ℤ A] [AddCommGroup B] [Module ℤ B]
    (e : A ≃ₗ[ℤ] (Fin 5 →₀ F2)) (f : B ≃ₗ[ℤ] (Fin 5 →₀ F2))
    (d : A →ₗ[ℤ] B)
    (h0 : d (e.symm (Finsupp.single 0 1))=0)
    (h1 : d (e.symm (Finsupp.single 1 1))=f.symm (Finsupp.single 1 1 + Finsupp.single 2 1))
    (h2 : d (e.symm (Finsupp.single 2 1))=f.symm (Finsupp.single 3 1 + Finsupp.single 4 1))
    (h3 : d (e.symm (Finsupp.single 3 1))=0)
    (h4 : d (e.symm (Finsupp.single 4 1))=f.symm (Finsupp.single 4 1))
    (x : A) (hx : d x=0) : e x 1=0 ∧ e x 2=0 ∧ e x 4=0 := by
  classical
  have hcoord (j : Fin 5) :
      f (d x) j = (if e x 0=0 then 0 else f (d (e.symm (Finsupp.single 0 1))) j) +
      ((if e x 1=0 then 0 else f (d (e.symm (Finsupp.single 1 1))) j) +
      ((if e x 2=0 then 0 else f (d (e.symm (Finsupp.single 2 1))) j) +
      ((if e x 3=0 then 0 else f (d (e.symm (Finsupp.single 3 1))) j) +
       (if e x 4=0 then 0 else f (d (e.symm (Finsupp.single 4 1))) j)))) := by
    have h := correctionPermanentImageCoord e f d x j
    simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero] at h
    delta Fin.succ at h
    exact h
  have hh1 := hcoord 1
  have hh2 := hcoord 3
  have hh4 := hcoord 4
  norm_num only [hx,h0,h1,h2,h3,h4,map_zero,Finsupp.add_apply,Finsupp.zero_apply,
    LinearEquiv.apply_symm_apply,Finsupp.single_apply,Fin.reduceEq,ite_true,ite_false,
    add_zero,zero_add,ite_self] at hh1 hh2 hh4
  norm_num [Fin.ext_iff] at hh1 hh2 hh4
  have c1 : e x 1=0 := by
    by_contra hc
    simpa only [hc,ite_false] using hh1
  have c2 : e x 2=0 := by
    by_contra hc
    simpa only [hc,ite_false] using hh2
  have c4 : e x 4=0 := by
    by_contra hc
    simp only [c2,ite_true,hc,ite_false,zero_add] at hh4
    exact zero_ne_one hh4
  exact ⟨c1,c2,c4⟩

private theorem correctionPermanentTenDegree :
    (10,135)+model.classical.sphere.diffDeg 2=(12,136) := by
  simp only [ClassicalAdamsFamily.sphere,ClassicalAdamsFamily.obj,
    model.classical.differentialDegree,Prod.mk_add_mk,Int.reduceAdd,Int.reduceSub]

private noncomputable def correctionPermanentTenD2 :
    model.classical.sphere.Page 2 (10,135) ⟶ model.classical.sphere.Page 2 (12,136) :=
  model.classical.sphere.d 2 (10,135) ≫
    eqToHom (congrArg (model.classical.sphere.Page 2) correctionPermanentTenDegree)

private theorem correctionPermanentTenValues (i : Fin 5) :
    correctionPermanentTenD2 (basis .sphere 10 135 i.val) =
      ![0, basis .sphere 12 136 1 + basis .sphere 12 136 2,
        basis .sphere 12 136 3 + basis .sphere 12 136 4, 0,
        basis .sphere 12 136 4] i := by
  with_unfolding_all
    let E := model.classical.sphere
    have hs2 : E.r₀≤2 := by rw [model.classical.firstPage]
    fin_cases i
    · obtain ⟨_,a,b,ha,hb,hd⟩ := correctionPermanentD322
      have hz := represents_d_zero_of_later hs2 (by decide : (2:ℤ)<3)
        (represents_two_self (basis .sphere 10 135 0)) ⟨a,ha⟩
      change (eqToHom (congrArg (E.Page 2) correctionPermanentTenDegree))
        (E.d 2 (10,135) (basis .sphere 10 135 0))=0
      change E.d 2 (10,135) (basis .sphere 10 135 0)=0 at hz
      rw [hz,map_zero]
    · exact correctionPermanentD300.eq_on_page_two.choose_spec
    · exact correctionPermanentD301.eq_on_page_two.choose_spec
    · obtain ⟨z,hz,hdz⟩ := differential_target_cycle correctionPermanentD251
      rw [←hz.eq_on_page_two] at hdz
      change (eqToHom (congrArg (E.Page 2) correctionPermanentTenDegree))
        (E.d 2 (10,135) (basis .sphere 10 135 3))=0
      rw [hdz,map_zero]
    · exact correctionPermanentD302.eq_on_page_two.choose_spec

private theorem correctionPermanentIncomingTwelveCoordinate
    (g : model.classical.sphere.Page 2 (12,136) ≃ₗ[ℤ] (Fin 5 →₀ F2))
    (hg : ∀ i : Fin 5, g.symm (Finsupp.single i 1)=basis .sphere 12 136 i.val)
    (x : model.classical.sphere.Page 2 (10,135)) :
    g (correctionPermanentTenD2 x) 0=0 := by
  with_unfolding_all
    obtain ⟨f,hf⟩ := basis_correct ⟨.sphere,10,135,["413,1", "412,1", "0,1,391,1", "0,1,390,1", "0,2,375,1"]⟩ (by
      exact List.mem_of_getElem? (i := 182) (by rfl))
    change model.classical.sphere.Page 2 (10,135) ≃ₗ[ℤ] (Fin 5 →₀ F2) at f
    change ∀ i : Fin 5, f.symm (Finsupp.single i 1)=basis .sphere 10 135 i.val at hf
    have each (i : Fin 5) : g (correctionPermanentTenD2 (f.symm (Finsupp.single i 1))) 0=0 := by
      rw [hf,correctionPermanentTenValues]
      have eg (i : Fin 5) : g (basis .sphere 12 136 i.val)=Finsupp.single i 1 := by
        rw [←hg i,LinearEquiv.apply_symm_apply]
      have eg1 : g (basis .sphere 12 136 1)=Finsupp.single (1:Fin 5) 1 := eg 1
      have eg2 : g (basis .sphere 12 136 2)=Finsupp.single (2:Fin 5) 1 := eg 2
      have eg3 : g (basis .sphere 12 136 3)=Finsupp.single (3:Fin 5) 1 := eg 3
      have eg4 : g (basis .sphere 12 136 4)=Finsupp.single (4:Fin 5) 1 := eg 4
      fin_cases i
      · change g 0 0=0
        simp only [map_zero,Finsupp.zero_apply]
      · change g (basis .sphere 12 136 1 + basis .sphere 12 136 2) 0=0
        rw [map_add,Finsupp.add_apply,eg1,eg2]
        norm_num [Finsupp.single_apply] <;> decide
      · change g (basis .sphere 12 136 3 + basis .sphere 12 136 4) 0=0
        rw [map_add,Finsupp.add_apply,eg3,eg4]
        norm_num [Finsupp.single_apply] <;> decide
      · change g 0 0=0
        simp only [map_zero,Finsupp.zero_apply]
      · change g (basis .sphere 12 136 4) 0=0
        rw [eg4]
        norm_num [Finsupp.single_apply] <;> decide
    rw [correctionPermanentImageCoord f g correctionPermanentTenD2.hom x 0]
    apply Finset.sum_eq_zero
    intro i hi
    by_cases hc : f x i=0
    · simp only [hc,ite_true]
    · simp only [hc,ite_false,each]

private theorem correctionPermanentTenFrame
    {a0 : model.classical.sphere.Page 3 (10,135)}
    (ha0 : RepresentsOnPage model.classical.sphere 3 (10,135) (basis .sphere 10 135 0) a0)
    (a : model.classical.sphere.Page 3 (10,135)) : a=0 ∨ a=a0 := by
  with_unfolding_all
    let E := model.classical.sphere
    have hs2 : E.r₀≤2 := by rw [model.classical.firstPage]
    obtain ⟨f,hf⟩ := basis_correct ⟨.sphere,10,135,["413,1", "412,1", "0,1,391,1", "0,1,390,1", "0,2,375,1"]⟩ (by
      exact List.mem_of_getElem? (i := 182) (by rfl))
    change E.Page 2 (10,135) ≃ₗ[ℤ] (Fin 5 →₀ F2) at f
    change ∀ i : Fin 5, f.symm (Finsupp.single i 1)=basis .sphere 10 135 i.val at hf
    obtain ⟨g,hg⟩ := basis_correct ⟨.sphere,12,136,["1,1,387,1", "0,1,410,1", "0,1,409,1", "0,2,389,1", "0,4,367,1"]⟩ (by
      exact List.mem_of_getElem? (i := 200) (by rfl))
    change E.Page 2 (12,136) ≃ₗ[ℤ] (Fin 5 →₀ F2) at g
    change ∀ i : Fin 5, g.symm (Finsupp.single i 1)=basis .sphere 12 136 i.val at hg
    obtain ⟨x,hx⟩ := page_has_initial_representative (by decide : (2:ℤ)≤3) a
    have hdx : E.d 2 (10,135) x=0 := represents_d_zero_of_later hs2 (by decide)
      (represents_two_self x) ⟨a,hx⟩
    have hmap : correctionPermanentTenD2 x=0 := by
      change (eqToHom (congrArg (E.Page 2) correctionPermanentTenDegree)) (E.d 2 (10,135) x)=0
      rw [hdx,map_zero]
    have h0 : correctionPermanentTenD2 (f.symm (Finsupp.single 0 1))=0 := by rw [hf]; exact correctionPermanentTenValues 0
    have h1 : correctionPermanentTenD2 (f.symm (Finsupp.single 1 1))=g.symm (Finsupp.single 1 1 + Finsupp.single 2 1) := by
      rw [hf,map_add,hg,hg]; exact correctionPermanentTenValues 1
    have h2 : correctionPermanentTenD2 (f.symm (Finsupp.single 2 1))=g.symm (Finsupp.single 3 1 + Finsupp.single 4 1) := by
      rw [hf,map_add,hg,hg]; exact correctionPermanentTenValues 2
    have h3 : correctionPermanentTenD2 (f.symm (Finsupp.single 3 1))=0 := by rw [hf]; exact correctionPermanentTenValues 3
    have h4 : correctionPermanentTenD2 (f.symm (Finsupp.single 4 1))=g.symm (Finsupp.single 4 1) := by
      rw [hf,hg]; exact correctionPermanentTenValues 4
    obtain ⟨c1,c2,c4⟩ := correctionPermanentKernelFive f g correctionPermanentTenD2.hom h0 h1 h2 h3 h4 x hmap
    have he := finite_basis_expansion f x
    simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero] at he
    delta Fin.succ at he
    change x=(if f x 0=0 then 0 else f.symm (Finsupp.single 0 1)) +
      ((if f x 1=0 then 0 else f.symm (Finsupp.single 1 1)) +
      ((if f x 2=0 then 0 else f.symm (Finsupp.single 2 1)) +
      ((if f x 3=0 then 0 else f.symm (Finsupp.single 3 1)) +
       (if f x 4=0 then 0 else f.symm (Finsupp.single 4 1))))) at he
    simp only [c1,c2,c4,ite_true,zero_add,add_zero] at he
    have hb3 : RepresentsOnPage E 3 (10,135) (f.symm (Finsupp.single 3 1)) 0 := by
      rw [hf]
      exact differential_target_later_zero hs2 (by decide) correctionPermanentD251
    have hb0 : RepresentsOnPage E 3 (10,135) (f.symm (Finsupp.single 0 1)) a0 := by rw [hf]; exact ha0
    have hrep := represents_add_tail (represents_bit (f x 0) hb0) (represents_bit (f x 3) hb3)
    simp only [ite_self,add_zero] at hrep
    rw [←he] at hrep
    have heq := represents_unique hx hrep
    by_cases hc : f x 0=0
    · exact Or.inl (by simpa only [hc,ite_true] using heq)
    · exact Or.inr (by simpa only [hc,ite_false] using heq)

private theorem correctionPermanentElevenDegree :
    (11,136)+model.classical.sphere.diffDeg 2=(13,137) := by
  simp only [ClassicalAdamsFamily.sphere,ClassicalAdamsFamily.obj,
    model.classical.differentialDegree,Prod.mk_add_mk,Int.reduceAdd,Int.reduceSub]

private noncomputable def correctionPermanentElevenD2 :
    model.classical.sphere.Page 2 (11,136) ⟶ model.classical.sphere.Page 2 (13,137) :=
  model.classical.sphere.d 2 (11,136) ≫
    eqToHom (congrArg (model.classical.sphere.Page 2) correctionPermanentElevenDegree)

private theorem correctionPermanentElevenValues (i : Fin 5) :
    correctionPermanentElevenD2 (basis .sphere 11 136 i.val) =
      if i=4 then basis .sphere 13 137 3 else 0 := by
  with_unfolding_all
    let E := model.classical.sphere
    have hs2 : E.r₀≤2 := by rw [model.classical.firstPage]
    have hz (i : Fin 5) (h : ReachesPage E 3 (11,136) (basis .sphere 11 136 i.val)) :
        correctionPermanentElevenD2 (basis .sphere 11 136 i.val)=0 := by
      have hd := represents_d_zero_of_later hs2 (by decide : (2:ℤ)<3)
        (represents_two_self (basis .sphere 11 136 i.val)) h
      change (eqToHom (congrArg (E.Page 2) correctionPermanentElevenDegree))
        (E.d 2 (11,136) (basis .sphere 11 136 i.val))=0
      change E.d 2 (11,136) (basis .sphere 11 136 i.val)=0 at hd
      rw [hd,map_zero]
    fin_cases i
    · change correctionPermanentElevenD2 (basis .sphere 11 136 0)=0
      obtain ⟨_,a,b,ha,hb,hd⟩ := correctionPermanentD282
      exact hz 0 (reaches_before (by decide) (by decide : (3:ℤ)≤4) ⟨a,ha⟩)
    · change correctionPermanentElevenD2 (basis .sphere 11 136 1)=0
      obtain ⟨_,a,b,ha,hb,hd⟩ := correctionPermanentD279
      exact hz 1 ⟨b,hb⟩
    · change correctionPermanentElevenD2 (basis .sphere 11 136 2)=0
      obtain ⟨_,a,b,ha,hb,hd⟩ := correctionPermanentD280
      exact hz 2 ⟨b,hb⟩
    · change correctionPermanentElevenD2 (basis .sphere 11 136 3)=0
      exact hz 3 (reaches_before (by decide) (by decide : (3:ℤ)≤5) correctionPermanentR281)
    · change correctionPermanentElevenD2 (basis .sphere 11 136 4)=basis .sphere 13 137 3
      exact correctionPermanentD321.eq_on_page_two.choose_spec

private theorem correctionPermanentReaches1000 :
    ReachesPage model.classical.sphere 1000 (13,137) correction := by
  have h := correctionPermanentR323
  rw [basis_correction] at h
  exact h

private theorem correctionPermanentSurvivesFour :
    SurvivesTo model.classical.sphere 4 (13,137) correction := by
  with_unfolding_all
    classical
    let E := model.classical.sphere
    have hs2 : E.r₀≤2 := by rw [model.classical.firstPage]
    obtain ⟨q4,hq4⟩ := reaches_before (by decide : (2:ℤ)≤4) (by decide : (4:ℤ)≤1000)
      correctionPermanentReaches1000
    obtain ⟨q3,hq3⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤4) hq4
    obtain ⟨e,he⟩ := basis_correct ⟨.sphere,13,137,["76,1,82,1", "9,1,251,1", "7,1,275,1", "0,5,367,1"]⟩ (by
      exact List.mem_of_getElem? (i := 208) (by rfl))
    change E.Page 2 (13,137) ≃ₗ[ℤ] (Fin 4 →₀ F2) at e
    change ∀ i : Fin 4, e.symm (Finsupp.single i 1)=basis .sphere 13 137 i.val at he
    let b0 : E.Page 2 (13,137) := basis .sphere 13 137 0
    let b3 : E.Page 2 (13,137) := basis .sphere 13 137 3
    have heQ : e.symm (Finsupp.single (1:Fin 4) 1)=correction := (he 1).trans basis_correction
    have heB0 : e.symm (Finsupp.single (0:Fin 4) 1)=b0 := he 0
    have heB3 : e.symm (Finsupp.single (3:Fin 4) 1)=b3 := he 3
    have eQ : e correction 1=1 := by
      rw [←heQ,LinearEquiv.apply_symm_apply,Finsupp.single_eq_same]
    have eb0 : e b0 1=0 := by
      rw [←heB0,LinearEquiv.apply_symm_apply]
      norm_num [Finsupp.single_apply] <;> decide
    have eb3 : e b3 1=0 := by
      rw [←heB3,LinearEquiv.apply_symm_apply]
      norm_num [Finsupp.single_apply] <;> decide
    obtain ⟨f,hf⟩ := basis_correct ⟨.sphere,11,136,["69,1,89,1", "1,1,389,1", "1,1,388,1", "0,2,391,1", "0,3,375,1"]⟩ (by
      exact List.mem_of_getElem? (i := 192) (by rfl))
    change E.Page 2 (11,136) ≃ₗ[ℤ] (Fin 5 →₀ F2) at f
    change ∀ i : Fin 5, f.symm (Finsupp.single i 1)=basis .sphere 11 136 i.val at hf
    have each0 (i : Fin 5) : e (correctionPermanentElevenD2 (f.symm (Finsupp.single i 1))) 1=0 := by
      rw [hf,correctionPermanentElevenValues]
      split_ifs
      · exact eb3
      · exact congrArg (fun z : Fin 4 →₀ F2 => z 1) e.map_zero
    have image1 (v : E.Page 2 (11,136)) : e (correctionPermanentElevenD2 v) 1=0 := by
      have hex := finite_basis_expansion f v
      rw [hex]
      simp only [map_sum,Finsupp.finsetSum_apply]
      apply Finset.sum_eq_zero
      intro i hi
      by_cases hc : f v i=0
      · simp only [hc,ite_true,map_zero,Finsupp.zero_apply]
      · simp only [hc,ite_false]
        exact each0 i
    have avoid (y : E.Page 2 (13,137)) (hy : e y 1=1) (v : E.Page 2 (11,136)) :
        correctionPermanentElevenD2 v≠y := by
      intro h
      have hh := congrArg (fun z => e z 1) h
      rw [image1,hy] at hh
      exact zero_ne_one hh
    obtain ⟨deg3,a0,c0,ha0,hc0,hd0⟩ := correctionPermanentD322
    have q3ne : q3≠0 := represents_next_nonzero_of_not_incoming_at
      correctionPermanentElevenDegree hs2 (by decide) hq3 (represents_two_self correction)
      (avoid correction eQ)
    have diff2 : e (correction-b0) 1=1 := by
      rw [map_sub,Finsupp.sub_apply,eQ,eb0,sub_zero]
    have diff3 : q3-c0≠0 := represents_next_nonzero_of_not_incoming_at
      correctionPermanentElevenDegree hs2 (by decide) (represents_sub hq3 hc0)
      (represents_two_self (correction-b0))
      (avoid _ diff2)
    have image3 (v : E.Page 3 (10,135)) :
        (E.d 3 (10,135) ≫ eqToHom (congrArg (E.Page 3) deg3)) v=0 ∨
        (E.d 3 (10,135) ≫ eqToHom (congrArg (E.Page 3) deg3)) v=c0 := by
      rcases correctionPermanentTenFrame ha0 v with h|h
      · rw [h,map_zero]; exact Or.inl rfl
      · rw [h,hd0]; exact Or.inr rfl
    exact ⟨q4,hq4,represents_next_nonzero_of_incoming_two_cases_at deg3
      (hs2.trans (by decide : (2:ℤ)≤3)) (by decide) hq4 hq3 image3 q3ne diff3⟩

private theorem correctionPermanentImageCoordFive
    {A B : Type} [AddCommGroup A] [Module ℤ A] [AddCommGroup B] [Module ℤ B]
    {m : ℕ} (e : A ≃ₗ[ℤ] (Fin 5 →₀ F2)) (f : B ≃ₗ[ℤ] (Fin m →₀ F2))
    (d : A →ₗ[ℤ] B) (x : A) (j : Fin m) :
    f (d x) j = (if e x 0=0 then 0 else f (d (e.symm (Finsupp.single 0 1))) j) +
      ((if e x 1=0 then 0 else f (d (e.symm (Finsupp.single 1 1))) j) +
      ((if e x 2=0 then 0 else f (d (e.symm (Finsupp.single 2 1))) j) +
      ((if e x 3=0 then 0 else f (d (e.symm (Finsupp.single 3 1))) j) +
       (if e x 4=0 then 0 else f (d (e.symm (Finsupp.single 4 1))) j)))) := by
  have h := correctionPermanentImageCoord e f d x j
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero] at h
  delta Fin.succ at h
  exact h

private theorem correctionPermanentNineDegree :
    (9,134)+model.classical.sphere.diffDeg 2=(11,135) := by
  simp only [ClassicalAdamsFamily.sphere,ClassicalAdamsFamily.obj,
    model.classical.differentialDegree,Prod.mk_add_mk,Int.reduceAdd,Int.reduceSub]

private noncomputable def correctionPermanentNineD2 :
    model.classical.sphere.Page 2 (9,134) ⟶ model.classical.sphere.Page 2 (11,135) :=
  model.classical.sphere.d 2 (9,134) ≫
    eqToHom (congrArg (model.classical.sphere.Page 2) correctionPermanentNineDegree)

private theorem correctionPermanentNineValues (i : Fin 5) :
    correctionPermanentNineD2 (basis .sphere 9 134 i.val) =
      ![basis .sphere 11 135 3 + basis .sphere 11 135 4,0,0,0,basis .sphere 11 135 4] i := by
  with_unfolding_all
    let E := model.classical.sphere
    have hs2 : E.r₀≤2 := by rw [model.classical.firstPage]
    have hz (i : Fin 5) (h : ReachesPage E 3 (9,134) (basis .sphere 9 134 i.val)) :
        correctionPermanentNineD2 (basis .sphere 9 134 i.val)=0 := by
      have hd := represents_d_zero_of_later hs2 (by decide : (2:ℤ)<3)
        (represents_two_self (basis .sphere 9 134 i.val)) h
      change (eqToHom (congrArg (E.Page 2) correctionPermanentNineDegree))
        (E.d 2 (9,134) (basis .sphere 9 134 i.val))=0
      change E.d 2 (9,134) (basis .sphere 9 134 i.val)=0 at hd
      rw [hd,map_zero]
    fin_cases i
    · exact correctionPermanentD227.eq_on_page_two.choose_spec
    · obtain ⟨_,a,b,ha,hb,hd⟩ := correctionPermanentD226
      exact hz 1 ⟨a,ha⟩
    · exact hz 2 (reaches_before (by decide) (by decide : (3:ℤ)≤1000) correctionPermanentR224)
    · exact hz 3 (reaches_before (by decide) (by decide : (3:ℤ)≤7) correctionPermanentR225)
    · exact correctionPermanentD228.eq_on_page_two.choose_spec

private theorem correctionPermanentFourthIncomingZero : model.classical.sphere.d 4 (9,134)=0 := by
  with_unfolding_all
    classical
    let E := model.classical.sphere
    have hs2 : E.r₀≤2 := by rw [model.classical.firstPage]
    obtain ⟨f,hf⟩ := basis_correct ⟨.sphere,9,134,["391,1", "390,1", "69,1,82,1", "18,1,190,1", "0,1,375,1"]⟩ (by
      exact List.mem_of_getElem? (i := 173) (by rfl))
    change E.Page 2 (9,134) ≃ₗ[ℤ] (Fin 5 →₀ F2) at f
    change ∀ i : Fin 5, f.symm (Finsupp.single i 1)=basis .sphere 9 134 i.val at hf
    obtain ⟨g,hg⟩ := basis_correct ⟨.sphere,11,135,["411,1", "410,1", "409,1", "0,1,389,1", "0,3,367,1"]⟩ (by
      exact List.mem_of_getElem? (i := 191) (by rfl))
    change E.Page 2 (11,135) ≃ₗ[ℤ] (Fin 5 →₀ F2) at g
    change ∀ i : Fin 5, g.symm (Finsupp.single i 1)=basis .sphere 11 135 i.val at hg
    obtain ⟨k,hk⟩ := basis_correct ⟨.sphere,12,136,["1,1,387,1", "0,1,410,1", "0,1,409,1", "0,2,389,1", "0,4,367,1"]⟩ (by
      exact List.mem_of_getElem? (i := 200) (by rfl))
    change E.Page 2 (12,136) ≃ₗ[ℤ] (Fin 5 →₀ F2) at k
    change ∀ i : Fin 5, k.symm (Finsupp.single i 1)=basis .sphere 12 136 i.val at hk
    obtain ⟨deg3,a1,b0,ha1,hb0,hd1⟩ := correctionPermanentD226
    have b0ne : b0≠0 := by
      apply represents_next_nonzero_of_not_incoming_at correctionPermanentTenDegree hs2 (by decide)
        hb0 (represents_two_self (basis .sphere 12 136 0))
      intro z hz
      change correctionPermanentTenD2 z=basis .sphere 12 136 0 at hz
      have hc := congrArg (fun y => k y 0) hz
      rw [correctionPermanentIncomingTwelveCoordinate k hk] at hc
      have ek0 : k (basis .sphere 12 136 0) 0=1 := by
        have hh : k.symm (Finsupp.single (0:Fin 5) 1)=basis .sphere 12 136 0 := hk 0
        rw [←hh,LinearEquiv.apply_symm_apply,Finsupp.single_eq_same]
      rw [ek0] at hc
      exact zero_ne_one hc
    obtain ⟨a2,ha2⟩ := reaches_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤1000) correctionPermanentR224
    obtain ⟨a3,ha3⟩ := reaches_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤7) correctionPermanentR225
    let d3 : E.Page 3 (9,134) ⟶ E.Page 3 (12,136) :=
      E.d 3 (9,134) ≫ eqToHom (congrArg (E.Page 3) deg3)
    have hda1 : d3 a1=b0 := hd1
    have hda2 : d3 a2=0 := by
      have hz := represents_d_zero_of_later (hs2.trans (by decide : (2:ℤ)≤3))
        (by decide : (3:ℤ)<4) ha2
        (reaches_before (by decide) (by decide : (4:ℤ)≤1000) correctionPermanentR224)
      change (eqToHom (congrArg (E.Page 3) deg3)) (E.d 3 (9,134) a2)=0
      rw [hz,map_zero]
    have hda3 : d3 a3=0 := by
      have hz := represents_d_zero_of_later (hs2.trans (by decide : (2:ℤ)≤3))
        (by decide : (3:ℤ)<4) ha3
        (reaches_before (by decide) (by decide : (4:ℤ)≤7) correctionPermanentR225)
      change (eqToHom (congrArg (E.Page 3) deg3)) (E.d 3 (9,134) a3)=0
      rw [hz,map_zero]
    have hvals (i : Fin 5) : correctionPermanentNineD2.hom (f.symm (Finsupp.single i 1)) =
        ![g.symm (Finsupp.single 3 1 + Finsupp.single 4 1),0,0,0,g.symm (Finsupp.single 4 1)] i := by
      change correctionPermanentNineD2 (f.symm (Finsupp.single i 1))=_
      rw [hf,correctionPermanentNineValues]
      have hg3 : g.symm (Finsupp.single (3:Fin 5) 1)=basis .sphere 11 135 3 := hg 3
      have hg4 : g.symm (Finsupp.single (4:Fin 5) 1)=basis .sphere 11 135 4 := hg 4
      fin_cases i
      · change basis .sphere 11 135 3 + basis .sphere 11 135 4 = g.symm (Finsupp.single 3 1 + Finsupp.single 4 1)
        rw [map_add,hg3,hg4]
      · rfl
      · rfl
      · rfl
      · exact hg4.symm
    ext v
    change E.d 4 (9,134) v=0
    obtain ⟨x,hx⟩ := page_has_initial_representative (by decide : (2:ℤ)≤4) v
    have hdx : E.d 2 (9,134) x=0 := represents_d_zero_of_later hs2 (by decide)
      (represents_two_self x) ⟨v,hx⟩
    have hmap : correctionPermanentNineD2 x=0 := by
      change (eqToHom (congrArg (E.Page 2) correctionPermanentNineDegree)) (E.d 2 (9,134) x)=0
      rw [hdx,map_zero]
    have hmap' : correctionPermanentNineD2.hom x=0 := hmap
    have hcoord3 := correctionPermanentImageCoordFive f g correctionPermanentNineD2.hom x 3
    have hcoord4 := correctionPermanentImageCoordFive f g correctionPermanentNineD2.hom x 4
    have hv0 : correctionPermanentNineD2.hom (f.symm (Finsupp.single (0:Fin 5) 1))=g.symm (Finsupp.single 3 1 + Finsupp.single 4 1) := hvals 0
    have hv1 : correctionPermanentNineD2.hom (f.symm (Finsupp.single (1:Fin 5) 1))=0 := hvals 1
    have hv2 : correctionPermanentNineD2.hom (f.symm (Finsupp.single (2:Fin 5) 1))=0 := hvals 2
    have hv3 : correctionPermanentNineD2.hom (f.symm (Finsupp.single (3:Fin 5) 1))=0 := hvals 3
    have hv4 : correctionPermanentNineD2.hom (f.symm (Finsupp.single (4:Fin 5) 1))=g.symm (Finsupp.single 4 1) := hvals 4
    erw [hmap',hv0,hv1,hv2,hv3,hv4] at hcoord3 hcoord4
    norm_num only [map_zero,Finsupp.add_apply,Finsupp.zero_apply,LinearEquiv.apply_symm_apply,
      Finsupp.single_apply,Fin.reduceEq,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_succ,
      ite_true,ite_false,ite_self,add_zero,zero_add] at hcoord3 hcoord4
    norm_num [Fin.ext_iff] at hcoord3 hcoord4
    have c0 : f x 0=0 := by
      by_contra hc
      simpa only [hc,ite_false] using hcoord3
    have c4 : f x 4=0 := by
      by_contra hc
      have hh : (0:F2)=1 := by simpa only [c0,ite_true,hc,ite_false,zero_add] using hcoord4
      exact zero_ne_one hh
    have he := finite_basis_expansion f x
    simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero] at he
    delta Fin.succ at he
    change x=(if f x 0=0 then 0 else f.symm (Finsupp.single 0 1)) +
      ((if f x 1=0 then 0 else f.symm (Finsupp.single 1 1)) +
      ((if f x 2=0 then 0 else f.symm (Finsupp.single 2 1)) +
      ((if f x 3=0 then 0 else f.symm (Finsupp.single 3 1)) +
       (if f x 4=0 then 0 else f.symm (Finsupp.single 4 1))))) at he
    simp only [c0,c4,ite_true,zero_add,add_zero] at he
    have h1 : RepresentsOnPage E 3 (9,134) (f.symm (Finsupp.single 1 1)) a1 := by rw [hf]; exact ha1
    have h2 : RepresentsOnPage E 3 (9,134) (f.symm (Finsupp.single 2 1)) a2 := by rw [hf]; exact ha2
    have h3 : RepresentsOnPage E 3 (9,134) (f.symm (Finsupp.single 3 1)) a3 := by rw [hf]; exact ha3
    have hrep := represents_add_tail (represents_bit (f x 1) h1)
      (represents_add_tail (represents_bit (f x 2) h2) (represents_bit (f x 3) h3))
    rw [←he] at hrep
    obtain ⟨v3,hv3⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤4) hx
    have heq := represents_unique hv3 hrep
    have hvzero : d3 v3=0 := by
      have hz := represents_d_zero_of_later (hs2.trans (by decide : (2:ℤ)≤3))
        (by decide : (3:ℤ)<4) hv3 ⟨v,hx⟩
      change (eqToHom (congrArg (E.Page 3) deg3)) (E.d 3 (9,134) v3)=0
      rw [hz,map_zero]
    have c1 : f x 1=0 := by
      by_contra hc
      rw [heq] at hvzero
      by_cases hc2 : f x 2=0 <;> by_cases hc3 : f x 3=0
      all_goals simp only [hc,hc2,hc3,ite_true,ite_false,map_add,map_zero,hda1,hda2,hda3,zero_add,add_zero] at hvzero
      all_goals exact b0ne hvzero
    have hx5 : ReachesPage E 5 (9,134) x := by
      apply reaches_from_support (by decide : (2:ℤ)≤5) f x
      intro i hi
      fin_cases i
      · exact (hi c0).elim
      · exact (hi c1).elim
      · rw [hf]
        exact reaches_before (by decide) (by decide : (5:ℤ)≤1000) correctionPermanentR224
      · rw [hf]
        exact reaches_before (by decide) (by decide : (5:ℤ)≤7) correctionPermanentR225
      · exact (hi c4).elim
    exact represents_d_zero_of_later (hs2.trans (by decide : (2:ℤ)≤4)) (by decide : (4:ℤ)<5) hx hx5

private theorem correctionLateD157 : HasDifferential model.classical.sphere 3 (4,130) (7,132)
    (basis .sphere 4 130 0) (basis .sphere 7 132 0) := by
  have hrow := result ⟨.sphere, .equation, 3, 4, 130, [0], 7, 132, [0], "S0_AdamsE2_ss", 2437⟩ (by
    exact List.mem_of_getElem? (i := 157) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential model.classical.sphere 3 (4,130) (7,132) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 4 130 [0]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 7 132 [0]=true := rfl
  delta decode at ha hb
  simp (config := { congrConsts := false }) only [vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  exact h

private theorem correctionLateD163 : HasDifferential model.classical.sphere 2 (5,130) (7,131)
    (basis .sphere 5 130 0) (basis .sphere 7 131 2) := by
  have hrow := result ⟨.sphere, .equation, 2, 5, 130, [0], 7, 131, [2], "S0_AdamsE2_ss", 2435⟩ (by
    exact List.mem_of_getElem? (i := 163) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential model.classical.sphere 2 (5,130) (7,131) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 5 130 [0]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 7 131 [2]=true := rfl
  delta decode at ha hb
  simp (config := { congrConsts := false }) only [vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  exact h

private theorem correctionLateLaterZero
    (E : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ×ℤ))
    (N r : ℤ) (hN : 2≤N) (hNr : N≤r) (p : ℤ×ℤ)
    (hz : Subsingleton (E.Page N p)) : Subsingleton (E.Page r p) := by
  have hall (a : E.Page r p) : a=0 := by
    obtain ⟨x,hx⟩ := page_has_initial_representative (hN.trans hNr) a
    obtain ⟨b,hb⟩ := represents_before hN hNr hx
    have hb0 : b=0 := hz.elim _ _
    rw [hb0] at hb
    exact represents_later_zero hNr hb hx
  exact ⟨fun a b => (hall a).trans (hall b).symm⟩

private theorem correctionLateSource6Zero :
    Subsingleton (model.classical.sphere.Page 6 (7,132)) := by
  let E := model.classical.sphere
  have hs2 : E.r₀≤2 := by
    change model.classical.sphere.r₀≤2
    rw [model.classical.firstPage]
  obtain ⟨e,he⟩ := basis_correct ⟨.sphere,7,132,["0,2,340,1"]⟩ (by
    exact List.mem_of_getElem? (i := 149) (by rfl))
  change E.Page 2 (7,132) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e
  change ∀ i : Fin 1, e.symm (Finsupp.single i 1)=basis .sphere 7 132 i.val at he
  have he0 : e.symm (Finsupp.single (0 : Fin 1) 1)=basis .sphere 7 132 0 := he 0
  exact choice_single_basis_zero_page (by decide) e _ he0
    (differential_target_later_zero (hs2.trans (by decide : (2:ℤ)≤3)) (by decide)
      correctionLateD157)

private theorem correctionLateSource8Zero :
    Subsingleton (model.classical.sphere.Page 8 (5,130)) := by
  let E := model.classical.sphere
  have hs2 : E.r₀≤2 := by
    change model.classical.sphere.r₀≤2
    rw [model.classical.firstPage]
  obtain ⟨f,hf⟩ := basis_correct ⟨.sphere,7,131,["353,1", "69,1,75,1", "0,1,339,1"]⟩ (by
    exact List.mem_of_getElem? (i := 148) (by rfl))
  change E.Page 2 (7,131) ≃ₗ[ℤ] (Fin 3 →₀ F2) at f
  change ∀ i : Fin 3, f.symm (Finsupp.single i 1)=basis .sphere 7 131 i.val at hf
  have hf2 : f.symm (Finsupp.single (2 : Fin 3) 1)=basis .sphere 7 131 2 := hf 2
  have targetne : basis .sphere 7 131 2≠0 := by
    rw [←hf2]
    exact basis_vector_ne_zero f 2
  have dnonzero : E.d 2 (5,130) (basis .sphere 5 130 0)≠0 := by
    intro hz
    apply targetne
    rw [←correctionLateD163.eq_on_page_two.2,ModuleCat.comp_apply,hz,map_zero]
  obtain ⟨e,he⟩ := basis_correct ⟨.sphere,5,130,["340,1"]⟩ (by
    exact List.mem_of_getElem? (i := 126) (by rfl))
  change E.Page 2 (5,130) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e
  change ∀ i : Fin 1, e.symm (Finsupp.single i 1)=basis .sphere 5 130 i.val at he
  have he0 : e.symm (Finsupp.single (0 : Fin 1) 1)=basis .sphere 5 130 0 := he 0
  have z3 : Subsingleton (E.Page 3 (5,130)) := by
    apply choice_next_zero_of_single_frame_nonzero_differential (by decide) hs2
      (basis .sphere 5 130 0) dnonzero
    intro x
    apply generated_one (by decide) e _ ?_ x
    rw [he0]
    exact represents_two_self _
  exact correctionLateLaterZero E 3 8 (by decide) (by decide) _ z3


private theorem correctionLate7D157 : HasDifferential model.classical.sphere 3 (4,130) (7,132)
    (basis .sphere 4 130 0) (basis .sphere 7 132 0) := by
  have hrow := result ⟨.sphere, .equation, 3, 4, 130, [0], 7, 132, [0], "S0_AdamsE2_ss", 2437⟩ (by
    exact List.mem_of_getElem? (i := 157) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential model.classical.sphere 3 (4,130) (7,132) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 4 130 [0]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 7 132 [0]=true := rfl
  delta decode at ha hb
  simp (config := { congrConsts := false }) only [vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  exact h

private theorem correctionLate7D171 : HasDifferential model.classical.sphere 4 (6,131) (10,134)
    (basis .sphere 6 131 0) (basis .sphere 10 134 0 + basis .sphere 10 134 3) := by
  have hrow := result ⟨.sphere, .equation, 4, 6, 131, [0], 10, 134, [0, 3], "S0_AdamsE2_ss", 2492⟩ (by
    exact List.mem_of_getElem? (i := 171) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential model.classical.sphere 4 (6,131) (10,134) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 6 131 [0]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 10 134 [0, 3]=true := rfl
  delta decode at ha hb
  simp (config := { congrConsts := false }) only [vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  exact h

private theorem correctionLate7D172 : HasDifferential model.classical.sphere 4 (6,131) (10,134)
    (basis .sphere 6 131 1) (basis .sphere 10 134 0 + (basis .sphere 10 134 1 + (basis .sphere 10 134 3 + basis .sphere 10 134 4))) := by
  have hrow := result ⟨.sphere, .equation, 4, 6, 131, [1], 10, 134, [0, 1, 3, 4], "S0_AdamsE2_ss", 2493⟩ (by
    exact List.mem_of_getElem? (i := 172) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential model.classical.sphere 4 (6,131) (10,134) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 6 131 [1]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 10 134 [0, 1, 3, 4]=true := rfl
  delta decode at ha hb
  simp (config := { congrConsts := false }) only [vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  exact h

private theorem correctionLate7D200 : HasDifferential model.classical.sphere 3 (8,133) (11,135)
    (basis .sphere 8 133 0) (basis .sphere 11 135 0) := by
  have hrow := result ⟨.sphere, .equation, 3, 8, 133, [0], 11, 135, [0], "S0_AdamsE2_ss", 2629⟩ (by
    exact List.mem_of_getElem? (i := 200) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential model.classical.sphere 3 (8,133) (11,135) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 133 [0]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 11 135 [0]=true := rfl
  delta decode at ha hb
  simp (config := { congrConsts := false }) only [vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  exact h

private theorem correctionLate7D201 : HasDifferential model.classical.sphere 2 (8,133) (10,134)
    (basis .sphere 8 133 1) (basis .sphere 10 134 2 + basis .sphere 10 134 4) := by
  have hrow := result ⟨.sphere, .equation, 2, 8, 133, [1], 10, 134, [2, 4], "S0_AdamsE2_ss", 2630⟩ (by
    exact List.mem_of_getElem? (i := 201) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential model.classical.sphere 2 (8,133) (10,134) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 133 [1]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 10 134 [2, 4]=true := rfl
  delta decode at ha hb
  simp (config := { congrConsts := false }) only [vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  exact h

private theorem correctionLate7LaterZero
    (E : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ×ℤ))
    (N r : ℤ) (hN : 2≤N) (hNr : N≤r) (p : ℤ×ℤ)
    (hz : Subsingleton (E.Page N p)) : Subsingleton (E.Page r p) := by
  have hall (a : E.Page r p) : a=0 := by
    obtain ⟨x,hx⟩ := page_has_initial_representative (hN.trans hNr) a
    obtain ⟨b,hb⟩ := represents_before hN hNr hx
    have hb0 : b=0 := hz.elim _ _
    rw [hb0] at hb
    exact represents_later_zero hNr hb hx
  exact ⟨fun a b => (hall a).trans (hall b).symm⟩

private theorem correctionLateSource7Zero :
    Subsingleton (model.classical.sphere.Page 7 (6,131)) := by
  classical
  let E := model.classical.sphere
  have hs2 : E.r₀≤2 := by
    change model.classical.sphere.r₀≤2
    rw [model.classical.firstPage]
  have hs3 : E.r₀≤3 := hs2.trans (by decide)
  have hs4 : E.r₀≤4 := hs2.trans (by decide)
  have d3zero : E.d 3 (7,132)=0 := by
    obtain ⟨e,he⟩ := basis_correct ⟨.sphere,7,132,["0,2,340,1"]⟩ (by
      exact List.mem_of_getElem? (i := 149) (by rfl))
    change E.Page 2 (7,132) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e
    change ∀ i : Fin 1, e.symm (Finsupp.single i 1)=basis .sphere 7 132 i.val at he
    apply d_zero_of_complete_representatives (by decide : (2:ℤ)≤3) e
    intro i
    have hi : i=0 := Subsingleton.elim _ _
    subst i
    have he0 : e.symm (Finsupp.single (0 : Fin 1) 1)=basis .sphere 7 132 0 := he 0
    rw [he0]
    exact differential_target_cycle correctionLate7D157
  obtain ⟨f,hf⟩ := basis_correct ⟨.sphere,8,133,["376,1", "375,1"]⟩ (by
    exact List.mem_of_getElem? (i := 161) (by rfl))
  change E.Page 2 (8,133) ≃ₗ[ℤ] (Fin 2 →₀ F2) at f
  change ∀ i : Fin 2, f.symm (Finsupp.single i 1)=basis .sphere 8 133 i.val at hf
  obtain ⟨g,hg⟩ := basis_correct
    ⟨.sphere,10,134,["389,1", "388,1", "1,1,366,1", "0,1,373,1", "0,2,367,1"]⟩ (by
      exact List.mem_of_getElem? (i := 181) (by rfl))
  change E.Page 2 (10,134) ≃ₗ[ℤ] (Fin 5 →₀ F2) at g
  change ∀ i : Fin 5, g.symm (Finsupp.single i 1)=basis .sphere 10 134 i.val at hg
  have gc (i : Fin 5) : g (basis .sphere 10 134 i.val)=Finsupp.single i 1 := by
    rw [←hg i,LinearEquiv.apply_symm_apply]
  have gc0 : g (basis .sphere 10 134 0)=Finsupp.single (0 : Fin 5) 1 := gc 0
  have gc1 : g (basis .sphere 10 134 1)=Finsupp.single (1 : Fin 5) 1 := gc 1
  have gc2 : g (basis .sphere 10 134 2)=Finsupp.single (2 : Fin 5) 1 := gc 2
  have gc3 : g (basis .sphere 10 134 3)=Finsupp.single (3 : Fin 5) 1 := gc 3
  have gc4 : g (basis .sphere 10 134 4)=Finsupp.single (4 : Fin 5) 1 := gc 4
  let δ : E.Page 2 (8,133) ⟶ E.Page 2 (10,134) :=
    E.d 2 (8,133) ≫ eqToHom (congrArg (E.Page 2) correctionLate7D201.target_degree)
  have d0 : E.d 2 (8,133) (basis .sphere 8 133 0)=0 := by
    obtain ⟨_,a,_,ha,_,_⟩ := correctionLate7D200
    exact represents_d_zero_of_later hs2 (by decide) (represents_two_self _) ⟨a,ha⟩
  have db0 : δ (basis .sphere 8 133 0)=0 := by
    simp only [δ,ModuleCat.comp_apply,d0,map_zero]
  have db1 : δ (basis .sphere 8 133 1)=basis .sphere 10 134 2+basis .sphere 10 134 4 :=
    correctionLate7D201.eq_on_page_two.2
  have columns (i : Fin 2) (j : Fin 5) (hj : j=0 ∨ j=1) :
      g (δ (f.symm (Finsupp.single i 1))) j=0 := by
    rw [hf i]
    fin_cases i
    · rw [db0,map_zero]
      rfl
    · rw [db1,map_add,gc2,gc4]
      rcases hj with rfl|rfl <;> simp only [Finsupp.add_apply,Finsupp.single_apply,Fin.reduceEq,if_true,if_false,zero_add,add_zero] <;> decide
  have incomingcoord (x : E.Page 2 (8,133)) (j : Fin 5) (hj : j=0 ∨ j=1) :
      g (δ x) j=0 := by
    have hx := finite_basis_expansion f x
    simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero] at hx
    rw [hx]
    split_ifs <;> simp only [map_add,map_zero,Finsupp.add_apply,Finsupp.zero_apply,
      columns _ j hj,zero_add,add_zero]
  have deg3 : (7,132)+E.diffDeg 3=(10,134) := by
    simp only [E,ClassicalAdamsFamily.sphere,ClassicalAdamsFamily.obj,
      model.classical.differentialDegree,Prod.mk_add_mk,Int.reduceAdd,Int.reduceSub]
  have targetne {y : E.Page 2 (10,134)} {c4 : E.Page 4 (10,134)}
      (hc4 : RepresentsOnPage E 4 (10,134) y c4)
      (j : Fin 5) (hj : j=0 ∨ j=1) (hcoord : g y j≠0) : c4≠0 := by
    obtain ⟨c3,hc3⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤4) hc4
    have c3ne : c3≠0 := by
      apply represents_next_nonzero_of_not_incoming_at correctionLate7D201.target_degree hs2
        (by decide) hc3 (represents_two_self _)
      intro v hv
      exact hcoord ((congrArg (fun z => g z j) hv).symm.trans (incomingcoord v j hj))
    exact represents_next_nonzero_of_incoming_zero_at hs3 (by decide) d3zero hc4 hc3 c3ne deg3
  obtain ⟨hdeg,a4,c04,ha4,hc04,da⟩ := correctionLate7D171
  obtain ⟨_,b4,c14,hb4,hc14,db⟩ := correctionLate7D172
  have c0ne : c04≠0 := targetne hc04 0 (Or.inl rfl) (by
    rw [map_add,gc0,gc3]
    simp only [Finsupp.add_apply,Finsupp.single_apply,Fin.reduceEq,if_true,if_false,zero_add,add_zero] <;> decide)
  have c1ne : c14≠0 := targetne hc14 1 (Or.inr rfl) (by
    simp only [map_add,gc0,gc1,gc3,gc4]
    simp only [Finsupp.add_apply,Finsupp.single_apply,Fin.reduceEq,if_true,if_false,zero_add,add_zero] <;> decide)
  have csumne : c04+c14≠0 := targetne (represents_add_tail hc04 hc14) 1 (Or.inr rfl) (by
    simp only [map_add,gc0,gc1,gc3,gc4]
    simp only [Finsupp.add_apply,Finsupp.single_apply,Fin.reduceEq,if_true,if_false,zero_add,add_zero] <;> decide)
  obtain ⟨e,he⟩ := basis_correct ⟨.sphere,6,131,["69,1,76,1", "0,1,340,1"]⟩ (by
    exact List.mem_of_getElem? (i := 137) (by rfl))
  change E.Page 2 (6,131) ≃ₗ[ℤ] (Fin 2 →₀ F2) at e
  change ∀ i : Fin 2, e.symm (Finsupp.single i 1)=basis .sphere 6 131 i.val at he
  have he0 : e.symm (Finsupp.single (0 : Fin 2) 1)=basis .sphere 6 131 0 := he 0
  have he1 : e.symm (Finsupp.single (1 : Fin 2) 1)=basis .sphere 6 131 1 := he 1
  have sourcecases (x : E.Page 4 (6,131)) : x=0 ∨ x=a4 ∨ x=b4 ∨ x=a4+b4 := by
    apply generated_two (by decide) e a4 b4 ?_ ?_ x
    · rw [he0]
      exact ha4
    · rw [he1]
      exact hb4
  let δ4 : E.Page 4 (6,131) ⟶ E.Page 4 (10,134) :=
    E.d 4 (6,131) ≫ eqToHom (congrArg (E.Page 4) hdeg)
  have da' : δ4 a4=c04 := da
  have db' : δ4 b4=c14 := db
  have kill (x : E.Page 4 (6,131)) (hx : E.d 4 (6,131) x=0) : δ4 x=0 := by
    simp only [δ4,ModuleCat.comp_apply,hx,map_zero]
  have z5 : Subsingleton (E.Page 5 (6,131)) := by
    apply next_page_zero_of_kernel hs4
    intro x hx
    rcases sourcecases x with hx0|hxa|hxb|hxab
    · exact hx0
    · exact (c0ne (da'.symm.trans (kill a4 (by simpa only [hxa] using hx)))).elim
    · exact (c1ne (db'.symm.trans (kill b4 (by simpa only [hxb] using hx)))).elim
    · have hh : c04+c14=δ4 (a4+b4) := by rw [map_add,da',db']
      exact (csumne (hh.trans (kill (a4+b4) (by simpa only [hxab] using hx)))).elim
  exact correctionLate7LaterZero E 5 7 (by decide) (by decide) _ z5

private theorem correctionPermanentIncomingElevenCoordinate
    (g : model.classical.sphere.Page 2 (11,135) ≃ₗ[ℤ] (Fin 5 →₀ F2))
    (hg : ∀ i : Fin 5, g.symm (Finsupp.single i 1)=basis .sphere 11 135 i.val)
    (x : model.classical.sphere.Page 2 (9,134)) :
    g (correctionPermanentNineD2 x) 0=0 := by
  obtain ⟨f,hf⟩ := basis_correct ⟨.sphere,9,134,["391,1", "390,1", "69,1,82,1", "18,1,190,1", "0,1,375,1"]⟩ (by
    exact List.mem_of_getElem? (i := 173) (by rfl))
  change model.classical.sphere.Page 2 (9,134) ≃ₗ[ℤ] (Fin 5 →₀ F2) at f
  change ∀ i : Fin 5, f.symm (Finsupp.single i 1)=basis .sphere 9 134 i.val at hf
  have hg3 : g.symm (Finsupp.single (3:Fin 5) 1)=basis .sphere 11 135 3 := hg 3
  have hg4 : g.symm (Finsupp.single (4:Fin 5) 1)=basis .sphere 11 135 4 := hg 4
  have each (i : Fin 5) : g (correctionPermanentNineD2 (f.symm (Finsupp.single i 1))) 0=0 := by
    rw [hf,correctionPermanentNineValues]
    fin_cases i
    · change g (basis .sphere 11 135 3 + basis .sphere 11 135 4) 0=0
      rw [←hg3,←hg4,g.map_add,Finsupp.add_apply,LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply]
      simp only [Finsupp.add_apply,Finsupp.single_apply,Fin.reduceEq,if_false,add_zero] <;> decide
    · change g 0 0=0
      exact congrArg (fun y : Fin 5 →₀ F2 => y 0) g.map_zero
    · change g 0 0=0
      exact congrArg (fun y : Fin 5 →₀ F2 => y 0) g.map_zero
    · change g 0 0=0
      exact congrArg (fun y : Fin 5 →₀ F2 => y 0) g.map_zero
    · change g (basis .sphere 11 135 4) 0=0
      rw [←hg4,LinearEquiv.apply_symm_apply]
      simp only [Finsupp.single_apply,Fin.reduceEq,if_false] <;> decide
  rw [correctionPermanentImageCoord f g correctionPermanentNineD2.hom x 0]
  apply Finset.sum_eq_zero
  intro i hi
  by_cases hc : f x i=0
  · simp only [hc,ite_true]
  · simp only [hc,ite_false]
    exact each i

private theorem correctionPermanentSource5Zero :
    Subsingleton (model.classical.sphere.Page 5 (8,133)) := by
  let E := model.classical.sphere
  have hs2 : E.r₀≤2 := by rw [model.classical.firstPage]
  obtain ⟨g,hg⟩ := basis_correct ⟨.sphere,11,135,["411,1", "410,1", "409,1", "0,1,389,1", "0,3,367,1"]⟩ (by
    exact List.mem_of_getElem? (i := 191) (by rfl))
  change E.Page 2 (11,135) ≃ₗ[ℤ] (Fin 5 →₀ F2) at g
  change ∀ i : Fin 5, g.symm (Finsupp.single i 1)=basis .sphere 11 135 i.val at hg
  obtain ⟨deg3,a,c,ha,hc,hd⟩ := correctionLate7D200
  have cne : c≠0 := by
    apply represents_next_nonzero_of_not_incoming_at correctionPermanentNineDegree hs2 (by decide)
      hc (represents_two_self (basis .sphere 11 135 0))
    intro z hz
    change correctionPermanentNineD2 z=basis .sphere 11 135 0 at hz
    have hh := congrArg (fun y => g y 0) hz
    rw [correctionPermanentIncomingElevenCoordinate g hg] at hh
    have hg0 : g.symm (Finsupp.single (0:Fin 5) 1)=basis .sphere 11 135 0 := hg 0
    rw [←hg0,LinearEquiv.apply_symm_apply,Finsupp.single_eq_same] at hh
    exact zero_ne_one hh
  obtain ⟨k,hk⟩ := basis_correct ⟨.sphere,10,134,["389,1", "388,1", "1,1,366,1", "0,1,373,1", "0,2,367,1"]⟩ (by
    exact List.mem_of_getElem? (i := 181) (by rfl))
  change E.Page 2 (10,134) ≃ₗ[ℤ] (Fin 5 →₀ F2) at k
  change ∀ i : Fin 5, k.symm (Finsupp.single i 1)=basis .sphere 10 134 i.val at hk
  have hk2 : k.symm (Finsupp.single (2:Fin 5) 1)=basis .sphere 10 134 2 := hk 2
  have hk4 : k.symm (Finsupp.single (4:Fin 5) 1)=basis .sphere 10 134 4 := hk 4
  have targetne : (basis .sphere 10 134 2 : E.Page 2 (10,134))+basis .sphere 10 134 4≠0 := by
    rw [←hk2,←hk4]
    exact basis_pair_sum_ne_zero k 2 4 (by decide)
  have dnonzero : E.d 2 (8,133) (basis .sphere 8 133 1)≠0 := by
    intro hz
    apply targetne
    rw [←correctionLate7D201.eq_on_page_two.2,ModuleCat.comp_apply,hz,map_zero]
  obtain ⟨f,hf⟩ := basis_correct ⟨.sphere,8,133,["376,1", "375,1"]⟩ (by
    exact List.mem_of_getElem? (i := 161) (by rfl))
  change E.Page 2 (8,133) ≃ₗ[ℤ] (Fin 2 →₀ F2) at f
  change ∀ i : Fin 2, f.symm (Finsupp.single i 1)=basis .sphere 8 133 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 2) 1)=basis .sphere 8 133 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 2) 1)=basis .sphere 8 133 1 := hf 1
  have ha' : RepresentsOnPage E 3 (8,133) (f.symm (Finsupp.single 0 1)) a := by rw [hf0]; exact ha
  have dn : E.d 2 (8,133) (f.symm (Finsupp.single 1 1))≠0 := by rw [hf1]; exact dnonzero
  have ker (v : E.Page 3 (8,133)) (hv : E.d 3 (8,133) v=0) : v=0 := by
    rcases frame_after_second (E := E) (r := 3) (p := (8,133)) hs2 (by decide : (3:ℤ)≤3) f ha' dn v with h0|hva
    · exact h0
    · exfalso
      apply cne
      rw [←hd,ModuleCat.comp_apply]
      have hda : E.d 3 (8,133) a=0 := by simpa only [hva] using hv
      rw [hda,map_zero]
  have hz4 : Subsingleton (E.Page 4 (8,133)) := next_page_zero_of_kernel (E := E) (r := 3) (p := (8,133))
    (hs2.trans (by decide : (2:ℤ)≤3)) ker
  exact correctionLateLaterZero E 4 5 (by decide) (by decide) _ hz4

private theorem correctionPermanentLateIncoming (r : ℤ) (hr : 4≤r) :
    model.classical.sphere.d r (((13:ℤ),137)-model.classical.sphere.diffDeg r)=0 := by
  let E := model.classical.sphere
  have hdeg : ((13:ℤ),137)-E.diffDeg r=(13-r,138-r) := by
    simp only [E,ClassicalAdamsFamily.sphere,ClassicalAdamsFamily.obj,
      model.classical.differentialDegree,Prod.mk_sub_mk]
    congr 1 <;> omega
  by_cases h4 : r=4
  · subst r
    rw [hdeg]
    exact correctionPermanentFourthIncomingZero
  · have hr5 : 5≤r := by omega
    have hz : Subsingleton (E.Page r (13-r,138-r)) := by
      by_cases hn : 14≤r
      · exact KIP126.AdamsSynthetic.Standard.classical_page_negative .sphere r (13-r) (138-r) (by omega)
      · by_cases h9 : 9≤r
        · have initial : Subsingleton (E.Page 2 (13-r,138-r)) := by
            interval_cases r <;> exact correctionPermanentInitialZero _ _ (by decide) (by decide)
          exact correctionPermanentPageZero E r (by omega) _ initial
        · interval_cases r
          · exact correctionPermanentSource5Zero
          · exact correctionLateSource6Zero
          · exact correctionLateSource7Zero
          · exact correctionLateSource8Zero
    rw [hdeg]
    letI := hz
    ext a
    have ha : a=0 := Subsingleton.elim _ _
    simp only [ha,map_zero]

private theorem correctionPermanentCycleCandidate : IsPermanentCycle model.classical.sphere (13,137) correction := by
  let E := model.classical.sphere
  apply isPermanentCycle_of_reachesPage E 1000
    (by change model.classical.sphere.r₀≤1000; rw [model.classical.firstPage]; omega)
    (13,137) correction correctionPermanentReaches1000
  intro r hr
  have hdeg : (13,137)+E.diffDeg r=(13+r,136+r) := by
    simp only [E,ClassicalAdamsFamily.sphere,ClassicalAdamsFamily.obj,
      model.classical.differentialDegree,Prod.mk_add_mk]
    congr 1 <;> omega
  have h2 : Subsingleton (E.Page 2 ((13,137)+E.diffDeg r)) := by
    rw [hdeg]
    exact KIP126.Literature.Standard.sphereVanishing (13+r) (136+r) (by omega) (by omega)
  letI := correctionPermanentPageZero E r (by omega) _ h2
  ext a
  exact Subsingleton.elim _ _

private theorem correctionPermanentCandidate : NonzeroSurvival model.classical.sphere (13,137) correction := by
  exact correctionPermanentNonzeroOfPermanentFinite model.classical.sphere 4
    (by rw [model.classical.firstPage]; omega) (13,137) correction
    correctionPermanentCycleCandidate correctionPermanentSurvivesFour correctionPermanentLateIncoming

/-- The fixed correction survives both early incoming quotients and has a nonzero
common infinite representative, with every later incoming map proved zero. -/
public theorem correction_permanent : NonzeroSurvival model.classical.sphere (13,137) correction := by
  exact correctionPermanentCandidate

private theorem pPermanentPageZero
    (E : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ×ℤ))
    (r : ℤ) (hr : 2 ≤ r) (p : ℤ×ℤ) (h2 : Subsingleton (E.Page 2 p)) :
    Subsingleton (E.Page r p) := by
  have hz (a : E.Page r p) : a=0 := by
    obtain ⟨x,hx⟩ := page_has_initial_representative hr a
    rw [h2.elim x 0] at hx
    exact represents_unique hx (RepresentsOnPage.zero hr)
  exact ⟨fun a b=>(hz a).trans (hz b).symm⟩

private theorem pPermanentInitialZero (s t : ℕ) (ht : t ≤ 261)
    (hdim : basisDimension s t=0) :
    Subsingleton (model.classical.sphere.Page 2 (s,t)) := by
  let e := coordinates s t ht
  have hn : archive.basisCount s t=0 := (archive_dimension s t ht).trans hdim
  haveI : Subsingleton (Fin (archive.basisCount s t) →₀ ZMod 2) := by
    rw [hn]
    infer_instance
  exact e.injective.subsingleton

private theorem pPermanentNonzeroOfPermanentFinite
    (E : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ))
    (N : ℤ) (hN : E.r₀ ≤ N) (p : ℤ × ℤ) (x : E.Page 2 p)
    (hperm : IsPermanentCycle E p x) (hsurv : SurvivesTo E N p x)
    (hin : ∀ r : ℤ, N ≤ r → E.d r (p-E.diffDeg r)=0) :
    NonzeroSurvival E p x := by
  let D := E.ssData p
  let n₂ : WithTop ℕ := ↑(2-E.r₀).toNat
  let n : WithTop ℕ := ↑(N-E.r₀).toNat
  obtain ⟨z,hz⟩ := hperm
  obtain ⟨a,ha,hane⟩ := hsurv
  let zN := Subobject.ofLE (D.Z ⊤) (D.Z n) (D.Z_anti le_top) z
  have hrep : RepresentsOnPage E N p x (D.pageπ n zN) := by
    refine ⟨ha.1,zN,?_,rfl⟩
    dsimp only [zN]
    rw [← CategoryTheory.comp_apply, ← Category.assoc, Subobject.ofLE_comp_ofLE]
    exact hz
  refine ⟨z,hz,?_⟩
  intro hz0
  apply hane
  rw [represents_unique ha hrep]
  have hB : D.B ⊤ = D.B n := boundaries_top_eq_of_d_eq_zero E N hN p hin
  have hb := (subobject_cokernel_π_eq_zero_iff (D.B ⊤) (D.Z ⊤) (D.B_le_Z ⊤) z).mp hz0
  apply (subobject_cokernel_π_eq_zero_iff (D.B n) (D.Z n) (D.B_le_Z n) zN).mpr
  change (Subobject.ofLE (D.Z ⊤) (D.Z n) (D.Z_anti le_top) ≫ (D.Z n).arrow) z ∈ _
  rw [Subobject.ofLE_arrow]
  rwa [← hB]

private theorem pPermanentD220 : HasDifferential model.classical.sphere 3 (9,132) (12,134)
    (basis .sphere 9 132 1) (basis .sphere 12 134 1 + basis .sphere 12 134 2) := by
  have hrow := result ⟨.sphere,.equation,3,9,132,[1],12,134,[1, 2],"S0_AdamsE2_ss",2570⟩ (by
    exact List.mem_of_getElem? (i := 220) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential model.classical.sphere 3 (9,132) (12,134) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 132 [1]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 134 [1, 2]=true := rfl
  delta decode at ha hb
  simp (config := { congrConsts := false }) only [vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  exact h

private theorem pPermanentD267 : HasDifferential model.classical.sphere 3 (8,131) (11,133)
    (basis .sphere 8 131 0) (basis .sphere 11 133 0 + basis .sphere 11 133 1) := by
  have hrow := result ⟨.sphere,.equation,3,8,131,[0],11,133,[0, 1],"S0_AdamsE2_ss",2621⟩ (by
    exact List.mem_of_getElem? (i := 267) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential model.classical.sphere 3 (8,131) (11,133) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 131 [0]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 11 133 [0, 1]=true := rfl
  delta decode at ha hb
  simp (config := { congrConsts := false }) only [vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  exact h

private theorem pPermanentD295 : HasDifferential model.classical.sphere 3 (9,132) (12,134)
    (basis .sphere 9 132 0) (basis .sphere 12 134 1) := by
  have hrow := result ⟨.sphere,.equation,3,9,132,[0],12,134,[1],"S0_AdamsE2_ss",2683⟩ (by
    exact List.mem_of_getElem? (i := 295) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential model.classical.sphere 3 (9,132) (12,134) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 132 [0]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 134 [1]=true := rfl
  delta decode at ha hb
  simp (config := { congrConsts := false }) only [vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  exact h

private theorem pPermanentReaches1000 : ReachesPage model.classical.sphere 1000 (11,133) P := by
  have hrow := result ⟨.sphere,.reaches,1000,11,133,[1],11,133,[],"S0_AdamsE2_ss",2622⟩ (by
    exact List.mem_of_getElem? (i := 268) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,h⟩ := hrow
  have vx : Raw.coordinatesValid Raw.degrees .sphere 11 133 [1]=true := rfl
  delta decode at ha
  simp (config := { congrConsts := false }) only [vx,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha
  rw [←ha,basis_P] at h
  exact h

private theorem pPermanentIncomingTwoZero : model.classical.sphere.d 2 (9,132)=0 := by
  let E := model.classical.sphere
  have hs2 : E.r₀≤2 := by
    change model.classical.sphere.r₀≤2
    rw [model.classical.firstPage]
  obtain ⟨_,a0,_,ha0,_,_⟩ := pPermanentD295
  obtain ⟨_,a1,_,ha1,_,_⟩ := pPermanentD220
  have d0 : E.d 2 (9,132) (basis .sphere 9 132 0)=0 :=
    represents_d_zero_of_later hs2 (by decide) (represents_two_self _) ⟨a0,ha0⟩
  have d1 : E.d 2 (9,132) (basis .sphere 9 132 1)=0 :=
    represents_d_zero_of_later hs2 (by decide) (represents_two_self _) ⟨a1,ha1⟩
  obtain ⟨e,he⟩ := basis_correct ⟨.sphere,9,132,["366,1", "0,1,352,1"]⟩ (by
    exact List.mem_of_getElem? (i := 171) (by rfl))
  change E.Page 2 (9,132) ≃ₗ[ℤ] (Fin 2 →₀ F2) at e
  change ∀ i : Fin 2, e.symm (Finsupp.single i 1)=basis .sphere 9 132 i.val at he
  apply d_zero_of_complete_representatives (by decide : (2:ℤ)≤2) e
  intro i
  refine ⟨e.symm (Finsupp.single i 1),represents_two_self _,?_⟩
  rw [he i]
  fin_cases i
  · exact d0
  · exact d1

private theorem pPermanentSurvivesFour : SurvivesTo model.classical.sphere 4 (11,133) P := by
  classical
  let E := model.classical.sphere
  have hs2 : E.r₀≤2 := by
    change model.classical.sphere.r₀≤2
    rw [model.classical.firstPage]
  obtain ⟨p4,hp4⟩ := reaches_before (by decide : (2:ℤ)≤4) (by decide : (4:ℤ)≤1000)
    pPermanentReaches1000
  obtain ⟨p3,hp3⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤4) hp4
  obtain ⟨hdeg,a3,c3,ha3,hc3,hd3⟩ := pPermanentD267
  obtain ⟨e,he⟩ := basis_correct ⟨.sphere,11,133,["371,1", "69,1,79,1"]⟩ (by
    exact List.mem_of_getElem? (i := 189) (by rfl))
  change E.Page 2 (11,133) ≃ₗ[ℤ] (Fin 2 →₀ F2) at e
  change ∀ i : Fin 2, e.symm (Finsupp.single i 1)=basis .sphere 11 133 i.val at he
  have he0 : e.symm (Finsupp.single (0 : Fin 2) 1)=basis .sphere 11 133 0 := he 0
  have he1 : e.symm (Finsupp.single (1 : Fin 2) 1)=basis .sphere 11 133 1 := he 1
  let b0 : E.Page 2 (11,133) := basis .sphere 11 133 0
  let b1 : E.Page 2 (11,133) := basis .sphere 11 133 1
  let c2 : E.Page 2 (11,133) := basis .sphere 11 133 0+basis .sphere 11 133 1
  have b0ne : b0≠0 := by
    change basis .sphere 11 133 0≠0
    rw [←he0]
    exact basis_vector_ne_zero e 0
  have pne : P≠0 := by
    rw [←basis_P,←he1]
    exact basis_vector_ne_zero e 1
  have diffne : P-c2≠0 := by
    have hp1 : P=b1 := basis_P.symm
    have hc : c2=b0+b1 := rfl
    rw [hp1,hc]
    have heq : b1-(b0+b1) = -b0 := by abel
    rw [heq]
    exact neg_ne_zero.mpr b0ne
  have deg2 : (9,132)+E.diffDeg 2=(11,133) := by
    simp only [E,ClassicalAdamsFamily.sphere,ClassicalAdamsFamily.obj,
      model.classical.differentialDegree,Prod.mk_add_mk,Int.reduceAdd,Int.reduceSub]
  have p3ne : p3≠0 := represents_next_nonzero_of_incoming_zero_at hs2 (by decide)
    pPermanentIncomingTwoZero hp3 (represents_two_self P) pne deg2
  have diff3ne : p3-c3≠0 := represents_next_nonzero_of_incoming_zero_at hs2 (by decide)
    pPermanentIncomingTwoZero (represents_sub hp3 hc3) (represents_two_self _) diffne deg2
  obtain ⟨f,hf⟩ := basis_correct ⟨.sphere,8,131,["352,1"]⟩ (by
    exact List.mem_of_getElem? (i := 159) (by rfl))
  change E.Page 2 (8,131) ≃ₗ[ℤ] (Fin 1 →₀ F2) at f
  change ∀ i : Fin 1, f.symm (Finsupp.single i 1)=basis .sphere 8 131 i.val at hf
  have sourcecases (v : E.Page 3 (8,131)) : v=0 ∨ v=a3 := by
    obtain ⟨x,hx⟩ := page_has_initial_representative (by decide : (2:ℤ)≤3) v
    have hex := finite_basis_expansion f x
    simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,hf,add_zero] at hex
    change x=(if f x 0=0 then 0 else basis .sphere 8 131 0) at hex
    by_cases hz : f x 0=0
    · left
      have hx0 : x=0 := by simpa only [hz,ite_true] using hex
      rw [hx0] at hx
      exact represents_unique hx (RepresentsOnPage.zero (by decide))
    · right
      have hx0 : x=basis .sphere 8 131 0 := by simpa only [hz,ite_false] using hex
      rw [hx0] at hx
      exact represents_unique hx ha3
  have himage (v : E.Page 3 (8,131)) :
      (E.d 3 (8,131) ≫ eqToHom (congrArg (E.Page 3) hdeg)) v=0 ∨
      (E.d 3 (8,131) ≫ eqToHom (congrArg (E.Page 3) hdeg)) v=c3 := by
    rcases sourcecases v with rfl|rfl
    · left
      exact map_zero _
    · exact Or.inr hd3
  refine ⟨p4,hp4,?_⟩
  exact represents_next_nonzero_of_incoming_two_cases_at hdeg
    (hs2.trans (by decide : (2:ℤ)≤3)) (by decide) hp4 hp3 himage p3ne diff3ne

private theorem pPermanentLateIncoming (r : ℤ) (hr : 4≤r) :
    model.classical.sphere.d r (((11:ℤ),133)-model.classical.sphere.diffDeg r)=0 := by
  let E := model.classical.sphere
  have hdeg : ((11:ℤ),133)-E.diffDeg r=(11-r,134-r) := by
    simp only [E,ClassicalAdamsFamily.sphere,ClassicalAdamsFamily.obj,
      model.classical.differentialDegree,Prod.mk_sub_mk]
    congr 1 <;> omega
  have hz : Subsingleton (E.Page r (11-r,134-r)) := by
    by_cases hhigh : 12≤r
    · exact KIP126.AdamsSynthetic.Standard.classical_page_negative .sphere r (11-r) (134-r) (by omega)
    · have initial : Subsingleton (E.Page 2 (11-r,134-r)) := by
        interval_cases r <;> exact pPermanentInitialZero _ _ (by decide) (by decide)
      exact pPermanentPageZero E r (by omega) _ initial
  rw [hdeg]
  letI := hz
  ext a
  have ha : a=0 := Subsingleton.elim _ _
  simp only [ha,map_zero]

private theorem pPermanentCycleCandidate : IsPermanentCycle model.classical.sphere (11,133) P := by
  let E := model.classical.sphere
  apply isPermanentCycle_of_reachesPage E 1000
    (by change model.classical.sphere.r₀≤1000; rw [model.classical.firstPage]; omega)
    (11,133) P pPermanentReaches1000
  intro r hr
  have hdeg : (11,133)+E.diffDeg r=(11+r,132+r) := by
    simp only [E,ClassicalAdamsFamily.sphere,ClassicalAdamsFamily.obj,
      model.classical.differentialDegree,Prod.mk_add_mk]
    congr 1 <;> omega
  have h2 : Subsingleton (E.Page 2 ((11,133)+E.diffDeg r)) := by
    rw [hdeg]
    exact KIP126.Literature.Standard.sphereVanishing (11+r) (132+r) (by omega) (by omega)
  letI := pPermanentPageZero E r (by omega) _ h2
  ext a
  exact Subsingleton.elim _ _

private theorem pPermanentCandidate : NonzeroSurvival model.classical.sphere (11,133) P := by
  exact pPermanentNonzeroOfPermanentFinite model.classical.sphere 4
    (by rw [model.classical.firstPage]; omega) (11,133) P
    pPermanentCycleCandidate pPermanentSurvivesFour pPermanentLateIncoming

/-- The same archived P has a nonzero fourth-page continuation and one common
infinite-cycle representative; every later incoming differential has zero source. -/
public theorem p_permanent : NonzeroSurvival model.classical.sphere (11,133) P := by
  exact pPermanentCandidate

private theorem qPermanentPageZero
    (E : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ×ℤ))
    (r : ℤ) (hr : 2 ≤ r) (p : ℤ×ℤ) (h2 : Subsingleton (E.Page 2 p)) :
    Subsingleton (E.Page r p) := by
  have hz (a : E.Page r p) : a=0 := by
    obtain ⟨x,hx⟩ := page_has_initial_representative hr a
    rw [h2.elim x 0] at hx
    exact represents_unique hx (RepresentsOnPage.zero hr)
  exact ⟨fun a b=>(hz a).trans (hz b).symm⟩

private theorem qPermanentInitialZero (s t : ℕ) (ht : t ≤ 261)
    (hdim : basisDimension s t=0) :
    Subsingleton (model.classical.sphere.Page 2 (s,t)) := by
  let e := coordinates s t ht
  have hn : archive.basisCount s t=0 := (archive_dimension s t ht).trans hdim
  haveI : Subsingleton (Fin (archive.basisCount s t) →₀ ZMod 2) := by
    rw [hn]
    infer_instance
  exact e.injective.subsingleton

private theorem qPermanentNonzeroOfPermanentFinite
    (E : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ))
    (N : ℤ) (hN : E.r₀ ≤ N) (p : ℤ × ℤ) (x : E.Page 2 p)
    (hperm : IsPermanentCycle E p x) (hsurv : SurvivesTo E N p x)
    (hin : ∀ r : ℤ, N ≤ r → E.d r (p-E.diffDeg r)=0) :
    NonzeroSurvival E p x := by
  let D := E.ssData p
  let n₂ : WithTop ℕ := ↑(2-E.r₀).toNat
  let n : WithTop ℕ := ↑(N-E.r₀).toNat
  obtain ⟨z,hz⟩ := hperm
  obtain ⟨a,ha,hane⟩ := hsurv
  let zN := Subobject.ofLE (D.Z ⊤) (D.Z n) (D.Z_anti le_top) z
  have hrep : RepresentsOnPage E N p x (D.pageπ n zN) := by
    refine ⟨ha.1,zN,?_,rfl⟩
    dsimp only [zN]
    rw [← CategoryTheory.comp_apply, ← Category.assoc, Subobject.ofLE_comp_ofLE]
    exact hz
  refine ⟨z,hz,?_⟩
  intro hz0
  apply hane
  rw [represents_unique ha hrep]
  have hB : D.B ⊤ = D.B n := boundaries_top_eq_of_d_eq_zero E N hN p hin
  have hb := (subobject_cokernel_π_eq_zero_iff (D.B ⊤) (D.Z ⊤) (D.B_le_Z ⊤) z).mp hz0
  apply (subobject_cokernel_π_eq_zero_iff (D.B n) (D.Z n) (D.B_le_Z n) zN).mpr
  change (Subobject.ofLE (D.Z ⊤) (D.Z n) (D.Z_anti le_top) ≫ (D.Z n).arrow) z ∈ _
  rw [Subobject.ofLE_arrow]
  rwa [← hB]

private theorem qPermanentD220 : HasDifferential model.classical.sphere 3 (9,132) (12,134)
    (basis .sphere 9 132 1) (basis .sphere 12 134 1 + basis .sphere 12 134 2) := by
  have hrow := result ⟨.sphere,.equation,3,9,132,[1],12,134,[1, 2],"S0_AdamsE2_ss",2570⟩ (by
    exact List.mem_of_getElem? (i := 220) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential model.classical.sphere 3 (9,132) (12,134) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 132 [1]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 134 [1, 2]=true := rfl
  delta decode at ha hb
  simp (config := { congrConsts := false }) only [vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  exact h

private theorem qPermanentD295 : HasDifferential model.classical.sphere 3 (9,132) (12,134)
    (basis .sphere 9 132 0) (basis .sphere 12 134 1) := by
  have hrow := result ⟨.sphere,.equation,3,9,132,[0],12,134,[1],"S0_AdamsE2_ss",2683⟩ (by
    exact List.mem_of_getElem? (i := 295) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential model.classical.sphere 3 (9,132) (12,134) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 132 [0]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 134 [1]=true := rfl
  delta decode at ha hb
  simp (config := { congrConsts := false }) only [vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  exact h

private theorem qSourceD220 : HasDifferential model.classical.sphere 3 (9,132) (12,134)
    (basis .sphere 9 132 1) (basis .sphere 12 134 1 + basis .sphere 12 134 2) := by
  have hrow := result ⟨.sphere,.equation,3,9,132,[1],12,134,[1, 2],"S0_AdamsE2_ss",2570⟩ (by
    exact List.mem_of_getElem? (i := 220) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential model.classical.sphere 3 (9,132) (12,134) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 132 [1]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 134 [1, 2]=true := rfl
  delta decode at ha hb
  simp (config := { congrConsts := false }) only [vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  exact h

private theorem qSourceD267 : HasDifferential model.classical.sphere 3 (8,131) (11,133)
    (basis .sphere 8 131 0) (basis .sphere 11 133 0 + basis .sphere 11 133 1) := by
  have hrow := result ⟨.sphere,.equation,3,8,131,[0],11,133,[0, 1],"S0_AdamsE2_ss",2621⟩ (by
    exact List.mem_of_getElem? (i := 267) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential model.classical.sphere 3 (8,131) (11,133) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 131 [0]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 11 133 [0, 1]=true := rfl
  delta decode at ha hb
  simp (config := { congrConsts := false }) only [vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  exact h

private theorem qSourceD295 : HasDifferential model.classical.sphere 3 (9,132) (12,134)
    (basis .sphere 9 132 0) (basis .sphere 12 134 1) := by
  have hrow := result ⟨.sphere,.equation,3,9,132,[0],12,134,[1],"S0_AdamsE2_ss",2683⟩ (by
    exact List.mem_of_getElem? (i := 295) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential model.classical.sphere 3 (9,132) (12,134) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 132 [0]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 134 [1]=true := rfl
  delta decode at ha hb
  simp (config := { congrConsts := false }) only [vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  exact h

private theorem qSourceIncomingTwoZero : model.classical.sphere.d 2 (9,132)=0 := by
  let E := model.classical.sphere
  have hs2 : E.r₀≤2 := by
    change model.classical.sphere.r₀≤2
    rw [model.classical.firstPage]
  obtain ⟨_,a0,_,ha0,_,_⟩ := qSourceD295
  obtain ⟨_,a1,_,ha1,_,_⟩ := qSourceD220
  have d0 : E.d 2 (9,132) (basis .sphere 9 132 0)=0 :=
    represents_d_zero_of_later hs2 (by decide) (represents_two_self _) ⟨a0,ha0⟩
  have d1 : E.d 2 (9,132) (basis .sphere 9 132 1)=0 :=
    represents_d_zero_of_later hs2 (by decide) (represents_two_self _) ⟨a1,ha1⟩
  obtain ⟨e,he⟩ := basis_correct ⟨.sphere,9,132,["366,1", "0,1,352,1"]⟩ (by
    exact List.mem_of_getElem? (i := 171) (by rfl))
  change E.Page 2 (9,132) ≃ₗ[ℤ] (Fin 2 →₀ F2) at e
  change ∀ i : Fin 2, e.symm (Finsupp.single i 1)=basis .sphere 9 132 i.val at he
  apply d_zero_of_complete_representatives (by decide : (2:ℤ)≤2) e
  intro i
  refine ⟨e.symm (Finsupp.single i 1),represents_two_self _,?_⟩
  rw [he i]
  fin_cases i
  · exact d0
  · exact d1

private theorem qPermanentSourceE4Zero :
    Subsingleton (model.classical.sphere.Page 4 (8,131)) := by
  classical
  let E := model.classical.sphere
  have hs2 : E.r₀≤2 := by
    change model.classical.sphere.r₀≤2
    rw [model.classical.firstPage]
  obtain ⟨hdeg,a3,c3,ha3,hc3,hd3⟩ := qSourceD267
  obtain ⟨e,he⟩ := basis_correct ⟨.sphere,11,133,["371,1", "69,1,79,1"]⟩ (by
    exact List.mem_of_getElem? (i := 189) (by rfl))
  change E.Page 2 (11,133) ≃ₗ[ℤ] (Fin 2 →₀ F2) at e
  change ∀ i : Fin 2, e.symm (Finsupp.single i 1)=basis .sphere 11 133 i.val at he
  have he0 : e.symm (Finsupp.single (0 : Fin 2) 1)=basis .sphere 11 133 0 := he 0
  have he1 : e.symm (Finsupp.single (1 : Fin 2) 1)=basis .sphere 11 133 1 := he 1
  have c2ne : basis .sphere 11 133 0+basis .sphere 11 133 1≠0 := by
    rw [←he0,←he1]
    exact basis_pair_sum_ne_zero e 0 1 (by decide)
  have deg2 : (9,132)+E.diffDeg 2=(11,133) := by
    simp only [E,ClassicalAdamsFamily.sphere,ClassicalAdamsFamily.obj,
      model.classical.differentialDegree,Prod.mk_add_mk,Int.reduceAdd,Int.reduceSub]
  have c3ne : c3≠0 := represents_next_nonzero_of_incoming_zero_at hs2 (by decide)
    qSourceIncomingTwoZero hc3 (represents_two_self _) c2ne deg2
  obtain ⟨f,hf⟩ := basis_correct ⟨.sphere,8,131,["352,1"]⟩ (by
    exact List.mem_of_getElem? (i := 159) (by rfl))
  change E.Page 2 (8,131) ≃ₗ[ℤ] (Fin 1 →₀ F2) at f
  change ∀ i : Fin 1, f.symm (Finsupp.single i 1)=basis .sphere 8 131 i.val at hf
  have sourcecases (v : E.Page 3 (8,131)) : v=0 ∨ v=a3 := by
    obtain ⟨x,hx⟩ := page_has_initial_representative (by decide : (2:ℤ)≤3) v
    have hex := finite_basis_expansion f x
    simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,hf,add_zero] at hex
    change x=(if f x 0=0 then 0 else basis .sphere 8 131 0) at hex
    by_cases hz : f x 0=0
    · left
      have hx0 : x=0 := by simpa only [hz,ite_true] using hex
      rw [hx0] at hx
      exact represents_unique hx (RepresentsOnPage.zero (by decide))
    · right
      have hx0 : x=basis .sphere 8 131 0 := by simpa only [hz,ite_false] using hex
      rw [hx0] at hx
      exact represents_unique hx ha3
  apply next_page_zero_of_kernel (hs2.trans (by decide : (2:ℤ)≤3))
  intro x hx
  rcases sourcecases x with hx0|hxa
  · exact hx0
  · subst x
    exfalso
    apply c3ne
    rw [←hd3,ModuleCat.comp_apply,hx,map_zero]

private theorem qPermanentD294 : HasDifferential model.classical.sphere 2 (10,133) (12,134)
    (basis .sphere 10 133 0) (basis .sphere 12 134 2) := by
  have hrow := result ⟨.sphere,.equation,2,10,133,[0],12,134,[2],"S0_AdamsE2_ss",2682⟩ (by
    exact List.mem_of_getElem? (i := 294) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential model.classical.sphere 2 (10,133) (12,134) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 133 [0]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 134 [2]=true := rfl
  delta decode at ha hb
  simp (config := { congrConsts := false }) only [vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  exact h

private theorem qPermanentD245 : HasDifferential model.classical.sphere 2 (10,133) (12,134)
    (basis .sphere 10 133 1) (basis .sphere 12 134 2) := by
  have hrow := result ⟨.sphere,.equation,2,10,133,[1],12,134,[2],"S0_AdamsE2_ss",2625⟩ (by
    exact List.mem_of_getElem? (i := 245) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential model.classical.sphere 2 (10,133) (12,134) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 133 [1]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 134 [2]=true := rfl
  delta decode at ha hb
  simp (config := { congrConsts := false }) only [vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  exact h

private theorem qPermanentD199 : HasDifferential model.classical.sphere 2 (8,132) (10,133)
    (basis .sphere 8 132 0) (basis .sphere 10 133 2) := by
  have hrow := result ⟨.sphere,.equation,2,8,132,[0],10,133,[2],"S0_AdamsE2_ss",2571⟩ (by
    exact List.mem_of_getElem? (i := 199) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential model.classical.sphere 2 (8,132) (10,133) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 132 [0]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 10 133 [2]=true := rfl
  delta decode at ha hb
  simp (config := { congrConsts := false }) only [vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  exact h

private theorem qPermanentReaches1000 : ReachesPage model.classical.sphere 1000 (12,134) Q := by
  have hrow := result ⟨.sphere,.reaches,1000,12,134,[0],12,134,[],"S0_AdamsE2_ss",2684⟩ (by
    exact List.mem_of_getElem? (i := 296) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,h⟩ := hrow
  have vx : Raw.coordinatesValid Raw.degrees .sphere 12 134 [0]=true := rfl
  delta decode at ha
  simp (config := { congrConsts := false }) only [vx,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha
  rw [←ha,basis_Q] at h
  exact h

private theorem qPermanentSurvivesFour : SurvivesTo model.classical.sphere 4 (12,134) Q := by
  classical
  let E := model.classical.sphere
  have hs2 : E.r₀≤2 := by
    change model.classical.sphere.r₀≤2
    rw [model.classical.firstPage]
  obtain ⟨q4,hq4⟩ := reaches_before (by decide : (2:ℤ)≤4) (by decide : (4:ℤ)≤1000)
    qPermanentReaches1000
  obtain ⟨q3,hq3⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤4) hq4
  obtain ⟨e,he⟩ := basis_correct ⟨.sphere,12,134,["18,1,188,1", "0,1,371,1", "0,1,69,1,79,1"]⟩ (by
    exact List.mem_of_getElem? (i := 198) (by rfl))
  change E.Page 2 (12,134) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e
  change ∀ i : Fin 3, e.symm (Finsupp.single i 1)=basis .sphere 12 134 i.val at he
  let b1 : E.Page 2 (12,134) := basis .sphere 12 134 1
  let b2 : E.Page 2 (12,134) := basis .sphere 12 134 2
  have heQ : e.symm (Finsupp.single (0 : Fin 3) 1)=Q := (he 0).trans basis_Q
  have heB1 : e.symm (Finsupp.single (1 : Fin 3) 1)=b1 := he 1
  have heB2 : e.symm (Finsupp.single (2 : Fin 3) 1)=b2 := he 2
  have eQ : e Q 0=1 := by
    rw [←heQ,LinearEquiv.apply_symm_apply]
    simp only [Finsupp.single_eq_same]
  have eb1 : e b1 0=0 := by
    rw [←heB1,LinearEquiv.apply_symm_apply]
    simp only [Finsupp.single_apply,show (1 : Fin 3) ≠ 0 by decide,ite_false]
  have eb2 : e b2 0=0 := by
    rw [←heB2,LinearEquiv.apply_symm_apply]
    simp only [Finsupp.single_apply,show (2 : Fin 3) ≠ 0 by decide,ite_false]
  have deg2 : (10,133)+E.diffDeg 2=(12,134) := by
    simp only [E,ClassicalAdamsFamily.sphere,ClassicalAdamsFamily.obj,
      model.classical.differentialDegree,Prod.mk_add_mk,Int.reduceAdd,Int.reduceSub]
  let d2 : E.Page 2 (10,133) ⟶ E.Page 2 (12,134) :=
    E.d 2 (10,133) ≫ eqToHom (congrArg (E.Page 2) deg2)
  have d20 : d2 (basis .sphere 10 133 0)=b2 := qPermanentD294.eq_on_page_two.choose_spec
  have d21 : d2 (basis .sphere 10 133 1)=b2 := qPermanentD245.eq_on_page_two.choose_spec
  obtain ⟨z2,hz2,hdz2⟩ := differential_target_cycle qPermanentD199
  rw [←hz2.eq_on_page_two] at hdz2
  have d22 : d2 (basis .sphere 10 133 2)=0 := by
    change (eqToHom (congrArg (E.Page 2) deg2)) (E.d 2 (10,133) (basis .sphere 10 133 2))=0
    rw [hdz2,map_zero]
  obtain ⟨f,hf⟩ := basis_correct ⟨.sphere,10,133,["372,1", "69,1,80,1", "0,1,366,1"]⟩ (by
    exact List.mem_of_getElem? (i := 180) (by rfl))
  change E.Page 2 (10,133) ≃ₗ[ℤ] (Fin 3 →₀ F2) at f
  change ∀ i : Fin 3, f.symm (Finsupp.single i 1)=basis .sphere 10 133 i.val at hf
  have each0 (i : Fin 3) : e (d2 (f.symm (Finsupp.single i 1))) 0=0 := by
    rw [hf i]
    fin_cases i
    · rw [d20]; exact eb2
    · rw [d21]; exact eb2
    · rw [d22]
      exact congrArg (fun z : Fin 3 →₀ F2 => z 0) e.map_zero
  have image0 (v : E.Page 2 (10,133)) : e (d2 v) 0=0 := by
    have hex := finite_basis_expansion f v
    rw [hex]
    simp only [map_sum,Finsupp.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro i hi
    by_cases hc : f v i=0
    · simp only [hc,ite_true,map_zero,Finsupp.zero_apply]
    · simp only [hc,ite_false]
      exact each0 i
  have avoid (y : E.Page 2 (12,134)) (hy : e y 0=1) (v : E.Page 2 (10,133)) : d2 v≠y := by
    intro h
    have hh := congrArg (fun t => e t 0) h
    rw [image0,hy] at hh
    exact zero_ne_one hh
  obtain ⟨deg3,a0,c0,ha0,hc0,hd0⟩ := qPermanentD295
  obtain ⟨_,a1,c1,ha1,hc1,hd1⟩ := qPermanentD220
  have q3ne : q3≠0 := represents_next_nonzero_of_not_incoming_at deg2 hs2 (by decide)
    hq3 (represents_two_self Q) (avoid Q eQ)
  have diff2 : e (Q-b1) 0=1 := by
    rw [map_sub,Finsupp.sub_apply,eQ,eb1,sub_zero]
  have diff3 : q3-c0≠0 := represents_next_nonzero_of_not_incoming_at deg2 hs2 (by decide)
    (represents_sub hq3 hc0) (represents_two_self (Q-b1)) (avoid (Q-b1) diff2)
  have bz : RepresentsOnPage E 3 (12,134) b2 0 :=
    differential_target_later_zero hs2 (by decide) qPermanentD294
  have c1eq : c1=c0 := by
    have hsum := represents_add_tail hc0 bz
    simp only [add_zero] at hsum
    exact represents_unique hc1 hsum
  have b1two : b1+b1=0 := by
    rw [←heB1,←map_add,←Finsupp.single_add]
    have hh : (1 : F2)+1=0 := rfl
    rw [hh,Finsupp.single_zero,map_zero]
  have c0two : c0+c0=0 := by
    have h := represents_add_tail hc0 hc0
    change RepresentsOnPage E 3 (12,134) (b1+b1) (c0+c0) at h
    rw [b1two] at h
    exact represents_unique h (RepresentsOnPage.zero (by decide))
  obtain ⟨g,hg⟩ := basis_correct ⟨.sphere,9,132,["366,1", "0,1,352,1"]⟩ (by
    exact List.mem_of_getElem? (i := 171) (by rfl))
  change E.Page 2 (9,132) ≃ₗ[ℤ] (Fin 2 →₀ F2) at g
  change ∀ i : Fin 2, g.symm (Finsupp.single i 1)=basis .sphere 9 132 i.val at hg
  have ga0 : RepresentsOnPage E 3 (9,132) (g.symm (Finsupp.single 0 1)) a0 := by rw [hg]; exact ha0
  have ga1 : RepresentsOnPage E 3 (9,132) (g.symm (Finsupp.single 1 1)) a1 := by rw [hg]; exact ha1
  have image3 (v : E.Page 3 (9,132)) :
      (E.d 3 (9,132) ≫ eqToHom (congrArg (E.Page 3) deg3)) v=0 ∨
      (E.d 3 (9,132) ≫ eqToHom (congrArg (E.Page 3) deg3)) v=c0 := by
    rcases generated_two (by decide : (2:ℤ)≤3) g a0 a1 ga0 ga1 v with h|h|h|h
    · rw [h,map_zero]; exact Or.inl rfl
    · rw [h,hd0]; exact Or.inr rfl
    · rw [h,hd1,c1eq]; exact Or.inr rfl
    · rw [h,map_add,hd0,hd1,c1eq,c0two]; exact Or.inl rfl
  exact ⟨q4,hq4,represents_next_nonzero_of_incoming_two_cases_at deg3
    (hs2.trans (by decide : (2:ℤ)≤3)) (by decide) hq4 hq3 image3 q3ne diff3⟩

private theorem qPermanentLateIncoming (r : ℤ) (hr : 4≤r) :
    model.classical.sphere.d r (((12:ℤ),134)-model.classical.sphere.diffDeg r)=0 := by
  let E := model.classical.sphere
  have hdeg : ((12:ℤ),134)-E.diffDeg r=(12-r,135-r) := by
    simp only [E,ClassicalAdamsFamily.sphere,ClassicalAdamsFamily.obj,
      model.classical.differentialDegree,Prod.mk_sub_mk]
    congr 1 <;> omega
  have hz : Subsingleton (E.Page r (12-r,135-r)) := by
    by_cases h4 : r=4
    · subst r
      exact qPermanentSourceE4Zero
    · by_cases hhigh : 13≤r
      · exact KIP126.AdamsSynthetic.Standard.classical_page_negative .sphere r (12-r) (135-r) (by omega)
      · have hr5 : 5≤r := by omega
        have initial : Subsingleton (E.Page 2 (12-r,135-r)) := by
          interval_cases r <;> exact qPermanentInitialZero _ _ (by decide) (by decide)
        exact qPermanentPageZero E r (by omega) _ initial
  rw [hdeg]
  letI := hz
  ext a
  have ha : a=0 := Subsingleton.elim _ _
  simp only [ha,map_zero]

private theorem qPermanentCycleCandidate : IsPermanentCycle model.classical.sphere (12,134) Q := by
  let E := model.classical.sphere
  apply isPermanentCycle_of_reachesPage E 1000
    (by change model.classical.sphere.r₀≤1000; rw [model.classical.firstPage]; omega)
    (12,134) Q qPermanentReaches1000
  intro r hr
  have hdeg : (12,134)+E.diffDeg r=(12+r,133+r) := by
    simp only [E,ClassicalAdamsFamily.sphere,ClassicalAdamsFamily.obj,
      model.classical.differentialDegree,Prod.mk_add_mk]
    congr 1 <;> omega
  have h2 : Subsingleton (E.Page 2 ((12,134)+E.diffDeg r)) := by
    rw [hdeg]
    exact KIP126.Literature.Standard.sphereVanishing (12+r) (133+r) (by omega) (by omega)
  letI := qPermanentPageZero E r (by omega) _ h2
  ext a
  exact Subsingleton.elim _ _

private theorem qPermanentCandidate : NonzeroSurvival model.classical.sphere (12,134) Q := by
  exact qPermanentNonzeroOfPermanentFinite model.classical.sphere 4
    (by rw [model.classical.firstPage]; omega) (12,134) Q
    qPermanentCycleCandidate qPermanentSurvivesFour qPermanentLateIncoming

/-- The fixed Q remains nonzero through both incoming boundary quotients and
has one common infinite representative, with no later incoming differential. -/
public theorem q_permanent : NonzeroSurvival model.classical.sphere (12,134) Q := by
  exact qPermanentCandidate

private theorem h2Boundary_p_basis : product (r := (12,137)) P h2 =
    basis .sphere 12 137 2 := by
  let c := generatorImage 89 10 72
  have hm : product (r := (11,73)) h2 (atom .M_mul_d_0) =
      product (r := (11,73)) h0 c := by
    simpa only [Expression.value, Expression.degree, atom_h2, atom_h0] using
      h2_obstruction_rel1
  have hcomm₁ : product (r := (11,73)) (atom .M_mul_d_0) h2 =
      product (r := (11,73)) h2 (atom .M_mul_d_0) := by
    exact product_comm 10 69 1 4 (by decide) _ _
  have hcomm₂ : product (r := (2,65)) h6 h0 =
      product (r := (2,65)) h0 h6 := by
    exact product_comm 1 64 1 1 (by decide) _ _
  have hassoc₁ : product (r := (12,137)) P h2 =
      product (r := (12,137)) h6
        (product (r := (11,73)) (atom .M_mul_d_0) h2) := by
    exact eq_of_heq (model.sphereAlgebra.assoc (1,64) (10,69) (1,4)
      h6 (atom .M_mul_d_0) h2)
  have hassoc₂ : product (r := (12,137))
      (product (r := (2,65)) h6 h0) c =
      product (r := (12,137)) h6 (product (r := (11,73)) h0 c) := by
    exact eq_of_heq (model.sphereAlgebra.assoc (1,64) (1,1) (10,72) h6 h0 c)
  have hassoc₃ : product (r := (12,137))
      (product (r := (2,65)) h0 h6) c =
      product (r := (12,137)) h0 (product (r := (11,136)) h6 c) := by
    exact eq_of_heq (model.sphereAlgebra.assoc (1,1) (1,64) (10,72) h0 h6 c)
  have hb : basis .sphere 12 137 2 =
      product (r := (12,137)) h0 (product (r := (11,136)) h6 c) := by
    have h := basis_value ⟨.mul (.named .h0) (.mul (.named .h6) (.generator 89 10 72)),2⟩
      (by decide)
    simpa only [Expression.value, Expression.degree, atom_h0, atom_h6] using h
  rw [hassoc₁, hcomm₁, hm, ← hassoc₂, hcomm₂, hassoc₃, ← hb]

private theorem h2Boundary_basis_12_137_2 :
    IsBoundaryBy model.classical.sphere 2 (12,137) (basis .sphere 12 137 2) := by
  let E := model.classical.sphere
  have hd : HasDifferential E 2 (10,136) (12,137)
      (basis .sphere 10 136 0) (basis .sphere 12 137 2) := by
    have hrow := result ⟨.sphere, .equation, 2, 10, 136, [0], 12, 137, [2],
      "S0_AdamsE2_ss", 2859⟩ (by
        exact List.mem_of_getElem? (i := 260) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,hd⟩ := hrow
    change HasDifferential E 2 (10,136) (12,137) a b at hd
    have vx : Raw.coordinatesValid Raw.degrees .sphere 10 136 [0] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 12 137 [2] = true := rfl
    simp only [decode,vx,if_true,List.map_cons,List.map_nil,List.sum_cons,
      List.sum_nil,add_zero,Option.some.injEq] at ha
    simp only [decode,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,
      List.sum_nil,add_zero,Option.some.injEq] at hb
    rw [←ha,←hb] at hd
    exact hd
  have hs : E.r₀ ≤ 2 := by
    change model.classical.sphere.r₀ ≤ 2
    rw [model.classical.firstPage]
  exact pq_rep3zero_boundary (differential_target_later_zero hs (by decide) hd)

public theorem p_h2_boundary : IsBoundaryBy model.classical.sphere 2 (12,137)
    (product P h2) := by
  rw [h2Boundary_p_basis]
  exact h2Boundary_basis_12_137_2

public theorem q_h2_boundary : IsBoundaryBy model.classical.sphere 2 (13,138)
    (product Q h2) := by
  exact qTransport_boundary_of_source nativeSourceQ

private theorem sphere_d3_12_136_zero :
    model.classical.sphere.d 3 (12,136) = 0 := by
  classical
  let E := model.classical.sphere
  have hs2 : E.r₀ ≤ 2 := by
    change (model.classical.obj KIP126.StableHomotopy.SphereSpectrum).r₀ ≤ 2
    rw [model.classical.firstPage]
  have h226 : HasDifferential E 3 (9,134) (12,136)
      (KIP126.Computation.Table.basis .sphere 9 134 1) (KIP126.Computation.Table.basis .sphere 12 136 0) := by
    have hrow := KIP126.Computation.Table.result ⟨.sphere, .equation, 3, 9, 134, [1], 12, 136, [0], "S0_AdamsE2_ss", 2697⟩ (by
      exact List.mem_of_getElem? (l := KIP126.Computation.Table.Raw.claims) (i := 226) rfl)
    dsimp only [KIP126.Computation.Table.Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 3 (9,134) (12,136) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 9 134 [1] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 12 136 [0] = true := rfl
    simp only [KIP126.Computation.Table.decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  have h253 : HasDifferential E 2 (10,135) (12,136)
      (KIP126.Computation.Table.basis .sphere 10 135 1) (KIP126.Computation.Table.basis .sphere 12 136 1 + KIP126.Computation.Table.basis .sphere 12 136 2) := by
    have hrow := KIP126.Computation.Table.result ⟨.sphere, .equation, 2, 10, 135, [1], 12, 136, [1, 2], "S0_AdamsE2_ss", 2785⟩ (by
      exact List.mem_of_getElem? (l := KIP126.Computation.Table.Raw.claims) (i := 253) rfl)
    dsimp only [KIP126.Computation.Table.Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (10,135) (12,136) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 10 135 [1] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 12 136 [1, 2] = true := rfl
    simp only [KIP126.Computation.Table.decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  have h254 : HasDifferential E 2 (10,135) (12,136)
      (KIP126.Computation.Table.basis .sphere 10 135 2) (KIP126.Computation.Table.basis .sphere 12 136 3 + KIP126.Computation.Table.basis .sphere 12 136 4) := by
    have hrow := KIP126.Computation.Table.result ⟨.sphere, .equation, 2, 10, 135, [2], 12, 136, [3, 4], "S0_AdamsE2_ss", 2786⟩ (by
      exact List.mem_of_getElem? (l := KIP126.Computation.Table.Raw.claims) (i := 254) rfl)
    dsimp only [KIP126.Computation.Table.Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (10,135) (12,136) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 10 135 [2] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 12 136 [3, 4] = true := rfl
    simp only [KIP126.Computation.Table.decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  have h255 : HasDifferential E 2 (10,135) (12,136)
      (KIP126.Computation.Table.basis .sphere 10 135 4) (KIP126.Computation.Table.basis .sphere 12 136 4) := by
    have hrow := KIP126.Computation.Table.result ⟨.sphere, .equation, 2, 10, 135, [4], 12, 136, [4], "S0_AdamsE2_ss", 2787⟩ (by
      exact List.mem_of_getElem? (l := KIP126.Computation.Table.Raw.claims) (i := 255) rfl)
    dsimp only [KIP126.Computation.Table.Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (10,135) (12,136) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 10 135 [4] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 12 136 [4] = true := rfl
    simp only [KIP126.Computation.Table.decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  have h304 : HasDifferential E 2 (12,136) (14,137)
      (KIP126.Computation.Table.basis .sphere 12 136 2) (KIP126.Computation.Table.basis .sphere 14 137 2) := by
    have hrow := KIP126.Computation.Table.result ⟨.sphere, .equation, 2, 12, 136, [2], 14, 137, [2], "S0_AdamsE2_ss", 2849⟩ (by
      exact List.mem_of_getElem? (l := KIP126.Computation.Table.Raw.claims) (i := 304) rfl)
    dsimp only [KIP126.Computation.Table.Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (12,136) (14,137) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 12 136 [2] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 14 137 [2] = true := rfl
    simp only [KIP126.Computation.Table.decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  obtain ⟨e,he⟩ := KIP126.Computation.Table.basis_correct
    ⟨.sphere,12,136,["1,1,387,1", "0,1,410,1", "0,1,409,1", "0,2,389,1", "0,4,367,1"]⟩ (by
      exact List.mem_of_getElem? (l := KIP126.Computation.Table.Raw.degrees) (i := 200) rfl)
  change E.Page 2 (12,136) ≃ₗ[ℤ] (Fin 5 →₀ F2) at e
  change ∀ i : Fin 5, e.symm (Finsupp.single i 1) =
    KIP126.Computation.Table.basis .sphere 12 136 i.val at he
  obtain ⟨f,hf⟩ := KIP126.Computation.Table.basis_correct
    ⟨.sphere,14,137,["23,1,181,1", "0,1,418,1", "0,3,386,1"]⟩ (by
      exact List.mem_of_getElem? (l := KIP126.Computation.Table.Raw.degrees) (i := 215) rfl)
  change E.Page 2 (14,137) ≃ₗ[ℤ] (Fin 3 →₀ F2) at f
  change ∀ i : Fin 3, f.symm (Finsupp.single i 1) =
    KIP126.Computation.Table.basis .sphere 14 137 i.val at hf
  have hf2 : f.symm (Finsupp.single (2 : Fin 3) 1) =
      KIP126.Computation.Table.basis .sphere 14 137 2 := hf 2
  have tne : KIP126.Computation.Table.basis .sphere 14 137 2 ≠ 0 := by
    intro ht
    have hsingle : Finsupp.single (2 : Fin 3) (1 : F2) = 0 :=
      f.symm.injective (by simpa only [map_zero] using hf2.trans ht)
    have hh := congrArg (fun a => a (2 : Fin 3)) hsingle
    norm_num [Finsupp.single_apply] at hh
  obtain ⟨a0,ha0,hda0⟩ := differential_target_cycle h226
  have r12 : RepresentsOnPage E 3 (12,136)
      (KIP126.Computation.Table.basis .sphere 12 136 1 +
        KIP126.Computation.Table.basis .sphere 12 136 2) 0 :=
    differential_target_later_zero hs2 (by decide) h253
  have r34 : RepresentsOnPage E 3 (12,136)
      (KIP126.Computation.Table.basis .sphere 12 136 3 +
        KIP126.Computation.Table.basis .sphere 12 136 4) 0 :=
    differential_target_later_zero hs2 (by decide) h254
  have r4 : RepresentsOnPage E 3 (12,136)
      (KIP126.Computation.Table.basis .sphere 12 136 4) 0 :=
    differential_target_later_zero hs2 (by decide) h255
  have r3 : RepresentsOnPage E 3 (12,136)
      (KIP126.Computation.Table.basis .sphere 12 136 3) 0 := by
    simpa only [add_sub_cancel_right,sub_self] using represents_sub r34 r4
  let δ : E.Page 2 (12,136) ⟶ E.Page 2 (14,137) :=
    E.d 2 (12,136) ≫ eqToHom (congrArg (E.Page 2) h304.target_degree)
  have before3 {x : E.Page 2 (12,136)} (hx : ReachesPage E 3 (12,136) x) :
      δ x = 0 := by
    have hd := represents_d_zero_of_later hs2 (by decide : (2:ℤ) < 3)
      (represents_two_self x) hx
    change (E.d 2 (12,136) ≫ _) x = 0
    rw [ModuleCat.comp_apply,hd,map_zero]
  have d0 : δ (KIP126.Computation.Table.basis .sphere 12 136 0) = 0 :=
    before3 ⟨a0,ha0⟩
  have d4 : δ (KIP126.Computation.Table.basis .sphere 12 136 4) = 0 :=
    before3 ⟨0,r4⟩
  have d3 : δ (KIP126.Computation.Table.basis .sphere 12 136 3) = 0 :=
    before3 ⟨0,r3⟩
  have d12 : δ (KIP126.Computation.Table.basis .sphere 12 136 1 +
        KIP126.Computation.Table.basis .sphere 12 136 2) = 0 :=
    before3 ⟨0,r12⟩
  have d2 : δ (KIP126.Computation.Table.basis .sphere 12 136 2) =
      KIP126.Computation.Table.basis .sphere 14 137 2 := h304.eq_on_page_two.2
  have d1 : δ (KIP126.Computation.Table.basis .sphere 12 136 1) =
      -KIP126.Computation.Table.basis .sphere 14 137 2 := by
    calc
      _ = (δ (KIP126.Computation.Table.basis .sphere 12 136 1) +
          δ (KIP126.Computation.Table.basis .sphere 12 136 2)) -
          δ (KIP126.Computation.Table.basis .sphere 12 136 2) :=
        (add_sub_cancel_right _ _).symm
      _ = _ := by rw [←map_add,d12,d2,zero_sub]
  have hz (z : E.Page 3 (12,136)) : E.d 3 (12,136) z = 0 := by
    obtain ⟨x,hx⟩ := page_has_initial_representative (by decide) z
    have dx : δ x = 0 := before3 ⟨z,hx⟩
    let c : Fin 5 → F2 := e x
    have hex := finite_basis_expansion e x
    simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,he,add_zero] at hex
    change x = (if c 0 = 0 then 0 else KIP126.Computation.Table.basis .sphere 12 136 0) +
      ((if c 1 = 0 then 0 else KIP126.Computation.Table.basis .sphere 12 136 1) +
      ((if c 2 = 0 then 0 else KIP126.Computation.Table.basis .sphere 12 136 2) +
      ((if c 3 = 0 then 0 else KIP126.Computation.Table.basis .sphere 12 136 3) +
       (if c 4 = 0 then 0 else KIP126.Computation.Table.basis .sphere 12 136 4)))) at hex
    have hd := congrArg δ hex
    rw [dx] at hd
    simp only [map_add,apply_ite,map_zero] at hd
    simp only [d0,d1,d2,d3,d4,ite_self,zero_add,add_zero] at hd
    have h12 : c 1 = 0 ↔ c 2 = 0 := by
      constructor
      · intro hc
        by_contra hn
        have ht : 0 = KIP126.Computation.Table.basis .sphere 14 137 2 := by
          simpa only [hc,hn,ite_true,ite_false,zero_add] using hd
        exact tne ht.symm
      · intro hc
        by_contra hn
        have ht : 0 = -KIP126.Computation.Table.basis .sphere 14 137 2 := by
          simpa only [hc,hn,ite_true,ite_false,add_zero] using hd
        exact tne (neg_eq_zero.mp ht.symm)
    have r12' : RepresentsOnPage E 3 (12,136)
        ((if c 1 = 0 then 0 else KIP126.Computation.Table.basis .sphere 12 136 1) +
         (if c 2 = 0 then 0 else KIP126.Computation.Table.basis .sphere 12 136 2)) 0 := by
      by_cases hc1 : c 1 = 0
      · have hc2 := h12.mp hc1
        simpa only [hc1,hc2,ite_true,zero_add] using
          (RepresentsOnPage.zero (E := E) (p := (12,136)) (by decide : (2:ℤ) ≤ 3))
      · have hc2 : c 2 ≠ 0 := fun h => hc1 (h12.mpr h)
        simpa only [hc1,hc2,ite_false] using r12
    have rsum := represents_add_tail (represents_bit (c 0) ha0)
      (represents_add_tail r12'
        (represents_add_tail (represents_bit (c 3) r3) (represents_bit (c 4) r4)))
    have rx : RepresentsOnPage E 3 (12,136) x (if c 0 = 0 then 0 else a0) := by
      rw [hex]
      simpa only [ite_self,zero_add,add_zero,add_assoc] using rsum
    have hform : z = (if c 0 = 0 then 0 else a0) := represents_unique hx rx
    rw [hform]
    by_cases hc0 : c 0 = 0
    · simp only [hc0,ite_true,map_zero]
    · simp only [hc0,ite_false,hda0]
  ext z
  exact hz z


private theorem sphere_d2_13_137_zero : model.classical.sphere.d 2 (13,137)=0 := by
  let E := model.classical.sphere
  have hs2 : E.r₀≤2 := by
    change model.classical.sphere.r₀≤2
    rw [model.classical.firstPage]
  have h321 : HasDifferential E 2 (11,136) (13,137)
      (basis .sphere 11 136 4) (basis .sphere 13 137 3) := by
    have hrow := result ⟨.sphere, .equation, 2, 11, 136, [4], 13, 137, [3], "S0_AdamsE2_ss", 2914⟩ (by
      exact List.mem_of_getElem? (i := 321) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 2 (11,136) (13,137) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 11 136 [4]=true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 13 137 [3]=true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    exact h
  have h322 : HasDifferential E 3 (10,135) (13,137)
      (basis .sphere 10 135 0) (basis .sphere 13 137 0) := by
    have hrow := result ⟨.sphere, .equation, 3, 10, 135, [0], 13, 137, [0], "S0_AdamsE2_ss", 2915⟩ (by
      exact List.mem_of_getElem? (i := 322) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 3 (10,135) (13,137) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 10 135 [0]=true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 13 137 [0]=true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    exact h
  have h324 : HasDifferential E 3 (13,137) (16,139)
      (basis .sphere 13 137 2) (basis .sphere 16 139 0) := by
    have hrow := result ⟨.sphere, .equation, 3, 13, 137, [2], 16, 139, [0], "S0_AdamsE2_ss", 2917⟩ (by
      exact List.mem_of_getElem? (i := 324) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 3 (13,137) (16,139) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 13 137 [2]=true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 16 139 [0]=true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    exact h
  have h323 : ReachesPage E 1000 (13,137) (basis .sphere 13 137 1) := by
    have hrow := result ⟨.sphere, .reaches, 1000, 13, 137, [1], 13, 137, [], "S0_AdamsE2_ss", 2916⟩ (by
      exact List.mem_of_getElem? (i := 323) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,h⟩ := hrow
    have vx : Raw.coordinatesValid Raw.degrees .sphere 13 137 [1]=true := rfl
    simp only [decode,vx,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      add_zero,Option.some.injEq] at ha
    rw [←ha] at h
    exact h
  have before3 (x : E.Page 2 (13,137)) (hx : ReachesPage E 3 (13,137) x) :
      E.d 2 (13,137) x=0 :=
    represents_d_zero_of_later hs2 (by decide) (represents_two_self x) hx
  obtain ⟨_,_,a0,_,ha0,_⟩ := h322
  obtain ⟨_,a2,_,ha2,_,_⟩ := h324
  have ha3 : RepresentsOnPage E 3 (13,137) (basis .sphere 13 137 3) 0 :=
    differential_target_later_zero hs2 (by decide) h321
  obtain ⟨e,he⟩ := basis_correct
    ⟨.sphere,13,137,["76,1,82,1", "9,1,251,1", "7,1,275,1", "0,5,367,1"]⟩ (by
      exact List.mem_of_getElem? (i := 208) (by rfl))
  change E.Page 2 (13,137) ≃ₗ[ℤ] (Fin 4 →₀ F2) at e
  change ∀ i : Fin 4, e.symm (Finsupp.single i 1)=basis .sphere 13 137 i.val at he
  apply d_zero_of_complete_representatives (by decide : (2:ℤ)≤2) e
  intro i
  refine ⟨e.symm (Finsupp.single i 1),represents_two_self _,?_⟩
  rw [he i]
  fin_cases i
  · exact before3 _ ⟨a0,ha0⟩
  · exact before3 _ (reaches_before (by decide) (by decide) h323)
  · exact before3 _ ⟨a2,ha2⟩
  · exact before3 _ ⟨0,ha3⟩

private theorem e5_stem124_af11_of_incoming_zero
    (hin2 : model.classical.sphere.d 2 (13,137)=0)
    (hin3 : model.classical.sphere.d 3 (12,136)=0) :
    Subsingleton (model.classical.sphere.Page 5 (11,135)) := by
  classical
  let E := model.classical.sphere
  have hs2 : E.r₀≤2 := by
    change model.classical.sphere.r₀≤2
    rw [model.classical.firstPage]
  have hs3 : E.r₀≤3 := hs2.trans (by decide)
  have hs4 : E.r₀≤4 := hs2.trans (by decide)
  have h274 : HasDifferential E 2 (9,134) (11,135)
      (basis .sphere 9 134 0) (basis .sphere 11 135 3 + basis .sphere 11 135 4) := by
    have hrow := result ⟨.sphere, .equation, 2, 9, 134, [0], 11, 135, [3, 4], "S0_AdamsE2_ss", 2778⟩ (by
      exact List.mem_of_getElem? (i := 274) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 2 (9,134) (11,135) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 9 134 [0]=true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 11 135 [3, 4]=true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    exact h
  have h275 : HasDifferential E 2 (9,134) (11,135)
      (basis .sphere 9 134 4) (basis .sphere 11 135 4) := by
    have hrow := result ⟨.sphere, .equation, 2, 9, 134, [4], 11, 135, [4], "S0_AdamsE2_ss", 2779⟩ (by
      exact List.mem_of_getElem? (i := 275) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 2 (9,134) (11,135) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 9 134 [4]=true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 11 135 [4]=true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    exact h
  have h276 : HasDifferential E 3 (8,133) (11,135)
      (basis .sphere 8 133 0) (basis .sphere 11 135 0) := by
    have hrow := result ⟨.sphere, .equation, 3, 8, 133, [0], 11, 135, [0], "S0_AdamsE2_ss", 2780⟩ (by
      exact List.mem_of_getElem? (i := 276) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 3 (8,133) (11,135) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 8 133 [0]=true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 11 135 [0]=true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    exact h
  have h277 : HasDifferential E 4 (11,135) (15,138)
      (basis .sphere 11 135 1 + basis .sphere 11 135 2) (basis .sphere 15 138 0) := by
    have hrow := result ⟨.sphere, .equation, 4, 11, 135, [1, 2], 15, 138, [0], "S0_AdamsE2_ss", 2781⟩ (by
      exact List.mem_of_getElem? (i := 277) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 4 (11,135) (15,138) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 11 135 [1, 2]=true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 15 138 [0]=true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    exact h
  have h278 : HasDifferential E 2 (11,135) (13,136)
      (basis .sphere 11 135 2) (basis .sphere 13 136 2) := by
    have hrow := result ⟨.sphere, .equation, 2, 11, 135, [2], 13, 136, [2], "S0_AdamsE2_ss", 2782⟩ (by
      exact List.mem_of_getElem? (i := 278) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 2 (11,135) (13,136) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 11 135 [2]=true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 13 136 [2]=true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    exact h
  obtain ⟨e,he⟩ := basis_correct
    ⟨.sphere,11,135,["411,1", "410,1", "409,1", "0,1,389,1", "0,3,367,1"]⟩ (by
      exact List.mem_of_getElem? (i := 191) (by rfl))
  change E.Page 2 (11,135) ≃ₗ[ℤ] (Fin 5 →₀ F2) at e
  change ∀ i : Fin 5, e.symm (Finsupp.single i 1)=basis .sphere 11 135 i.val at he
  obtain ⟨f,hf⟩ := basis_correct
    ⟨.sphere,13,136,["418,1", "417,1", "0,2,386,1"]⟩ (by
      exact List.mem_of_getElem? (i := 207) (by rfl))
  change E.Page 2 (13,136) ≃ₗ[ℤ] (Fin 3 →₀ F2) at f
  change ∀ i : Fin 3, f.symm (Finsupp.single i 1)=basis .sphere 13 136 i.val at hf
  have target2ne : basis .sphere 13 136 2≠0 := by
    have hh : f.symm (Finsupp.single (2:Fin 3) 1)=basis .sphere 13 136 2 := hf 2
    rw [←hh]
    exact basis_vector_ne_zero f 2
  obtain ⟨g,hg⟩ := basis_correct
    ⟨.sphere,15,138,["438,1", "7,1,279,1", "0,2,418,1"]⟩ (by
      exact List.mem_of_getElem? (i := 222) (by rfl))
  change E.Page 2 (15,138) ≃ₗ[ℤ] (Fin 3 →₀ F2) at g
  change ∀ i : Fin 3, g.symm (Finsupp.single i 1)=basis .sphere 15 138 i.val at hg
  have target0ne : basis .sphere 15 138 0≠0 := by
    have hh : g.symm (Finsupp.single (0:Fin 3) 1)=basis .sphere 15 138 0 := hg 0
    rw [←hh]
    exact basis_vector_ne_zero g 0
  obtain ⟨hd4,a4,c4,ha4,hc4,heq4⟩ := h277
  obtain ⟨c3,hc3⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤4) hc4
  have deg2 : (13,137)+E.diffDeg 2=(15,138) := by
    simp only [E,KIP126.Classical.Adams.ClassicalAdamsFamily.sphere,
      KIP126.Classical.Adams.ClassicalAdamsFamily.obj,model.classical.differentialDegree,
      Prod.mk_add_mk,Int.reduceAdd,Int.reduceSub]
  have deg3 : (12,136)+E.diffDeg 3=(15,138) := by
    simp only [E,KIP126.Classical.Adams.ClassicalAdamsFamily.sphere,
      KIP126.Classical.Adams.ClassicalAdamsFamily.obj,model.classical.differentialDegree,
      Prod.mk_add_mk,Int.reduceAdd,Int.reduceSub]
  have c3ne : c3≠0 := represents_next_nonzero_of_incoming_zero_at hs2 (by decide) hin2
    hc3 (represents_two_self _) target0ne deg2
  have c4ne : c4≠0 := represents_next_nonzero_of_incoming_zero_at hs3 (by decide) hin3
    hc4 hc3 c3ne deg3
  have da4ne : E.d 4 (11,135) a4≠0 := by
    intro hz
    apply c4ne
    simpa only [ModuleCat.comp_apply,hz,map_zero] using heq4.symm
  have r0 : RepresentsOnPage E 4 (11,135) (basis .sphere 11 135 0) 0 :=
    differential_target_later_zero hs3 (by decide) h276
  have r34 : RepresentsOnPage E 4 (11,135)
      (basis .sphere 11 135 3+basis .sphere 11 135 4) 0 :=
    differential_target_later_zero hs2 (by decide) h274
  have r4 : RepresentsOnPage E 4 (11,135) (basis .sphere 11 135 4) 0 :=
    differential_target_later_zero hs2 (by decide) h275
  have r3 : RepresentsOnPage E 4 (11,135) (basis .sphere 11 135 3) 0 := by
    simpa only [add_sub_cancel_right,sub_self] using represents_sub r34 r4
  let δ : E.Page 2 (11,135) ⟶ E.Page 2 (13,136) :=
    E.d 2 (11,135) ≫ eqToHom (congrArg (E.Page 2) h278.target_degree)
  have before4 (x : E.Page 2 (11,135)) (hx : ReachesPage E 4 (11,135) x) : δ x=0 := by
    have h := represents_d_zero_of_later hs2 (by decide : (2:ℤ)<4) (represents_two_self x) hx
    change (E.d 2 (11,135) ≫ _) x=0
    rw [ModuleCat.comp_apply,h,map_zero]
  have d0 : δ (basis .sphere 11 135 0)=0 := before4 _ ⟨0,r0⟩
  have d3 : δ (basis .sphere 11 135 3)=0 := before4 _ ⟨0,r3⟩
  have d4 : δ (basis .sphere 11 135 4)=0 := before4 _ ⟨0,r4⟩
  have d12 : δ (basis .sphere 11 135 1+basis .sphere 11 135 2)=0 := before4 _ ⟨a4,ha4⟩
  have d2 : δ (basis .sphere 11 135 2)=basis .sphere 13 136 2 := h278.eq_on_page_two.2
  have d1 : δ (basis .sphere 11 135 1) = -basis .sphere 13 136 2 := by
    calc
      _ = (δ (basis .sphere 11 135 1)+δ (basis .sphere 11 135 2))-
          δ (basis .sphere 11 135 2) := (add_sub_cancel_right _ _).symm
      _ = _ := by rw [←map_add,d12,d2,zero_sub]
  have δbit (b : F2) (a : E.Page 2 (11,135)) :
      δ (if b=0 then 0 else a)=if b=0 then 0 else δ a := by
    by_cases hb : b=0 <;> simp only [hb,ite_true,ite_false,map_zero]
  have kill0 : RepresentsOnPage E 5 (11,135) (basis .sphere 11 135 0) 0 :=
    differential_target_later_zero hs3 (by decide) h276
  have kill34 : RepresentsOnPage E 5 (11,135)
      (basis .sphere 11 135 3+basis .sphere 11 135 4) 0 :=
    differential_target_later_zero hs2 (by decide) h274
  have kill4 : RepresentsOnPage E 5 (11,135) (basis .sphere 11 135 4) 0 :=
    differential_target_later_zero hs2 (by decide) h275
  have kill3 : RepresentsOnPage E 5 (11,135) (basis .sphere 11 135 3) 0 := by
    simpa only [add_sub_cancel_right,sub_self] using represents_sub kill34 kill4
  have hz (y : E.Page 5 (11,135)) : y=0 := by
    obtain ⟨x,hxy⟩ := page_has_initial_representative (by decide) y
    have hx := finite_basis_expansion e x
    simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero,he] at hx
    change x=(if e x 0=0 then 0 else basis .sphere 11 135 0)+
      ((if e x 1=0 then 0 else basis .sphere 11 135 1)+
      ((if e x 2=0 then 0 else basis .sphere 11 135 2)+
      ((if e x 3=0 then 0 else basis .sphere 11 135 3)+
       (if e x 4=0 then 0 else basis .sphere 11 135 4)))) at hx
    have dx : δ x=0 := by
      have hd := represents_d_zero_of_later hs2 (by decide : (2:ℤ)<5)
        (represents_two_self x) ⟨y,hxy⟩
      change (E.d 2 (11,135) ≫ _) x=0
      rw [ModuleCat.comp_apply,hd,map_zero]
    have heq := congrArg δ hx
    rw [dx] at heq
    simp only [map_add,δbit,d0,d1,d2,d3,d4,ite_self,zero_add,add_zero] at heq
    have h12 : e x 1=0 ↔ e x 2=0 := by
      constructor
      · intro h1
        by_contra h2
        apply target2ne
        have hh : 0=basis .sphere 13 136 2 := by
          simpa only [h1,h2,ite_true,ite_false,zero_add] using heq
        exact hh.symm
      · intro h2
        by_contra h1
        apply target2ne
        have hh : 0= -basis .sphere 13 136 2 := by
          simpa only [h1,h2,ite_true,ite_false,add_zero] using heq
        exact neg_eq_zero.mp hh.symm
    have pairrep : RepresentsOnPage E 4 (11,135)
        ((if e x 1=0 then 0 else basis .sphere 11 135 1)+
         (if e x 2=0 then 0 else basis .sphere 11 135 2))
        (if e x 1=0 then 0 else a4) := by
      by_cases h1 : e x 1=0
      · have h2 := h12.mp h1
        simpa only [h1,h2,ite_true,zero_add] using
          (RepresentsOnPage.zero (E:=E) (p:=(11,135)) (by decide : (2:ℤ)≤4))
      · have h2 : e x 2≠0 := fun h=>h1 (h12.mpr h)
        simpa only [h1,h2,ite_false] using ha4
    have reps4 := represents_add_tail (represents_bit (e x 0) r0)
      (represents_add_tail pairrep (represents_add_tail (represents_bit (e x 3) r3)
        (represents_bit (e x 4) r4)))
    have rep4x : RepresentsOnPage E 4 (11,135) x (if e x 1=0 then 0 else a4) := by
      simp only [ite_self,zero_add,add_zero,add_assoc] at reps4
      rw [←hx] at reps4
      exact reps4
    have h1 : e x 1=0 := by
      by_contra hh
      have hd := represents_d_zero_of_later hs4 (by decide : (4:ℤ)<5) rep4x ⟨y,hxy⟩
      apply da4ne
      simpa only [hh,ite_false] using hd
    have h2 : e x 2=0 := h12.mp h1
    have reps5 := represents_add_tail (represents_bit (e x 0) kill0)
      (represents_add_tail (represents_bit (e x 3) kill3) (represents_bit (e x 4) kill4))
    have rep5x : RepresentsOnPage E 5 (11,135) x 0 := by
      rw [hx]
      simpa only [h1,h2,ite_true,zero_add,ite_self] using reps5
    exact represents_unique hxy rep5x
  exact ⟨fun x y=>(hz x).trans (hz y).symm⟩


public theorem e5_stem124_af11 : Subsingleton (model.classical.sphere.Page 5 (11,135)) := by
  exact e5_stem124_af11_of_incoming_zero sphere_d2_13_137_zero sphere_d3_12_136_zero

/-- The outgoing d₂ column detects the only possible residual coordinate;
all other d₂ cycles are actual incoming d₂/d₃ boundaries. -/
public theorem e4_stem124_af12 : Subsingleton (model.classical.sphere.Page 4 (12,136)) := by
  classical
  let E := model.classical.sphere
  have hs2 : E.r₀ ≤ 2 := by
    change (model.classical.obj KIP126.StableHomotopy.SphereSpectrum).r₀ ≤ 2
    rw [model.classical.firstPage]
  have hs3 : E.r₀ ≤ 3 := le_trans hs2 (by decide)
  have h226 : HasDifferential E 3 (9,134) (12,136)
      (KIP126.Computation.Table.basis .sphere 9 134 1) (KIP126.Computation.Table.basis .sphere 12 136 0) := by
    have hrow := KIP126.Computation.Table.result ⟨.sphere, .equation, 3, 9, 134, [1], 12, 136, [0], "S0_AdamsE2_ss", 2697⟩ (by
      exact List.mem_of_getElem? (l := KIP126.Computation.Table.Raw.claims) (i := 226) rfl)
    dsimp only [KIP126.Computation.Table.Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 3 (9,134) (12,136) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 9 134 [1] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 12 136 [0] = true := rfl
    simp only [KIP126.Computation.Table.decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  have h253 : HasDifferential E 2 (10,135) (12,136)
      (KIP126.Computation.Table.basis .sphere 10 135 1) (KIP126.Computation.Table.basis .sphere 12 136 1 + KIP126.Computation.Table.basis .sphere 12 136 2) := by
    have hrow := KIP126.Computation.Table.result ⟨.sphere, .equation, 2, 10, 135, [1], 12, 136, [1, 2], "S0_AdamsE2_ss", 2785⟩ (by
      exact List.mem_of_getElem? (l := KIP126.Computation.Table.Raw.claims) (i := 253) rfl)
    dsimp only [KIP126.Computation.Table.Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (10,135) (12,136) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 10 135 [1] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 12 136 [1, 2] = true := rfl
    simp only [KIP126.Computation.Table.decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  have h254 : HasDifferential E 2 (10,135) (12,136)
      (KIP126.Computation.Table.basis .sphere 10 135 2) (KIP126.Computation.Table.basis .sphere 12 136 3 + KIP126.Computation.Table.basis .sphere 12 136 4) := by
    have hrow := KIP126.Computation.Table.result ⟨.sphere, .equation, 2, 10, 135, [2], 12, 136, [3, 4], "S0_AdamsE2_ss", 2786⟩ (by
      exact List.mem_of_getElem? (l := KIP126.Computation.Table.Raw.claims) (i := 254) rfl)
    dsimp only [KIP126.Computation.Table.Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (10,135) (12,136) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 10 135 [2] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 12 136 [3, 4] = true := rfl
    simp only [KIP126.Computation.Table.decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  have h255 : HasDifferential E 2 (10,135) (12,136)
      (KIP126.Computation.Table.basis .sphere 10 135 4) (KIP126.Computation.Table.basis .sphere 12 136 4) := by
    have hrow := KIP126.Computation.Table.result ⟨.sphere, .equation, 2, 10, 135, [4], 12, 136, [4], "S0_AdamsE2_ss", 2787⟩ (by
      exact List.mem_of_getElem? (l := KIP126.Computation.Table.Raw.claims) (i := 255) rfl)
    dsimp only [KIP126.Computation.Table.Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (10,135) (12,136) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 10 135 [4] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 12 136 [4] = true := rfl
    simp only [KIP126.Computation.Table.decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  have h304 : HasDifferential E 2 (12,136) (14,137)
      (KIP126.Computation.Table.basis .sphere 12 136 2) (KIP126.Computation.Table.basis .sphere 14 137 2) := by
    have hrow := KIP126.Computation.Table.result ⟨.sphere, .equation, 2, 12, 136, [2], 14, 137, [2], "S0_AdamsE2_ss", 2849⟩ (by
      exact List.mem_of_getElem? (l := KIP126.Computation.Table.Raw.claims) (i := 304) rfl)
    dsimp only [KIP126.Computation.Table.Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (12,136) (14,137) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 12 136 [2] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 14 137 [2] = true := rfl
    simp only [KIP126.Computation.Table.decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  obtain ⟨e,he⟩ := KIP126.Computation.Table.basis_correct
    ⟨.sphere,12,136,["1,1,387,1", "0,1,410,1", "0,1,409,1", "0,2,389,1", "0,4,367,1"]⟩ (by
      exact List.mem_of_getElem? (l := KIP126.Computation.Table.Raw.degrees) (i := 200) rfl)
  change E.Page 2 (12,136) ≃ₗ[ℤ] (Fin 5 →₀ F2) at e
  change ∀ i : Fin 5, e.symm (Finsupp.single i 1) =
    KIP126.Computation.Table.basis .sphere 12 136 i.val at he
  obtain ⟨f,hf⟩ := KIP126.Computation.Table.basis_correct
    ⟨.sphere,14,137,["23,1,181,1", "0,1,418,1", "0,3,386,1"]⟩ (by
      exact List.mem_of_getElem? (l := KIP126.Computation.Table.Raw.degrees) (i := 215) rfl)
  change E.Page 2 (14,137) ≃ₗ[ℤ] (Fin 3 →₀ F2) at f
  change ∀ i : Fin 3, f.symm (Finsupp.single i 1) =
    KIP126.Computation.Table.basis .sphere 14 137 i.val at hf
  have hf2 : f.symm (Finsupp.single (2 : Fin 3) 1) =
      KIP126.Computation.Table.basis .sphere 14 137 2 := hf 2
  have tne : KIP126.Computation.Table.basis .sphere 14 137 2 ≠ 0 := by
    intro ht
    have hsingle : Finsupp.single (2 : Fin 3) (1 : F2) = 0 :=
      f.symm.injective (by simpa only [map_zero] using hf2.trans ht)
    have hh := congrArg (fun a => a (2 : Fin 3)) hsingle
    norm_num [Finsupp.single_apply] at hh
  have r0 : RepresentsOnPage E 4 (12,136)
      (KIP126.Computation.Table.basis .sphere 12 136 0) 0 :=
    differential_target_later_zero hs3 (by decide) h226
  have r12 : RepresentsOnPage E 4 (12,136)
      (KIP126.Computation.Table.basis .sphere 12 136 1 +
        KIP126.Computation.Table.basis .sphere 12 136 2) 0 :=
    differential_target_later_zero hs2 (by decide) h253
  have r34 : RepresentsOnPage E 4 (12,136)
      (KIP126.Computation.Table.basis .sphere 12 136 3 +
        KIP126.Computation.Table.basis .sphere 12 136 4) 0 :=
    differential_target_later_zero hs2 (by decide) h254
  have r4 : RepresentsOnPage E 4 (12,136)
      (KIP126.Computation.Table.basis .sphere 12 136 4) 0 :=
    differential_target_later_zero hs2 (by decide) h255
  have r3 : RepresentsOnPage E 4 (12,136)
      (KIP126.Computation.Table.basis .sphere 12 136 3) 0 := by
    simpa only [add_sub_cancel_right,sub_self] using represents_sub r34 r4
  let δ : E.Page 2 (12,136) ⟶ E.Page 2 (14,137) :=
    E.d 2 (12,136) ≫ eqToHom (congrArg (E.Page 2) h304.target_degree)
  have before4 {x : E.Page 2 (12,136)} (hx : ReachesPage E 4 (12,136) x) :
      δ x = 0 := by
    have hd := represents_d_zero_of_later hs2 (by decide : (2:ℤ) < 4)
      (represents_two_self x) hx
    change (E.d 2 (12,136) ≫ _) x = 0
    rw [ModuleCat.comp_apply,hd,map_zero]
  have d0 : δ (KIP126.Computation.Table.basis .sphere 12 136 0) = 0 :=
    before4 ⟨0,r0⟩
  have d4 : δ (KIP126.Computation.Table.basis .sphere 12 136 4) = 0 :=
    before4 ⟨0,r4⟩
  have d3 : δ (KIP126.Computation.Table.basis .sphere 12 136 3) = 0 :=
    before4 ⟨0,r3⟩
  have d12 : δ (KIP126.Computation.Table.basis .sphere 12 136 1 +
        KIP126.Computation.Table.basis .sphere 12 136 2) = 0 :=
    before4 ⟨0,r12⟩
  have d2 : δ (KIP126.Computation.Table.basis .sphere 12 136 2) =
      KIP126.Computation.Table.basis .sphere 14 137 2 := h304.eq_on_page_two.2
  have d1 : δ (KIP126.Computation.Table.basis .sphere 12 136 1) =
      -KIP126.Computation.Table.basis .sphere 14 137 2 := by
    calc
      _ = (δ (KIP126.Computation.Table.basis .sphere 12 136 1) +
          δ (KIP126.Computation.Table.basis .sphere 12 136 2)) -
          δ (KIP126.Computation.Table.basis .sphere 12 136 2) :=
        (add_sub_cancel_right _ _).symm
      _ = _ := by rw [←map_add,d12,d2,zero_sub]
  have hz (z : E.Page 4 (12,136)) : z = 0 := by
    obtain ⟨x,hx⟩ := page_has_initial_representative (by decide) z
    have dx : δ x = 0 := before4 ⟨z,hx⟩
    let c : Fin 5 → F2 := e x
    have hex := finite_basis_expansion e x
    simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,he,add_zero] at hex
    change x = (if c 0 = 0 then 0 else KIP126.Computation.Table.basis .sphere 12 136 0) +
      ((if c 1 = 0 then 0 else KIP126.Computation.Table.basis .sphere 12 136 1) +
      ((if c 2 = 0 then 0 else KIP126.Computation.Table.basis .sphere 12 136 2) +
      ((if c 3 = 0 then 0 else KIP126.Computation.Table.basis .sphere 12 136 3) +
       (if c 4 = 0 then 0 else KIP126.Computation.Table.basis .sphere 12 136 4)))) at hex
    have hd := congrArg δ hex
    rw [dx] at hd
    simp only [map_add,apply_ite,map_zero] at hd
    simp only [d0,d1,d2,d3,d4,ite_self,zero_add,add_zero] at hd
    have h12 : c 1 = 0 ↔ c 2 = 0 := by
      constructor
      · intro hc
        by_contra hn
        have ht : 0 = KIP126.Computation.Table.basis .sphere 14 137 2 := by
          simpa only [hc,hn,ite_true,ite_false,zero_add] using hd
        exact tne ht.symm
      · intro hc
        by_contra hn
        have ht : 0 = -KIP126.Computation.Table.basis .sphere 14 137 2 := by
          simpa only [hc,hn,ite_true,ite_false,add_zero] using hd
        exact tne (neg_eq_zero.mp ht.symm)
    have r12' : RepresentsOnPage E 4 (12,136)
        ((if c 1 = 0 then 0 else KIP126.Computation.Table.basis .sphere 12 136 1) +
         (if c 2 = 0 then 0 else KIP126.Computation.Table.basis .sphere 12 136 2)) 0 := by
      by_cases hc1 : c 1 = 0
      · have hc2 := h12.mp hc1
        simpa only [hc1,hc2,ite_true,zero_add] using
          (RepresentsOnPage.zero (E := E) (p := (12,136)) (by decide : (2:ℤ) ≤ 4))
      · have hc2 : c 2 ≠ 0 := fun h => hc1 (h12.mpr h)
        simpa only [hc1,hc2,ite_false] using r12
    have rsum := represents_add_tail (represents_bit (c 0) r0)
      (represents_add_tail r12'
        (represents_add_tail (represents_bit (c 3) r3) (represents_bit (c 4) r4)))
    have rx0 : RepresentsOnPage E 4 (12,136) x 0 := by
      rw [hex]
      simpa only [ite_self,zero_add,add_assoc] using rsum
    exact represents_unique hx rx0
  exact ⟨fun a b => (hz a).trans (hz b).symm⟩


/-- On E₂, the two outgoing d₂ columns exclude the first two coordinates.
The remaining coordinates are actual d₂/d₃ boundaries, so E₄ is zero. -/
public theorem e4_stem125_af12 : Subsingleton (model.classical.sphere.Page 4 (12,137)) := by
  classical
  let E := model.classical.sphere
  have hstart : E.r₀=2 := model.classical.firstPage _
  have h305 : HasDifferential E 2 (10,136) (12,137)
      (basis .sphere 10 136 0) (basis .sphere 12 137 2) := by
    have hrow := result ⟨.sphere, .equation, 2, 10, 136, [0], 12, 137, [2], "S0_AdamsE2_ss", 2918⟩ (by
      exact List.mem_of_getElem? (i := 305) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 2 (10,136) (12,137) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 10 136 [0] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 12 137 [2] = true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    exact h
  have h306 : HasDifferential E 3 (9,135) (12,137)
      (basis .sphere 9 135 0) (basis .sphere 12 137 3 + basis .sphere 12 137 4) := by
    have hrow := result ⟨.sphere, .equation, 3, 9, 135, [0], 12, 137, [3, 4], "S0_AdamsE2_ss", 2919⟩ (by
      exact List.mem_of_getElem? (i := 306) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 3 (9,135) (12,137) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 9 135 [0] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 12 137 [3, 4] = true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    exact h
  have h307 : HasDifferential E 3 (9,135) (12,137)
      (basis .sphere 9 135 0 + basis .sphere 9 135 3) (basis .sphere 12 137 4) := by
    have hrow := result ⟨.sphere, .equation, 3, 9, 135, [0, 3], 12, 137, [4], "S0_AdamsE2_ss", 2920⟩ (by
      exact List.mem_of_getElem? (i := 307) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 3 (9,135) (12,137) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 9 135 [0, 3] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 12 137 [4] = true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    exact h
  have h308 : HasDifferential E 2 (12,137) (14,138)
      (basis .sphere 12 137 1) (basis .sphere 14 138 4) := by
    have hrow := result ⟨.sphere, .equation, 2, 12, 137, [1], 14, 138, [4], "S0_AdamsE2_ss", 2921⟩ (by
      exact List.mem_of_getElem? (i := 308) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 2 (12,137) (14,138) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 12 137 [1] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 14 138 [4] = true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    exact h
  have h309 : HasDifferential E 2 (12,137) (14,138)
      (basis .sphere 12 137 0) (basis .sphere 14 138 3) := by
    have hrow := result ⟨.sphere, .equation, 2, 12, 137, [0], 14, 138, [3], "S0_AdamsE2_ss", 2922⟩ (by
      exact List.mem_of_getElem? (i := 309) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 2 (12,137) (14,138) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 12 137 [0] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 14 138 [3] = true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    exact h
  obtain ⟨e,he⟩ := basis_correct
    ⟨.sphere,12,137,["426,1", "425,1", "0,1,69,1,89,1", "0,3,391,1", "0,4,375,1"]⟩ (by
      exact List.mem_of_getElem? (i := 201) (by rfl))
  change E.Page 2 (12,137) ≃ₗ[ℤ] (Fin 5 →₀ F2) at e
  change ∀ i : Fin 5, e.symm (Finsupp.single i 1) = basis .sphere 12 137 i.val at he
  obtain ⟨f,hf⟩ := basis_correct
    ⟨.sphere,14,138,["440,1", "439,1", "23,1,190,1", "1,1,418,1", "1,1,417,1"]⟩ (by
      exact List.mem_of_getElem? (i := 216) (by rfl))
  change E.Page 2 (14,138) ≃ₗ[ℤ] (Fin 5 →₀ F2) at f
  change ∀ i : Fin 5, f.symm (Finsupp.single i 1) = basis .sphere 14 138 i.val at hf
  have hf3 : f.symm (Finsupp.single (3:Fin 5) 1) = basis .sphere 14 138 3 := hf 3
  have hf4 : f.symm (Finsupp.single (4:Fin 5) 1) = basis .sphere 14 138 4 := hf 4
  let δ : E.Page 2 (12,137) ⟶ E.Page 2 (14,138) :=
    E.d 2 (12,137) ≫ eqToHom (congrArg (E.Page 2) h309.target_degree)
  have d0 : δ (basis .sphere 12 137 0) = basis .sphere 14 138 3 :=
    h309.eq_on_page_two.2
  have d1 : δ (basis .sphere 12 137 1) = basis .sphere 14 138 4 :=
    h308.eq_on_page_two.2
  have d2 : δ (basis .sphere 12 137 2) = 0 := by
    obtain ⟨a,ha,hda⟩ := differential_target_cycle h305
    rw [←ha.eq_on_page_two] at hda
    change (E.d 2 (12,137) ≫ _) (basis .sphere 12 137 2) = 0
    rw [ModuleCat.comp_apply,hda,map_zero]
  have before3 {x : E.Page 2 (12,137)} (hx : ReachesPage E 3 (12,137) x) :
      δ x = 0 := by
    have hd := represents_d_zero_of_later (E:=E) (r:=2)
      (by rw [hstart]) (by decide : (2:ℤ)<3)
      (represents_two_self x) hx
    change (E.d 2 (12,137) ≫ _) x = 0
    rw [ModuleCat.comp_apply,hd,map_zero]
  have d4 : δ (basis .sphere 12 137 4) = 0 :=
    by
    obtain ⟨_,_,b,_,hb,_⟩ := h307
    exact before3 ⟨b,hb⟩
  have d3 : δ (basis .sphere 12 137 3) = 0 := by
    obtain ⟨_,_,b,_,hb,_⟩ := h306
    have hd := before3 ⟨b,hb⟩
    simpa only [map_add,d4,add_zero] using hd
  have hb2 : RepresentsOnPage E 4 (12,137) (basis .sphere 12 137 2) 0 :=
    differential_target_later_zero (by rw [hstart]) (by decide) h305
  have hb34 : RepresentsOnPage E 4 (12,137)
      (basis .sphere 12 137 3 + basis .sphere 12 137 4) 0 :=
    differential_target_later_zero (by rw [hstart]; omega) (by decide) h306
  have hb4 : RepresentsOnPage E 4 (12,137) (basis .sphere 12 137 4) 0 :=
    differential_target_later_zero (by rw [hstart]; omega) (by decide) h307
  have hb3 : RepresentsOnPage E 4 (12,137) (basis .sphere 12 137 3) 0 := by
    simpa only [add_sub_cancel_right,sub_self] using represents_sub hb34 hb4
  have hz (y : E.Page 4 (12,137)) : y=0 := by
    obtain ⟨x,hxy⟩ := page_has_initial_representative (by decide) y
    have hc : E.d 2 (12,137) x = 0 :=
      represents_d_zero_of_later (by rw [hstart]) (by decide)
        (represents_two_self _) ⟨y,hxy⟩
    have hx := finite_basis_expansion e x
    simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero,he] at hx
    change x = (if e x 0=0 then 0 else basis .sphere 12 137 0) +
      ((if e x 1=0 then 0 else basis .sphere 12 137 1) +
      ((if e x 2=0 then 0 else basis .sphere 12 137 2) +
      ((if e x 3=0 then 0 else basis .sphere 12 137 3) +
      (if e x 4=0 then 0 else basis .sphere 12 137 4)))) at hx
    have hcδ : δ x = 0 := by
      change (E.d 2 (12,137) ≫ _) x=0
      rw [ModuleCat.comp_apply,hc,map_zero]
    have δbit (c : F2) (b : E.Page 2 (12,137)) :
        δ (if c=0 then 0 else b) = if c=0 then 0 else δ b := by
      by_cases h : c=0 <;> simp only [h,ite_true,ite_false,map_zero]
    have hd := congrArg δ hx
    simp only [map_add,δbit,d0,d1,d2,d3,d4,ite_self,add_zero,hcδ] at hd
    have c0 : e x 0=0 := by
      by_contra h0
      by_cases h1 : e x 1=0
      all_goals
        have hh := congrArg (fun a=>f a 3) hd
        simp only [h0,h1,ite_true,ite_false,map_add,map_zero,Finsupp.add_apply,
          Finsupp.zero_apply,←hf3,←hf4,LinearEquiv.apply_symm_apply] at hh
        norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    have c1 : e x 1=0 := by
      by_contra h1
      have hh := congrArg (fun a=>f a 4) hd
      simp only [h1,c0,ite_false,ite_true,map_add,map_zero,Finsupp.add_apply,
        Finsupp.zero_apply,←hf3,←hf4,LinearEquiv.apply_symm_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    have hr := represents_add_tail (represents_bit (e x 2) hb2)
      (represents_add_tail (represents_bit (e x 3) hb3) (represents_bit (e x 4) hb4))
    simp only [ite_self,zero_add] at hr
    simp only [c0,c1,ite_true,zero_add] at hx
    rw [←hx] at hr
    exact represents_unique hxy hr
  exact ⟨fun x y=>(hz x).trans (hz y).symm⟩


set_option maxHeartbeats 3000000 in
private theorem target_basis1_third_nonzero
    (c : model.classical.sphere.Page 3 (16,140))
    (hc : RepresentsOnPage model.classical.sphere 3 (16,140)
      (KIP126.Computation.Table.basis .sphere 16 140 1) c) : c ≠ 0 := by
  classical
  let E := model.classical.sphere
  have hs2 : E.r₀ ≤ 2 := by
    change (model.classical.obj KIP126.StableHomotopy.SphereSpectrum).r₀ ≤ 2
    rw [model.classical.firstPage]
  have h341 : HasDifferential E 2 (12,138) (14,139)
      (KIP126.Computation.Table.basis .sphere 12 138 1)
      (KIP126.Computation.Table.basis .sphere 14 139 2) := by
    have hrow := KIP126.Computation.Table.result ⟨.sphere, .equation, 2, 12, 138, [1], 14, 139, [2], "S0_AdamsE2_ss", 3079⟩ (by
      exact List.mem_of_getElem? (l := KIP126.Computation.Table.Raw.claims) (i := 341) rfl)
    dsimp only [KIP126.Computation.Table.Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (12,138) (14,139) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees
      .sphere 12 138 [1] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees
      .sphere 14 139 [2] = true := rfl
    simp only [KIP126.Computation.Table.decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  have h343 : HasDifferential E 2 (14,139) (16,140)
      (KIP126.Computation.Table.basis .sphere 14 139 0)
      (KIP126.Computation.Table.basis .sphere 16 140 2) := by
    have hrow := KIP126.Computation.Table.result ⟨.sphere, .equation, 2, 14, 139, [0], 16, 140, [2], "S0_AdamsE2_ss", 3081⟩ (by
      exact List.mem_of_getElem? (l := KIP126.Computation.Table.Raw.claims) (i := 343) rfl)
    dsimp only [KIP126.Computation.Table.Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (14,139) (16,140) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees
      .sphere 14 139 [0] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees
      .sphere 16 140 [2] = true := rfl
    simp only [KIP126.Computation.Table.decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  have h342 : ReachesPage E 1000 (14,139)
      (KIP126.Computation.Table.basis .sphere 14 139 1) := by
    have hrow := KIP126.Computation.Table.result ⟨.sphere, .reaches, 1000, 14, 139, [1], 14, 139, [], "S0_AdamsE2_ss", 3080⟩ (by
      exact List.mem_of_getElem? (l := KIP126.Computation.Table.Raw.claims) (i := 342) rfl)
    dsimp only [KIP126.Computation.Table.Statement] at hrow
    obtain ⟨x,hx,hxlate⟩ := hrow
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees
      .sphere 14 139 [1] = true := rfl
    simp only [KIP126.Computation.Table.decode,vx,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
    rw [←hx] at hxlate
    exact hxlate
  obtain ⟨f,hf⟩ := KIP126.Computation.Table.basis_correct
    ⟨.sphere, 14, 139, ["449,1", "1,1,7,1,275,1", "0,2,425,1"]⟩ (by
      exact List.mem_of_getElem? (l := KIP126.Computation.Table.Raw.degrees) (i := 217) rfl)
  change E.Page 2 (14,139) ≃ₗ[ℤ] (Fin 3 →₀ F2) at f
  change ∀ i : Fin 3, f.symm (Finsupp.single i 1) =
    KIP126.Computation.Table.basis .sphere 14 139 i.val at hf
  obtain ⟨g,hg⟩ := KIP126.Computation.Table.basis_correct
    ⟨.sphere, 16, 140, ["9,1,261,1", "1,1,438,1", "0,1,448,1", "0,2,440,1", "0,2,439,1"]⟩ (by
      exact List.mem_of_getElem? (l := KIP126.Computation.Table.Raw.degrees) (i := 231) rfl)
  change E.Page 2 (16,140) ≃ₗ[ℤ] (Fin 5 →₀ F2) at g
  change ∀ i : Fin 5, g.symm (Finsupp.single i 1) =
    KIP126.Computation.Table.basis .sphere 16 140 i.val at hg
  have hg1 : g.symm (Finsupp.single (1 : Fin 5) 1) =
      KIP126.Computation.Table.basis .sphere 16 140 1 := hg 1
  have hg2 : g.symm (Finsupp.single (2 : Fin 5) 1) =
      KIP126.Computation.Table.basis .sphere 16 140 2 := hg 2
  have g1 : g (KIP126.Computation.Table.basis .sphere 16 140 1) =
      Finsupp.single (1 : Fin 5) 1 := by
    simpa only [LinearEquiv.apply_symm_apply] using (congrArg g hg1).symm
  have g2 : g (KIP126.Computation.Table.basis .sphere 16 140 2) =
      Finsupp.single (2 : Fin 5) 1 := by
    simpa only [LinearEquiv.apply_symm_apply] using (congrArg g hg2).symm
  let δ : E.Page 2 (14,139) ⟶ E.Page 2 (16,140) :=
    E.d 2 (14,139) ≫ eqToHom (congrArg (E.Page 2) h343.target_degree)
  have d0 : δ (KIP126.Computation.Table.basis .sphere 14 139 0) =
      KIP126.Computation.Table.basis .sphere 16 140 2 := h343.eq_on_page_two.2
  have d1 : δ (KIP126.Computation.Table.basis .sphere 14 139 1) = 0 := by
    have hd := represents_d_zero_of_later hs2 (by decide : (2 : ℤ) < 1000)
      (represents_two_self _) h342
    change (E.d 2 (14,139) ≫ _) _ = 0
    rw [ModuleCat.comp_apply,hd,map_zero]
  have d2 : δ (KIP126.Computation.Table.basis .sphere 14 139 2) = 0 := by
    obtain ⟨a,ha,hda⟩ := differential_target_cycle h341
    rw [←ha.eq_on_page_two] at hda
    change (E.d 2 (14,139) ≫ _) _ = 0
    rw [ModuleCat.comp_apply,hda,map_zero]
  have incoming (v : E.Page 2 (14,139)) : g (δ v) 1 = 0 := by
    have hex := finite_basis_expansion f v
    simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,hf,add_zero] at hex
    change v = (if f v 0 = 0 then 0 else KIP126.Computation.Table.basis .sphere 14 139 0) +
      ((if f v 1 = 0 then 0 else KIP126.Computation.Table.basis .sphere 14 139 1) +
       (if f v 2 = 0 then 0 else KIP126.Computation.Table.basis .sphere 14 139 2)) at hex
    have hd := congrArg δ hex
    simp only [map_add,apply_ite,map_zero] at hd
    simp only [d0,d1,d2,ite_self,add_zero] at hd
    have hh := congrArg (fun a => g a (1 : Fin 5)) hd
    by_cases h0 : f v 0 = 0
    · simpa only [h0,ite_true,map_zero,Finsupp.zero_apply] using hh
    · have hcoord : g (KIP126.Computation.Table.basis .sphere 16 140 2) 1 = 0 := by
        rw [g2]
        norm_num [Finsupp.single_apply,Fin.ext_iff]
      simpa only [h0,ite_false,hcoord] using hh
  apply represents_next_nonzero_of_not_incoming_at h343.target_degree hs2 (by decide)
    hc (RepresentsOnPage.self_two _)
  intro v hv
  have hzero := incoming v
  have heq := congrArg (fun a => g a (1 : Fin 5)) hv
  have hone : g (KIP126.Computation.Table.basis .sphere 16 140 1) 1 = 1 := by
    rw [g1]
    exact Finsupp.single_eq_same
  exact zero_ne_one (hzero.symm.trans (heq.trans hone))


set_option maxHeartbeats 3000000 in
private theorem e5_zero_of_c1_nonzero
    (hne : ∀ c : model.classical.sphere.Page 3 (16,140),
      RepresentsOnPage model.classical.sphere 3 (16,140)
        (basis .sphere 16 140 1) c → c≠0) :
    Subsingleton (model.classical.sphere.Page 5 (13,138)) := by
  classical
  let E := model.classical.sphere
  have hs2 : E.r₀≤2 := by
    change model.classical.sphere.r₀≤2
    rw [model.classical.firstPage]
  have hs3 : E.r₀≤3 := hs2.trans (by decide)
  have h325 : HasDifferential E 2 (11,137) (13,138)
      (basis .sphere 11 137 0) (basis .sphere 13 138 3) := by
    have hrow := result ⟨.sphere, .equation, 2, 11, 137, [0], 13, 138, [3], "S0_AdamsE2_ss", 3008⟩ (by
      exact List.mem_of_getElem? (i := 325) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 2 (11,137) (13,138) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 11 137 [0]=true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 13 138 [3]=true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    exact h
  have h326 : HasDifferential E 2 (11,137) (13,138)
      (basis .sphere 11 137 3) (basis .sphere 13 138 4) := by
    have hrow := result ⟨.sphere, .equation, 2, 11, 137, [3], 13, 138, [4], "S0_AdamsE2_ss", 3009⟩ (by
      exact List.mem_of_getElem? (i := 326) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 2 (11,137) (13,138) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 11 137 [3]=true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 13 138 [4]=true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    exact h
  have h327 : HasDifferential E 4 (9,135) (13,138)
      (basis .sphere 9 135 2) (basis .sphere 13 138 0) := by
    have hrow := result ⟨.sphere, .equation, 4, 9, 135, [2], 13, 138, [0], "S0_AdamsE2_ss", 3010⟩ (by
      exact List.mem_of_getElem? (i := 327) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 4 (9,135) (13,138) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 9 135 [2]=true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 13 138 [0]=true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    exact h
  have h328 : HasDifferential E 4 (9,135) (13,138)
      (basis .sphere 9 135 1) (basis .sphere 13 138 2) := by
    have hrow := result ⟨.sphere, .equation, 4, 9, 135, [1], 13, 138, [2], "S0_AdamsE2_ss", 3011⟩ (by
      exact List.mem_of_getElem? (i := 328) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 4 (9,135) (13,138) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 9 135 [1]=true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 13 138 [2]=true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    exact h
  have h329 : HasDifferential E 3 (13,138) (16,140)
      (basis .sphere 13 138 1) (basis .sphere 16 140 1) := by
    have hrow := result ⟨.sphere, .equation, 3, 13, 138, [1], 16, 140, [1], "S0_AdamsE2_ss", 3012⟩ (by
      exact List.mem_of_getElem? (i := 329) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 3 (13,138) (16,140) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 13 138 [1]=true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 16 140 [1]=true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    exact h
  obtain ⟨e,he⟩ := basis_correct
    ⟨.sphere,13,138,["24,1,190,1", "3,1,335,1", "0,1,425,1", "0,4,391,1", "0,5,375,1"]⟩ (by
      exact List.mem_of_getElem? (i := 209) (by rfl))
  change E.Page 2 (13,138) ≃ₗ[ℤ] (Fin 5 →₀ F2) at e
  change ∀ i : Fin 5, e.symm (Finsupp.single i 1)=basis .sphere 13 138 i.val at he
  have kill0 : RepresentsOnPage E 5 (13,138) (basis .sphere 13 138 0) 0 :=
    differential_target_later_zero (hs2.trans (by decide)) (by decide) h327
  have kill2 : RepresentsOnPage E 5 (13,138) (basis .sphere 13 138 2) 0 :=
    differential_target_later_zero (hs2.trans (by decide)) (by decide) h328
  have kill3 : RepresentsOnPage E 5 (13,138) (basis .sphere 13 138 3) 0 :=
    differential_target_later_zero hs2 (by decide) h325
  have kill4 : RepresentsOnPage E 5 (13,138) (basis .sphere 13 138 4) 0 :=
    differential_target_later_zero hs2 (by decide) h326
  obtain ⟨_,_,a04,_,ha04,_⟩ := h327
  obtain ⟨a0,ha0⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤4) ha04
  obtain ⟨_,_,a24,_,ha24,_⟩ := h328
  obtain ⟨a2,ha2⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤4) ha24
  obtain ⟨hdeg,a1,c1,ha1,hc1,hd1⟩ := h329
  have c1ne : c1≠0 := hne c1 hc1
  have hd0 : E.d 3 (13,138) a0=0 :=
    represents_d_zero_of_later hs3 (by decide : (3:ℤ)<4) ha0 ⟨a04,ha04⟩
  have hd2 : E.d 3 (13,138) a2=0 :=
    represents_d_zero_of_later hs3 (by decide : (3:ℤ)<4) ha2 ⟨a24,ha24⟩
  have ha3 : RepresentsOnPage E 3 (13,138) (basis .sphere 13 138 3) 0 :=
    differential_target_later_zero hs2 (by decide) h325
  have ha4 : RepresentsOnPage E 3 (13,138) (basis .sphere 13 138 4) 0 :=
    differential_target_later_zero hs2 (by decide) h326
  let δ : E.Page 3 (13,138) ⟶ E.Page 3 (16,140) :=
    E.d 3 (13,138) ≫ eqToHom (congrArg (E.Page 3) hdeg)
  have d0 : δ a0=0 := by
    change (E.d 3 (13,138) ≫ _) a0=0
    rw [ModuleCat.comp_apply,hd0,map_zero]
  have d1 : δ a1=c1 := hd1
  have d2 : δ a2=0 := by
    change (E.d 3 (13,138) ≫ _) a2=0
    rw [ModuleCat.comp_apply,hd2,map_zero]
  have δbit (b : F2) (a : E.Page 3 (13,138)) :
      δ (if b=0 then 0 else a)=if b=0 then 0 else δ a := by
    by_cases hb : b=0 <;> simp only [hb,ite_true,ite_false,map_zero]
  have hz (y : E.Page 5 (13,138)) : y=0 := by
    obtain ⟨x,hxy⟩ := page_has_initial_representative (by decide) y
    have hx := finite_basis_expansion e x
    simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero,he] at hx
    change x=(if e x 0=0 then 0 else basis .sphere 13 138 0) +
      ((if e x 1=0 then 0 else basis .sphere 13 138 1) +
      ((if e x 2=0 then 0 else basis .sphere 13 138 2) +
      ((if e x 3=0 then 0 else basis .sphere 13 138 3) +
       (if e x 4=0 then 0 else basis .sphere 13 138 4)))) at hx
    have sumrep3 := represents_add_tail (represents_bit (e x 0) ha0)
      (represents_add_tail (represents_bit (e x 1) ha1)
        (represents_add_tail (represents_bit (e x 2) ha2)
          (represents_add_tail (represents_bit (e x 3) ha3) (represents_bit (e x 4) ha4))))
    have rep3x : RepresentsOnPage E 3 (13,138) x
        ((if e x 0=0 then 0 else a0) + ((if e x 1=0 then 0 else a1) +
          (if e x 2=0 then 0 else a2))) := by
      simp only [ite_self,add_zero] at sumrep3
      rw [←hx] at sumrep3
      exact sumrep3
    have dx : δ ((if e x 0=0 then 0 else a0) + ((if e x 1=0 then 0 else a1) +
        (if e x 2=0 then 0 else a2)))=0 := by
      have hd := represents_d_zero_of_later hs3 (by decide : (3:ℤ)<5) rep3x ⟨y,hxy⟩
      change (E.d 3 (13,138) ≫ _) _=0
      rw [ModuleCat.comp_apply,hd,map_zero]
    have hbit1 : e x 1=0 := by
      by_contra hh
      apply c1ne
      simpa only [map_add,δbit,d0,d1,d2,ite_self,hh,ite_false,zero_add,add_zero] using dx
    have sumrep5 := represents_add_tail (represents_bit (e x 0) kill0)
      (represents_add_tail (represents_bit (e x 2) kill2)
        (represents_add_tail (represents_bit (e x 3) kill3) (represents_bit (e x 4) kill4)))
    have rep5x : RepresentsOnPage E 5 (13,138) x 0 := by
      rw [hx]
      simpa only [hbit1,ite_true,zero_add,ite_self] using sumrep5
    exact represents_unique hxy rep5x
  exact ⟨fun x y=>(hz x).trans (hz y).symm⟩

public theorem e5_stem125_af13 : Subsingleton (model.classical.sphere.Page 5 (13,138)) := by
  exact e5_zero_of_c1_nonzero target_basis1_third_nonzero

public theorem p_permanent_cycle : IsPermanentCycle model.classical.sphere (11,133) P := by
  obtain ⟨z, hz, _⟩ := p_permanent
  exact ⟨z, hz⟩
public theorem q_permanent_cycle : IsPermanentCycle model.classical.sphere (12,134) Q := by
  obtain ⟨z, hz, _⟩ := q_permanent
  exact ⟨z, hz⟩

public theorem table9 (r : ℤ) (_hr : 2 ≤ r) :
    ¬ HasNonzeroDifferential model.classical.sphere r (6,132) (14,139) (atom .x_126_6) T := by
  intro hd
  have hp := congrArg Prod.fst hd.toHasDifferential.target_degree
  have hdeg : (6 : ℤ) + r = 14 := by
    simpa only [ClassicalAdamsFamily.sphere, ClassicalAdamsFamily.obj,
      model.classical.differentialDegree, Prod.mk_add_mk, Prod.fst] using hp
  rcases t_only_incoming r hd.hit_target with hh | hh
  · omega
  · omega
public theorem no_other_incoming {r s t : ℤ} (_hr : 2 ≤ r) (h6 : r ≠ 6) (h12 : r ≠ 12)
    (x : model.classical.sphere.Page 2 (s,t)) :
    ¬ HasNonzeroDifferential model.classical.sphere r (s,t) (14,139) x T := by
  intro hx
  rcases t_only_incoming r hx.hit_target with hx | hx
  · exact h6 hx.1
  · exact h12 hx.1

public theorem cofiber_d3 : HasNonzeroDifferential nuCofiberSequence 3 (8,134) (11,136)
    cofiberSource (bottom 11 136 Y) := by sorry
/- Actual first-quotient exactness and finite Cν-page construction.
General naturality/suspension arguments adapted from Literature/Standard/
FiniteQuotientTriangle.lean and FiniteQuotientNaturality.lean (ef1c6c7);
finite incoming calculations adapted from historical 71e63c4,
Computation/LinCoordinates/Certificates/SphereAndCofiber/CofiberCoordinates.lean.
All are private proofs using the current fixed maps and registered inputs.
The literal bottom map is shown injective by an 8/16/2 cardinality argument;
no historical inclusion-coordinate equation or new public premise is assumed. -/
section
namespace CofiberResearch
open KIP126.Literature
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open CategoryTheory.Pretriangulated KIP126.StableHomotopy
open KIP126.Synthetic.Context KIP126.AdamsSynthetic KIP126.Kervaire.Route
open KIP126.Literature.Standard
open KIP126.AdamsSynthetic.Standard
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1800000

set_option maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
private theorem finite_quotient_shift_comparison (coh : BiShiftCoherence SyntheticSpectrum)
    (a : ℤ × ℤ) (q : ℕ) (X : SyntheticSpectrum)
    [cs : (SyntheticCategory.biShift (Syn := SyntheticSpectrum) a).CommShift ℤ]
    [(SyntheticCategory.biShift (Syn := SyntheticSpectrum) a).IsTriangulated] :
    ∃ e : XModLambdaN ((SyntheticCategory.biShift a).obj X) q ≅
      (SyntheticCategory.biShift a).obj (XModLambdaN X q),
      XModLambdaN.incl ((SyntheticCategory.biShift a).obj X) q ≫ e.hom =
        (SyntheticCategory.biShift a).map (XModLambdaN.incl X q) := by
  let oneComm (a : ℤ × ℤ) :
      SyntheticCategory.biShift (Syn := SyntheticSpectrum) a ⋙ SyntheticCategory.biShift (lambdaDegree 1) ≅
        SyntheticCategory.biShift (lambdaDegree 1) ⋙ SyntheticCategory.biShift a :=
    biShiftAddIso a (0,-1) (a+(0,-1)) rfl ≪≫
      (biShiftAddIso (0,-1) a (a+(0,-1)) (add_comm _ _)).symm

  let powerComm (a : ℤ × ℤ) : (q : ℕ) →
      SyntheticCategory.biShift (Syn := SyntheticSpectrum) a ⋙ SyntheticCategory.biShift (lambdaDegree q) ≅
        SyntheticCategory.biShift (lambdaDegree q) ⋙ SyntheticCategory.biShift a := fun q =>
    Nat.rec (motive := fun q =>
      SyntheticCategory.biShift (Syn := SyntheticSpectrum) a ⋙ SyntheticCategory.biShift (lambdaDegree q) ≅
        SyntheticCategory.biShift (lambdaDegree q) ⋙ SyntheticCategory.biShift a)
      (isoWhiskerLeft _ SyntheticCategory.biShift_zero ≪≫
        Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm ≪≫
        (isoWhiskerRight SyntheticCategory.biShift_zero _).symm)
      (fun q ih =>
        isoWhiskerLeft _ (lambdaShiftAddIso 1 q (q+1) (by omega)).symm ≪≫
        (Functor.associator _ _ _).symm ≪≫
        isoWhiskerRight (oneComm a) _ ≪≫ Functor.associator _ _ _ ≪≫
        isoWhiskerLeft _ ih ≪≫
        (Functor.associator _ _ _).symm ≪≫
        isoWhiskerRight (lambdaShiftAddIso 1 q (q+1) (by omega)) _) q

  have powerComm_square (coh : BiShiftCoherence SyntheticSpectrum) (a : ℤ × ℤ)
      (q : ℕ) (X : SyntheticSpectrum) :
      lambdaPow q ((SyntheticCategory.biShift a).obj X) =
        (powerComm a q).hom.app X ≫ (SyntheticCategory.biShift a).map (lambdaPow q X) := by
    induction q generalizing X with
    | zero =>
      simp (config := {congrConsts := false}) [powerComm, lambdaPow, ← Functor.map_comp]
    | succ q ih =>
      have h1 : (oneComm a).hom.app X ≫
          (SyntheticCategory.biShift a).map (SyntheticCategory.lam.app X) =
          SyntheticCategory.lam.app ((SyntheticCategory.biShift a).obj X) := by
        simpa (config := {congrConsts := false}) [oneComm, Category.assoc] using (coh.lambda_comm a X).symm
      apply (cancel_epi ((lambdaShiftAddIso 1 q (q+1) (by omega)).hom.app
        ((SyntheticCategory.biShift a).obj X))).mp
      rw [lambdaPow_succ_comparison]
      simp (config := {congrConsts := false}) only [powerComm, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
        isoWhiskerLeft_hom, isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app,
        Functor.associator_inv_app, Functor.associator_hom_app, Category.id_comp, Category.assoc]
      rw [Iso.hom_inv_id_app_assoc]
      rw [← Functor.map_comp, lambdaPow_succ_comparison, Functor.map_comp]
      have hn := (powerComm a q).hom.naturality (SyntheticCategory.lam.app X)
      have hn' := congrArg (fun h => h ≫ (SyntheticCategory.biShift a).map (lambdaPow q X)) hn
      simp (config := {congrConsts := false}) only [Functor.comp_map, Category.assoc] at hn'
      dsimp only [KIP126.Synthetic.Context.lambdaDegree, Functor.id_obj] at hn' ⊢
      erw [← hn']
      rw [← Category.assoc, ← Functor.map_comp, h1, ih]

  let F := SyntheticCategory.biShift (Syn := SyntheticSpectrum) a
  let T := Triangle.mk (lambdaPow q X) (XModLambdaN.incl X q) (XModLambdaN.proj X q)
  let T' := Triangle.mk (lambdaPow q (F.obj X))
    (XModLambdaN.incl (F.obj X) q) (XModLambdaN.proj (F.obj X) q)
  have hT : T ∈ distTriang SyntheticSpectrum := HasFunctorialCofiber.cofib_distinguished _
  have hT' : T' ∈ distTriang SyntheticSpectrum := HasFunctorialCofiber.cofib_distinguished _
  let e := isoTriangleOfIso₁₂ T' (F.mapTriangle.obj T) hT'
    (F.map_distinguished T hT) ((powerComm a q).app X) (Iso.refl _) (by
      change lambdaPow q (F.obj X) ≫ 𝟙 _ =
        (powerComm a q).hom.app X ≫ F.map (lambdaPow q X)
      simpa (config := {congrConsts := false}) only [Category.comp_id] using powerComm_square coh a q X)
  refine ⟨Triangle.π₃.mapIso e, ?_⟩
  have h := e.hom.comm₂
  change XModLambdaN.incl (F.obj X) q ≫ e.hom.hom₃ =
    e.hom.hom₂ ≫ F.map (XModLambdaN.incl X q) at h
  change XModLambdaN.incl (F.obj X) q ≫ e.hom.hom₃ =
    F.map (XModLambdaN.incl X q)
  simpa (config := {congrConsts := false}) only [e, isoTriangleOfIso₁₂_hom_hom₂, Iso.refl_hom, Category.id_comp] using h

/-- An actual finite quotient comparison with ordinary suspension, preserving
the selected quotient inclusion. This construction alone does not assert
that the quotient of a normalized triangle is distinguished. -/
private theorem finite_quotient_suspension_comparison
    (q : ℕ) (X : SyntheticSpectrum) :
    ∃ esusp : XModLambdaN (X⟦(1:ℤ)⟧) q ≅ (XModLambdaN X q)⟦(1:ℤ)⟧,
      XModLambdaN.incl (X⟦(1:ℤ)⟧) q ≫ esusp.hom =
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl X q) := by
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (1,0)
  let η := SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1
  letI := model.exactness.shiftCommShift (1,0)
  letI := model.exactness.shiftExact (1,0)
  obtain ⟨e,he⟩ := finite_quotient_shift_comparison model.quotients.coherence (1,0) q X
  let eQ := (model.quotients.functoriality.functor q).mapIso (η.symm.app X)
  refine ⟨eQ ≪≫ e ≪≫ η.app (XModLambdaN X q), ?_⟩
  change XModLambdaN.incl (X⟦(1:ℤ)⟧) q ≫ XModLambdaN.map (η.inv.app X) q ≫
      e.hom ≫ η.hom.app (XModLambdaN X q) = _
  calc
    _ = (XModLambdaN.incl (X⟦(1:ℤ)⟧) q ≫ XModLambdaN.map (η.inv.app X) q) ≫
        e.hom ≫ η.hom.app (XModLambdaN X q) := by simp (config := {congrConsts := false}) only [Category.assoc]
    _ = (η.inv.app X ≫ XModLambdaN.incl (F.obj X) q) ≫
        e.hom ≫ η.hom.app (XModLambdaN X q) := by
      rw [←XModLambdaN.incl_naturality]
    _ = η.inv.app X ≫ F.map (XModLambdaN.incl X q) ≫
        η.hom.app (XModLambdaN X q) := by
      simpa (config := {congrConsts := false}) only [Category.assoc] using congrArg
        (fun z => η.inv.app X ≫ z ≫ η.hom.app (XModLambdaN X q)) he
    _ = η.inv.app X ≫ η.hom.app X ≫
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl X q) := by
      rw [η.hom.naturality]
    _ = _ := by rw [←Category.assoc,η.inv_hom_id_app,Category.id_comp]

end
end CofiberResearch
end

section
namespace CofiberResearch
open KIP126.Literature
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.Literature.Standard
open KIP126.AdamsSynthetic.Standard
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000

section Generic
private theorem first_quotient_infinity_rep_morphism
    {E E' : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) Tridegree}
    (f : E ⟶ E') (i : Tridegree) {x : E.Page 2 i} {e : (E.ssData i).eInfty}
    (h : ∃ z : (Subobject.underlying.obj ((E.ssData i).Z ⊤) : ModuleCat ℤ),
      (Subobject.ofLE _ _ ((E.ssData i).Z_anti le_top) ≫
        (E.ssData i).pageπ (↑(2-E.r₀).toNat : WithTop ℕ)) z = x ∧
      (E.ssData i).pageπ ⊤ z = e) :
    ∃ z : (Subobject.underlying.obj ((E'.ssData i).Z ⊤) : ModuleCat ℤ),
      (Subobject.ofLE _ _ ((E'.ssData i).Z_anti le_top) ≫
        (E'.ssData i).pageπ (↑(2-E'.r₀).toNat : WithTop ℕ)) z = f.pageMap 2 i x ∧
      (E'.ssData i).pageπ ⊤ z = f.eInftyMap i e := by
  have hstart := f.r₀_eq
  rcases E with ⟨⟨r₀,D,δ,d⟩,dd,Zs,Bs⟩
  rcases E' with ⟨⟨r₀',D',δ',d'⟩,dd',Zs',Bs'⟩
  dsimp at hstart
  subst r₀'
  obtain ⟨z,hz,he⟩ := h
  let n : WithTop ℕ := ↑(2-r₀).toNat
  refine ⟨f.toSSDataMorphism.cycleMap i ⊤ z, ?_, ?_⟩
  · have hs := f.toSSDataMorphism.cycleMap_ofLE_assoc i
      (r := n) (s := ⊤) le_top ((D' i).pageπ n)
    have hp := f.toSSDataMorphism.pageπ_pageMap i n
    have hq : (Subobject.ofLE ((D i).Z ⊤) ((D i).Z n) ((D i).Z_anti le_top) ≫
        (D i).pageπ n) ≫ f.toSSDataMorphism.pageMap i n =
        f.toSSDataMorphism.cycleMap i ⊤ ≫
          Subobject.ofLE ((D' i).Z ⊤) ((D' i).Z n) ((D' i).Z_anti le_top) ≫ (D' i).pageπ n := by
      rw [Category.assoc,hp]
      exact hs
    change ((Subobject.ofLE _ _ _ ≫ (D' i).pageπ n)
      (f.toSSDataMorphism.cycleMap i ⊤ z)) =
      ((f.toSSDataMorphism.pageMap i n ≫ eqToHom _) x)
    simpa only [ModuleCat.comp_apply, hz, eqToHom_refl, Category.comp_id, n]
      using (ConcreteCategory.congr_hom hq z).symm
  · have hp := f.toSSDataMorphism.pageπ_pageMap i ⊤
    change (D' i).pageπ ⊤ (f.toSSDataMorphism.cycleMap i ⊤ z) =
      f.toSSDataMorphism.pageMap i ⊤ e
    simpa only [ModuleCat.comp_apply, he] using
      (ConcreteCategory.congr_hom hp z).symm

private theorem first_quotient_infinity_rep_map {Syn : Type u} [SyntheticCategory.{u,v} Syn]
    {F : SyntheticAdamsFamily Syn} {X Y : Syn} (g : X ⟶ Y)
    (i : Tridegree) {x : (F.obj X).Page 2 i}
    {e : ((F.obj X).sequence.ssData i).eInfty}
    (h : HasInfinityRepresentative (F.obj X) 2 i x e) :
    HasInfinityRepresentative (F.obj Y) 2 i (F.pageMap g 2 i x)
      ((F.map g).eInftyMap i e) := by
  obtain ⟨hr,z,hz,he⟩ := h
  obtain ⟨z',hz',he'⟩ := first_quotient_infinity_rep_morphism (F.map g) i ⟨z,hz,he⟩
  exact ⟨hr,z',hz',he'⟩

/-- Detection is natural for the prescribed homotopy and E∞ maps of one convergent map. -/
private theorem first_quotient_detects_map {Syn : Type u} [SyntheticCategory.{u,v} Syn]
    [HasFunctorialCofiber (C := Syn)] {H : Syn} {unit : S_0_0 ⟶ H}
    {F : SyntheticAdamsFamily Syn} {P : SyntheticTowerPresentation unit F}
    {X Y : Syn} {g : X ⟶ Y} {cx : SyntheticTowerConvergence P X}
    {cy : SyntheticTowerConvergence P Y}
    (M : ConvergentMap F g cx.toConvergence cy.toConvergence)
    (i : Tridegree) {x : (F.obj X).Page 2 i}
    {a : BiHom (i.2.1-i.1) i.2.2 X}
    (h : KIP126.AdamsSynthetic.Detects cx i x a) :
    KIP126.AdamsSynthetic.Detects cy i (F.pageMap g 2 i x) (a ≫ g) := by
  obtain ⟨e, he, b, hb, hgr⟩ := h
  let hc := M.comparison.filtration_compat i.1 (i.2.1-i.1,i.2.2)
  let b' := hc.choose b
  refine ⟨(F.map g).eInftyMap i e, first_quotient_infinity_rep_map g i he, b', ?_, ?_⟩
  · have hmap := ConcreteCategory.congr_hom hc.choose_spec b
    have heq := ConcreteCategory.congr_hom
      (congrFun M.abutment_eq (i.2.1-i.1,i.2.2))
      (((P.filtration X).F i.1 (i.2.1-i.1,i.2.2)).arrow b)
    change ((P.filtration Y).F i.1 (i.2.1-i.1,i.2.2)).arrow b' = _
    exact hmap.trans (heq.trans (congrArg (fun z => z ≫ g) hb))
  · have hm := M.comparison.iso_compat i
    simp only [SyntheticTowerConvergence.toConvergence, Filtration.transportGraded_self,
      Category.comp_id] at hm
    rw [M.infinity_eq] at hm
    have hm' := ConcreteCategory.congr_hom hm e
    change (cy.identification i).hom ((F.map g).eInftyMap i e) =
      Filtration.inducedAssocGradedMap M.comparison.aMap M.comparison.filtration_compat
        i.1 (i.2.1-i.1,i.2.2) ((cx.identification i).hom e) at hm'
    rw [hgr] at hm'
    have hg : (P.filtration X).toAssociatedGraded i.1 (i.2.1-i.1,i.2.2) ≫
        Filtration.inducedAssocGradedMap M.comparison.aMap M.comparison.filtration_compat
          i.1 (i.2.1-i.1,i.2.2) =
        hc.choose ≫ (P.filtration Y).toAssociatedGraded i.1 (i.2.1-i.1,i.2.2) := by
      exact cokernel.π_desc _ _ _
    exact hm'.trans (ConcreteCategory.congr_hom hg b)

private theorem first_quotient_familyPageMap_comp {Syn : Type u} [SyntheticCategory.{u,v} Syn]
    (F : SyntheticAdamsFamily Syn) {X Y Z : Syn} (f : X ⟶ Y) (g : Y ⟶ Z)
    (r : ℤ) (i : Tridegree) :
    F.pageMap (f ≫ g) r i = F.pageMap f r i ≫ F.pageMap g r i := by
  change (F.map (f ≫ g)).pageMap r i =
    (F.map f).pageMap r i ≫ (F.map g).pageMap r i
  rw [F.map_comp, SpectralSequenceMorphism.pageMap_comp]


variable {Syn : Type u} [SyntheticCategory.{u,v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  {H : Syn} {unit : S_0_0 ⟶ H} {F : SyntheticAdamsFamily Syn}
  {P : SyntheticTowerPresentation unit F} {X : Syn}

private theorem first_quotient_filtration_iff_of_infinity_zero (c : SyntheticTowerConvergence P X)
    (s t m w : ℤ) (hst : s ≤ t)
    (hz : ∀ j, s ≤ j → j < t → IsZero (((F.obj X).sequence.ssData (j,m+j,w)).eInfty))
    (a : BiHom m w X) : FiltrationAtLeast P s a ↔ FiltrationAtLeast P t a := by
  have hgraded (j : ℤ) (hj : s ≤ j) (hjt : j < t) :
      IsZero ((P.filtration X).associatedGraded j (m,w)) :=
    (hz j hj hjt).of_iso (towerGradedIso c (m,w) j).symm
  have he := (P.filtration X).eq_of_associatedGraded_isZero s t (m,w) hst hgraded
  have he' := congrArg (fun Q => a ∈ (ModuleCat.subobjectModule (syntheticHomotopy X (m,w))) Q) he
  simpa only [SyntheticTowerPresentation.filtration, OrderIso.apply_symm_apply,
    FiltrationAtLeast] using Iff.of_eq he'
private theorem first_quotient_filtration_map
    {Y : Syn} (f : X ⟶ Y) (s : ℤ) (p : ℤ × ℤ)
    (a : BiHom p.1 p.2 X) (ha : FiltrationAtLeast P s a) :
    FiltrationAtLeast P s (a ≫ f) := by
  obtain ⟨b,hb⟩ := ha
  refine ⟨b ≫ (P.map f).stage s.toNat,?_⟩
  change (b ≫ (P.map f).stage s.toNat) ≫ (P.tower Y).projection s = a ≫ f
  rw [Category.assoc,(P.map f).projection,←Category.assoc]
  exact congrArg (fun z => z ≫ f) hb

end Generic

private theorem first_quotient_finite_infinity_zero_outside (X : ClassicalObject) (q : ℕ) (hq : 0 < q)
    (s t w : ℤ) (hw : ¬ (0 ≤ t-w ∧ t-w < q)) :
    IsZero (((model.family.quotient (model.nu.functor.obj (X.obj model.auxiliary)) q).sequence.ssData
      (s,t,w)).eInfty) := by
  haveI : Subsingleton (KIP126.Literature.finiteEInftyModel model X q (s,t) w) := by
    dsimp only [KIP126.Literature.finiteEInftyModel]
    simp only [hw, ite_false]
    infer_instance
  haveI : Subsingleton (((model.family.quotient
      (model.nu.functor.obj (X.obj model.auxiliary)) q).sequence.ssData (s,t,w)).eInfty) :=
    (KIP126.Literature.Standard.eInfinity_finite X q hq (s,t) w).injective.subsingleton
  exact ModuleCat.isZero_of_subsingleton _

private theorem first_quotient_finite_high_filtration_zero (X : ClassicalObject) (q : ℕ) (hq : 0 < q)
    (m w s : ℤ) (hs : (q:ℤ) ≤ m+s-w)
    (a : BiHom m w (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
    (ha : FiltrationAtLeast model.syntheticTower s a) : a = 0 := by
  apply synthetic_homotopy_separated (.nu X) q m w a
  intro j
  by_cases hj : s ≤ (j:ℤ)
  · exact (first_quotient_filtration_iff_of_infinity_zero (model.convergence (.quotient q (.nu X)))
      s j m w hj (fun k hk _ => first_quotient_finite_infinity_zero_outside X q hq k (m+k) w (by omega)) a).mp ha
  · exact model.syntheticTower.filtrationSubmodule_antitone _ (m,w) (by omega) ha

/-- At the first quotient's upper filtration edge, the actual class is zero.
The quotient is taken after the given weight shift, exactly as in firstQuotient. -/
private theorem first_quotient_shifted_high_filtration_zero
    (Y : ClassicalObject) (a s t : ℤ)
    (d : BiHom (t-s) (t+a)
      (XModLambdaN ((SyntheticCategory.biShift (0,a)).obj
        (model.nu.functor.obj (Y.obj model.auxiliary))) 1))
    (hd : FiltrationAtLeast model.syntheticTower (s+1) d) : d = 0 := by
  letI := model.exactness.shiftCommShift (0,a)
  letI := model.exactness.shiftExact (0,a)
  let V := model.nu.functor.obj (Y.obj model.auxiliary)
  let A : SyntheticObject := .quotient 1 (.shift (0,a) (.nu Y))
  let B : SyntheticObject := .shift (0,a) (.quotient 1 (.nu Y))
  obtain ⟨e,_⟩ := finite_quotient_shift_comparison model.quotients.coherence
    (0,a) 1 V
  have hde : FiltrationAtLeast model.syntheticTower (s+1) (d ≫ e.hom) :=
    first_quotient_filtration_map e.hom (s+1) (t-s,t+a) d hd
  let E : FilteredPieceIso (model.convergence (.quotient 1 (.nu Y))).filtration
      (model.convergence B).filtration (t-s,t) (t-s,t+a) := by
    have hp : (t-s,t)+(0,a) = (t-s,t+a) := by ext <;> simp
    exact hp ▸ (essShift (0,a)).filtered (.quotient 1 (.nu Y)) (t-s,t)
  have hmem : d ≫ e.hom ∈ ModuleCat.subobjectModule _
      ((model.convergence B).filtration.F (s+1) (t-s,t+a)) := by
    dsimp only [SyntheticTowerConvergence.filtration,SyntheticTowerPresentation.filtration,
      FiltrationAtLeast,B,V,SyntheticObject.obj,syntheticHomotopy] at hde ⊢
    simpa only [OrderIso.apply_symm_apply] using hde
  obtain ⟨b,hb⟩ := hmem
  have hcomm := ConcreteCategory.congr_hom (E.symm.level_arrow (s+1)) b
  dsimp only [FilteredPieceIso.symm] at hcomm
  simp only [ModuleCat.comp_apply] at hcomm
  have hbase : FiltrationAtLeast model.syntheticTower (s+1)
      (E.ambient.inv (d ≫ e.hom)) := by
    have hbase' : E.ambient.inv (d ≫ e.hom) ∈ ModuleCat.subobjectModule _
        ((model.convergence (.quotient 1 (.nu Y))).filtration.F (s+1) (t-s,t)) := by
      refine ⟨(E.level (s+1)).inv b,?_⟩
      change ((model.convergence (.quotient 1 (.nu Y))).filtration.F
        (s+1) (t-s,t)).arrow ((E.level (s+1)).inv b) = E.ambient.inv (d ≫ e.hom)
      simpa only [hb,Iso.symm_hom] using hcomm
    simpa only [SyntheticTowerConvergence.filtration,SyntheticTowerPresentation.filtration,
      OrderIso.apply_symm_apply,FiltrationAtLeast] using hbase'
  have hzero := first_quotient_finite_high_filtration_zero Y 1 (by decide)
    (t-s) t (s+1) (by omega) (E.ambient.inv (d ≫ e.hom)) hbase
  have hdzero : d ≫ e.hom = 0 := by
    apply (ModuleCat.mono_iff_injective E.ambient.inv).mp inferInstance
    simpa only [map_zero] using hzero
  apply (cancel_mono e.hom).mp
  simpa only [zero_comp] using hdzero

private def first_quotient_nu_label
    (X : ClassicalObject) (a s t : ℤ)
    (x : (model.classical.obj (X.obj model.auxiliary)).Page 2 (s,t)) :
    (model.family.obj ((SyntheticCategory.biShift (0,a)).obj
      (model.nu.functor.obj (X.obj model.auxiliary)))).Page 2 (s,t,t+a) := by
  simpa only [Nat.cast_zero,sub_zero] using model.comparison.nuE2 X a s t 0 x

private theorem first_quotient_nu_label_natural
    (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary) (a s t : ℤ)
    (x : (model.classical.obj (X.obj model.auxiliary)).Page 2 (s,t)) :
    model.family.pageMap ((SyntheticCategory.biShift (0,a)).map
      (model.nu.functor.map f)) 2 (s,t,t+a) (first_quotient_nu_label X a s t x) =
      first_quotient_nu_label Y a s t
        ((model.classical.functor.map f).pageMap 2 (s,t) x) := by
  have regrade (w w' : ℤ) (hw : w=w')
      (g : ((SyntheticCategory.biShift (0,a)).obj
          (model.nu.functor.obj (X.obj model.auxiliary))) ⟶
        ((SyntheticCategory.biShift (0,a)).obj
          (model.nu.functor.obj (Y.obj model.auxiliary))))
      (b : (model.family.obj ((SyntheticCategory.biShift (0,a)).obj
        (model.nu.functor.obj (X.obj model.auxiliary)))).Page 2 (s,t,w))
      (c : (model.family.obj ((SyntheticCategory.biShift (0,a)).obj
        (model.nu.functor.obj (Y.obj model.auxiliary)))).Page 2 (s,t,w))
      (h : model.family.pageMap g 2 (s,t,w) b = c) :
      model.family.pageMap g 2 (s,t,w')
        (Eq.mp (congrArg (fun w => ↥((model.family.obj
          ((SyntheticCategory.biShift (0,a)).obj
            (model.nu.functor.obj (X.obj model.auxiliary)))).Page 2 (s,t,w))) hw) b) =
      Eq.mp (congrArg (fun w => ↥((model.family.obj
        ((SyntheticCategory.biShift (0,a)).obj
          (model.nu.functor.obj (Y.obj model.auxiliary)))).Page 2 (s,t,w))) hw) c := by
    subst w'
    exact h
  exact regrade (t+a-(0:ℕ)) (t+a) (by simp)
    _ _ _ (model.comparison.nu_natural X Y f a s t 0 x)

/-- Before finite-window vanishing, naturality already holds modulo precisely
one next filtration step, with the same x and the actual Q_1(nu f). -/
private theorem first_quotient_nu_naturality_next_filtration
    (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary) (a s t : ℤ)
    (x : (model.classical.obj (X.obj model.auxiliary)).Page 2 (s,t)) :
    FiltrationAtLeast model.syntheticTower (s+1)
      ((model.firstQuotient X a s t).symm x ≫
        XModLambdaN.map ((SyntheticCategory.biShift (0,a)).map (model.nu.functor.map f)) 1 -
      (model.firstQuotient Y a s t).symm
        ((model.classical.functor.map f).pageMap 2 (s,t) x)) := by
  let VX := (SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,a)).obj
    (model.nu.functor.obj (X.obj model.auxiliary))
  let VY := (SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,a)).obj
    (model.nu.functor.obj (Y.obj model.auxiliary))
  let g : VX ⟶ VY := (SyntheticCategory.biShift (0,a)).map (model.nu.functor.map f)
  let qg := XModLambdaN.map g 1
  let AX : SyntheticObject := .quotient 1 (.shift (0,a) (.nu X))
  let AY : SyntheticObject := .quotient 1 (.shift (0,a) (.nu Y))
  have hdX := model.comparisonCompatible.first_quotient X a s t x
  have hdY := model.comparisonCompatible.first_quotient Y a s t
    ((model.classical.functor.map f).pageMap 2 (s,t) x)
  have hdMap := first_quotient_detects_map (model.convergentMap AX AY qg) (s,t,t+a) hdX
  have hlabels : model.family.pageMap qg 2 (s,t,t+a)
      (model.family.pageMap (XModLambdaN.incl VX 1) 2 (s,t,t+a)
        (first_quotient_nu_label X a s t x)) =
    model.family.pageMap (XModLambdaN.incl VY 1) 2 (s,t,t+a)
      (first_quotient_nu_label Y a s t
        ((model.classical.functor.map f).pageMap 2 (s,t) x)) := by
    rw [←ModuleCat.comp_apply,←first_quotient_familyPageMap_comp,
      ←XModLambdaN.incl_naturality,first_quotient_familyPageMap_comp,ModuleCat.comp_apply]
    rw [first_quotient_nu_label_natural X Y f a s t x]
  have hdMap' : Detects (model.convergence AY) (s,t,t+a)
      (model.family.pageMap (XModLambdaN.incl VY 1) 2 (s,t,t+a)
        (first_quotient_nu_label Y a s t
          ((model.classical.functor.map f).pageMap 2 (s,t) x)))
      ((model.firstQuotient X a s t).symm x ≫ qg) := by
    rw [←hlabels]
    exact hdMap
  exact detects_sub_filtration (model.convergence AY) (s,t,t+a) hdMap' hdY

/-- Strict naturality of the specified first-quotient coordinates for actual
weight-shifted nu-images of classical maps. This is not an assertion about
positive-exponent normalized lifts. -/
private theorem first_quotient_nu_naturality
    (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary) (a s t : ℤ)
    (x : (model.classical.obj (X.obj model.auxiliary)).Page 2 (s,t)) :
    (model.firstQuotient X a s t).symm x ≫
        XModLambdaN.map ((SyntheticCategory.biShift (0,a)).map (model.nu.functor.map f)) 1 =
      (model.firstQuotient Y a s t).symm
        ((model.classical.functor.map f).pageMap 2 (s,t) x) := by
  apply sub_eq_zero.mp
  exact first_quotient_shifted_high_filtration_zero Y a s t _
    (first_quotient_nu_naturality_next_filtration X Y f a s t x)


/-- Zero positive lambda power is exactly the existing inverse zero shift.
This uses the unit coherence of the given bigraded action. -/
private theorem normalized_zero_positive_power (A : SyntheticSpectrum) :
    lambdaToPositivePow 0 A = SyntheticCategory.biShift_zero.inv.app A := by
  have hu := model.quotients.coherence.right_unit (0,0) A
  dsimp only [biShiftAddIso] at hu
  simp only [eqToIso_refl,Iso.trans_refl] at hu
  dsimp only [lambdaToPositivePow]
  norm_num only
  simp only [eqToHom_refl,Category.id_comp]
  change SyntheticCategory.biShift_zero.inv.app A ≫
    ((SyntheticCategory.biShift_comp (0,0) (0,0)).inv.app A ≫
      SyntheticCategory.biShift_zero.hom.app ((SyntheticCategory.biShift (0,0)).obj A)) = _
  erw [←hu,Iso.inv_hom_id_app,Category.comp_id]

private theorem normalized_zero_factorization_form {A B : SyntheticSpectrum} {k : ℕ}
    (hk : k=0) (M : (SyntheticCategory.biShift (0,(k:ℤ))).obj A ⟶ B)
    (g : A ⟶ B) (hM : lambdaToPositivePow k A ≫ M = g) :
    M = eqToHom (congrArg (fun j : ℕ =>
      (SyntheticCategory.biShift (0,(j:ℤ))).obj A) hk) ≫
        SyntheticCategory.biShift_zero.hom.app A ≫ g := by
  subst k
  rw [normalized_zero_positive_power] at hM
  have h := congrArg (fun z => SyntheticCategory.biShift_zero.hom.app A ≫ z) hM
  erw [←Category.assoc,Iso.hom_inv_id_app,Category.id_comp] at h
  simpa only [eqToHom_refl,Category.id_comp] using h

/-- The explicit source comparison to F_(0,0) nu X; its only transport is
exactly the given equality of the actual normalization exponent with zero. -/
private def normalized_zero_source_iso (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (h0 : normalizedExponent model.classicalTower f = 0) :
    (SyntheticCategory.biShift (0,(normalizedExponent model.classicalTower f:ℤ))).obj
        (model.nu.functor.obj (X.obj model.auxiliary)) ≅
      (SyntheticCategory.biShift (0,0)).obj
        (model.nu.functor.obj (X.obj model.auxiliary)) :=
  eqToIso (congrArg (fun k : ℕ => (SyntheticCategory.biShift (0,(k:ℤ))).obj
    (model.nu.functor.obj (X.obj model.auxiliary))) h0)

/-- A selected normalized map of exponent zero is strictly the nu-image
through the displayed source comparison and the existing zero-shift iso. -/
private theorem normalized_map_at_zero (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (h0 : normalizedExponent model.classicalTower f = 0) :
    (model.normalizedMap X Y f).map =
      (normalized_zero_source_iso X Y f h0).hom ≫
        SyntheticCategory.biShift_zero.hom.app _ ≫ model.nu.functor.map f := by
  exact normalized_zero_factorization_form h0 _ _ (model.normalizedMap X Y f).factorization

/-- The same first-quotient coordinates calibrate the actual selected
normalized map when its exponent is zero. The source class is transported
by the inverse of the explicit F_(0,0) comparison, through the actual Q_1. -/
private theorem first_quotient_normalized_map_at_zero
    (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (h0 : normalizedExponent model.classicalTower f = 0) (s t : ℤ)
    (x : (model.classical.obj (X.obj model.auxiliary)).Page 2 (s,t)) :
    (model.firstQuotient X 0 s t).symm x ≫
        XModLambdaN.map (normalized_zero_source_iso X Y f h0).inv 1 ≫
        XModLambdaN.map (model.normalizedMap X Y f).map 1 =
      (model.firstQuotient Y 0 s t).symm
          ((model.classical.functor.map f).pageMap 2 (s,t) x) ≫
        XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1 := by
  have hM := normalized_map_at_zero X Y f h0
  have hzero := SyntheticCategory.biShift_zero.hom.naturality (model.nu.functor.map f)
  dsimp only [Functor.id_map] at hzero
  calc
    _ = (model.firstQuotient X 0 s t).symm x ≫
        XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _ ≫
          model.nu.functor.map f) 1 := by
      rw [hM,model.quotients.functoriality.map_comp]
      rw [←Category.assoc (XModLambdaN.map _ _),
        ←model.quotients.functoriality.map_comp]
      simp only [Iso.inv_hom_id,model.quotients.functoriality.map_id,Category.id_comp]
    _ = (model.firstQuotient X 0 s t).symm x ≫
        XModLambdaN.map ((SyntheticCategory.biShift (0,0)).map (model.nu.functor.map f) ≫
          SyntheticCategory.biShift_zero.hom.app _) 1 := by rw [hzero]
    _ = ((model.firstQuotient X 0 s t).symm x ≫
        XModLambdaN.map ((SyntheticCategory.biShift (0,0)).map (model.nu.functor.map f)) 1) ≫
        XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1 := by
      rw [model.quotients.functoriality.map_comp,Category.assoc]
    _ = _ := by rw [first_quotient_nu_naturality X Y f 0 s t x]


/-- At exponent zero the negative-target version is the original map
followed by the explicit inverse zero shift and the same index transport. -/
private theorem normalized_negative_lift_at_zero {A B : SyntheticSpectrum} {k : ℕ}
    (h0 : k=0) (M : (SyntheticCategory.biShift (0,(k:ℤ))).obj A ⟶ B)
    (g : A ⟶ B) (hM : lambdaToPositivePow k A ≫ M = g) :
    negativeLift k M = g ≫ SyntheticCategory.biShift_zero.inv.app B ≫
      eqToHom (congrArg (fun j : ℕ =>
        (SyntheticCategory.biShift (0,-(j:ℤ))).obj B) h0).symm := by
  subst k
  simp only [eqToHom_refl,Category.comp_id]
  apply ((SyntheticCategory.biShift_zero.app B).eq_comp_inv).mpr
  have hnegative : negativeLift 0 M ≫ lambdaPow 0 B = lambdaToPositivePow 0 A ≫ M := by
    dsimp only [negativeLift,lambdaToPositivePow]
    simp only [Category.assoc]
    rw [lambdaPow_naturality]
  exact hnegative.trans hM


/-- Direct first-quotient calibration of the literal negative-target
normalized map of exponent zero. The target comparison to F_(0,0) is
explicit and retains the original dependent exponent transport. -/
private theorem first_quotient_normalized_negative_lift_at_zero
    (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (h0 : normalizedExponent model.classicalTower f = 0) (s t : ℤ)
    (x : (model.classical.obj (X.obj model.auxiliary)).Page 2 (s,t)) :
    let eNeg : (SyntheticCategory.biShift
          (0,-(normalizedExponent model.classicalTower f:ℤ))).obj
          (model.nu.functor.obj (Y.obj model.auxiliary)) ≅
        (SyntheticCategory.biShift (0,0)).obj
          (model.nu.functor.obj (Y.obj model.auxiliary)) :=
      eqToIso (congrArg (fun k : ℕ => (SyntheticCategory.biShift (0,-(k:ℤ))).obj
        (model.nu.functor.obj (Y.obj model.auxiliary))) h0)
    (model.firstQuotient X 0 s t).symm x ≫
        XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1 ≫
        XModLambdaN.map (negativeLift (normalizedExponent model.classicalTower f)
          (model.normalizedMap X Y f).map) 1 =
      (model.firstQuotient Y 0 s t).symm
          ((model.classical.functor.map f).pageMap 2 (s,t) x) ≫
        XModLambdaN.map eNeg.inv 1 := by
  dsimp only
  let eNeg : (SyntheticCategory.biShift
        (0,-(normalizedExponent model.classicalTower f:ℤ))).obj
        (model.nu.functor.obj (Y.obj model.auxiliary)) ≅
      (SyntheticCategory.biShift (0,0)).obj
        (model.nu.functor.obj (Y.obj model.auxiliary)) :=
    eqToIso (congrArg (fun k : ℕ => (SyntheticCategory.biShift (0,-(k:ℤ))).obj
      (model.nu.functor.obj (Y.obj model.auxiliary))) h0)
  have hneg := normalized_negative_lift_at_zero h0 (model.normalizedMap X Y f).map
    (model.nu.functor.map f) (model.normalizedMap X Y f).factorization
  have hzero := SyntheticCategory.biShift_zero.hom.naturality (model.nu.functor.map f)
  dsimp only [Functor.id_map] at hzero
  have hcomp : SyntheticCategory.biShift_zero.hom.app _ ≫
      negativeLift (normalizedExponent model.classicalTower f)
        (model.normalizedMap X Y f).map =
    (SyntheticCategory.biShift (0,0)).map (model.nu.functor.map f) ≫ eNeg.inv := by
    rw [hneg,←Category.assoc _ (model.nu.functor.map f),←hzero]
    simp only [Category.assoc,←Category.assoc (SyntheticCategory.biShift_zero.hom.app _),
      Iso.hom_inv_id_app,Category.id_comp]
    rfl
  calc
    _ = (model.firstQuotient X 0 s t).symm x ≫
        XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _ ≫
          negativeLift (normalizedExponent model.classicalTower f)
            (model.normalizedMap X Y f).map) 1 := by
      rw [model.quotients.functoriality.map_comp]
    _ = (model.firstQuotient X 0 s t).symm x ≫
        XModLambdaN.map ((SyntheticCategory.biShift (0,0)).map (model.nu.functor.map f) ≫
          eNeg.inv) 1 := by rw [hcomp]
    _ = ((model.firstQuotient X 0 s t).symm x ≫
        XModLambdaN.map ((SyntheticCategory.biShift (0,0)).map (model.nu.functor.map f)) 1) ≫
        XModLambdaN.map eNeg.inv 1 := by
      rw [model.quotients.functoriality.map_comp,Category.assoc]
    _ = _ := by rw [first_quotient_nu_naturality X Y f 0 s t x]

end
end CofiberResearch
end

section
namespace CofiberResearch
open KIP126.Literature
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.AdamsSynthetic
open KIP126.AdamsSynthetic.Standard KIP126.Kervaire.Route KIP126.Literature
open KIP126.Literature.Standard KIP126.Computation.Table
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
section
variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  [Finite A] [Finite C]
private theorem exact_card_8_16_2_injective (f : A →+ B) (g : B →+ C)
    (hgf : ∀ a, g (f a)=0) (hex : ∀ b, g b=0 → ∃ a, f a=b)
    (hcA : Nat.card A=8) (hcB : Nat.card B=16) (hcC : Nat.card C≤2) :
    Function.Injective f := by
  let fker : A → g.ker := fun a => ⟨f a,hgf a⟩
  have hsurj : Function.Surjective fker := by
    rintro ⟨b,hb⟩
    obtain ⟨a,ha⟩ := hex b hb
    exact ⟨a,Subtype.ext ha⟩
  have hker : Nat.card g.ker≤8 := (Nat.card_le_card_of_surjective fker hsurj).trans hcA.le
  have hrange : Nat.card g.range≤2 :=
    (Nat.card_le_card_of_injective (fun b : g.range => b.val) Subtype.val_injective).trans hcC
  have hprod : Nat.card g.ker*Nat.card g.range=16 := by
    rw [←AddSubgroup.index_ker g,AddSubgroup.card_mul_index,hcB]
  have hle : 16≤Nat.card g.ker*2 := by
    rw [←hprod]
    exact Nat.mul_le_mul_left _ hrange
  have hcard : Nat.card A≤Nat.card g.ker := by omega
  have hinj := (hsurj.bijective_of_nat_card_le hcard).injective
  intro a b hab
  exact hinj (Subtype.ext hab)
end


private theorem actual_bottom_14_139_kernel_zero
    (x : model.classical.sphere.Page 2 (14,139))
    (hx : (model.classical.pageMap
      (HasFunctorialCofiber.cofibι model.auxiliary.nuMap) 2 (14,139)) x=0) : x=0 := by
  classical
  let N := KIP126.Literature.normalizedTriangle model model.auxiliary.nuRouteTriangle
    nuCofiber_exponent_sum
  let U := Smn (Syn:=SyntheticSpectrum) 125 139
  let Q := model.quotients.functoriality.functor 1
  let A := U ⟶ XModLambdaN N.obj₂ 1
  let B := U ⟶ XModLambdaN N.obj₃ 1
  let C := U ⟶ XModLambdaN (N.obj₁⟦(1:ℤ)⟧) 1
  let S := shiftFunctor SyntheticSpectrum (1:ℤ)
  let eN2 : N.obj₂ ≅ (SyntheticCategory.biShift (0,0)).obj
      (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary)) :=
    SyntheticCategory.biShift_zero.symm.app _
  let eA : A ≃ model.classical.sphere.Page 2 (14,139) :=
    (Iso.homCongr (Iso.refl U) (Q.mapIso eN2)).trans
      (model.firstQuotient .sphere 0 14 139).toEquiv
  have hnA : Standard.archive.basisCount 14 139=3 :=
    (archive_dimension 14 139 (by decide)).trans (by decide)
  let coordA : model.classical.sphere.Page 2 (14,139) ≃ (Fin 3 →₀ ZMod 2) := by
    rw [←hnA]
    exact (Standard.coordinates 14 139 (by decide)).toEquiv
  letI : Finite A := Finite.of_equiv (Fin 3 →₀ ZMod 2) (eA.trans coordA).symm
  have cardA : Nat.card A=8 := (Nat.card_congr (eA.trans coordA)).trans (by
    rw [Nat.card_congr Finsupp.equivFunOnFinite]
    simp [Nat.card_eq_fintype_card])
  let eN3 : N.obj₃ ≅ (SyntheticCategory.biShift (0,0)).obj
      (model.nu.functor.obj (ClassicalObject.nuCofiber.obj model.auxiliary)) := by
    change (SyntheticCategory.biShift
      (0,-(normalizedExponent model.classicalTower model.auxiliary.nuRouteTriangle.g:ℤ))).obj
      (model.nu.functor.obj (ClassicalObject.nuCofiber.obj model.auxiliary)) ≅ _
    rw [nuCofiber_bottom_exponent]
    exact Iso.refl _
  let eB : B ≃ (model.classical.obj (ClassicalObject.nuCofiber.obj model.auxiliary)).Page 2 (14,139) :=
    (Iso.homCongr (Iso.refl U) (Q.mapIso eN3)).trans
      (model.firstQuotient .nuCofiber 0 14 139).toEquiv
  obtain ⟨coordB,hcoordB⟩ := cofiber_basis_correct
    ⟨.nuCofiber,14,139,["372","449,1,0","1,1,7,1,275,1,0","0,2,425,1,0"]⟩
    (by exact List.mem_of_getElem? (i:=54) rfl) rfl
  let coordB' : (model.classical.obj (ClassicalObject.nuCofiber.obj model.auxiliary)).Page 2 (14,139) ≃
      (Fin 4 →₀ ZMod 2) := coordB.toEquiv
  letI : Finite B := Finite.of_equiv (Fin 4 →₀ ZMod 2) (eB.trans coordB').symm
  have cardB : Nat.card B=16 := (Nat.card_congr (eB.trans coordB')).trans (by
    rw [Nat.card_congr Finsupp.equivFunOnFinite]
    simp [Nat.card_eq_fintype_card])
  let eN1 : N.obj₁⟦(1:ℤ)⟧ ≅ Smn (Syn:=SyntheticSpectrum) 4 4 := by
    change ((SyntheticCategory.biShift
      (0,(normalizedExponent model.classicalTower model.auxiliary.nuMap:ℤ))).obj
      (model.nu.functor.obj (Sphere (C:=Spectrum) 3)))⟦(1:ℤ)⟧ ≅ _
    rw [nuCofiber_nu_exponent]
    exact S.mapIso
        ((SyntheticCategory.biShift (0,(1:ℤ))).mapIso (KIP126.Literature.nuSphereThree model) ≪≫
          (biShiftAddIso (3,3) (0,1) (3,4) (by decide)).app S_0_0) ≪≫
      (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).symm.app _ ≪≫
        (biShiftAddIso (3,4) (1,0) (4,4) (by decide)).app S_0_0
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (4,4)
  letI := model.exactness.shiftCommShift (4,4)
  letI := model.exactness.shiftExact (4,4)
  obtain ⟨eQ,hQ⟩ := finite_quotient_shift_comparison model.quotients.coherence
    (4,4) 1 (S_0_0 : SyntheticSpectrum)
  let eU : F.obj (Smn (Syn:=SyntheticSpectrum) 121 135) ≅ U :=
    (biShiftAddIso (121,135) (4,4) (125,139) (by decide)).app S_0_0
  let eC : C ≃ model.classical.sphere.Page 2 (14,135) :=
    (Iso.homCongr (Iso.refl U) (Q.mapIso eN1 ≪≫ eQ)).trans
      ((Iso.homCongr eU.symm (Iso.refl (F.obj (XModLambdaN S_0_0 1)))).trans
        ((SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) (4,4)).homEquiv.symm.trans
          (KIP126.Literature.sphereFirstQuotient model 14 135).toEquiv))
  have hnC : Standard.archive.basisCount 14 135=1 :=
    (archive_dimension 14 135 (by decide)).trans (by decide)
  let coordC : model.classical.sphere.Page 2 (14,135) ≃ (Fin 1 →₀ ZMod 2) := by
    rw [←hnC]
    exact (Standard.coordinates 14 135 (by decide)).toEquiv
  letI : Finite C := Finite.of_equiv (Fin 1 →₀ ZMod 2) (eC.trans coordC).symm
  have cardC : Nat.card C≤2 := (Nat.card_congr (eC.trans coordC)).le.trans (by
    rw [Nat.card_congr Finsupp.equivFunOnFinite]
    simp [Nat.card_eq_fintype_card])
  obtain ⟨esusp,hinc,hR⟩ := normalized_finite_quotient_horizontal_row
    model.auxiliary.nuRouteTriangle nuCofiber_exponent_sum (nuCofiber_triangle _) 1 (by decide)
  let R := Triangle.mk (XModLambdaN.map N.mor₂ 1) (XModLambdaN.map N.mor₃ 1)
    (-(XModLambdaN.map (S.map N.mor₁) 1 ≫ esusp.hom))
  let f : A →+ B := Preadditive.rightComp U (XModLambdaN.map N.mor₂ 1)
  let g : B →+ C := Preadditive.rightComp U (XModLambdaN.map N.mor₃ 1)
  have gf : ∀ a, g (f a)=0 := by
    intro a
    change (a≫R.mor₁)≫R.mor₂=0
    rw [Category.assoc,comp_distTriang_mor_zero₁₂ R hR,comp_zero]
  have hex : ∀ b, g b=0 → ∃ a, f a=b := by
    intro b hb
    obtain ⟨a,ha⟩ := R.coyoneda_exact₂ hR b hb
    exact ⟨a,ha.symm⟩
  have finj := exact_card_8_16_2_injective f g gf hex cardA cardB cardC
  let a : A := (model.firstQuotient .sphere 0 14 139).symm x ≫
    XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1
  have ha : f a=0 := by
    change a ≫ XModLambdaN.map N.mor₂ 1 = 0
    have hc := first_quotient_normalized_negative_lift_at_zero
      model.auxiliary.nuRouteTriangle.Y model.auxiliary.nuRouteTriangle.Z
      model.auxiliary.nuRouteTriangle.g nuCofiber_bottom_exponent 14 139 x
    dsimp only at hc
    have hb := hx
    change ((model.classical.functor.map model.auxiliary.nuRouteTriangle.g).pageMap 2 (14,139)) x=0 at hb
    have hz (j : XModLambdaN ((SyntheticCategory.biShift (0,0)).obj
        (model.nu.functor.obj (ClassicalObject.nuCofiber.obj model.auxiliary))) 1 ⟶
        XModLambdaN N.obj₃ 1) :
      (model.firstQuotient .nuCofiber 0 14 139).symm
        (((model.classical.functor.map model.auxiliary.nuRouteTriangle.g).pageMap 2 (14,139)) x)≫j=0 := by
      calc
        _ = (model.firstQuotient .nuCofiber 0 14 139).symm 0≫j :=
          congrArg (fun y => (model.firstQuotient .nuCofiber 0 14 139).symm y≫j) hb
        _ = 0 := by rw [LinearEquiv.map_zero,zero_comp]
    have hcz := hc.trans (hz _)
    dsimp only [f,R,a,N,KIP126.Literature.normalizedTriangle,Triangle.mk,
      KIP126.Kervaire.Route.AuxiliaryData.nuRouteTriangle] at hcz ⊢
    simpa only [Category.assoc] using hcz
  have ha0 : a=0 := finj (ha.trans f.map_zero.symm)
  let ezero := Q.mapIso (SyntheticCategory.biShift_zero.app
    (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary)))
  have hq0 : (model.firstQuotient .sphere 0 14 139).symm x=0 := by
    apply (cancel_mono ezero.hom).mp
    change a=0≫ezero.hom
    simpa only [zero_comp] using ha0
  apply (model.firstQuotient .sphere 0 14 139).symm.injective
  exact hq0.trans (LinearEquiv.map_zero _).symm

open KIP126.Core.SpectralSequence KIP126.Core.SpectralSequence.FinitePageCalculus
private abbrev E := KIP126.Computation.Table.sequence .nuCofiber
private theorem E_start : E.r₀ = 2 := model.classical.firstPage _
private theorem degree_2_12 : (12,138) + E.diffDeg 2 = (14,139) := by
  change (12,138) + (model.classical.obj (object .nuCofiber)).diffDeg 2 = (14,139)
  rw [model.classical.differentialDegree]
  decide
private abbrev delta2_12 : E.Page 2 (12,138) ⟶ E.Page 2 (14,139) :=
  E.d 2 (12,138) ≫ eqToHom (congrArg (E.Page 2) degree_2_12)
/-- The finite Cnu incoming exclusion used at the end of Proposition 7.9.
It uses complete degrees, not just the single level-9000 target row. -/
private theorem cnu_d2_d3_incoming14_zero  :
    ((E)).d 2 (11,137) = 0 ∧ ((E)).d 3 (11,137) = 0 := by
  classical
  have hdecode (indices : List ℕ)
      (hv : Raw.coordinatesValid Raw.degrees .nuCofiber 11 137 indices = true) :
      decode .nuCofiber 11 137 indices =
        some ((indices.map (basis .nuCofiber 11 137)).sum) := by
    simp only [decode,hv,ite_true]
  have h0 : ∃ xr : ((E)).Page 3 (11,137),
      RepresentsOnPage (E) 3 (11,137) (basis .nuCofiber 11 137 0) xr ∧
      ((E)).d 3 (11,137) xr = 0 := by
    obtain ⟨x,hx,y,hy,h⟩ := result _ (List.mem_of_getElem? (i := 76) (by rfl))
    have hy' : y = basis .nuCofiber 11 137 0 := by
      simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] using
        Option.some.inj (hy.symm.trans (hdecode [0] (by decide)))
    subst y
    exact differential_target_cycle h
  have h3 : RepresentsOnPage (E) 3 (11,137) (basis .nuCofiber 11 137 3) 0 := by
    obtain ⟨x,hx,y,hy,h⟩ := result _ (List.mem_of_getElem? (i := 75) (by rfl))
    have hy' : y = basis .nuCofiber 11 137 3 := by
      simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] using
        Option.some.inj (hy.symm.trans (hdecode [3] (by decide)))
    subst y
    exact differential_target_later_zero (by change E.r₀ ≤ 2; exact le_of_eq E_start) (by decide) h
  have h12 : ReachesPage (E) 1000 (11,137)
      (basis .nuCofiber 11 137 1 + basis .nuCofiber 11 137 2) := by
    obtain ⟨x,hx,h⟩ := result _ (List.mem_of_getElem? (i := 77) (by rfl))
    have hx' : x = basis .nuCofiber 11 137 1 + basis .nuCofiber 11 137 2 := by
      simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] using
        Option.some.inj (hx.symm.trans (hdecode [1,2] (by decide)))
    exact hx' ▸ h
  have h2 : ReachesPage (E) 14 (11,137) (basis .nuCofiber 11 137 2) := by
    obtain ⟨x,hx,h⟩ := result _ (List.mem_of_getElem? (i := 78) (by rfl))
    have hx' : x = basis .nuCofiber 11 137 2 := by
      simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] using
        Option.some.inj (hx.symm.trans (hdecode [2] (by decide)))
    exact hx' ▸ h
  obtain ⟨x12,hx12⟩ := reaches_earlier (by decide : (2 : ℤ) ≤ 3) (by decide : (3 : ℤ) ≤ 1000) h12
  obtain ⟨x2,hx2⟩ := reaches_earlier (by decide : (2 : ℤ) ≤ 3) (by decide : (3 : ℤ) ≤ 14) h2
  have hd12 : ((E)).d 3 (11,137) x12 = 0 := represents_d_zero_of_later
    (by have hstart := E_start; omega) (by decide) hx12 h12
  have hd2 : ((E)).d 3 (11,137) x2 = 0 := represents_d_zero_of_later
    (by have hstart := E_start; omega) (by decide) hx2 h2
  obtain ⟨e,he⟩ := basis_correct _ (List.mem_of_getElem? (i := 44) (by rfl))
  change ((E)).Page 2 (11,137) ≃ₗ[ℤ] (Fin 4 →₀ KIP126.Core.Algebra.F2) at e
  change ∀ i : Fin 4, e.symm (Finsupp.single i 1) = basis .nuCofiber 11 137 i.val at he
  have hgen (i : Fin 4) : ∃ xr : ((E)).Page 3 (11,137),
      RepresentsOnPage (E) 3 (11,137) (e.symm (Finsupp.single i 1)) xr ∧ ((E)).d 3 (11,137) xr = 0 := by
    rw [he]
    fin_cases i
    · exact h0
    · exact ⟨x12-x2, by simpa only [add_sub_cancel_right] using represents_sub hx12 hx2,
        by rw [map_sub,hd12,hd2,sub_self]⟩
    · exact ⟨x2,hx2,hd2⟩
    · exact ⟨0,h3,map_zero _⟩
  refine ⟨?_,d_zero_of_complete_representatives (by decide) e hgen⟩
  apply d_zero_of_complete_representatives (by decide) e
  intro i
  obtain ⟨xr,hxr,_⟩ := hgen i
  refine ⟨e.symm (Finsupp.single i 1),represents_two_self _,?_⟩
  exact represents_d_zero_of_later (by have hstart := E_start; omega) (by decide)
    (represents_two_self _) ⟨xr,hxr⟩

private theorem degree_2_11 : (11,137) + E.diffDeg 2 = (13,138) := by
  change (11,137) + (model.classical.obj (object .nuCofiber)).diffDeg 2 = (13,138)
  rw [model.classical.differentialDegree]
  decide
private theorem degree_2_10 : (10,136) + E.diffDeg 2 = (12,137) := by
  change (10,136) + (model.classical.obj (object .nuCofiber)).diffDeg 2 = (12,137)
  rw [model.classical.differentialDegree]
  decide
private theorem degree_3_10 : (10,136) + E.diffDeg 3 = (13,138) := by
  change (10,136) + (model.classical.obj (object .nuCofiber)).diffDeg 3 = (13,138)
  rw [model.classical.differentialDegree]
  decide
private abbrev delta3_10 : E.Page 3 (10,136) ⟶ E.Page 3 (13,138) :=
  E.d 3 (10,136) ≫ eqToHom (congrArg (E.Page 3) degree_3_10)
private theorem degree_3_9 : (9,135) + E.diffDeg 3 = (12,137) := by
  change (9,135) + (model.classical.obj (object .nuCofiber)).diffDeg 3 = (12,137)
  rw [model.classical.differentialDegree]
  decide
private abbrev delta3_9 : E.Page 3 (9,135) ⟶ E.Page 3 (12,137) :=
  E.d 3 (9,135) ≫ eqToHom (congrArg (E.Page 3) degree_3_9)
private theorem degree_4_9 : (9,135) + E.diffDeg 4 = (13,138) := by
  change (9,135) + (model.classical.obj (object .nuCofiber)).diffDeg 4 = (13,138)
  rw [model.classical.differentialDegree]
  decide
private abbrev delta4_9 : E.Page 4 (9,135) ⟶ E.Page 4 (13,138) :=
  E.d 4 (9,135) ≫ eqToHom (congrArg (E.Page 4) degree_4_9)
private theorem retarget_zero {r : ℤ} {p q : ℤ × ℤ}
    (hdeg : p + E.diffDeg r = q) {a : E.Page r p} (hz : E.d r p a = 0) :
    (E.d r p ≫ eqToHom (congrArg (E.Page r) hdeg)) a = 0 := by
  change (eqToHom (congrArg (E.Page r) hdeg)) (E.d r p a) = 0
  rw [hz, map_zero]
private theorem third_labels_eq_of_incoming_zero_at
    {E : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)}
    {p q : ℤ × ℤ} (hdeg : q + E.diffDeg 2 = p)
    (hstart : E.r₀ ≤ 2) (hin : E.d 2 q = 0)
    {x y : E.Page 2 p} {a : E.Page 3 p}
    (hx : RepresentsOnPage E 3 p x a) (hy : RepresentsOnPage E 3 p y a) : x = y := by
  subst p
  have hm := (PageThree.equal_iff_sub_mem_d2_range hstart q hx hy).mp rfl
  obtain ⟨b,hb⟩ := hm
  apply sub_eq_zero.mp
  exact hb.symm.trans (by rw [hin]; rfl)
private theorem page_four_subsingleton_of_frame
    {E : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)}
    {p : ℤ × ℤ} (hstart : E.r₀ ≤ 3) (xr : E.Page 3 p)
    (hcases : ∀ a : E.Page 3 p, a = 0 ∨ a = xr)
    (hne : E.d 3 p xr ≠ 0) : Subsingleton (E.Page 4 p) := by
  have hz (a : E.Page 4 p) : a = 0 := by
    obtain ⟨x,hx4⟩ := page_has_initial_representative (by decide) a
    obtain ⟨a3,ha3⟩ := reaches_earlier (by decide : (2:ℤ) ≤ 3)
      (by decide : (3:ℤ) ≤ 4) ⟨a,hx4⟩
    have hdzero := represents_d_zero_of_later hstart (by decide) ha3 ⟨a,hx4⟩
    have ha3zero : a3 = 0 := by
      rcases hcases a3 with hzero | heq
      · exact hzero
      · exact False.elim (hne (heq ▸ hdzero))
    exact represents_later_zero (by decide : (3:ℤ) ≤ 4) (ha3zero ▸ ha3) hx4
  exact ⟨fun a b => (hz a).trans (hz b).symm⟩

private theorem cnu_10_136_data  :
    ((E)).d 2 (10,136) = 0 ∧
    (∀ a : ((E)).Page 3 (10,136),
      RepresentsOnPage (E) 3 (13,138) 0 (delta3_10 a) ∨
      RepresentsOnPage (E) 3 (13,138) (basis .nuCofiber 13 138 1) (delta3_10 a)) ∧
    Subsingleton (((E)).Page 4 (10,136)) := by
  classical
  have hdecode (s t : ℕ) (indices : List ℕ)
      (hv : Raw.coordinatesValid Raw.degrees .nuCofiber s t indices = true) :
      decode .nuCofiber s t indices =
        some ((indices.map (basis .nuCofiber s t)).sum) := by
    simp only [decode,hv,ite_true]
  obtain ⟨x,hx,y,hy,h⟩ := result _ (List.mem_of_getElem? (i := 64) (by rfl))
  have hx' : x = basis .nuCofiber 10 136 0 := by
    simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] using
      Option.some.inj (hx.symm.trans (hdecode 10 136 [0] (by decide)))
  have hy' : y = basis .nuCofiber 13 138 1 := by
    simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] using
      Option.some.inj (hy.symm.trans (hdecode 13 138 [1] (by decide)))
  subst x y
  change HasDifferential (E) 3 (10,136) (13,138) _ _ at h
  obtain ⟨hdeg,xr,yr,hxr,hyr,hd⟩ := h
  have hd' : delta3_10 xr = yr := by
    change delta3_10 xr = yr at hd
    exact hd
  have hne : yr ≠ 0 := by
    obtain ⟨e,he⟩ := basis_correct _ (List.mem_of_getElem? (i := 51) (by rfl))
    change ((E)).Page 2 (13,138) ≃ₗ[ℤ] (Fin 4 →₀ KIP126.Core.Algebra.F2) at e
    change ∀ i : Fin 4, e.symm (Finsupp.single i 1) = basis .nuCofiber 13 138 i.val at he
    have hn : basis .nuCofiber 13 138 1 ≠ 0 := by
      rw [← he ⟨1,by decide⟩]
      intro hz
      have hh := congrArg e hz
      simp only [LinearEquiv.apply_symm_apply,map_zero] at hh
      change (Finsupp.single (⟨1,by decide⟩ : Fin 4) (1 : KIP126.Core.Algebra.F2)) = 0 at hh
      exact Finsupp.single_ne_zero.mpr one_ne_zero hh
    exact represents_next_nonzero_of_incoming_zero_at
      (by change E.r₀ ≤ 2; exact le_of_eq E_start) (by decide)
      cnu_d2_d3_incoming14_zero.1 hyr (represents_two_self _) hn degree_2_11
  have h1 : RepresentsOnPage (E) 3 (10,136) (basis .nuCofiber 10 136 1) 0 := by
    obtain ⟨x,hx,y,hy,h⟩ := result _ (List.mem_of_getElem? (i := 62) (by rfl))
    have hy' : y = basis .nuCofiber 10 136 1 := by
      simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] using
        Option.some.inj (hy.symm.trans (hdecode 10 136 [1] (by decide)))
    subst y
    exact differential_target_later_zero (by change E.r₀ ≤ 2; exact le_of_eq E_start) (by decide) h
  have h2 : RepresentsOnPage (E) 3 (10,136) (basis .nuCofiber 10 136 2) 0 := by
    obtain ⟨x,hx,y,hy,h⟩ := result _ (List.mem_of_getElem? (i := 63) (by rfl))
    have hy' : y = basis .nuCofiber 10 136 2 := by
      simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] using
        Option.some.inj (hy.symm.trans (hdecode 10 136 [2] (by decide)))
    subst y
    exact differential_target_later_zero (by change E.r₀ ≤ 2; exact le_of_eq E_start) (by decide) h
  obtain ⟨e,he⟩ := basis_correct _ (List.mem_of_getElem? (i := 39) (by rfl))
  change ((E)).Page 2 (10,136) ≃ₗ[ℤ] (Fin 3 →₀ KIP126.Core.Algebra.F2) at e
  change ∀ i : Fin 3, e.symm (Finsupp.single i 1) = basis .nuCofiber 10 136 i.val at he
  have hbas (i : Fin 3) : RepresentsOnPage (E) 3 (10,136) (e.symm (Finsupp.single i 1)) (![xr,0,0] i) := by
    rw [he]
    fin_cases i
    · exact hxr
    · exact h1
    · exact h2
  have hd2 : ((E)).d 2 (10,136) = 0 := by
    apply d_zero_of_complete_representatives (by decide) e
    intro i
    refine ⟨e.symm (Finsupp.single i 1),represents_two_self _,?_⟩
    exact represents_d_zero_of_later (by have hs := E_start; omega) (by decide)
      (represents_two_self _) ⟨_,hbas i⟩
  have himage (a : ((E)).Page 3 (10,136)) :
      RepresentsOnPage (E) 3 (13,138) 0 (delta3_10 a) ∨
      RepresentsOnPage (E) 3 (13,138) (basis .nuCofiber 13 138 1) (delta3_10 a) := by
    obtain ⟨c,hc⟩ := page_eq_sum_of_complete_representatives (by decide) e ![xr,0,0] hbas a
    simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero,Matrix.cons_val_zero,
      Matrix.cons_val_succ,ite_self] at hc
    by_cases hc0 : c 0 = 0
    · have ha : a = 0 := by simpa only [hc0,ite_true] using hc
      left
      have hda : delta3_10 a = (0 : ((E)).Page 3 (13,138)) := by rw [ha,map_zero]
      exact hda.symm ▸ (RepresentsOnPage.zero (E := (E)) (p := (13,138)) (by decide))
    · have ha : a = xr := by simpa only [hc0,ite_false] using hc
      right
      have hda : delta3_10 a = yr := (congrArg (delta3_10) ha).trans hd'
      exact hda.symm ▸ hyr
  have hcases (a : E.Page 3 (10,136)) : a = 0 ∨ a = xr := by
    obtain ⟨c,hc⟩ := page_eq_sum_of_complete_representatives (by decide) e ![xr,0,0] hbas a
    simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero,Matrix.cons_val_zero,
      Matrix.cons_val_succ,ite_self] at hc
    by_cases hc0 : c 0 = 0
    · exact Or.inl (by simpa only [hc0,ite_true] using hc)
    · exact Or.inr (by simpa only [hc0,ite_false] using hc)
  have hrawne : E.d 3 (10,136) xr ≠ 0 := by
    intro hz
    exact hne (hd'.symm.trans (retarget_zero degree_3_10 hz))
  exact ⟨hd2,himage,page_four_subsingleton_of_frame
    (by have hs := E_start; omega) xr hcases hrawne⟩

private theorem cnu_page4_target3_nonzero
    (yr : E.Page 4 (13,138))
    (hy : RepresentsOnPage E 4 (13,138) (basis .nuCofiber 13 138 3) yr) : yr ≠ 0 := by
  classical
  obtain ⟨e,he⟩ := basis_correct _ (List.mem_of_getElem? (i := 51) (by rfl))
  change E.Page 2 (13,138) ≃ₗ[ℤ] (Fin 4 →₀ KIP126.Core.Algebra.F2) at e
  change ∀ i : Fin 4, e.symm (Finsupp.single i 1) = basis .nuCofiber 13 138 i.val at he
  have hn0 : basis .nuCofiber 13 138 3 ≠ 0 := by
    rw [← he ⟨3,by decide⟩]
    exact basis_vector_ne_zero e _
  have hn1 : basis .nuCofiber 13 138 3 ≠ basis .nuCofiber 13 138 1 := by
    rw [← he ⟨3,by decide⟩,← he ⟨1,by decide⟩]
    intro hz
    have hh := e.symm.injective hz
    have hv := congrArg (fun f : Fin 4 →₀ KIP126.Core.Algebra.F2 => f ⟨3,by decide⟩) hh
    simp at hv
  obtain ⟨ar,har⟩ := represents_before (by decide : (2:ℤ) ≤ 3)
    (by decide : (3:ℤ) ≤ 4) hy
  apply represents_next_nonzero_of_not_incoming_at degree_3_10
    (by have hs := E_start; omega) (by decide) hy har
  intro a ha
  rcases cnu_10_136_data.2.1 a with h0 | h1
  · have hrep : RepresentsOnPage E 3 (13,138) 0 ar := ha ▸ h0
    exact hn0 (third_labels_eq_of_incoming_zero_at degree_2_11
      (by change E.r₀ ≤ 2; exact le_of_eq E_start)
      cnu_d2_d3_incoming14_zero.1 har hrep)
  · have hrep : RepresentsOnPage E 3 (13,138) (basis .nuCofiber 13 138 1) ar := ha ▸ h1
    exact hn1 (third_labels_eq_of_incoming_zero_at degree_2_11
      (by change E.r₀ ≤ 2; exact le_of_eq E_start)
      cnu_d2_d3_incoming14_zero.1 har hrep)

private theorem cnu_d4_incoming14_zero : E.d 4 (10,136) = 0 := by
  haveI := cnu_10_136_data.2.2
  ext x
  change E.d 4 (10,136) x = 0
  rw [Subsingleton.elim x 0, map_zero]

private theorem cnu_d5_incoming14_zero  : ((E)).d 5 (9,135) = 0 := by
  classical
  have hdecode (s t : ℕ) (indices : List ℕ)
      (hv : Raw.coordinatesValid Raw.degrees .nuCofiber s t indices = true) :
      decode .nuCofiber s t indices =
        some ((indices.map (basis .nuCofiber s t)).sum) := by
    as_aux_lemma =>
      simp only [decode,hv,ite_true]
  obtain ⟨x0,hx0,y0,hy0,h0⟩ := result _ (List.mem_of_getElem? (i := 51) (by rfl))
  have hx0' : x0 = basis .nuCofiber 9 135 0 := by
    as_aux_lemma =>
      simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] using
        Option.some.inj (hx0.symm.trans (hdecode 9 135 [0] (by decide)))
  have hy0' : y0 = basis .nuCofiber 12 137 4 := by
    as_aux_lemma =>
      simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] using
        Option.some.inj (hy0.symm.trans (hdecode 12 137 [4] (by decide)))
  subst x0 y0
  change HasDifferential (E) 3 (9,135) (12,137) _ _ at h0
  obtain ⟨_,xr0,yr0,hxr0,hyr0,hd0⟩ := h0
  change delta3_9 xr0 = yr0 at hd0
  have hn0 : yr0 ≠ 0 := by
    as_aux_lemma =>
      obtain ⟨e,he⟩ := basis_correct _ (List.mem_of_getElem? (i := 47) (by rfl))
      change ((E)).Page 2 (12,137) ≃ₗ[ℤ] (Fin 5 →₀ KIP126.Core.Algebra.F2) at e
      change ∀ i : Fin 5, e.symm (Finsupp.single i 1) = basis .nuCofiber 12 137 i.val at he
      have hn : basis .nuCofiber 12 137 4 ≠ 0 := by
        as_aux_lemma =>
          rw [← he ⟨4,by decide⟩]
          intro hz
          have hh := congrArg e hz
          simp only [LinearEquiv.apply_symm_apply,map_zero] at hh
          change (Finsupp.single (⟨4,by decide⟩ : Fin 5) (1 : KIP126.Core.Algebra.F2)) = 0 at hh
          exact Finsupp.single_ne_zero.mpr one_ne_zero hh
      exact represents_next_nonzero_of_incoming_zero_at
        (by change E.r₀ ≤ 2; exact le_of_eq E_start) (by decide)
        cnu_10_136_data.1 hyr0 (represents_two_self _) hn degree_2_10
  obtain ⟨x2,hx2,y2,hy2,h2⟩ := result _ (List.mem_of_getElem? (i := 50) (by rfl))
  have hx2' : x2 = basis .nuCofiber 9 135 2 := by
    as_aux_lemma =>
      simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] using
        Option.some.inj (hx2.symm.trans (hdecode 9 135 [2] (by decide)))
  have hy2' : y2 = basis .nuCofiber 13 138 3 := by
    as_aux_lemma =>
      simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] using
        Option.some.inj (hy2.symm.trans (hdecode 13 138 [3] (by decide)))
  subst x2 y2
  change HasDifferential (E) 4 (9,135) (13,138) _ _ at h2
  obtain ⟨_,xr2,yr2,hxr2,hyr2,hd2⟩ := h2
  change delta4_9 xr2 = yr2 at hd2
  have hn2 : yr2 ≠ 0 := cnu_page4_target3_nonzero yr2 hyr2
  obtain ⟨x23,hx23⟩ := reaches_earlier (by decide : (2 : ℤ) ≤ 3) (by decide : (3 : ℤ) ≤ 4) ⟨xr2,hxr2⟩
  have hd23 : delta3_9 x23 = 0 := by
    apply retarget_zero degree_3_9
    exact represents_d_zero_of_later
      (by have hs := E_start; omega) (by decide) hx23 ⟨xr2,hxr2⟩
  have h1 : ReachesPage (E) 16 (9,135) (basis .nuCofiber 9 135 1) := by
    as_aux_lemma =>
      obtain ⟨x,hx,h⟩ := result _ (List.mem_of_getElem? (i := 49) (by rfl))
      have hx' : x = basis .nuCofiber 9 135 1 := by
        as_aux_lemma =>
          simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] using
            Option.some.inj (hx.symm.trans (hdecode 9 135 [1] (by decide)))
      exact hx' ▸ h
  obtain ⟨x13,hx13⟩ := reaches_earlier (by decide : (2 : ℤ) ≤ 3) (by decide : (3 : ℤ) ≤ 16) h1
  obtain ⟨x14,hx14⟩ := reaches_earlier (by decide : (2 : ℤ) ≤ 4) (by decide : (4 : ℤ) ≤ 16) h1
  obtain ⟨x15,hx15⟩ := reaches_earlier (by decide : (2 : ℤ) ≤ 5) (by decide : (5 : ℤ) ≤ 16) h1
  have hd13 : delta3_9 x13 = 0 := by
    apply retarget_zero degree_3_9
    exact represents_d_zero_of_later
      (by have hs := E_start; omega) (by decide) hx13 h1
  have hd14 : delta4_9 x14 = 0 := by
    apply retarget_zero degree_4_9
    exact represents_d_zero_of_later
      (by have hs := E_start; omega) (by decide) hx14 h1
  have hd15 : ((E)).d 5 (9,135) x15 = 0 := represents_d_zero_of_later
    (by have hs := E_start; omega) (by decide) hx15 h1
  have h3 : RepresentsOnPage (E) 3 (9,135) (basis .nuCofiber 9 135 3) 0 := by
    as_aux_lemma =>
      obtain ⟨x,hx,y,hy,h⟩ := result _ (List.mem_of_getElem? (i := 47) (by rfl))
      have hy' : y = basis .nuCofiber 9 135 3 := by
        as_aux_lemma =>
          simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] using
            Option.some.inj (hy.symm.trans (hdecode 9 135 [3] (by decide)))
      subst y
      exact differential_target_later_zero (by change E.r₀ ≤ 2; exact le_of_eq E_start) (by decide) h
  have h4 : RepresentsOnPage (E) 3 (9,135) (basis .nuCofiber 9 135 4) 0 := by
    as_aux_lemma =>
      obtain ⟨x,hx,y,hy,h⟩ := result _ (List.mem_of_getElem? (i := 48) (by rfl))
      have hy' : y = basis .nuCofiber 9 135 4 := by
        as_aux_lemma =>
          simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] using
            Option.some.inj (hy.symm.trans (hdecode 9 135 [4] (by decide)))
      subst y
      exact differential_target_later_zero (by change E.r₀ ≤ 2; exact le_of_eq E_start) (by decide) h
  obtain ⟨e,he⟩ := basis_correct _ (List.mem_of_getElem? (i := 34) (by rfl))
  change ((E)).Page 2 (9,135) ≃ₗ[ℤ] (Fin 5 →₀ KIP126.Core.Algebra.F2) at e
  change ∀ i : Fin 5, e.symm (Finsupp.single i 1) = basis .nuCofiber 9 135 i.val at he
  have hbas (i : Fin 5) : RepresentsOnPage (E) 3 (9,135) (e.symm (Finsupp.single i 1)) (![xr0,x13,x23,0,0] i) := by
    as_aux_lemma =>
      rw [he]
      fin_cases i
      · exact hxr0
      · exact hx13
      · exact hx23
      · exact h3
      · exact h4
  ext a
  change ((E)).d 5 (9,135) a = 0
  obtain ⟨x,hx5⟩ := page_has_initial_representative (by decide) a
  obtain ⟨ar3,har3⟩ := reaches_earlier (by decide : (2 : ℤ) ≤ 3) (by decide : (3 : ℤ) ≤ 5) ⟨a,hx5⟩
  obtain ⟨ar4,har4⟩ := reaches_earlier (by decide : (2 : ℤ) ≤ 4) (by decide : (4 : ℤ) ≤ 5) ⟨a,hx5⟩
  have hda3 : delta3_9 ar3 = 0 := by
    apply retarget_zero degree_3_9
    exact represents_d_zero_of_later
      (by have hs := E_start; omega) (by decide) har3 ⟨a,hx5⟩
  have hda4 : delta4_9 ar4 = 0 := by
    apply retarget_zero degree_4_9
    exact represents_d_zero_of_later
      (by have hs := E_start; omega) (by decide) har4 ⟨a,hx5⟩
  obtain ⟨c,hc⟩ := page_eq_sum_of_complete_representatives (by decide) e ![xr0,x13,x23,0,0] hbas ar3
  have ha3 : ar3 = (if c 0=0 then 0 else xr0)+(if c 1=0 then 0 else x13)+(if c 2=0 then 0 else x23) := by
    as_aux_lemma =>
      simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero,Matrix.cons_val_zero,
        Matrix.cons_val_succ,ite_self,← add_assoc] at hc
      exact hc
  have hb13 : delta3_9 (if c 1=0 then 0 else x13) = 0 := by
    as_aux_lemma =>
      split_ifs
      · exact map_zero _
      · exact hd13
  have hb23 : delta3_9 (if c 2=0 then 0 else x23) = 0 := by
    as_aux_lemma =>
      split_ifs
      · exact map_zero _
      · exact hd23
  have hc0 : c 0=0 := by
    as_aux_lemma =>
      by_contra hne
      rw [ha3,map_add,map_add,hb13,hb23,add_zero,add_zero,if_neg hne,hd0] at hda3
      exact hn0 hda3
  have ha3' : ar3 = (if c 1=0 then 0 else x13)+(if c 2=0 then 0 else x23) := by
    as_aux_lemma =>
      simpa only [hc0,ite_true,zero_add] using ha3
  have hbit3 := middle_add (represents_bit (c 1) hx13) (represents_bit (c 2) hx23)
  have hbit3' : RepresentsOnPage (E) 3 (9,135) _ ar3 := ha3'.symm ▸ hbit3
  have hbit4 := middle_add (represents_bit (c 1) hx14) (represents_bit (c 2) hxr2)
  have ha4 := represents_transport_eq (by decide : (3 : ℤ) ≤ 4) har3 hbit3' har4 hbit4
  have hb14 : delta4_9 (if c 1=0 then 0 else x14) = 0 := by
    as_aux_lemma =>
      split_ifs
      · exact map_zero _
      · exact hd14
  have hc2 : c 2=0 := by
    as_aux_lemma =>
      by_contra hne
      rw [ha4,map_add,hb14,zero_add,if_neg hne,hd2] at hda4
      exact hn2 hda4
  have ha4' : ar4 = (if c 1=0 then 0 else x14) := by simpa only [hc2,ite_true,add_zero] using ha4
  have hbit4' : RepresentsOnPage (E) 4 (9,135) _ ar4 := ha4'.symm ▸ (represents_bit (c 1) hx14)
  have ha5 := represents_transport_eq (by decide : (4 : ℤ) ≤ 5) har4 hbit4' hx5 (represents_bit (c 1) hx15)
  rw [ha5]
  split_ifs
  · exact map_zero _
  · exact hd15

private theorem cnu_d2_incoming14_image  (a : ((E)).Page 2 (12,138)) :
    delta2_12 a = 0 ∨
    delta2_12 a = basis .nuCofiber 14 139 3 := by
  classical
  have hdecode (s t : ℕ) (indices : List ℕ)
      (hv : Raw.coordinatesValid Raw.degrees .nuCofiber s t indices = true) :
      decode .nuCofiber s t indices =
        some ((indices.map (basis .nuCofiber s t)).sum) := by
    simp only [decode,hv,ite_true]
  have h0 : delta2_12 (basis .nuCofiber 12 138 0) = 0 := by
    obtain ⟨x,hx,y,hy,h⟩ := result _ (List.mem_of_getElem? (i := 92) (by rfl))
    have hx' : x = basis .nuCofiber 12 138 0 := by
      simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] using
        Option.some.inj (hx.symm.trans (hdecode 12 138 [0] (by decide)))
    subst x
    obtain ⟨_,xr,_,hxr,_,_⟩ := h
    have hz := represents_d_zero_of_later (E := E) (by change E.r₀ ≤ 2; exact le_of_eq E_start) (by decide)
      (represents_two_self _) ⟨xr,hxr⟩
    exact (congrArg (fun z => (eqToHom (congrArg (E.Page 2) degree_2_12)) z) hz).trans
      (map_zero _)
  have h1 : delta2_12 (basis .nuCofiber 12 138 1) = 0 := by
    obtain ⟨x,hx,y,hy,h⟩ := result _ (List.mem_of_getElem? (i := 90) (by rfl))
    have hy' : y = basis .nuCofiber 12 138 1 := by
      simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] using
        Option.some.inj (hy.symm.trans (hdecode 12 138 [1] (by decide)))
    subst y
    change HasDifferential (E) 2 (10,137) (12,138) x _ at h
    obtain ⟨yr,hyr,hd⟩ := differential_target_cycle h
    have hz := (congrArg (E.d 2 (12,138)) hyr.eq_on_page_two).trans hd
    exact (congrArg (fun z => (eqToHom (congrArg (E.Page 2) degree_2_12)) z) hz).trans
      (map_zero _)
  have h3 : delta2_12 (basis .nuCofiber 12 138 3) = 0 := by
    obtain ⟨x,hx,y,hy,h⟩ := result _ (List.mem_of_getElem? (i := 91) (by rfl))
    have hy' : y = basis .nuCofiber 12 138 3 := by
      simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] using
        Option.some.inj (hy.symm.trans (hdecode 12 138 [3] (by decide)))
    subst y
    change HasDifferential (E) 2 (10,137) (12,138) x _ at h
    obtain ⟨yr,hyr,hd⟩ := differential_target_cycle h
    have hz := (congrArg (E.d 2 (12,138)) hyr.eq_on_page_two).trans hd
    exact (congrArg (fun z => (eqToHom (congrArg (E.Page 2) degree_2_12)) z) hz).trans
      (map_zero _)
  have h2 : delta2_12 (basis .nuCofiber 12 138 2) =
      basis .nuCofiber 14 139 3 := by
    obtain ⟨x,hx,y,hy,h⟩ := result _ (List.mem_of_getElem? (i := 93) (by rfl))
    have hx' : x = basis .nuCofiber 12 138 2 := by
      simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] using
        Option.some.inj (hx.symm.trans (hdecode 12 138 [2] (by decide)))
    have hy' : y = basis .nuCofiber 14 139 3 := by
      simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] using
        Option.some.inj (hy.symm.trans (hdecode 14 139 [3] (by decide)))
    subst x y
    change HasDifferential (E) 2 (12,138) (14,139) _ _ at h
    obtain ⟨hd, heq⟩ := h.eq_on_page_two
    exact heq
  obtain ⟨e,he⟩ := basis_correct _ (List.mem_of_getElem? (i := 48) (by rfl))
  change ((E)).Page 2 (12,138) ≃ₗ[ℤ] (Fin 4 →₀ KIP126.Core.Algebra.F2) at e
  change ∀ i : Fin 4, e.symm (Finsupp.single i 1) = basis .nuCofiber 12 138 i.val at he
  have hbas (i : Fin 4) : RepresentsOnPage (E) 2 (12,138) (e.symm (Finsupp.single i 1))
      (basis .nuCofiber 12 138 i.val) := (he i) ▸ represents_two_self _
  obtain ⟨c,hc⟩ := page_eq_sum_of_complete_representatives (by decide) e
    (fun i => basis .nuCofiber 12 138 i.val) hbas a
  have ha : a = (if c 0=0 then 0 else basis .nuCofiber 12 138 0)+
      (if c 1=0 then 0 else basis .nuCofiber 12 138 1)+
      (if c 2=0 then 0 else basis .nuCofiber 12 138 2)+
      (if c 3=0 then 0 else basis .nuCofiber 12 138 3) := by
    simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero,← add_assoc] at hc
    exact hc
  let f : ((E)).Page 2 (12,138) →+ ((E)).Page 2 (14,139) := (delta2_12).hom.toAddMonoidHom
  change f (basis .nuCofiber 12 138 0) = 0 at h0
  change f (basis .nuCofiber 12 138 1) = 0 at h1
  change f (basis .nuCofiber 12 138 2) = basis .nuCofiber 14 139 3 at h2
  change f (basis .nuCofiber 12 138 3) = 0 at h3
  have hd : f a = if c 2=0 then 0 else basis .nuCofiber 14 139 3 := by
    rw [ha,map_add,map_add,map_add]
    split_ifs <;> simp only [map_zero,h0,h1,h2,h3,zero_add,add_zero]

  change f a = 0 ∨ f a = basis .nuCofiber 14 139 3
  by_cases hc2 : c 2=0
  · exact Or.inl (by simpa only [hc2,ite_true] using hd)
  · exact Or.inr (by simpa only [hc2,ite_false] using hd)


private theorem cofiber_bottom_T_reaches_six : ReachesPage nuCofiberSequence 6 (14,139) (bottom 14 139 T) := by
  let E := model.classical.sphere
  let A := E.ssData (14,139)
  obtain ⟨z,hz⟩ := t_permanent_cycle
  let k : WithTop ℕ := ↑(6-E.r₀).toNat
  let n : WithTop ℕ := ↑(2-E.r₀).toNat
  let z6 := (Subobject.ofLE (A.Z ⊤) (A.Z k) (A.Z_anti le_top)) z
  have hrep : RepresentsOnPage E 6 (14,139) T (A.pageπ k z6) := by
    refine ⟨by decide,z6,?_,rfl⟩
    change (Subobject.ofLE (A.Z k) (A.Z n) _ ≫ A.pageπ n) z6 = T
    dsimp only [z6]
    rw [← ModuleCat.comp_apply, ← Category.assoc, Subobject.ofLE_comp_ofLE]
    exact hz
  let f := model.classical.map (HasFunctorialCofiber.cofibι model.auxiliary.nuMap)
  exact ⟨_, f.representsOnPage hrep⟩


private theorem actual_bottom_14_139_injective : Function.Injective (bottom 14 139) := by
  intro a b hab
  have hz : bottom 14 139 (a-b)=0 := by rw [map_sub,hab,sub_self]
  exact sub_eq_zero.mp (actual_bottom_14_139_kernel_zero (a-b) hz)

/-- Full frozen target candidate, using the literal bottom image of T. -/
private theorem cofiber_target_to_e6_candidate :
    SurvivesTo nuCofiberSequence 6 (14,139) (bottom 14 139 T) := by
  classical
  have hs2 : nuCofiberSequence.r₀≤2 := (model.classical.firstPage _).le
  obtain ⟨e,he⟩ := tInBasis217
  have b2ne : basis .sphere 14 139 2≠0 := by
    intro hz
    exact (basis_vector_ne_zero e (2:Fin 3)) ((he (2:Fin 3)).trans hz)
  have tne : T≠0 := by
    intro hz
    exact (basis_vector_ne_zero e (1:Fin 3)) ((he (1:Fin 3)).trans (basis_T.trans hz))
  let incl := model.classical.map (HasFunctorialCofiber.cofibι model.auxiliary.nuMap)
  have hmap := incl.hasDifferential tInRow314
  change HasDifferential nuCofiberSequence 2 (12,138) (14,139)
    (bottom 12 138 (basis .sphere 12 138 1))
    (bottom 14 139 (basis .sphere 14 139 2)) at hmap
  have himage : delta2_12 (bottom 12 138 (basis .sphere 12 138 1)) =
      bottom 14 139 (basis .sphere 14 139 2) := hmap.eq_on_page_two.2
  have bb : bottom 14 139 (basis .sphere 14 139 2)=basis .nuCofiber 14 139 3 := by
    rcases cnu_d2_incoming14_image (bottom 12 138 (basis .sphere 12 138 1)) with hzero | hbasis
    · have hz : bottom 14 139 (basis .sphere 14 139 2)=0 := himage.symm.trans hzero
      exact False.elim (b2ne (actual_bottom_14_139_kernel_zero _ hz))
    · exact himage.symm.trans hbasis
  have avoid : ∀ a : nuCofiberSequence.Page 2 (12,138), delta2_12 a≠bottom 14 139 T := by
    intro a hit
    rcases cnu_d2_incoming14_image a with hzero | hbasis
    · exact tne (actual_bottom_14_139_kernel_zero T (hit.symm.trans hzero))
    · have hb : bottom 14 139 T=bottom 14 139 (basis .sphere 14 139 2) :=
        hit.symm.trans (hbasis.trans bb.symm)
      have ht : T=basis .sphere 14 139 2 := actual_bottom_14_139_injective hb
      exact (tIn_second_avoid (basis .sphere 12 138 1))
        (tInRow314.eq_on_page_two.2.trans ht.symm)
  obtain ⟨y6,hy6⟩ := cofiber_bottom_T_reaches_six
  obtain ⟨y3,hy3⟩ := reaches_earlier (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤6) ⟨y6,hy6⟩
  obtain ⟨y4,hy4⟩ := reaches_earlier (by decide : (2:ℤ)≤4) (by decide : (4:ℤ)≤6) ⟨y6,hy6⟩
  obtain ⟨y5,hy5⟩ := reaches_earlier (by decide : (2:ℤ)≤5) (by decide : (5:ℤ)≤6) ⟨y6,hy6⟩
  have y3ne : y3≠0 := represents_next_nonzero_of_not_incoming_at degree_2_12
    hs2 (by decide) hy3 (represents_two_self _) avoid
  have deg3 : (11,137)+nuCofiberSequence.diffDeg 3=(14,139) := by
    change (11,137)+(model.classical.obj _).diffDeg 3=(14,139)
    rw [model.classical.differentialDegree]
    decide
  have deg4 : (10,136)+nuCofiberSequence.diffDeg 4=(14,139) := by
    change (10,136)+(model.classical.obj _).diffDeg 4=(14,139)
    rw [model.classical.differentialDegree]
    decide
  have deg5 : (9,135)+nuCofiberSequence.diffDeg 5=(14,139) := by
    change (9,135)+(model.classical.obj _).diffDeg 5=(14,139)
    rw [model.classical.differentialDegree]
    decide
  have y4ne : y4≠0 := represents_next_nonzero_of_incoming_zero_at
    (hs2.trans (by decide : (2:ℤ)≤3)) (by decide) cnu_d2_d3_incoming14_zero.2 hy4 hy3 y3ne deg3
  have y5ne : y5≠0 := represents_next_nonzero_of_incoming_zero_at
    (hs2.trans (by decide : (2:ℤ)≤4)) (by decide) cnu_d4_incoming14_zero hy5 hy4 y4ne deg4
  have y6ne : y6≠0 := represents_next_nonzero_of_incoming_zero_at
    (hs2.trans (by decide : (2:ℤ)≤5)) (by decide) cnu_d5_incoming14_zero hy6 hy5 y5ne deg5
  exact ⟨y6,hy6,y6ne⟩

end
end CofiberResearch
end

public theorem cofiber_target_to_e6 :
    SurvivesTo nuCofiberSequence 6 (14,139) (bottom 14 139 T) := by
  exact CofiberResearch.cofiber_target_to_e6_candidate
/-- A hit before page six would kill the same nonzero E₆ continuation. -/
public theorem cofiber_target_not_hit_through5 :
    NeverHitOnWindow nuCofiberSequence 2 5 (14,139) (bottom 14 139 T) := by
  refine ⟨by decide,by decide,?_⟩
  intro r hr hlast
  exact no_earlier_hit_of_survival
    (by rw [model.classical.firstPage]; omega) hr (by omega) cofiber_target_to_e6

/-- Derived from the fixed literature result, rather than a duplicate assumption. -/
public theorem d2_h6 : HasNonzeroDifferential model.classical.sphere 2 (1,64) (3,65)
    h6 (product h0 h5Square) := by
  have h := KIP126.Literature.Standard.adamsOneLine_d2 6 (by decide)
  change HasNonzeroDifferential model.classical.sphere 2 (1,64) (3,65)
    h6 (product h0 h5Square) at h
  exact h

/-- The actual detector differential uses the same source isomorphism and labels. -/
public theorem detector_d3 :
    HasDifferential (model.classical.obj model.auxiliary.detector) 3 (16,112) (19,114)
      (detectorComparison 16 112 detector_v2_agrees._proof_1 detectorV2Sixteen)
      (detectorComparison 19 114 detector_beta_agrees._proof_1 detectorBetaGFour) := by
  rw [detector_v2_agrees, detector_beta_agrees]
  exact KIP126.Literature.Standard.detector_d3

end KIP126.Computation.Standard
