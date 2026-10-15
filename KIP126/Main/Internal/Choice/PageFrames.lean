module

public import KIP126.Main.Conditions
import all KIP126.Main.Internal.PageCalculus

/-! Finite page calculations retained from Selected/ChoiceInvariance:409–507
at bbac1fc05843 (MIT). The fixed table is supplied separately. -/
@[expose] section
namespace KIP126.Main.Internal.Choice
open CategoryTheory CategoryTheory.Limits KIP126.Core.Algebra
open KIP126.Core.SpectralSequence KIP126.Core.SpectralSequence.FinitePageCalculus
open KIP126.Main.Internal
universe v
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
private theorem late_page_generic
    (E : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ×ℤ))
    (hr0 : E.r₀≤2) (hdeg2 : E.diffDeg 2=(2,1))
    (b5 : Fin 3 → E.Page 2 (5,67)) (b6 : Fin 2 → E.Page 2 (6,68))
    (b7 : Fin 2 → E.Page 2 (7,68)) (b8 : Fin 1 → E.Page 2 (8,69))
    (e5 : E.Page 2 (5,67) ≃ₗ[ℤ] (Fin 3 →₀ KIP126.Core.Algebra.F2))
    (he5 : ∀i:Fin 3, e5.symm (Finsupp.single i 1)=b5 i)
    (e6 : E.Page 2 (6,68) ≃ₗ[ℤ] (Fin 2 →₀ KIP126.Core.Algebra.F2))
    (he6 : ∀i:Fin 2, e6.symm (Finsupp.single i 1)=b6 i)
    (e7 : E.Page 2 (7,68) ≃ₗ[ℤ] (Fin 2 →₀ KIP126.Core.Algebra.F2))
    (he7 : ∀i:Fin 2, e7.symm (Finsupp.single i 1)=b7 i)
    (e8 : E.Page 2 (8,69) ≃ₗ[ℤ] (Fin 1 →₀ KIP126.Core.Algebra.F2))
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
    · change x=e6.symm (Finsupp.single 0 (0:KIP126.Core.Algebra.F2)+Finsupp.single 1 (0:KIP126.Core.Algebra.F2)) at hx
      simp only [Finsupp.single_zero,map_zero,add_zero] at hx
      rw [hx]
      simp only [map_zero]
    · change x=e6.symm (Finsupp.single 0 (0:KIP126.Core.Algebra.F2)+Finsupp.single 1 (1:KIP126.Core.Algebra.F2)) at hx
      simp only [Finsupp.single_zero,zero_add,he61] at hx
      rw [hx]
      simp only [hd61]
    · change x=e6.symm (Finsupp.single 0 (1:KIP126.Core.Algebra.F2)+Finsupp.single 1 (0:KIP126.Core.Algebra.F2)) at hx
      simp only [Finsupp.single_zero,add_zero,he60] at hx
      rw [hx]
      simp only [hd60]
    · change x=e6.symm (Finsupp.single 0 (1:KIP126.Core.Algebra.F2)+Finsupp.single 1 (1:KIP126.Core.Algebra.F2)) at hx
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
  have hbn : b3≠0 := next_nonzero_of_not_hit hr0
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


end KIP126.Main.Internal.Choice
end
