module
public import KIP126.Main.Conditions
import all KIP126.Main.Internal.Selected.NormalizedFacts
import all KIP126.Main.Internal.Selected.FinitePages
import all KIP126.Main.Internal.PageCalculus

/-! Finite incoming window from Kervaire126 8cb35dad5,
Main/Solution/Computation/Route.lean:364–418 and
Computation/Route/SphereIncoming.lean:2673–2757 (MIT).
The Y argument needs only pages 2 through 6. It uses the same actual
finite table and does not assume the old unrestricted y_not_hit theorem. -/
@[expose] section
namespace KIP126.Main.Internal.NuNinth
open CategoryTheory CategoryTheory.Limits KIP126.Core.Algebra
open KIP126.Core.SpectralSequence KIP126.Core.SpectralSequence.FinitePageCalculus
open KIP126.Synthetic.Context KIP126.StableHomotopy KIP126.AdamsSynthetic
open KIP126.AdamsSynthetic.Standard (model)
open KIP126.Main.Internal KIP126.Main.Internal.Selected
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
private theorem y_source_four_d2  : HasDifferential Normalized.sphere 2 (4,131) (6,132)
    (Normalized.basis .sphere 4 131 0) (Normalized.basis .sphere 6 132 1) := by
  classical
  have hrow := Normalized.result ⟨.sphere,.equation,2,4,131,[0],6,132,[1],"S0_AdamsE2_ss",2573⟩ (by
    exact List.mem_of_getElem? (i := 173) (by rfl))
  dsimp only [Normalized.Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential Normalized.sphere 2 (4,131) (6,132) x y at hd
  have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 4 131 [0] = true := rfl
  have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 6 132 [1] = true := rfl
  simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem y_source_four_zero  :
    Subsingleton (Normalized.sphere.Page 4 (6,132)) := by
  classical
  let E := Normalized.sphere
  have h173 : HasDifferential E 2 (4,131) (6,132)
      (Normalized.basis .sphere 4 131 0) (Normalized.basis .sphere 6 132 1) := y_source_four_d2
  obtain ⟨e,he⟩ := Normalized.basis_correct ⟨.sphere,6,132,["368,1", "0,4,69,2"]⟩ (by
    exact List.mem_of_getElem? (i := 138) (by rfl))
  change E.Page 2 (6,132) ≃ₗ[ℤ] (Fin 2 →₀ F2) at e
  change ∀ i : Fin 2, e.symm (Finsupp.single i 1) = Normalized.basis .sphere 6 132 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 2) 1) = Normalized.basis .sphere 6 132 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 2) 1) = Normalized.basis .sphere 6 132 1 := he 1
  have n659 : ¬ HasDifferential E 3 (6,132) (9,134) (Normalized.basis .sphere 6 132 0) (0) := by
    have hh := Normalized.result ⟨.sphere,.refutation,3,6,132,[0],9,134,[],"proofs.db/log",2047477⟩ (by
      exact List.mem_of_getElem? (i := 659) (by rfl))
    dsimp only [Normalized.Statement] at hh
    obtain ⟨x,hx,y,hy,hh⟩ := hh
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 6 132 [0]=true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 9 134 []=true := rfl
    simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hh
    exact hh
  have hz1 : RepresentsOnPage E 4 (6,132) (Normalized.basis .sphere 6 132 1) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide) h173
  have hn {a : E.Page 4 (6,132)} (ha : RepresentsOnPage E 4 (6,132) (Normalized.basis .sphere 6 132 0) a) : False := by
    obtain ⟨a3,ha3⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤4) ha
    have hd : E.d 3 (6,132) a3=0 := represents_d_zero_of_later
      (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<4) ha3 ⟨a,ha⟩
    apply n659
    refine ⟨rfl,a3,0,ha3,RepresentsOnPage.zero (by decide),?_⟩
    exact hd
  have hall (a : E.Page 4 (6,132)) : a=0 := by
    let A := E.ssData (6,132)
    haveI : Epi (A.pageπ 2) := inferInstanceAs (Epi (cokernel.π _))
    obtain ⟨z,hz⟩ := (ModuleCat.epi_iff_surjective (A.pageπ 2)).mp inferInstance a
    let x := (Subobject.ofLE (A.Z 2) (A.Z 0) (A.Z_anti (by decide : (0:WithTop ℕ)≤2)) ≫ A.pageπ 0) z
    have hx : RepresentsOnPage E 4 (6,132) x a := ⟨by decide,z,rfl,hz⟩
    have heq : e x=Finsupp.single 0 (e x 0)+Finsupp.single 1 (e x 1) := by
      apply Finsupp.ext
      intro i
      fin_cases i <;> simp
    have hxe : x=e.symm (Finsupp.single 0 (e x 0)+Finsupp.single 1 (e x 1)) := by rw [←heq,LinearEquiv.symm_apply_apply]
    generalize hc0 : e x 0=c0 at hxe
    generalize hc1 : e x 1=c1 at hxe
    fin_cases c0 <;> fin_cases c1
    · change x=e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 1 (0:F2)) at hxe
      simp only [Finsupp.single_zero,add_zero,e.symm.map_zero] at hxe
      rw [hxe] at hx
      exact represents_unique hx (RepresentsOnPage.zero (by decide))
    · change x=e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 1 (1:F2)) at hxe
      simp only [Finsupp.single_zero,zero_add,he1] at hxe
      rw [hxe] at hx
      exact represents_unique hx hz1
    · change x=e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 1 (0:F2)) at hxe
      simp only [Finsupp.single_zero,add_zero,he0] at hxe
      rw [hxe] at hx
      exact False.elim (hn hx)
    · change x=e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 1 (1:F2)) at hxe
      simp only [map_add,he0,he1] at hxe
      rw [hxe] at hx
      have hh := represents_add_tail hx hz1
      have heq : (Normalized.basis .sphere 6 132 0 + Normalized.basis .sphere 6 132 1) + Normalized.basis .sphere 6 132 1 = Normalized.basis .sphere 6 132 0 := by
        apply e.injective
        simp only [map_add,←he0,←he1,LinearEquiv.apply_symm_apply]
        apply Finsupp.ext
        intro i
        fin_cases i <;> norm_num [Finsupp.add_apply,Finsupp.single_apply,Fin.ext_iff]; decide
      rw [heq,add_zero] at hh
      exact False.elim (hn hh)
  exact ⟨fun a b=>(hall a).trans (hall b).symm⟩


private theorem y_source_six_d2 :
    HasDifferential Normalized.sphere 2 (3,130) (5,131)
      (Normalized.basis .sphere 3 130 1) (Normalized.basis .sphere 5 131 0) := by
  have hrow := Normalized.result
    ⟨.sphere,.equation,2,3,130,[1],5,131,[0],"S0_AdamsE2_ss",2494⟩ (by
      exact List.mem_of_getElem? (i := 164) (by rfl))
  dsimp only [Normalized.Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  have vx : KIP126.Computation.Table.Raw.coordinatesValid
      KIP126.Computation.Table.Raw.degrees .sphere 3 130 [1] = true := rfl
  have vy : KIP126.Computation.Table.Raw.coordinatesValid
      KIP126.Computation.Table.Raw.degrees .sphere 5 131 [0] = true := rfl
  simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem y_source_six_zero :
    Subsingleton (Normalized.sphere.Page 6 (5,131)) := by
  obtain ⟨e,he⟩ := Normalized.basis_correct ⟨.sphere,5,131,["0,3,69,2"]⟩ (by
    exact List.mem_of_getElem? (i := 127) (by rfl))
  change Normalized.sphere.Page 2 (5,131) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e
  change ∀ i : Fin 1, e.symm (Finsupp.single i 1) = Normalized.basis .sphere 5 131 i.val at he
  have hz : RepresentsOnPage Normalized.sphere 6 (5,131)
      (Normalized.basis .sphere 5 131 0) 0 :=
    differential_target_later_zero (by decide) (by decide) y_source_six_d2
  have hall (a : Normalized.sphere.Page 6 (5,131)) : a = 0 := by
    obtain ⟨c,hc⟩ := page_generated_from_representatives (by decide : (2:ℤ)≤6)
      e (fun _ => 0) (by intro i; rw [he i]; fin_cases i; exact hz) a
    simpa using hc
  exact ⟨fun a b => (hall a).trans (hall b).symm⟩

private theorem target_no_incoming_through_six
    (x : Normalized.sphere.Page 2 (11,136))
    (hx : SurvivesTo Normalized.sphere 5 (11,136) x) :
    NeverHitOnWindow Normalized.sphere 2 6 (11,136) x := by
  refine ⟨by decide, by decide, ?_⟩
  intro r hr hr6
  let E := Normalized.sphere
  rintro ⟨q,h,z,y,hy,hyn,hd⟩
  by_cases hlow : r < 5
  · obtain ⟨a,ha⟩ := page_has_representative hr z
    have hdiff : HasDifferential E r q (11,136) a x := ⟨h,z,y,ha,hy,hd⟩
    have hzero := differential_target_later_zero (by exact hr) hlow hdiff
    obtain ⟨y5,hy5,hyn5⟩ := hx
    exact hyn5 (represents_unique hy5 hzero)
  · have hq : q = (11,136) - E.diffDeg r := eq_sub_iff_add_eq.mpr h
    subst q
    have hs : Subsingleton (E.Page r ((11,136) - E.diffDeg r)) := by
      interval_cases r
      · exact page_subsingleton_of_le 4 5 6 132 (by decide) (by decide) y_source_four_zero
      · exact y_source_six_zero
    have hz : z = 0 := hs.elim _ _
    rw [hz, map_zero] at hd
    exact hyn hd.symm

private theorem y_not_hit_through_six :
    NeverHitOnWindow model.classical.sphere 2 6 (11,136) KIP126.Computation.Standard.Y := by
  have h := target_no_incoming_through_six
  rw [Normalized.sphere_eq] at h
  exact h _ KIP126.Computation.Standard.y_to_e5

end
end KIP126.Main.Internal.NuNinth
