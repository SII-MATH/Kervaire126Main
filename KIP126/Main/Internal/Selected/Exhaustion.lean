module
public import KIP126.Main.Conditions
import all KIP126.Main.Internal.Selected.FinitePages
import all KIP126.Main.Internal.Selected.NormalizedFacts

/-! The complete AF13 and AF10 exhaustion arguments from pinned
Selected/ThetaData:884–1658. All finite rows are consumed from the fixed
computation interface; normalization is proved equal to the same sequence. -/
@[expose] section
namespace KIP126.Main.Internal.Selected
open CategoryTheory CategoryTheory.Limits KIP126.Core.Algebra
open KIP126.StableHomotopy KIP126.Core.SpectralSequence
open KIP126.Core.SpectralSequence.FinitePageCalculus
open KIP126.AdamsSynthetic.Standard (model)
open Normalized
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000

private def InfinityGenerated (E : KIP126.Core.SpectralSequence (ModuleCat ℤ) (ℤ×ℤ))
    (p : ℤ×ℤ) (x : E.Page 2 p) : Prop :=
  let A := E.ssData p
  let n : WithTop ℕ := ↑(2-E.r₀).toNat
  ∃ z : (Subobject.underlying.obj (A.Z ⊤) : ModuleCat ℤ),
    (Subobject.ofLE (A.Z ⊤) (A.Z n) (A.Z_anti le_top) ≫ A.pageπ n) z=x ∧
    A.pageπ ⊤ z ≠ 0 ∧ ∀ e : A.eInfty, e=0 ∨ e=A.pageπ ⊤ z

private theorem stem124_af13_exhaustion
    : InfinityGenerated Normalized.sphere (13,137) (basis .sphere 13 137 1) := by
  classical
  classical
  let E := Normalized.sphere
  let A := E.ssData (13,137)
  obtain ⟨z,hz,hzn⟩ := Normalized.correction_permanent
  change (Subobject.ofLE (A.Z ⊤) (A.Z 0) (A.Z_anti le_top) ≫ A.pageπ 0) z = _ at hz
  change A.pageπ ⊤ z ≠ 0 at hzn
  have h321 : HasDifferential E 2 (11,136) (13,137)
      (basis .sphere 11 136 4) (basis .sphere 13 137 3) := by
    have hrow := result ⟨.sphere,.equation,2,11,136,[4],13,137,[3],"S0_AdamsE2_ss",2914⟩ (by
      exact List.mem_of_getElem? (i := 321) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 2 (11,136) (13,137) a b at h
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 11 136 [4] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 13 137 [3] = true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    exact h
  have h322 : HasDifferential E 3 (10,135) (13,137)
      (basis .sphere 10 135 0) (basis .sphere 13 137 0) := by
    have hrow := result ⟨.sphere,.equation,3,10,135,[0],13,137,[0],"S0_AdamsE2_ss",2915⟩ (by
      exact List.mem_of_getElem? (i := 322) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 3 (10,135) (13,137) a b at h
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 10 135 [0] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 13 137 [0] = true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    exact h
  obtain ⟨_,incoming,a,hincoming,ha,hda⟩ := h322
  have hd2 := Normalized.d3_h4_x109
  obtain ⟨_,c,t,hc,ht,hdc,htn⟩ := hd2
  have hdc' : E.d 3 (13,137) c = t := hdc
  have hda' : E.d 3 (10,135) incoming = a := hda
  let down (r : ℤ) := Subobject.ofLE (A.Z ⊤) (A.Z ↑(r-2).toNat) (A.Z_anti le_top)
  let val (r : ℤ) := down r ≫ A.pageπ ↑(r-2).toNat
  have rep (r : ℤ) (hr : 2 ≤ r) (q : (Subobject.underlying.obj (A.Z ⊤) : ModuleCat ℤ)) :
      RepresentsOnPage E r (13,137) (val 2 q) (val r q) := by
    refine ⟨hr, down r q, ?_, rfl⟩
    change (Subobject.ofLE _ _ _ ≫ A.pageπ 0) ((down r) q) = val 2 q
    dsimp only [val, down]
    rw [← CategoryTheory.comp_apply, ← Category.assoc, Subobject.ofLE_comp_ofLE]
    rfl
  let b : E.Page 3 (13,137) := val 3 z
  have hb : RepresentsOnPage E 3 (13,137) (basis .sphere 13 137 1) b := by
    have h := rep 3 (by decide) z
    change val 2 z = _ at hz
    rw [hz] at h
    exact h
  have hthree : RepresentsOnPage E 3 (13,137) (basis .sphere 13 137 3) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) h321
  obtain ⟨e,he⟩ := basis_correct ⟨.sphere,13,137,["76,1,82,1", "9,1,251,1", "7,1,275,1", "0,5,367,1"]⟩ (by
    exact List.mem_of_getElem? (i := 208) (by rfl))
  change E.Page 2 (13,137) ≃ₗ[ℤ] (Fin 4 →₀ (ZMod 2)) at e
  change ∀i : Fin 4, e.symm (Finsupp.single i 1) = basis .sphere 13 137 i.val at he
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
  have kill (q : (Subobject.underlying.obj (A.Z ⊤) : ModuleCat ℤ)) (hq : val 3 q=0 ∨ val 3 q=a) : A.pageπ ⊤ q=0 := by
    have hfour : A.pageπ 2 (down 4 q)=0 := by
      apply (next_projection_zero_iff_incoming E 3 (by change (2:ℤ)≤3; omega) (10,135) (down 4 q)).mpr
      have hdown : (Subobject.ofLE (A.Z 2) (A.Z 1) (A.Z_anti (by decide : (1:WithTop ℕ)≤2)) ≫ A.pageπ 1) (down 4 q) = val 3 q := by
        change (Subobject.ofLE (A.Z 2) (A.Z 1) _ ≫ A.pageπ 1)
          ((Subobject.ofLE (A.Z ⊤) (A.Z 2) _) q) =
          (Subobject.ofLE (A.Z ⊤) (A.Z 1) _ ≫ A.pageπ 1) q
        rw [← CategoryTheory.comp_apply, ← Category.assoc, Subobject.ofLE_comp_ofLE]
      change ∃ x, E.d 3 (10,135) x = (Subobject.ofLE (A.Z 2) (A.Z 1) _ ≫ A.pageπ 1) (down 4 q)
      rw [hdown]
      rcases hq with hq|hq
      · exact ⟨0, by rw [hq,map_zero]⟩
      · exact ⟨incoming, hda'.trans hq.symm⟩
    change (A.pageπ 2) ((Subobject.ofLE (A.Z ⊤) (A.Z 2) _) q)=0 at hfour
    have heq := A.infinity_projection_eq_of_page_projection_eq 2 q 0 (by simpa only [CategoryTheory.comp_apply,map_zero] using hfour)
    simpa only [map_zero] using heq
  refine ⟨z,hz,hzn,?_⟩
  intro y
  haveI : Epi (A.pageπ ⊤) := inferInstanceAs (Epi (cokernel.π _))
  obtain ⟨q,rfl⟩ := (ModuleCat.epi_iff_surjective (A.pageπ ⊤)).mp inferInstance y
  have hqzero : E.d 3 (13,137) (val 3 q)=0 := by
    exact represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<4)
      (rep 3 (by decide) q) ⟨val 4 q,rep 4 (by decide) q⟩
  rcases hkernel (val 3 q) hqzero with hq|hq|hq|hq
  · exact Or.inl (kill q (Or.inl hq))
  · exact Or.inl (kill q (Or.inr hq))
  · apply Or.inr
    change A.pageπ ⊤ q = A.pageπ ⊤ z
    apply sub_eq_zero.mp
    rw [← map_sub]
    apply kill (q-z)
    left
    simp only [map_sub,hq,b,sub_self]
  · apply Or.inr
    change A.pageπ ⊤ q = A.pageπ ⊤ z
    apply sub_eq_zero.mp
    rw [← map_sub]
    apply kill (q-z)
    right
    simp only [map_sub,hq,b,add_sub_cancel_right]

private theorem stem124_af10_exhaustion
    : InfinityGenerated Normalized.sphere (10,134) (basis .sphere 10 134 4) := by
  classical
  let E := Normalized.sphere
  obtain ⟨e10_134,he10_134⟩ := basis_correct ⟨.sphere, 10, 134, ["389,1", "388,1", "1,1,366,1", "0,1,373,1", "0,2,367,1"]⟩ (by
    exact List.mem_of_getElem? (i := 181) (by rfl))
  change E.Page 2 (10,134) ≃ₗ[ℤ] (Fin 5 →₀ (ZMod 2)) at e10_134
  change ∀i : Fin 5, e10_134.symm (Finsupp.single i 1) = basis .sphere 10 134 i.val at he10_134
  have he10_134_0 : e10_134.symm (Finsupp.single 0 1) = basis .sphere 10 134 0 := he10_134 0
  have he10_134_1 : e10_134.symm (Finsupp.single 1 1) = basis .sphere 10 134 1 := he10_134 1
  have he10_134_2 : e10_134.symm (Finsupp.single 2 1) = basis .sphere 10 134 2 := he10_134 2
  have he10_134_3 : e10_134.symm (Finsupp.single 3 1) = basis .sphere 10 134 3 := he10_134 3
  have he10_134_4 : e10_134.symm (Finsupp.single 4 1) = basis .sphere 10 134 4 := he10_134 4
  obtain ⟨e11_135,he11_135⟩ := basis_correct ⟨.sphere, 11, 135, ["411,1", "410,1", "409,1", "0,1,389,1", "0,3,367,1"]⟩ (by
    exact List.mem_of_getElem? (i := 191) (by rfl))
  change E.Page 2 (11,135) ≃ₗ[ℤ] (Fin 5 →₀ (ZMod 2)) at e11_135
  change ∀i : Fin 5, e11_135.symm (Finsupp.single i 1) = basis .sphere 11 135 i.val at he11_135
  have he11_135_0 : e11_135.symm (Finsupp.single 0 1) = basis .sphere 11 135 0 := he11_135 0
  have he11_135_1 : e11_135.symm (Finsupp.single 1 1) = basis .sphere 11 135 1 := he11_135 1
  have he11_135_2 : e11_135.symm (Finsupp.single 2 1) = basis .sphere 11 135 2 := he11_135 2
  have he11_135_3 : e11_135.symm (Finsupp.single 3 1) = basis .sphere 11 135 3 := he11_135 3
  have he11_135_4 : e11_135.symm (Finsupp.single 4 1) = basis .sphere 11 135 4 := he11_135 4
  obtain ⟨e12_136,he12_136⟩ := basis_correct ⟨.sphere, 12, 136, ["1,1,387,1", "0,1,410,1", "0,1,409,1", "0,2,389,1", "0,4,367,1"]⟩ (by
    exact List.mem_of_getElem? (i := 200) (by rfl))
  change E.Page 2 (12,136) ≃ₗ[ℤ] (Fin 5 →₀ (ZMod 2)) at e12_136
  change ∀i : Fin 5, e12_136.symm (Finsupp.single i 1) = basis .sphere 12 136 i.val at he12_136
  have he12_136_0 : e12_136.symm (Finsupp.single 0 1) = basis .sphere 12 136 0 := he12_136 0
  have he12_136_1 : e12_136.symm (Finsupp.single 1 1) = basis .sphere 12 136 1 := he12_136 1
  have he12_136_2 : e12_136.symm (Finsupp.single 2 1) = basis .sphere 12 136 2 := he12_136 2
  have he12_136_3 : e12_136.symm (Finsupp.single 3 1) = basis .sphere 12 136 3 := he12_136 3
  have he12_136_4 : e12_136.symm (Finsupp.single 4 1) = basis .sphere 12 136 4 := he12_136 4
  obtain ⟨e13_137,he13_137⟩ := basis_correct ⟨.sphere, 13, 137, ["76,1,82,1", "9,1,251,1", "7,1,275,1", "0,5,367,1"]⟩ (by
    exact List.mem_of_getElem? (i := 208) (by rfl))
  change E.Page 2 (13,137) ≃ₗ[ℤ] (Fin 4 →₀ (ZMod 2)) at e13_137
  change ∀i : Fin 4, e13_137.symm (Finsupp.single i 1) = basis .sphere 13 137 i.val at he13_137
  have he13_137_0 : e13_137.symm (Finsupp.single 0 1) = basis .sphere 13 137 0 := he13_137 0
  have he13_137_1 : e13_137.symm (Finsupp.single 1 1) = basis .sphere 13 137 1 := he13_137 1
  have he13_137_2 : e13_137.symm (Finsupp.single 2 1) = basis .sphere 13 137 2 := he13_137 2
  have he13_137_3 : e13_137.symm (Finsupp.single 3 1) = basis .sphere 13 137 3 := he13_137 3
  obtain ⟨e15_138,he15_138⟩ := basis_correct ⟨.sphere, 15, 138, ["438,1", "7,1,279,1", "0,2,418,1"]⟩ (by
    exact List.mem_of_getElem? (i := 222) (by rfl))
  change E.Page 2 (15,138) ≃ₗ[ℤ] (Fin 3 →₀ (ZMod 2)) at e15_138
  change ∀i : Fin 3, e15_138.symm (Finsupp.single i 1) = basis .sphere 15 138 i.val at he15_138
  have he15_138_0 : e15_138.symm (Finsupp.single 0 1) = basis .sphere 15 138 0 := he15_138 0
  have he15_138_1 : e15_138.symm (Finsupp.single 1 1) = basis .sphere 15 138 1 := he15_138 1
  have he15_138_2 : e15_138.symm (Finsupp.single 2 1) = basis .sphere 15 138 2 := he15_138 2
  obtain ⟨e13_136,he13_136⟩ := basis_correct ⟨.sphere, 13, 136, ["418,1", "417,1", "0,2,386,1"]⟩ (by
    exact List.mem_of_getElem? (i := 207) (by rfl))
  change E.Page 2 (13,136) ≃ₗ[ℤ] (Fin 3 →₀ (ZMod 2)) at e13_136
  change ∀i : Fin 3, e13_136.symm (Finsupp.single i 1) = basis .sphere 13 136 i.val at he13_136
  have he13_136_0 : e13_136.symm (Finsupp.single 0 1) = basis .sphere 13 136 0 := he13_136 0
  have he13_136_1 : e13_136.symm (Finsupp.single 1 1) = basis .sphere 13 136 1 := he13_136 1
  have he13_136_2 : e13_136.symm (Finsupp.single 2 1) = basis .sphere 13 136 2 := he13_136 2
  obtain ⟨e14_137,he14_137⟩ := basis_correct ⟨.sphere, 14, 137, ["23,1,181,1", "0,1,418,1", "0,3,386,1"]⟩ (by
    exact List.mem_of_getElem? (i := 215) (by rfl))
  change E.Page 2 (14,137) ≃ₗ[ℤ] (Fin 3 →₀ (ZMod 2)) at e14_137
  change ∀i : Fin 3, e14_137.symm (Finsupp.single i 1) = basis .sphere 14 137 i.val at he14_137
  have he14_137_0 : e14_137.symm (Finsupp.single 0 1) = basis .sphere 14 137 0 := he14_137 0
  have he14_137_1 : e14_137.symm (Finsupp.single 1 1) = basis .sphere 14 137 1 := he14_137 1
  have he14_137_2 : e14_137.symm (Finsupp.single 2 1) = basis .sphere 14 137 2 := he14_137 2
  have h171 : HasDifferential E 4 (6,131) (10,134) (basis .sphere 6 131 0) (basis .sphere 10 134 0 + basis .sphere 10 134 3) := by
    have hrow := result ⟨.sphere, .equation, 4, 6, 131, [0], 10, 134, [0, 3], "S0_AdamsE2_ss", 2492⟩ (by
      exact List.mem_of_getElem? (i := 171) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 4 (6,131) (10,134) a b at h
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 6 131 [0] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 10 134 [0, 3] = true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    simpa only [add_assoc] using h
  have h172 : HasDifferential E 4 (6,131) (10,134) (basis .sphere 6 131 1) (basis .sphere 10 134 0 + basis .sphere 10 134 1 + basis .sphere 10 134 3 + basis .sphere 10 134 4) := by
    have hrow := result ⟨.sphere, .equation, 4, 6, 131, [1], 10, 134, [0, 1, 3, 4], "S0_AdamsE2_ss", 2493⟩ (by
      exact List.mem_of_getElem? (i := 172) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 4 (6,131) (10,134) a b at h
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 6 131 [1] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 10 134 [0, 1, 3, 4] = true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    simpa only [add_assoc] using h
  have h201 : HasDifferential E 2 (8,133) (10,134) (basis .sphere 8 133 1) (basis .sphere 10 134 2 + basis .sphere 10 134 4) := by
    have hrow := result ⟨.sphere, .equation, 2, 8, 133, [1], 10, 134, [2, 4], "S0_AdamsE2_ss", 2630⟩ (by
      exact List.mem_of_getElem? (i := 201) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 2 (8,133) (10,134) a b at h
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 8 133 [1] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 10 134 [2, 4] = true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    simpa only [add_assoc] using h
  have h250 : HasDifferential E 5 (10,134) (15,138) (basis .sphere 10 134 3) (basis .sphere 15 138 1) := by
    have hrow := result ⟨.sphere, .equation, 5, 10, 134, [3], 15, 138, [1], "S0_AdamsE2_ss", 2694⟩ (by
      exact List.mem_of_getElem? (i := 250) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 5 (10,134) (15,138) a b at h
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 10 134 [3] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 15 138 [1] = true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    simpa only [add_assoc] using h
  have h200 : HasDifferential E 3 (8,133) (11,135) (basis .sphere 8 133 0) (basis .sphere 11 135 0) := by
    have hrow := result ⟨.sphere, .equation, 3, 8, 133, [0], 11, 135, [0], "S0_AdamsE2_ss", 2629⟩ (by
      exact List.mem_of_getElem? (i := 200) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 3 (8,133) (11,135) a b at h
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 8 133 [0] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 11 135 [0] = true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    simpa only [add_assoc] using h
  have h226 : HasDifferential E 3 (9,134) (12,136) (basis .sphere 9 134 1) (basis .sphere 12 136 0) := by
    have hrow := result ⟨.sphere, .equation, 3, 9, 134, [1], 12, 136, [0], "S0_AdamsE2_ss", 2697⟩ (by
      exact List.mem_of_getElem? (i := 226) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 3 (9,134) (12,136) a b at h
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 9 134 [1] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 12 136 [0] = true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    simpa only [add_assoc] using h
  have h227 : HasDifferential E 2 (9,134) (11,135) (basis .sphere 9 134 0) (basis .sphere 11 135 3 + basis .sphere 11 135 4) := by
    have hrow := result ⟨.sphere, .equation, 2, 9, 134, [0], 11, 135, [3, 4], "S0_AdamsE2_ss", 2698⟩ (by
      exact List.mem_of_getElem? (i := 227) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 2 (9,134) (11,135) a b at h
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 9 134 [0] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 11 135 [3, 4] = true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    simpa only [add_assoc] using h
  have h228 : HasDifferential E 2 (9,134) (11,135) (basis .sphere 9 134 4) (basis .sphere 11 135 4) := by
    have hrow := result ⟨.sphere, .equation, 2, 9, 134, [4], 11, 135, [4], "S0_AdamsE2_ss", 2699⟩ (by
      exact List.mem_of_getElem? (i := 228) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 2 (9,134) (11,135) a b at h
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 9 134 [4] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 11 135 [4] = true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    simpa only [add_assoc] using h
  have h253 : HasDifferential E 2 (10,135) (12,136) (basis .sphere 10 135 1) (basis .sphere 12 136 1 + basis .sphere 12 136 2) := by
    have hrow := result ⟨.sphere, .equation, 2, 10, 135, [1], 12, 136, [1, 2], "S0_AdamsE2_ss", 2785⟩ (by
      exact List.mem_of_getElem? (i := 253) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 2 (10,135) (12,136) a b at h
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 10 135 [1] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 12 136 [1, 2] = true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    simpa only [add_assoc] using h
  have h254 : HasDifferential E 2 (10,135) (12,136) (basis .sphere 10 135 2) (basis .sphere 12 136 3 + basis .sphere 12 136 4) := by
    have hrow := result ⟨.sphere, .equation, 2, 10, 135, [2], 12, 136, [3, 4], "S0_AdamsE2_ss", 2786⟩ (by
      exact List.mem_of_getElem? (i := 254) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 2 (10,135) (12,136) a b at h
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 10 135 [2] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 12 136 [3, 4] = true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    simpa only [add_assoc] using h
  have h255 : HasDifferential E 2 (10,135) (12,136) (basis .sphere 10 135 4) (basis .sphere 12 136 4) := by
    have hrow := result ⟨.sphere, .equation, 2, 10, 135, [4], 12, 136, [4], "S0_AdamsE2_ss", 2787⟩ (by
      exact List.mem_of_getElem? (i := 255) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 2 (10,135) (12,136) a b at h
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 10 135 [4] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 12 136 [4] = true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    simpa only [add_assoc] using h
  have h277 : HasDifferential E 4 (11,135) (15,138) (basis .sphere 11 135 1 + basis .sphere 11 135 2) (basis .sphere 15 138 0) := by
    have hrow := result ⟨.sphere, .equation, 4, 11, 135, [1, 2], 15, 138, [0], "S0_AdamsE2_ss", 2781⟩ (by
      exact List.mem_of_getElem? (i := 277) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 4 (11,135) (15,138) a b at h
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 11 135 [1, 2] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 15 138 [0] = true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    simpa only [add_assoc] using h
  have h278 : HasDifferential E 2 (11,135) (13,136) (basis .sphere 11 135 2) (basis .sphere 13 136 2) := by
    have hrow := result ⟨.sphere, .equation, 2, 11, 135, [2], 13, 136, [2], "S0_AdamsE2_ss", 2782⟩ (by
      exact List.mem_of_getElem? (i := 278) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 2 (11,135) (13,136) a b at h
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 11 135 [2] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 13 136 [2] = true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    simpa only [add_assoc] using h
  have h304 : HasDifferential E 2 (12,136) (14,137) (basis .sphere 12 136 2) (basis .sphere 14 137 2) := by
    have hrow := result ⟨.sphere, .equation, 2, 12, 136, [2], 14, 137, [2], "S0_AdamsE2_ss", 2849⟩ (by
      exact List.mem_of_getElem? (i := 304) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 2 (12,136) (14,137) a b at h
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 12 136 [2] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 14 137 [2] = true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    simpa only [add_assoc] using h
  have h321 : HasDifferential E 2 (11,136) (13,137) (basis .sphere 11 136 4) (basis .sphere 13 137 3) := by
    have hrow := result ⟨.sphere, .equation, 2, 11, 136, [4], 13, 137, [3], "S0_AdamsE2_ss", 2914⟩ (by
      exact List.mem_of_getElem? (i := 321) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 2 (11,136) (13,137) a b at h
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 11 136 [4] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 13 137 [3] = true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    simpa only [add_assoc] using h
  have h322 : HasDifferential E 3 (10,135) (13,137) (basis .sphere 10 135 0) (basis .sphere 13 137 0) := by
    have hrow := result ⟨.sphere, .equation, 3, 10, 135, [0], 13, 137, [0], "S0_AdamsE2_ss", 2915⟩ (by
      exact List.mem_of_getElem? (i := 322) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 3 (10,135) (13,137) a b at h
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 10 135 [0] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 13 137 [0] = true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    simpa only [add_assoc] using h
  have h323 : ReachesPage E 1000 (13,137) (basis .sphere 13 137 1) := by
    have hrow := result ⟨.sphere, .reaches, 1000, 13, 137, [1], 13, 137, [], "S0_AdamsE2_ss", 2916⟩ (by
      exact List.mem_of_getElem? (i := 323) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,h⟩ := hrow
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 13 137 [1] = true := rfl
    simp only [decode,vx,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha
    rw [←ha] at h
    exact h
  have h324 : HasDifferential E 3 (13,137) (16,139) (basis .sphere 13 137 2) (basis .sphere 16 139 0) := by
    have hrow := result ⟨.sphere, .equation, 3, 13, 137, [2], 16, 139, [0], "S0_AdamsE2_ss", 2917⟩ (by
      exact List.mem_of_getElem? (i := 324) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 3 (13,137) (16,139) a b at h
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 13 137 [2] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 16 139 [0] = true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    simpa only [add_assoc] using h
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
  have f2_expand {N : ℕ} (f : Fin N →₀ (ZMod 2)) :
      f = ∑ i : Fin N, if f i=0 then 0 else Finsupp.single i 1 := by
    exact FinitePageCalculus.f2_expand f
  have rep_zero {r : ℤ} {p : ℤ × ℤ} {x : E.Page r p}
      (h : RepresentsOnPage E r p 0 x) : x=0 :=
    represents_unique h (RepresentsOnPage.zero h.1)
  have rep_double {r : ℤ} {p : ℤ × ℤ} {x : E.Page 2 p} {a : E.Page r p}
      (hx : x+x=0) (ha : RepresentsOnPage E r p x a) : a+a=0 := by
    exact rep_zero (by simpa only [hx] using hadd ha ha)
  -- All four possible incoming d2 directions reach E3.
  have d2_13 : E.d 2 (13,137)=0 := by
    obtain ⟨_,x0,y0,hx0,hy0,_⟩ := h322
    obtain ⟨_,x2,y2,hx2,hy2,_⟩ := h324
    have h0 := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) (hrep2 _) ⟨y0,hy0⟩
    have h1 := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<1000) (hrep2 _) h323
    have h2 := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) (hrep2 _) ⟨x2,hx2⟩
    have h3 : E.d 2 (13,137) (basis .sphere 13 137 3)=0 := by
      have hd := h321.eq_on_page_two.2
      change E.d 2 (11,136) _ = _ at hd
      rw [←hd]
      exact congrArg (fun f => f (basis .sphere 11 136 4)) (E.d_comp_d 2 (11,136))
    have one (i : Fin 4) : E.d 2 (13,137) (e13_137.symm (Finsupp.single i 1))=0 := by
      rw [he13_137]
      fin_cases i
      · exact h0
      · exact h1
      · exact h2
      · exact h3
    have all (f : Fin 4 →₀ (ZMod 2)) : E.d 2 (13,137) (e13_137.symm f)=0 := by
      induction f using Finsupp.induction with
      | zero => simp
      | @single_add i a f hi ha ih =>
        rw [map_add,map_add,ih,add_zero]
        fin_cases a
        · simp
        · exact one i
    ext x
    simpa only [LinearEquiv.symm_apply_apply,ModuleCat.hom_zero,LinearMap.zero_apply] using all (e13_137 x)
  have hif {r : ℤ} {p : ℤ × ℤ} {x : E.Page 2 p} {a : E.Page r p}
      (c : (ZMod 2)) (h : RepresentsOnPage E r p x a) :
      RepresentsOnPage E r p (if c=0 then 0 else x) (if c=0 then 0 else a) := by
    split
    · exact RepresentsOnPage.zero h.1
    · exact h
  -- The complete d2 kernel in degree (12,136) consists of the d3 target
  -- basis0 and three d2 boundaries; consequently its entire d3 map is zero.
  have d3_12 : E.d 3 (12,136)=0 := by
    obtain ⟨_,in0,a0,hin0,ha0,hda0⟩ := h226
    have hd0 : E.d 3 (12,136) a0=0 :=
      IsPageBoundary.d_eq_zero (E:=E) (r:=3) (p:=(9,134)) ⟨in0,hda0⟩
    have rz12 : RepresentsOnPage E 3 (12,136)
        (basis .sphere 12 136 1 + basis .sphere 12 136 2) 0 :=
      differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) h253
    have rz34 : RepresentsOnPage E 3 (12,136)
        (basis .sphere 12 136 3 + basis .sphere 12 136 4) 0 :=
      differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) h254
    have rz4 : RepresentsOnPage E 3 (12,136) (basis .sphere 12 136 4) 0 :=
      differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) h255
    have rz3 : RepresentsOnPage E 3 (12,136) (basis .sphere 12 136 3) 0 := by
      simpa only [add_sub_cancel_right,sub_self] using hsub rz34 rz4
    have d0 := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) (hrep2 _) ⟨a0,ha0⟩
    have d12 := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) (hrep2 _) ⟨0,rz12⟩
    have d3 := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) (hrep2 _) ⟨0,rz3⟩
    have d4 := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) (hrep2 _) ⟨0,rz4⟩
    have d2 := h304.eq_on_page_two.2
    change E.d 2 (12,136) (basis .sphere 12 136 2) = basis .sphere 14 137 2 at d2
    have tn : basis .sphere 14 137 2 ≠ 0 := by
      rw [←he14_137_2]
      intro h
      have hh := congrArg e14_137 h
      simp only [LinearEquiv.apply_symm_apply,map_zero] at hh
      have hh' := congrArg (fun f : Fin 3 →₀ (ZMod 2) => f 2) hh
      norm_num at hh'
    have d1 : E.d 2 (12,136) (basis .sphere 12 136 1) = -basis .sphere 14 137 2 := by
      simpa only [map_add,d2,eq_neg_iff_add_eq_zero] using d12
    ext x
    obtain ⟨a,ha⟩ := lift_e2 (by decide : (2:ℤ)≤3) x
    have da := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) (hrep2 a) ⟨x,ha⟩
    let c : Fin 5 → (ZMod 2) := e12_136 a
    have hcoef := congrArg e12_136.symm (f2_expand (e12_136 a))
    simp only [LinearEquiv.symm_apply_apply,map_sum,map_add,Fin.sum_univ_succ,apply_ite,map_zero] at hcoef
    change a = (if c 0=0 then 0 else e12_136.symm (Finsupp.single 0 1)) + ((if c 1=0 then 0 else e12_136.symm (Finsupp.single 1 1)) + ((if c 2=0 then 0 else e12_136.symm (Finsupp.single 2 1)) + ((if c 3=0 then 0 else e12_136.symm (Finsupp.single 3 1)) + ((if c 4=0 then 0 else e12_136.symm (Finsupp.single 4 1)) + 0)))) at hcoef
    simp only [he12_136_0,he12_136_1,he12_136_2,he12_136_3,he12_136_4,add_zero] at hcoef
    have hc : (c 1=0) ↔ (c 2=0) := by
      have hd := congrArg (E.d 2 (12,136)) hcoef
      simp only [map_add,apply_ite,map_zero] at hd
      rw [da,d0,d1,d2,d3,d4] at hd
      simp only [ite_self,zero_add,add_zero] at hd
      constructor
      · intro h1
        by_contra h2
        simp only [h1,h2,ite_true,ite_false,zero_add] at hd
        exact tn hd.symm
      · intro h2
        by_contra h1
        simp only [h1,h2,ite_true,ite_false,add_zero] at hd
        exact tn (neg_eq_zero.mp hd.symm)
    have hacomb : a = (if c 0=0 then 0 else basis .sphere 12 136 0) +
        (if c 1=0 then 0 else basis .sphere 12 136 1 + basis .sphere 12 136 2) +
        (if c 3=0 then 0 else basis .sphere 12 136 3) +
        (if c 4=0 then 0 else basis .sphere 12 136 4) := by
      rw [hcoef]
      by_cases h1 : c 1=0
      · have h2 := hc.mp h1
        simp only [h1,h2,ite_true,zero_add,add_zero]
        abel
      · have h2 := mt hc.mpr h1
        simp only [h1,h2,ite_false]
        abel
    have hx : x=(if c 0=0 then 0 else a0) := by
      apply represents_unique ha
      rw [hacomb]
      simpa only [ite_self,add_zero] using hadd (hadd (hadd (hif (c 0) ha0) (hif (c 1) rz12)) (hif (c 3) rz3)) (hif (c 4) rz4)
    rw [hx]
    simp only [apply_ite,map_zero,hd0,ite_self,ModuleCat.hom_zero,LinearMap.zero_apply]
  obtain ⟨_,a4,t0,ha4,ht0,hda4⟩ := h277
  have hd4 : E.d 4 (11,135) a4=t0 := hda4
  -- Incoming d2 and d3 kill every E4 direction except basis1+basis2.
  have kernel_11 (x : E.Page 4 (11,135)) : x=0 ∨ x=a4 := by
    have rz0 : RepresentsOnPage E 4 (11,135) (basis .sphere 11 135 0) 0 :=
      differential_target_later_zero (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<4) h200
    have rz34 : RepresentsOnPage E 4 (11,135)
        (basis .sphere 11 135 3 + basis .sphere 11 135 4) 0 :=
      differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4) h227
    have rz4 : RepresentsOnPage E 4 (11,135) (basis .sphere 11 135 4) 0 :=
      differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4) h228
    have rz3 : RepresentsOnPage E 4 (11,135) (basis .sphere 11 135 3) 0 := by
      simpa only [add_sub_cancel_right,sub_self] using hsub rz34 rz4
    have d0 := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4) (hrep2 _) ⟨0,rz0⟩
    have d12 := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4) (hrep2 _) ⟨a4,ha4⟩
    have d3 := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4) (hrep2 _) ⟨0,rz3⟩
    have d4 := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4) (hrep2 _) ⟨0,rz4⟩
    have d2 := h278.eq_on_page_two.2
    change E.d 2 (11,135) (basis .sphere 11 135 2) = basis .sphere 13 136 2 at d2
    have tn : basis .sphere 13 136 2 ≠ 0 := by
      rw [←he13_136_2]
      intro h
      have hh := congrArg e13_136 h
      simp only [LinearEquiv.apply_symm_apply,map_zero] at hh
      have hh' := congrArg (fun f : Fin 3 →₀ (ZMod 2) => f 2) hh
      norm_num at hh'
    have d1 : E.d 2 (11,135) (basis .sphere 11 135 1) = -basis .sphere 13 136 2 := by
      simpa only [map_add,d2,eq_neg_iff_add_eq_zero] using d12
    obtain ⟨a,ha⟩ := lift_e2 (by decide : (2:ℤ)≤4) x
    have da := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4) (hrep2 a) ⟨x,ha⟩
    let c : Fin 5 → (ZMod 2) := e11_135 a
    have hcoef := congrArg e11_135.symm (f2_expand (e11_135 a))
    simp only [LinearEquiv.symm_apply_apply,map_sum,map_add,Fin.sum_univ_succ,apply_ite,map_zero] at hcoef
    change a = (if c 0=0 then 0 else e11_135.symm (Finsupp.single 0 1)) + ((if c 1=0 then 0 else e11_135.symm (Finsupp.single 1 1)) + ((if c 2=0 then 0 else e11_135.symm (Finsupp.single 2 1)) + ((if c 3=0 then 0 else e11_135.symm (Finsupp.single 3 1)) + ((if c 4=0 then 0 else e11_135.symm (Finsupp.single 4 1)) + 0)))) at hcoef
    simp only [he11_135_0,he11_135_1,he11_135_2,he11_135_3,he11_135_4,add_zero] at hcoef
    have hc : (c 1=0) ↔ (c 2=0) := by
      have hd := congrArg (E.d 2 (11,135)) hcoef
      simp only [map_add,apply_ite,map_zero] at hd
      rw [da,d0,d1,d2,d3,d4] at hd
      simp only [ite_self,zero_add,add_zero] at hd
      constructor
      · intro h1
        by_contra h2
        simp only [h1,h2,ite_true,ite_false,zero_add] at hd
        exact tn hd.symm
      · intro h2
        by_contra h1
        simp only [h1,h2,ite_true,ite_false,add_zero] at hd
        exact tn (neg_eq_zero.mp hd.symm)
    have hacomb : a = (if c 0=0 then 0 else basis .sphere 11 135 0) +
        (if c 1=0 then 0 else basis .sphere 11 135 1 + basis .sphere 11 135 2) +
        (if c 3=0 then 0 else basis .sphere 11 135 3) +
        (if c 4=0 then 0 else basis .sphere 11 135 4) := by
      rw [hcoef]
      by_cases h1 : c 1=0
      · have h2 := hc.mp h1
        simp only [h1,h2,ite_true,zero_add,add_zero]
        abel
      · have h2 := mt hc.mpr h1
        simp only [h1,h2,ite_false]
        abel
    have hx : x=(if c 1=0 then 0 else a4) := by
      apply represents_unique ha
      rw [hacomb]
      simpa only [ite_self,add_zero,zero_add] using hadd (hadd (hadd (hif (c 0) rz0) (hif (c 1) ha4)) (hif (c 3) rz3)) (hif (c 4) rz4)
    by_cases h : c 1=0
    · exact Or.inl (by simpa only [h,ite_true] using hx)
    · exact Or.inr (by simpa only [h,ite_false] using hx)
  -- No d2 or d3 enters the d5 target degree, so distinct E2 labels
  -- that reach E4 remain distinct there.
  have nonzero4 {x : E.Page 2 (15,138)} (hx : x ≠ 0) {a : E.Page 4 (15,138)}
      (ha : RepresentsOnPage E 4 (15,138) x a) : a ≠ 0 := by
    obtain ⟨b,hb⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤4) ha
    have hn3 : b ≠ 0 := represents_next_nonzero_of_incoming_zero
      (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)≤2) (by exact d2_13) hb (hrep2 x) hx
    exact represents_next_nonzero_of_incoming_zero
      (by change (2:ℤ)≤3; omega) (by decide : (2:ℤ)≤3) (by exact d3_12) ha hb hn3
  obtain ⟨_,c5,t1,hc5,ht1,hdc5⟩ := h250
  have hd5 : E.d 5 (10,134) c5=t1 := hdc5
  -- The only possible d4 image is target basis0, independent of basis1.
  have t1n : t1 ≠ 0 := by
    obtain ⟨_,z,hz2,hz5⟩ := ht1
    let T := E.ssData (15,138)
    let i := Subobject.ofLE (T.Z 3) (T.Z 2) (T.Z_anti (by decide : (2:WithTop ℕ)≤3))
    let t14 := T.pageπ 2 (i z)
    have ht14 : RepresentsOnPage E 4 (15,138) (basis .sphere 15 138 1) t14 := by
      refine ⟨by decide,i z,?_,rfl⟩
      change (i ≫ Subobject.ofLE (T.Z 2) (T.Z 0) _ ≫ T.pageπ 0) z = _
      dsimp only [i]
      rw [←Category.assoc,Subobject.ofLE_comp_ofLE]
      exact hz2
    have hn : t14 ≠ 0 := nonzero4 (by
      rw [←he15_138_1]
      intro h
      have hh := congrArg e15_138 h
      simp only [LinearEquiv.apply_symm_apply,map_zero] at hh
      have hh' := congrArg (fun f : Fin 3 →₀ (ZMod 2) => f 1) hh
      norm_num at hh') ht14
    have hne : t14 ≠ t0 := by
      intro heq
      have hh := nonzero4 (x:=basis .sphere 15 138 1 - basis .sphere 15 138 0) (by
        rw [←he15_138_1,←he15_138_0]
        intro h
        have hh := congrArg e15_138 h
        simp only [map_sub,LinearEquiv.apply_symm_apply,map_zero] at hh
        have hh' := congrArg (fun f : Fin 3 →₀ (ZMod 2) => f 1) hh
        norm_num at hh') (hsub ht14 ht0)
      exact hh (sub_eq_zero.mpr heq)
    intro hzero
    have hinc := (next_projection_zero_iff_incoming E 4
      (by change (2:ℤ)≤4; omega) (11,135) z).mp (hz5.trans hzero)
    change t14 ∈ LinearMap.range (E.d 4 (11,135)).hom at hinc
    obtain ⟨a,ha⟩ := hinc
    rcases kernel_11 a with h|h
    · apply hn
      simpa only [h,map_zero] using ha.symm
    · apply hne
      simpa only [h,hd4] using ha.symm
  let A := E.ssData (10,134)
  obtain ⟨z,hz,hzn⟩ := Normalized.u_permanent
  change (Subobject.ofLE (A.Z ⊤) (A.Z 0) (A.Z_anti le_top) ≫ A.pageπ 0) z = _ at hz
  change A.pageπ ⊤ z ≠ 0 at hzn
  let down (r : ℤ) := Subobject.ofLE (A.Z ⊤) (A.Z ↑(r-2).toNat) (A.Z_anti le_top)
  let val (r : ℤ) := down r ≫ A.pageπ ↑(r-2).toNat
  have rep (r : ℤ) (hr : 2≤r) (q : (Subobject.underlying.obj (A.Z ⊤) : ModuleCat ℤ)) :
      RepresentsOnPage E r (10,134) (val 2 q) (val r q) := by
    refine ⟨hr,down r q,?_,rfl⟩
    change (Subobject.ofLE _ _ _ ≫ A.pageπ 0) ((down r) q) = val 2 q
    dsimp only [val,down]
    rw [←CategoryTheory.comp_apply,←Category.assoc,Subobject.ofLE_comp_ofLE]
    rfl
  let u5 : E.Page 5 (10,134) := val 5 z
  have hu5 : RepresentsOnPage E 5 (10,134) (basis .sphere 10 134 4) u5 := by
    have h := rep 5 (by decide) z
    change val 2 z = _ at hz
    rw [hz] at h
    exact h
  have hu0 : E.d 5 (10,134) u5=0 :=
    represents_d_zero_of_later (by change (2:ℤ)≤5; omega) (by decide : (5:ℤ)<6)
      (rep 5 (by decide) z) ⟨val 6 z,rep 6 (by decide) z⟩
  have r03 : RepresentsOnPage E 5 (10,134)
      (basis .sphere 10 134 0 + basis .sphere 10 134 3) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤4; omega) (by decide : (4:ℤ)<5) h171
  have r0134 : RepresentsOnPage E 5 (10,134)
      (basis .sphere 10 134 0 + basis .sphere 10 134 1 +
        basis .sphere 10 134 3 + basis .sphere 10 134 4) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤4; omega) (by decide : (4:ℤ)<5) h172
  have r24 : RepresentsOnPage E 5 (10,134)
      (basis .sphere 10 134 2 + basis .sphere 10 134 4) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<5) h201
  have ddouble (i : Fin 5) : basis .sphere 10 134 i.val + basis .sphere 10 134 i.val=0 := by
    rw [←he10_134 i]
    have hh : (Finsupp.single i (1:ZMod 2) : Fin 5 →₀ (ZMod 2)) + Finsupp.single i 1 = 0 := by
      rw [←Finsupp.single_add,show (1:ZMod 2)+1=0 from by decide,Finsupp.single_zero]
    have h := congrArg e10_134.symm hh
    simpa only [map_add,map_zero] using h
  have cdouble : c5+c5=0 := rep_double (ddouble 3) hc5
  have udouble : u5+u5=0 := rep_double (ddouble 4) hu5
  have cneg : -c5=c5 := by simpa only [add_sub_cancel_right,zero_sub] using (congrArg (fun t => t-c5) cdouble).symm
  have uneg : -u5=u5 := by simpa only [add_sub_cancel_right,zero_sub] using (congrArg (fun t => t-u5) udouble).symm
  have r0 : RepresentsOnPage E 5 (10,134) (basis .sphere 10 134 0) c5 := by
    simpa only [add_sub_cancel_right,zero_sub,cneg] using hsub r03 hc5
  have r1 : RepresentsOnPage E 5 (10,134) (basis .sphere 10 134 1) u5 := by
    have he : (basis .sphere 10 134 0 + basis .sphere 10 134 1 + basis .sphere 10 134 3 + basis .sphere 10 134 4) - (basis .sphere 10 134 0 + basis .sphere 10 134 3) - basis .sphere 10 134 4 = basis .sphere 10 134 1 := by abel
    simpa only [he,sub_self,zero_sub,uneg] using hsub (hsub r0134 r03) hu5
  have r2 : RepresentsOnPage E 5 (10,134) (basis .sphere 10 134 2) u5 := by
    simpa only [add_sub_cancel_right,zero_sub,uneg] using hsub r24 hu5
  -- At E5 the complete five-element basis maps to [c,U,U,c,U].
  -- The nonzero differential of c leaves precisely zero and U in its kernel.
  have kernel5 (x : E.Page 5 (10,134)) (hx : E.d 5 (10,134) x=0) : x=0 ∨ x=u5 := by
    let vv : Fin 5 → E.Page 5 (10,134) := ![c5,u5,u5,c5,u5]
    have hv (i : Fin 5) : RepresentsOnPage E 5 (10,134) (e10_134.symm (Finsupp.single i 1)) (vv i) := by
      rw [he10_134]
      fin_cases i
      · exact r0
      · exact r1
      · exact r2
      · exact hc5
      · exact hu5
    obtain ⟨coef,hcoef⟩ := page_generated_from_representatives (by decide : (2:ℤ)≤5) e10_134 vv hv x
    simp only [Fin.sum_univ_succ] at hcoef
    change x = (if coef 0=0 then 0 else c5) + ((if coef 1=0 then 0 else u5) + ((if coef 2=0 then 0 else u5) + ((if coef 3=0 then 0 else c5) + ((if coef 4=0 then 0 else u5) + 0)))) at hcoef
    have hc : (coef 0=0) ↔ (coef 3=0) := by
      have hd := congrArg (E.d 5 (10,134)) hcoef
      simp only [map_add,apply_ite,map_zero] at hd
      rw [hx,hd5,hu0] at hd
      simp only [ite_self,zero_add,add_zero] at hd
      constructor
      · intro h0
        by_contra h3
        simp only [h0,h3,ite_true,ite_false,zero_add] at hd
        exact t1n hd.symm
      · intro h3
        by_contra h0
        simp only [h0,h3,ite_true,ite_false,add_zero] at hd
        exact t1n hd.symm
    have hform : x=(if coef 1=0 then 0 else u5) + (if coef 2=0 then 0 else u5) + (if coef 4=0 then 0 else u5) := by
      rw [hcoef]
      by_cases h0 : coef 0=0
      · have h3 := hc.mp h0
        simp only [h0,h3,ite_true,zero_add,add_zero]
        abel
      · have h3 := mt hc.mpr h0
        simp only [h0,h3,ite_false,add_zero]
        calc
          _ = (c5+c5) + ((if coef 1=0 then 0 else u5) + (if coef 2=0 then 0 else u5) + (if coef 4=0 then 0 else u5)) := by abel
          _ = _ := by rw [cdouble,zero_add]
    by_cases h1 : coef 1=0 <;> by_cases h2 : coef 2=0 <;> by_cases h4 : coef 4=0
    all_goals simp only [h1,h2,h4,ite_true,ite_false,zero_add,add_zero,udouble] at hform
    all_goals first | exact Or.inl hform | exact Or.inr hform
  refine ⟨z,hz,hzn,?_⟩
  intro y
  haveI : Epi (A.pageπ ⊤) := inferInstanceAs (Epi (cokernel.π _))
  obtain ⟨q,rfl⟩ := (ModuleCat.epi_iff_surjective (A.pageπ ⊤)).mp inferInstance y
  have hqzero : E.d 5 (10,134) (val 5 q)=0 :=
    represents_d_zero_of_later (by change (2:ℤ)≤5; omega) (by decide : (5:ℤ)<6)
      (rep 5 (by decide) q) ⟨val 6 q,rep 6 (by decide) q⟩
  rcases kernel5 (val 5 q) hqzero with hq|hq
  · left
    have h := A.infinity_projection_eq_of_page_projection_eq 3 q 0 (by
      change val 5 q = val 5 0
      rw [map_zero]
      exact hq)
    simpa only [map_zero] using h
  · right
    exact A.infinity_projection_eq_of_page_projection_eq 3 q z hq


end
end KIP126.Main.Internal.Selected
