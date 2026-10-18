module

public import KIP126.Main.Conditions
import all KIP126.Main.Internal.Choice.LambdaInjectivity
import all KIP126.Main.Internal.Choice.Filtration
import all KIP126.Main.Internal.High125.Pages
import all KIP126.Main.Internal.Selected.NormalizedTable
import all KIP126.Main.Internal.Selected.ThetaFrames
import all KIP126.Main.Internal.Selected.ProductDetection

/-! Local finite-page and lambda arguments for LWX Remark 7.4 and Lemma 7.11.
The quotient-frame and eta-product arguments extend the existing Main ports
of Selected/ThetaData and Selected/DetectionData at bbac1fc05843 (MIT; see
the retained source LICENSE). Every computation is read through the fixed
public table API; these helpers introduce no new mathematical input. -/
@[expose] section
namespace KIP126.Main.Internal.Choice.Completion
open CategoryTheory CategoryTheory.Limits KIP126.Core.Algebra
open KIP126.Core.SpectralSequence KIP126.Core.SpectralSequence.FinitePageCalculus
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Kervaire.Route KIP126.Literature
open KIP126.AdamsSynthetic.Standard (model SyntheticSpectrum)
open KIP126.Main.Internal.Selected
open KIP126.Literature.Standard (eta)
open KIP126.Computation.Standard (correction)
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
open KIP126.Main.Internal.Selected.Normalized
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000

private theorem one_basis_cases {A : Type*} [AddCommGroup A] [Module ℤ A]
    (e : A ≃ₗ[ℤ] (Fin 1 →₀ F2)) (b : A)
    (hb : e.symm (Finsupp.single 0 1) = b) (x : A) : x=0 ∨ x=b := by
  have h := finite_basis_expansion e x
  simp only [Fin.sum_univ_one, hb] at h
  split_ifs at h with hc
  · exact Or.inl h
  · exact Or.inr h

private theorem stem126_three_d2 : HasDifferential Normalized.sphere 2
    (1,128) (3,129) (basis .sphere 1 128 0) (basis .sphere 3 129 0) := by
  have hrow := result ⟨.sphere,.equation,2,1,128,[0],3,129,[0],"S0_AdamsE2_ss",2315⟩
    (by exact List.mem_of_getElem? (i := 143) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  have vx : KIP126.Computation.Table.Raw.coordinatesValid
      KIP126.Computation.Table.Raw.degrees .sphere 1 128 [0] = true := rfl
  have vy : KIP126.Computation.Table.Raw.coordinatesValid
      KIP126.Computation.Table.Raw.degrees .sphere 3 129 [0] = true := rfl
  simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,
    List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  exact h

private theorem no_outgoing_126_three : NoOutgoingAt model.classical.sphere 3 129 := by
  have hnorm : NoOutgoingAt Normalized.sphere 3 129 := by
    obtain ⟨e,he⟩ := basis_correct ⟨.sphere,3,129,["0,1,69,2"]⟩
      (by exact List.mem_of_getElem? (i := 108) (by rfl))
    change Normalized.sphere.Page 2 (3,129) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e
    change ∀ i : Fin 1, e.symm (Finsupp.single i 1) = basis .sphere 3 129 i.val at he
    have he0 : e.symm (Finsupp.single 0 1) = basis .sphere 3 129 0 := he 0
    have hp : Subsingleton (Normalized.sphere.Page 3 (3,129)) :=
      choice_single_basis_zero_page (by decide) e _ he0
        (differential_target_later_zero (by decide) (by decide : (2:ℤ)<3) stem126_three_d2)
    intro r hr x
    by_cases h2 : r=2
    · subst r
      rcases one_basis_cases e _ he0 x with hx|hx
      · rw [hx,map_zero]
      · rw [hx]
        obtain ⟨_,hd⟩ := stem126_three_d2.eq_on_page_two
        change Normalized.sphere.d 2 (1,128) (basis .sphere 1 128 0) = _ at hd
        rw [←hd]
        exact congrArg (fun f => f (basis .sphere 1 128 0))
          (Normalized.sphere.d_comp_d 2 (1,128))
    · have hz := KIP126.Main.Internal.High125.page_subsingleton_of_le Normalized.sphere 3 r 3 129
        (by decide) (by omega) hp
      rw [hz.elim x 0,map_zero]
  rwa [Normalized.sphere_eq] at hnorm

private theorem stem125_five_third_zero : Subsingleton (Normalized.sphere.Page 3 (5,130)) := by
  have hrow := result ⟨.sphere,.equation,2,5,130,[0],7,131,[2],"S0_AdamsE2_ss",2435⟩
    (by exact List.mem_of_getElem? (i := 163) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  have vx : KIP126.Computation.Table.Raw.coordinatesValid
      KIP126.Computation.Table.Raw.degrees .sphere 5 130 [0] = true := rfl
  have vy : KIP126.Computation.Table.Raw.coordinatesValid
      KIP126.Computation.Table.Raw.degrees .sphere 7 131 [2] = true := rfl
  simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,
    List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  obtain ⟨e,he⟩ := basis_correct ⟨.sphere,5,130,["340,1"]⟩
    (by exact List.mem_of_getElem? (i := 126) (by rfl))
  obtain ⟨f,hf⟩ := basis_correct ⟨.sphere,7,131,["353,1","69,1,75,1","0,1,339,1"]⟩
    (by exact List.mem_of_getElem? (i := 148) (by rfl))
  change Normalized.sphere.Page 2 (5,130) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e
  change Normalized.sphere.Page 2 (7,131) ≃ₗ[ℤ] (Fin 3 →₀ F2) at f
  change ∀ i : Fin 1, e.symm (Finsupp.single i 1) = basis .sphere 5 130 i.val at he
  change ∀ i : Fin 3, f.symm (Finsupp.single i 1) = basis .sphere 7 131 i.val at hf
  have hn : basis .sphere 7 131 2 ≠ 0 := by
    have hf2 : f.symm (Finsupp.single 2 1) = basis .sphere 7 131 2 := hf 2
    rw [←hf2]
    exact basis_vector_ne_zero f 2
  apply next_page_zero_of_kernel (by decide : Normalized.sphere.r₀ ≤ 2)
  intro x hx
  have he0 : e.symm (Finsupp.single 0 1) = basis .sphere 5 130 0 := he 0
  rcases one_basis_cases e _ he0 x with h0|h1
  · exact h0
  · obtain ⟨_,hd⟩ := h.eq_on_page_two
    change Normalized.sphere.d 2 (5,130) (basis .sphere 5 130 0) = _ at hd
    rw [h1,hd] at hx
    exact (hn hx).elim

private theorem no_outgoing_125_low_late (s r : ℤ) (hs : s≤5) (hr : 3≤r)
    (x : Normalized.sphere.Page r (s,s+125)) : Normalized.sphere.d r (s,s+125) x=0 := by
  by_cases hs5 : s=5
  · subst s
    have hz := KIP126.Main.Internal.High125.page_subsingleton_of_le Normalized.sphere 3 r 5 130
      (by decide) hr stem125_five_third_zero
    rw [hz.elim x 0,map_zero]
  · exact no_outgoing_stem125_low s (by omega) r (by omega) x

private theorem regrade_heq {w w' : ℤ} (h : w=w')
    (a : BiHom 125 w (S_0_0 : SyntheticSpectrum)) :
    HEq a (homotopyRegrade rfl h a) := by
  subst w'
  rfl

private theorem multiply_heq (n : ℕ) {w w' : ℤ} (h : w=w')
    {a : BiHom 125 w (S_0_0 : SyntheticSpectrum)}
    {b : BiHom 125 w' (S_0_0 : SyntheticSpectrum)} (hab : HEq a b) :
    HEq (lambdaMultiply n a) (lambdaMultiply n b) := by
  subst w'
  cases hab
  rfl

private def lambdaAt (n : ℕ) (w v : ℤ)
    (h : ((125:ℤ),w)+(0,-(n:ℤ))=((125:ℤ),v))
    (a : BiHom 125 w (S_0_0 : SyntheticSpectrum)) : BiHom 125 v (S_0_0 : SyntheticSpectrum) :=
  (biShiftAddIso ((125:ℤ),w) (0,-(n:ℤ)) ((125:ℤ),v) h).inv.app S_0_0 ≫
    lambdaPow n (Smn 125 w) ≫ a

private theorem lambdaAt_heq (n : ℕ) (w v : ℤ)
    (h : ((125:ℤ),w)+(0,-(n:ℤ))=((125:ℤ),v))
    (a : BiHom 125 w (S_0_0 : SyntheticSpectrum)) :
    HEq (lambdaAt n w v h a) (lambdaMultiply n a) := by
  unfold lambdaAt lambdaMultiply
  simp only [biShiftAddIso,Iso.trans_inv,NatTrans.comp_app,eqToIso.inv,eqToHom_app,
    Category.assoc,eqToHom_comp_heq_iff,heq_eqToHom_comp_iff]
  rfl

private theorem lambda_one_power (n : ℕ)
    (a : BiHom 125 (130+(n:ℤ)) (S_0_0 : SyntheticSpectrum)) :
    HEq (lambdaMultiply 1 (lambdaMultiply n a)) (lambdaMultiply (n+1) a) := by
  let hn : ((125:ℤ),130+(n:ℤ))+(0,-(n:ℤ))=((125:ℤ),130) := by ext <;> dsimp <;> omega
  let h1 : ((125:ℤ),130)+(0,-(1:ℤ))=((125:ℤ),129) := by decide
  let hn1 : ((125:ℤ),130+(n:ℤ))+(0,-((n+1:ℕ):ℤ))=((125:ℤ),129) := by ext <;> dsimp <;> omega
  have ha := shift_assoc_inv model.quotients.coherence ((125:ℤ),130+(n:ℤ)) (0,-(n:ℤ)) (0,-1)
    ((125:ℤ),130) (0,-((n+1:ℕ):ℤ)) ((125:ℤ),129)
    hn (by ext <;> dsimp <;> omega) h1 hn1 (S_0_0 : SyntheticSpectrum)
  have heq : lambdaAt 1 130 129 h1 (lambdaAt n (130+(n:ℤ)) 130 hn a) =
      lambdaAt (n+1) (130+(n:ℤ)) 129 hn1 a := by
    unfold lambdaAt
    erw [←reassoc_of% (lambdaPow_naturality 1
      ((biShiftAddIso ((125:ℤ),130+(n:ℤ)) (0,-(n:ℤ)) ((125:ℤ),130) hn).inv.app (S_0_0 : SyntheticSpectrum)))]
    erw [←reassoc_of% (lambdaPow_naturality 1 (lambdaPow n (Smn 125 (130+(n:ℤ)))))]
    erw [←Category.assoc,ha]
    erw [lambdaPow_add model.quotients.coherence n 1 (n+1) rfl (Smn 125 (130+(n:ℤ)))]
    simp only [lambdaShiftAddIso, lambdaDegree, Category.assoc]
    rfl
  have houter := lambdaAt_heq 1 130 129 h1 (lambdaAt n (130+(n:ℤ)) 130 hn a)
  have hinner := multiply_heq 1 (by omega : (130:ℤ)=130+(n:ℤ)-(n:ℤ))
    (lambdaAt_heq n (130+(n:ℤ)) 130 hn a)
  exact (houter.trans hinner).symm.trans ((heq_of_eq heq).trans (lambdaAt_heq (n+1) _ _ hn1 a))

private theorem quotient_zero_iff_multiple (n : ℕ) (w : ℤ)
    (a : BiHom 125 w (S_0_0 : SyntheticSpectrum)) :
    quotientClass n a=0 ↔ ∃ b : BiHom 125 (w+(n:ℤ)) (S_0_0 : SyntheticSpectrum),
      HEq (lambdaMultiply n b) a := by
  generalize hv : w+(n:ℤ)=v
  have hw : w=v-(n:ℤ) := by omega
  subst w
  simpa only [heq_eq_eq] using vanishes_mod_lambda_iff_multiple n 125 v a

private theorem lambda_injective_125_130 :
    Function.Injective (fun a : BiHom 125 130 (S_0_0 : SyntheticSpectrum) => lambdaMultiply 1 a) := by
  have hnu := nu_lambda_injective_from_source .sphere 125 130 no_outgoing_126_three
  have hone (x : BiHom 125 130 (model.nu.functor.obj SphereSpectrum)) :
      lambdaMultiply 1 x = lambdaAction 125 130 _ x := by
    dsimp only [lambdaMultiply, lambdaAction]
    rw [lambdaPow_one model.quotients.coherence]
    rfl
  intro a b hab
  apply (cancel_mono model.nu.unitIso.inv).mp
  apply hnu
  have hh : lambdaMultiply 1 (a ≫ model.nu.unitIso.inv) =
      lambdaMultiply 1 (b ≫ model.nu.unitIso.inv) := by
    simpa only [lambdaMultiply,Category.assoc] using
      congrArg (fun z => z ≫ model.nu.unitIso.inv) hab
  exact (hone _).symm.trans (hh.trans (hone _))

private theorem normalized_quotient (n : ℕ)
    (a : BiHom 125 130 (S_0_0 : SyntheticSpectrum)) :
    quotientClass n a=0 ↔ quotientClass (n+1) (lambdaMultiply 1 a)=0 := by
  rw [quotient_zero_iff_multiple n 130 a,
    quotient_zero_iff_multiple (n+1) 129 (lambdaMultiply 1 a)]
  rw [show (129:ℤ)+((n+1:ℕ):ℤ)=130+(n:ℤ) by omega]
  constructor
  · rintro ⟨b,hb⟩
    exact ⟨b,(lambda_one_power n b).symm.trans (multiply_heq 1 (by omega) hb)⟩
  · rintro ⟨b,hb⟩
    let c : BiHom 125 130 (S_0_0 : SyntheticSpectrum) :=
      homotopyRegrade rfl (by omega : 130+(n:ℤ)-(n:ℤ)=130) (lambdaMultiply n b)
    have hc : HEq (lambdaMultiply n b) c := regrade_heq _ _
    have he : HEq (lambdaMultiply 1 c) (lambdaMultiply 1 a) :=
      (multiply_heq 1 (by omega) hc).symm.trans ((lambda_one_power n b).trans hb)
    have hca := lambda_injective_125_130 (eq_of_heq he)
    exact ⟨b,hc.trans (heq_of_eq hca)⟩

private theorem choice_quotient_frame_late (s t : ℤ) (k : ℕ) (hst : t=s+124) (hsk : s-(k+2)≤5) (hk : 1≤k)
    (x : model.classical.sphere.Page 2 (s,t)) (hx : InfinityGenerated model.classical.sphere (s,t) x) :
    ∃ x' : permanentCycles model .sphere (s,t), x'.val=x ∧
      ∀ q : PermanentQuotient model .sphere (1+(k:ℤ)) (s,t), q=0 ∨ q=subquotientClass _ _ x' := by
  let E := Normalized.sphere
  let A := E.ssData (s,t)
  have hB : A.B ⊤=A.B (k:WithTop ℕ) := by
    have hin (r : ℤ) (hr : (k:ℤ)+2≤r) : E.d r ((s,t)-E.diffDeg r)=0 := by
      change E.d r (s-r,t-(r-1))=0
      rw [show t-(r-1)=(s-r)+125 by omega]
      ext z
      exact no_outgoing_125_low_late (s-r) r (by omega) (by omega) z
    have h := boundaries_top_eq_of_d_eq_zero E (k+2) (by change (2:ℤ)≤_; omega) (s,t) hin
    change A.B ⊤=A.B ↑((k:ℤ)+2-2).toNat at h
    simpa only [add_sub_cancel_right,Int.toNat_natCast] using h
  obtain ⟨z,hz,_,hall⟩ := hx
  have hz' : cycleLabel model .sphere ⊤ (s,t) z=x := by
    have norm (P : SSData (ModuleCat ℤ)) (n : WithTop ℕ) (hn : n=0) :
        Subobject.ofLE (P.Z ⊤) (P.Z n) (P.Z_anti le_top) ≫ P.pageπ n =
          Subobject.ofLE (P.Z ⊤) (P.Z 0) (P.Z_anti le_top) ≫ P.pageπ 0 ≫
            eqToHom (congrArg P.page hn.symm) := by
      subst n
      simp only [eqToHom_refl,Category.comp_id]
    have hn := norm (model.classical.sphere.ssData (s,t)) (↑(2-model.classical.sphere.r₀).toNat)
      (by rw [model.classical.firstPage]; rfl)
    exact (congrArg (fun f => f z) hn).symm.trans hz
  let x' : permanentCycles model .sphere (s,t) := ⟨x,⟨z,hz'⟩⟩
  refine ⟨x',rfl,?_⟩
  intro q
  obtain ⟨y,rfl⟩ := Quotient.exists_rep q
  obtain ⟨z',hz''⟩ := y.property
  have zero_mem (v : (Subobject.underlying.obj (A.Z ⊤) : ModuleCat ℤ)) (hv : A.pageπ ⊤ v=0) :
      cycleLabel model .sphere ⊤ (s,t) v∈boundaries model .sphere (1+(k:ℤ)) (s,t) := by
    apply infinity_zero_boundary_mem (s,t) (1+(k:ℤ)) _ v hv
    have hb := hB
    change (Normalized.sphere.ssData (s,t)).B ⊤=(Normalized.sphere.ssData (s,t)).B ↑k at hb
    rw [Normalized.sphere_eq] at hb
    simpa only [show 1+(k:ℤ)-1=(k:ℤ) by omega,Int.toNat_natCast] using hb
  rcases hall (A.pageπ ⊤ z') with h0|h1
  · left
    apply (subquotientClass_eq_zero_iff _ _ _).mpr
    rw [←hz'']
    exact zero_mem z' h0
  · right
    apply sub_eq_zero.mp
    change subquotientClass _ _ y-subquotientClass _ _ x'=0
    rw [←map_sub]
    apply (subquotientClass_eq_zero_iff _ _ _).mpr
    change y.val-x'.val∈_
    have hzX : cycleLabel model .sphere ⊤ (s,t) z=x'.val := hz'
    rw [←hz'',←hzX,←map_sub]
    let z0 : (Subobject.underlying.obj (((model.classical.obj (ClassicalObject.sphere.obj model.auxiliary)).ssData (s,t)).Z ⊤) : ModuleCat ℤ) := z
    exact zero_mem (z'-z0) (by rw [map_sub,h1]; exact sub_self _)

private theorem choice_sphere_frame_late (s t : ℤ) (k : ℕ) (hst : t=s+124) (hsk : s-(k+2)≤5) (hk : 1≤k)
    (x : model.classical.sphere.Page 2 (s,t)) (hx : InfinityGenerated model.classical.sphere (s,t) x) :
    ∀ e : (model.family.sphere.sequence.ssData (s,t,t-k)).eInfty,
      e=0 ∨ HasInfinityRepresentative model.family.sphere 2 (s,t,t-k)
        (model.comparison.sphereE2 s t k x) e := by
  apply sphere_frame_of_permanent_quotient
  rw [show 1+t-(t-(k:ℤ))=1+(k:ℤ) by omega]
  exact choice_quotient_frame_late s t k hst hsk hk x hx

private theorem eta_weight131_branches_filtration_fifteen
    (b : BiHom 124 131 (S_0_0 : SyntheticSpectrum))
    (hbranch : DetectsNonzero (model.convergence .sphere) (13,137,131)
        (model.comparison.sphereE2 13 137 6 correction) b ∨
      ∃ a : BiHom 124 138 (S_0_0 : SyntheticSpectrum), lambdaMultiply 7 a=b) :
    FiltrationAtLeast model.syntheticTower 15 (sphereProduct eta b) := by
  rcases hbranch with h13 | ⟨a,ha⟩
  · have hd := model.multiplicationCompatible 1 2 13 137 0 6
      (model.standardClasses.standardHi 1) correction eta b eta_detected h13.1
    change Detects (model.convergence .sphere) (14,139,133)
      (model.comparison.sphereE2 14 139 6 (KIP126.Computation.Standard.product (r := (14,139))
        KIP126.Computation.Standard.h1 correction)) (sphereProduct eta b) at hd
    rw [KIP126.Computation.Standard.h1_correction_zero,map_zero] at hd
    exact detects_zero_filtration (model.convergence .sphere) (14,139,133) hd
  · have had := model.sphereDetectionCompatible.homotopy_lambda 14 138 7 a
    rw [ha] at had
    have hd := model.multiplicationCompatible 1 2 14 138 0 7
      (model.standardClasses.standardHi 1) (sphereFirstQuotient model 14 138 (quotientClass 1 a))
      eta b eta_detected had
    change Detects (model.convergence .sphere) (15,140,133) _ (sphereProduct eta b) at hd
    obtain ⟨e,he,a',ha',hgr⟩ := hd
    rw [←ha']
    have hm : ((model.syntheticTower.filtration (S_0_0 : SyntheticSpectrum)).F 15 ((125:ℤ),133)).arrow a' ∈
        (ModuleCat.subobjectModule (syntheticHomotopy (S_0_0 : SyntheticSpectrum) ((125:ℤ),133)))
          ((model.syntheticTower.filtration (S_0_0 : SyntheticSpectrum)).F 15 ((125:ℤ),133)) := ⟨a',rfl⟩
    simpa only [FiltrationAtLeast,SyntheticTowerPresentation.filtration,OrderIso.apply_symm_apply,
      SyntheticObject.obj,Int.reduceAdd,Int.reduceSub] using hm

private theorem stem124_weight131_filtration11_branches
    (hframe : ∀ e : (model.family.sphere.sequence.ssData (13,137,131)).eInfty,
      e=0 ∨ HasInfinityRepresentative model.family.sphere 2 (13,137,131)
        (model.comparison.sphereE2 13 137 6 correction) e)
    (a : BiHom 124 131 (S_0_0 : SyntheticSpectrum))
    (ha11 : FiltrationAtLeast model.syntheticTower 11 a) :
    DetectsNonzero (model.convergence .sphere) (13,137,131)
        (model.comparison.sphereE2 13 137 6 correction) a ∨
      ∃ b : BiHom 124 138 (S_0_0 : SyntheticSpectrum), lambdaMultiply 7 b=a := by
  have ha13 : FiltrationAtLeast model.syntheticTower 13 a := by
    apply (filtration_iff_of_infinity_zero (model.convergence .sphere)
      11 13 124 131 (by decide) ?_ a).mp ha11
    intro j hj hj'
    apply sphere_infinity_zero_of_permanent_quotient_zero j (124+j) 131 (by omega)
    interval_cases j
    · exact permanent_quotient_zero_of_page_zero .sphere 5 5 (by decide) (by decide) (11,135)
        KIP126.Computation.Standard.e5_stem124_af11
    · exact permanent_quotient_zero_of_page_zero .sphere 4 6 (by decide) (by decide) (12,136)
        KIP126.Computation.Standard.e4_stem124_af12
  rcases theta_detection_step (13,137,131)
    (model.comparison.sphereE2 13 137 6 correction) hframe a ha13 with hdet|ha14
  · exact Or.inl hdet
  right
  have h := KIP126.Literature.Standard.selected_filtration_lambda .sphere 124 131 14 (by decide)
    (a ≫ model.nu.unitIso.inv)
  change FiltrationAtLeast model.syntheticTower 14 (a ≫ model.nu.unitIso.inv) ↔
    ∃ b : BiHom 124 138 (model.nu.functor.obj SphereSpectrum), lambdaMultiply 7 b=a ≫ model.nu.unitIso.inv at h
  obtain ⟨b,hb⟩ := h.mp (map_filtration .sphere (.nu .sphere) model.nu.unitIso.inv a ha14)
  refine ⟨b ≫ model.nu.unitIso.hom,?_⟩
  simpa [lambdaMultiply,Category.assoc] using congrArg (fun q => q ≫ model.nu.unitIso.hom) hb


private theorem u_eta_difference_fifteen
    (u v : BiHom 124 134 (S_0_0 : SyntheticSpectrum)) (hu : UChoice u) (hv : UChoice v) :
    FiltrationAtLeast model.syntheticTower 15
      ((show BiHom 125 133 (S_0_0 : SyntheticSpectrum) from lambdaMultiply 3 (sphereProduct KIP126.Literature.Standard.eta u)) -
        (show BiHom 125 133 (S_0_0 : SyntheticSpectrum) from lambdaMultiply 3 (sphereProduct KIP126.Literature.Standard.eta v))) := by
  have hu0 := sphere_zero_weight_label_10_134 KIP126.Computation.Standard.U u hu.1
  have hv0 := sphere_zero_weight_label_10_134 KIP126.Computation.Standard.U v hv.1
  have hdu := model.sphereDetectionCompatible.homotopy_lambda 10 134 3 u
  have hdv := model.sphereDetectionCompatible.homotopy_lambda 10 134 3 v
  dsimp only [KIP126.Literature.sphereFirstQuotient] at hu0 hv0
  rw [hu0] at hdu
  rw [hv0] at hdv
  have hd := detects_sub_filtration (model.convergence .sphere) (10,134,131) hdu hdv
  have he := eta_weight131_branches_filtration_fifteen _
    (stem124_weight131_filtration11_branches
      (choice_sphere_frame_late 13 137 6 (by decide) (by decide) (by decide) _
        correction_infinity_generated) _ hd)
  have hlinear : sphereProduct KIP126.Literature.Standard.eta
      ((show BiHom 124 131 (S_0_0 : SyntheticSpectrum) from lambdaMultiply 3 u) -
        (show BiHom 124 131 (S_0_0 : SyntheticSpectrum) from lambdaMultiply 3 v)) =
      (show BiHom 125 133 (S_0_0 : SyntheticSpectrum) from lambdaMultiply 3 (sphereProduct KIP126.Literature.Standard.eta u)) -
        (show BiHom 125 133 (S_0_0 : SyntheticSpectrum) from lambdaMultiply 3 (sphereProduct KIP126.Literature.Standard.eta v)) := by
    have hh : sphereProduct KIP126.Literature.Standard.eta
        ((show BiHom 124 131 (S_0_0 : SyntheticSpectrum) from lambdaMultiply 3 u) -
          (show BiHom 124 131 (S_0_0 : SyntheticSpectrum) from lambdaMultiply 3 v)) =
        sphereProduct KIP126.Literature.Standard.eta (lambdaMultiply 3 u) -
          sphereProduct KIP126.Literature.Standard.eta (lambdaMultiply 3 v) := by
      simp only [sphereProduct, Int.reduceAdd, Int.reduceSub, Nat.cast_ofNat, Preadditive.comp_sub]
    rw [hh, eta_lambda3_right, eta_lambda3_right]
  rwa [hlinear] at he

end
end KIP126.Main.Internal.Choice.Completion
end
