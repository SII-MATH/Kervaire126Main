module

public import KIP126.ProofTools.Language
public import KIP126.ProofTools.Operations
import all KIP126.ProofTools.Operations
import all KIP126.ProofTools.GeneralizedLeibniz.WeightedReverse
import all KIP126.ProofTools.GeneralizedLeibniz.SquareRepresentatives
import all KIP126.ProofTools.GeneralizedMahowald.SphereAutomorphismDetection

/-! Synthetic boundary extensions in AimPaper, Proposition 4.6 and Corollary
4.10. All representatives and connecting maps use the fixed synthetic model.
The classical differential is an input, not an extra extension-equation axiom. -/

section
namespace KIP126.ProofTools.Paper
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Standard
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
open KIP126.ProofTools.Internal.Leibniz
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
set_option Elab.async false

private theorem nu_weight_as_target (X : ClassicalObject) (s t : ℤ) (k : ℕ)
    (y : Ambient model X (s,t)) :
    nuWeightLabel model X s t (t-k) (by omega) y = targetNuLabel model X s t k y := by
  have hk : (t-(t-k)).toNat=k := by omega
  have transport (a b : ℕ) (hab : a=b) (h : (s,t,t-a)=(s,t,t-b)) :
      regradeE2 h (targetNuLabel model X s t a y)=targetNuLabel model X s t b y := by
    subst b
    rfl
  exact transport _ k hk _

private theorem nu_sphere_automorphism_detects (X : ClassicalObject)
    (s t : ℤ) (k : ℕ) (y : Ambient model X (s,t))
    (u : Smn (Syn:=SyntheticSpectrum) (t-s) (t-k) ≅ Smn (t-s) (t-k))
    (a : BiHom (t-s) (t-k) (model.nu.functor.obj (X.obj model.auxiliary)))
    (ha : Detects (model.convergence (.nu X)) (s,t,t-k)
      (targetNuLabel model X s t k y) a) :
    Detects (model.convergence (.nu X)) (s,t,t-k)
      (targetNuLabel model X s t k y) (u.hom ≫ a) := by
  let q := k+1
  have hq : 0<q := by dsimp [q]; omega
  have hmap := detects_map (.nu X) (.quotient q (.nu X)) (XModLambdaN.incl _ q)
    (s,t,t-k) _ a ha
  have hauto := sphere_automorphism_finite_detects X q k (by dsimp [q]; omega)
    s t y u (a≫XModLambdaN.incl _ q) hmap
  have hfil := detects_filtration (.nu X) _ _ _ ha
  obtain ⟨e,he,_,_,_⟩ := ha
  apply detects_reflect (.nu X) (.quotient q (.nu X)) (XModLambdaN.incl _ q)
    (s,t,t-k) (nu_projection_infinity_injective X q hq s t (t-k) (by dsimp [q]; omega))
    _ e he (u.hom≫a)
    (sphere_precomp_preserves_filtration (t-s) (t-k) s u.hom a
      hfil)
  simpa only [finiteTargetLabel, SyntheticAdamsFamily.pageMap,
    familyPageMap, SyntheticAdamsFamily.map, SyntheticObject.obj, Category.assoc] using hauto

private theorem nu_sphere_weight_detects (X : ClassicalObject)
    (s t w m : ℤ) (hw : w≤t) (hm : m=t-s) (y : Ambient model X (s,t))
    (u : Smn (Syn:=SyntheticSpectrum) m w ≅ Smn m w)
    (a : BiHom m w (model.nu.functor.obj (X.obj model.auxiliary)))
    (ha : Detects (model.convergence (.nu X)) (s,t,w)
      (nuWeightLabel model X s t w hw y) (homotopyRegrade hm rfl a)) :
    Detects (model.convergence (.nu X)) (s,t,w)
      (nuWeightLabel model X s t w hw y) (homotopyRegrade hm rfl (u.hom≫a)) := by
  subst m
  generalize hk : (t-w).toNat=k at *
  have he : w=t-k := by omega
  subst w
  rw [nu_weight_as_target] at ha ⊢
  exact nu_sphere_automorphism_detects X s t k y u a ha

private theorem weighted_absolute_boundary (X : ClassicalObject)
    (n k a : ℕ) (ha : a<n) (hnk : n≤a+k) (s t : ℤ)
    (x : Ambient model X (s,t)) (y : Ambient model X (s+k+1,t+k))
    (hd : HasDifferential (model.classical.obj (X.obj model.auxiliary))
      (k+1) (s,t) (s+k+1,t+k) x y)
    (hy : y∈permanentCycles model X (s+k+1,t+k)) :
    ∃ b : BiHom (t-s) (t-a) (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) n),
      Detects (model.convergence (.quotient n (.nu X))) (s,t,t-a)
        (finiteTargetLabel model X n s t a x) b ∧
      Detects (model.convergence (.nu X)) (s+k+1,t+k,t-a+n)
        (nuWeightLabel model X (s+k+1) (t+k) (t-a+n) (by omega) y)
        (homotopyRegrade (by dsimp; omega) rfl
          (biSuspensionHomEquiv (t-s) (t-a) n (model.nu.functor.obj (X.obj model.auxiliary))
            (b≫XModLambdaN.proj _ n))) := by
  by_cases ha0 : a=0
  · subst a
    obtain ⟨b,hb,hδ⟩ := differential_absolute_boundary X n k (by omega) (by omega) s t x y hd hy
    have H (w : ℤ) (hw : w=t) :
        ∃ c : BiHom (t-s) w (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) n),
          Detects (model.convergence (.quotient n (.nu X))) (s,t,w)
            (regradeE2 (show (s,t,t-(0:ℕ))=(s,t,w) by simp [hw])
              (finiteTargetLabel model X n s t 0 x)) c ∧
          Detects (model.convergence (.nu X)) (s+k+1,t+k,w+n)
            (nuWeightLabel model X (s+k+1) (t+k) (w+n) (by omega) y)
            (homotopyRegrade (by dsimp; omega) rfl
              (biSuspensionHomEquiv (t-s) w n (model.nu.functor.obj (X.obj model.auxiliary))
                (c≫XModLambdaN.proj _ n))) := by
      subst w
      exact ⟨b, first_label_detects_unshifted X n (by omega) s t x b hb, hδ⟩
    simpa only [regradeE2, eqToHom_refl,ConcreteCategory.id_apply] using H (t-(0:ℕ)) (by simp)
  have ha' : 0<a := by omega
  obtain ⟨b,hb,hδ⟩ := differential_absolute_boundary X (n-a) k (by omega) (by omega) s t x y hd hy
  let c := finiteLambdaClass X n a ha' ha s t b
  have hc := finite_quotient_lambda_detects X n a ha' ha s t x b hb
  refine ⟨c,hc,?_⟩
  have hauto := nu_sphere_weight_detects X (s+k+1) (t+k) (t+(n-a:ℕ)) ((t-s)-1)
    (by omega) (by omega) y (boundaryDivisionSourceIso a n ha.le (t-s) t)
    (biSuspensionHomEquiv (t-s) t ((n-a:ℕ):ℤ)
      (model.nu.functor.obj (X.obj model.auxiliary)) (b≫XModLambdaN.proj _ (n-a))) hδ
  have hdiv := divided_boundary_eq_reindex X a n ha' ha (t-s) t b
  dsimp only at hdiv
  rw [boundaryDivisionReindex_eq_precomp] at hdiv
  have transport_weight (w w' : ℤ) (he : w=w') (hw : w≤t+k) (hw' : w'≤t+k)
      (z : BiHom ((t-s)-1) w (model.nu.functor.obj (X.obj model.auxiliary)))
      (hz : Detects (model.convergence (.nu X)) (s+k+1,t+k,w)
        (nuWeightLabel model X (s+k+1) (t+k) w hw y)
        (homotopyRegrade (by dsimp; omega) rfl z)) :
      Detects (model.convergence (.nu X)) (s+k+1,t+k,w')
        (nuWeightLabel model X (s+k+1) (t+k) w' hw' y)
        (homotopyRegrade (by dsimp; omega) he z) := by
    subst w'
    exact hz
  have ht := transport_weight (t+(n-a:ℕ)) (t-a+n) (by omega) (by omega) (by omega) _ hauto
  rw [←hdiv] at ht
  convert ht using 1
  dsimp only [c]
  rw [finiteLambdaClass_vertical]
  simp only [regrade_precomp,←Category.assoc,eqToHom_trans]

private theorem detects_zero_representative (B : SyntheticObject) (i : Tridegree)
    (x : (model.family.obj (B.obj model.nu model.auxiliary)).E₂ i)
    (hx : HasInfinityRepresentative _ 2 i x 0) :
    Detects (model.convergence B) i x 0 := by
  refine ⟨0,hx,0,map_zero _,?_⟩
  simp only [map_zero]

private theorem nu_boundary_detects_zero (X : ClassicalObject) (s t w : ℤ)
    (hw : w≤t) (y : Ambient model X (s,t))
    (hy : y∈permanentCycles model X (s,t))
    (hb : y∈boundaries model X (1+t-w) (s,t)) :
    Detects (model.convergence (.nu X)) (s,t,w) (nuWeightLabel model X s t w hw y) 0 := by
  apply detects_zero_representative
  apply (KIP126.Literature.Standard.eInfinity_nu_labels X s t w hw y 0).mpr
  refine ⟨hy,?_⟩
  rw [map_zero]
  exact ((CrossingLabels.subquotient_zero_iff _ _ ⟨y,hy⟩).mpr hb).symm

private theorem weighted_absolute_boundary_closed (X : ClassicalObject)
    (n k a : ℕ) (hn : 0<n) (ha : a≤n) (hnk : n≤a+k) (s t : ℤ)
    (x : Ambient model X (s,t)) (y : Ambient model X (s+k+1,t+k))
    (hd : HasDifferential (model.classical.obj (X.obj model.auxiliary))
      (k+1) (s,t) (s+k+1,t+k) x y)
    (hy : y∈permanentCycles model X (s+k+1,t+k)) :
    ∃ b : BiHom (t-s) (t-a) (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) n),
      Detects (model.convergence (.quotient n (.nu X))) (s,t,t-a)
        (finiteTargetLabel model X n s t a x) b ∧
      Detects (model.convergence (.nu X)) (s+k+1,t+k,t-a+n)
        (nuWeightLabel model X (s+k+1) (t+k) (t-a+n) (by omega) y)
        (homotopyRegrade (by dsimp; omega) rfl
          (biSuspensionHomEquiv (t-s) (t-a) n (model.nu.functor.obj (X.obj model.auxiliary))
            (b≫XModLambdaN.proj _ n))) := by
  rcases ha.lt_or_eq with ha | heq
  · exact weighted_absolute_boundary X n k a ha hnk s t x y hd hy
  subst a
  have hzero := KIP126.Literature.Standard.finite_quotient_vanishing X n hn 2 (by omega)
    s t (t-n) (Or.inr (by omega))
  have hsource : finiteTargetLabel model X n s t n x=0 :=
    (ModuleCat.isZero_iff_subsingleton.mp hzero).elim _ _
  have hsourceDet := detects_zero_representative (.quotient n (.nu X)) (s,t,t-n)
    (finiteTargetLabel model X n s t n x) (by
      rw [hsource]
      exact HasInfinityRepresentative.zero _ 2 (by omega) _)
  have hr : 2≤(k:ℤ)+1 := by
    obtain ⟨_,_,_,hx,_,_⟩ := hd
    exact hx.1
  have hlater := FinitePageCalculus.differential_target_later_zero
    (t := (k:ℤ)+2) (by rw [model.classical.firstPage]; omega) (by omega) hd
  have hbound := represents_zero_mem_boundary model X ((k:ℤ)+2) (s+k+1,t+k) y hlater
  have htarget := nu_boundary_detects_zero X (s+k+1) (t+k) (t-n+n) (by omega) y hy (by
    convert hbound using 1
    congr 1
    omega)
  refine ⟨0,hsourceDet,?_⟩
  have hz {m m' w w' : ℤ} (hm : m=m') (hw : w=w') (A : SyntheticSpectrum) :
      homotopyRegrade hm hw (0 : BiHom m w A)=0 := by
    subst m'; subst w'; rfl
  simpa only [zero_comp,map_zero,hz] using htarget

/-- The actual absolute λ-boundary, with the fixed bigraded suspension. -/
@[expose] public def syntheticAbsoluteBoundary (X : ClassicalObject) (n : ℕ) :=
  XModLambdaN.proj (model.nu.functor.obj (X.obj model.auxiliary)) n ≫
    (Operations.biSuspensionIso n (model.nu.functor.obj (X.obj model.auxiliary))).inv

/-- The λ^a x label in the actual n-th quotient, indexed by its stem. -/
@[expose] public def syntheticDeltaSourceLabel (X : ClassicalObject) (n : ℕ) (s t : ℤ)
    (a : ℕ) (x : Ambient model X (s,t)) :
    (model.family.obj ((SyntheticObject.quotient n (.nu X)).obj model.nu model.auxiliary)).E₂
      (s,(t-s)+s,t-a) :=
  regradeE2 (by simp) (finiteTargetLabel model X n s t a x)

/-- Shift a boundary target label to the actual target of δ_n. -/
@[expose] public def syntheticBoundaryLabel (B : SyntheticObject) (n : ℕ) (m w v : ℤ)
    (y : (model.family.obj (B.obj model.nu model.auxiliary)).E₂ (v,m-1+v,w+n)) :
    (model.family.obj ((SyntheticObject.shift (1,-(n:ℤ)) B).obj model.nu model.auxiliary)).E₂
      (v,m+v,w) :=
  regradeE2 (by ext <;> dsimp <;> omega)
    (((essShift (1,-(n:ℤ))).page B 2 (by decide) (m-1,w+n) v).hom y)

private theorem boundary_detects_shifted (B : SyntheticObject) (n : ℕ) (m w v : ℤ)
    (a : BiHom m w ((SyntheticObject.quotient n B).obj model.nu model.auxiliary))
    (y : (model.family.obj (B.obj model.nu model.auxiliary)).E₂ (v,m-1+v,w+n))
    (hy : Detects (model.convergence B) (v,m-1+v,w+n) y
      (homotopyRegrade (by dsimp; omega) rfl
        (biSuspensionHomEquiv m w n (B.obj model.nu model.auxiliary)
          (a≫XModLambdaN.proj _ n)))) :
    Detects (model.convergence (.shift (1,-(n:ℤ)) B)) (v,m+v,w)
      (syntheticBoundaryLabel B n m w v y)
      (homotopyRegrade (by dsimp; omega) rfl (a≫absoluteBoundary (B.obj model.nu model.auxiliary) n)) := by
  let β := biSuspensionHomEquiv m w n (B.obj model.nu model.auxiliary) (a≫XModLambdaN.proj _ n)
  have hd := detects_shift B (1,-(n:ℤ)) (m-1,w+n) v y β hy
  have he : a≫absoluteBoundary (B.obj model.nu model.auxiliary) n =
      homotopyRegrade (sub_add_cancel m 1) (add_neg_cancel_right w (n:ℤ))
        (shiftHomotopyClass (1,-(n:ℤ)) (m-1,w+n) β) := by
    have h := congrArg (fun z => z≫(biSuspensionIso n (B.obj model.nu model.auxiliary)).inv)
      (bi_susp_symm_eq m w n (B.obj model.nu model.auxiliary) β)
    simpa [β,absoluteBoundary,shiftHomotopyClass,susp_invariance,Iso.homCongr] using h
  have hind : (v,((m-1,w+n)+(1,-(n:ℤ))).1+v,((m-1,w+n)+(1,-(n:ℤ))).2)=(v,m+v,w) := by
    ext <;> dsimp <;> omega
  have hd := detects_transport hind _ _ hd
  convert hd using 1
  · rfl
  · rw [he]
    simp only [regrade_precomp,←Category.assoc,eqToHom_trans]

/-- The target λ^(a+r-n-1)y in the shifted ν object; r is k+1. -/
@[expose] public def syntheticDeltaNuLabel (X : ClassicalObject) (n k a : ℕ) (s t : ℤ)
    (hnk : n≤a+k) (y : Ambient model X (s+k+1,t+k)) :=
  syntheticBoundaryLabel (.nu X) n (t-s) (t-a) (s+(k+1))
    (regradeE2 (by ext <;> dsimp <;> omega)
      (nuWeightLabel model X (s+k+1) (t+k) (t-a+n) (by omega) y))

/-- Corollary 4.10, absolute target: every λ-weight 0≤a≤n,
including both r≥n+1 and r<n+1, gives the actual δ_n extension equation.
The endpoint a=n is included and has both labels zero. The source and
target are labels in the fixed Adams systems. -/
public theorem syntheticDeltaExtension_absolute (X : ClassicalObject)
    (n k a : ℕ) (hn : 0<n) (ha : a≤n) (hnk : n≤a+k) (s t : ℤ)
    (x : Ambient model X (s,t)) (y : Ambient model X (s+k+1,t+k))
    (hd : HasDifferential (model.classical.obj (X.obj model.auxiliary))
      (k+1) (s,t) (s+k+1,t+k) x y)
    (hy : y∈permanentCycles model X (s+k+1,t+k)) :
    ∃ ex ey,
      HasInfinityRepresentative _ 2 (s,(t-s)+s,t-a)
        (syntheticDeltaSourceLabel X n s t a x) ex ∧
      HasInfinityRepresentative _ 2 (s+(k+1),(t-s)+(s+(k+1)),t-a)
        (syntheticDeltaNuLabel X n k a s t hnk y) ey ∧
      TowerExtensionEquation (model.convergentMap (.quotient n (.nu X))
        (.shift (1,-(n:ℤ)) (.nu X)) (syntheticAbsoluteBoundary X n))
        (t-s,t-a) s (k+1) ex ey := by
  obtain ⟨b,hb,hδ⟩ := weighted_absolute_boundary_closed X n k a hn ha hnk s t x y hd hy
  have hb' := detects_transport (show (s,t,t-a)=(s,(t-s)+s,t-a) by simp) _ _ hb
  have hδ' := detects_transport
    (show (s+k+1,t+k,t-a+n)=(s+(k+1),(t-s)-1+(s+(k+1)),t-a+n) by ext <;> dsimp <;> omega)
    _ _ hδ
  have hδ' := boundary_detects_shifted (.nu X) n (t-s) (t-a) (s+(k+1)) b _ (by
    convert hδ' using 1
    simp only [SyntheticObject.obj,regrade_precomp,←Category.assoc,eqToHom_trans])
  have he := extension_equation_of_detected_pair
    (model.convergentMap (.quotient n (.nu X)) (.shift (1,-(n:ℤ)) (.nu X))
      (syntheticAbsoluteBoundary X n)) (t-s,t-a) s (k+1) (by omega)
      (syntheticDeltaSourceLabel X n s t a x) _ b (b≫syntheticAbsoluteBoundary X n)
      (by exact hb') (by
          simpa only [syntheticAbsoluteBoundary, absoluteBoundary,Operations.biSuspensionIso,
            SyntheticObject.obj] using hδ') rfl
  exact he

/-- The actual finite connecting map δ_(n,m), in bigraded coordinates. -/
@[expose] public def syntheticFiniteBoundary (X : ClassicalObject) (n m : ℕ)
    (hn : 0<n) (hnm : n<m) :=
  ((model.quotients.tower (model.nu.functor.obj (X.obj model.auxiliary))).triangle hn hnm).delta ≫
    (Operations.biSuspensionIso n
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (m-n))).inv

private theorem finite_boundary_evaluation (X : ClassicalObject) (n m : ℕ)
    (hn : 0<n) (hnm : n<m) (v w : ℤ)
    (b : BiHom v w (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) n)) :
    b≫syntheticFiniteBoundary X n m hn hnm =
      (b≫syntheticAbsoluteBoundary X n)≫(SyntheticCategory.biShift (1,-(n:ℤ))).map
        (XModLambdaN.incl (model.nu.functor.obj (X.obj model.auxiliary)) (m-n)) := by
  let A := model.nu.functor.obj (X.obj model.auxiliary)
  apply (cancel_mono (biSuspensionIso n (XModLambdaN A (m-n))).hom).mp
  simp only [A,syntheticFiniteBoundary,syntheticAbsoluteBoundary,Operations.biSuspensionIso,
    Category.assoc,Iso.inv_hom_id,Category.comp_id]
  rw [biSuspensionIso_natural]
  simp only [Iso.inv_hom_id_assoc]
  exact selected_delta_evaluation_eq_cofiber X n m _ v w b

/-- The finite target λ^(a+r-n-1)y is the image of its absolute label under
exactly the quotient projection in the target triangle. -/
@[expose] public def syntheticDeltaFiniteLabel (X : ClassicalObject) (n m k a : ℕ) (s t : ℤ)
    (hnk : n≤a+k) (y : Ambient model X (s+k+1,t+k)) :=
  familyPageMap model.family
    ((SyntheticCategory.biShift (1,-(n:ℤ))).map
      (XModLambdaN.incl (model.nu.functor.obj (X.obj model.auxiliary)) (m-n)))
    2 (s+(k+1),(t-s)+(s+(k+1)),t-a)
    (syntheticDeltaNuLabel X n k a s t hnk y)

/-- Proposition 4.6 and Corollary 4.10 for finite m: the map is the actual
δ_(n,m), not a separately chosen extension relation. No bound r≤m is imposed;
the out-of-strip target is consequently zero. -/
public theorem syntheticDeltaExtension_finite (X : ClassicalObject)
    (n m k a : ℕ) (hn : 0<n) (ha : a≤n) (hnm : n<m) (hnk : n≤a+k) (s t : ℤ)
    (x : Ambient model X (s,t)) (y : Ambient model X (s+k+1,t+k))
    (hd : HasDifferential (model.classical.obj (X.obj model.auxiliary))
      (k+1) (s,t) (s+k+1,t+k) x y)
    (hy : y∈permanentCycles model X (s+k+1,t+k)) :
    ∃ ex ey,
      HasInfinityRepresentative _ 2 (s,(t-s)+s,t-a)
        (syntheticDeltaSourceLabel X n s t a x) ex ∧
      HasInfinityRepresentative _ 2 (s+(k+1),(t-s)+(s+(k+1)),t-a)
        (syntheticDeltaFiniteLabel X n m k a s t hnk y) ey ∧
      TowerExtensionEquation (model.convergentMap (.quotient n (.nu X))
        (.shift (1,-(n:ℤ)) (.quotient (m-n) (.nu X)))
        (syntheticFiniteBoundary X n m (by omega) hnm))
        (t-s,t-a) s (k+1) ex ey := by
  obtain ⟨b,hb,hδ⟩ := weighted_absolute_boundary_closed X n k a hn ha hnk s t x y hd hy
  have hb' := detects_transport (show (s,t,t-a)=(s,(t-s)+s,t-a) by simp) _ _ hb
  have hδ' := detects_transport
    (show (s+k+1,t+k,t-a+n)=(s+(k+1),(t-s)-1+(s+(k+1)),t-a+n) by ext <;> dsimp <;> omega)
    _ _ hδ
  have hδ' := boundary_detects_shifted (.nu X) n (t-s) (t-a) (s+(k+1)) b _ (by
    convert hδ' using 1
    simp only [SyntheticObject.obj,regrade_precomp,←Category.assoc,eqToHom_trans])
  let g := (SyntheticCategory.biShift (1,-(n:ℤ))).map
    (XModLambdaN.incl (model.nu.functor.obj (X.obj model.auxiliary)) (m-n))
  have hδf := detects_map (.shift (1,-(n:ℤ)) (.nu X))
    (.shift (1,-(n:ℤ)) (.quotient (m-n) (.nu X))) g
    (s+(k+1),(t-s)+(s+(k+1)),t-a) _ _ hδ'
  have heval := finite_boundary_evaluation X n m (by omega) hnm (t-s) (t-a) b
  have hdetection : Detects (model.convergence (.shift (1,-(n:ℤ)) (.quotient (m-n) (.nu X))))
      (s+(k+1),(t-s)+(s+(k+1)),t-a) (syntheticDeltaFiniteLabel X n m k a s t hnk y)
      (homotopyRegrade (by dsimp; omega) rfl (b≫syntheticFiniteBoundary X n m (by omega) hnm)) := by
    rw [heval]
    convert hδf using 1
    · rfl
    · simp only [g,syntheticAbsoluteBoundary,absoluteBoundary,Operations.biSuspensionIso,
        SyntheticObject.obj,regrade_precomp,Category.assoc]
  exact extension_equation_of_detected_pair
    (model.convergentMap (.quotient n (.nu X))
      (.shift (1,-(n:ℤ)) (.quotient (m-n) (.nu X)))
      (syntheticFiniteBoundary X n m (by omega) hnm))
    (t-s,t-a) s (k+1) (by omega) _ _ b
    (b≫syntheticFiniteBoundary X n m (by omega) hnm) hb' hdetection rfl

/-- Once a≥n, the source lies outside the n-th quotient's strip and is zero.
This includes the upper endpoint and the source-trivial cases of Corollary 4.10. -/
public theorem syntheticDeltaSource_vanishes (X : ClassicalObject)
    (n a : ℕ) (hn : 0<n) (hna : n≤a) (s t : ℤ)
    (e : ((model.family.obj ((SyntheticObject.quotient n (.nu X)).obj
      model.nu model.auxiliary)).sequence.ssData (s,(t-s)+s,t-a)).eInfty) : e=0 := by
  have hzero := finite_infinity_zero_outside X n hn s ((t-s)+s) (t-a) (by omega)
  exact (ModuleCat.isZero_iff_subsingleton.mp hzero).elim _ _

/-- Every finite target group outside the permitted λ range is zero.
For a=0 this is exactly the r>m vanishing in Proposition 4.6(1). -/
public theorem syntheticDeltaFiniteTarget_vanishes (X : ClassicalObject)
    (n m k a : ℕ) (hnm : n<m) (hout : m≤a+k) (s t : ℤ)
    (e : ((model.family.obj ((SyntheticObject.shift (1,-(n:ℤ))
      (.quotient (m-n) (.nu X))).obj model.nu model.auxiliary)).sequence.ssData
      (s+(k+1),(t-s)+(s+(k+1)),t-a)).eInfty) : e=0 := by
  let B : SyntheticObject := .quotient (m-n) (.nu X)
  let δ : ℤ×ℤ := (1,-(n:ℤ))
  let p : ℤ×ℤ := (t-s-1,t-a+n)
  let v := s+(k+1)
  have hzero := finite_infinity_zero_outside X (m-n) (by omega) v (p.1+v) p.2 (by
    dsimp [v,p]
    omega)
  let I := towerInfinityIso (model.convergence B) (model.convergence (.shift δ B))
    ((essShift δ).filtered B p) v
  have hind : (v,(p+δ).1+v,(p+δ).2)=(s+(k+1),(t-s)+(s+(k+1)),t-a) := by
    ext <;> dsimp [v,p,δ] <;> omega
  let J := I ≪≫ eqToIso (congrArg
    (fun j => ((model.family.obj ((SyntheticObject.shift δ B).obj model.nu model.auxiliary)).sequence.ssData j).eInfty) hind)
  have hz : IsZero ((model.family.obj ((SyntheticObject.shift δ B).obj model.nu model.auxiliary)).sequence.ssData
      (s+(k+1),(t-s)+(s+(k+1)),t-a)).eInfty :=
    hzero.of_iso J.symm
  exact (ModuleCat.isZero_iff_subsingleton.mp hz).elim _ _

/-- Proposition 4.6(1), r=k+1≥n+1, absolute target. -/
public theorem syntheticDeltaExtension_prop46_above_absolute (X : ClassicalObject)
    (n k : ℕ) (hn : 0<n) (hnk : n≤k) (s t : ℤ)
    (x : Ambient model X (s,t)) (y : Ambient model X (s+k+1,t+k))
    (hd : HasDifferential (model.classical.obj (X.obj model.auxiliary))
      (k+1) (s,t) (s+k+1,t+k) x y)
    (hy : y∈permanentCycles model X (s+k+1,t+k)) :
    ∃ ex ey,
      HasInfinityRepresentative _ 2 (s,(t-s)+s,t-0)
        (syntheticDeltaSourceLabel X n s t 0 x) ex ∧
      HasInfinityRepresentative _ 2 (s+(k+1),(t-s)+(s+(k+1)),t-0)
        (syntheticDeltaNuLabel X n k 0 s t (by omega) y) ey ∧
      TowerExtensionEquation (model.convergentMap (.quotient n (.nu X))
        (.shift (1,-(n:ℤ)) (.nu X)) (syntheticAbsoluteBoundary X n))
        (t-s,t-0) s (k+1) ex ey :=
  syntheticDeltaExtension_absolute X n k 0 hn (by omega) (by omega) s t x y hd hy

/-- Proposition 4.6(2), r=k+1<n+1, absolute target, with source λ^(n-k)x. -/
public theorem syntheticDeltaExtension_prop46_below_absolute (X : ClassicalObject)
    (n k : ℕ) (hn : 0<n) (hkn : k<n) (s t : ℤ)
    (x : Ambient model X (s,t)) (y : Ambient model X (s+k+1,t+k))
    (hd : HasDifferential (model.classical.obj (X.obj model.auxiliary))
      (k+1) (s,t) (s+k+1,t+k) x y)
    (hy : y∈permanentCycles model X (s+k+1,t+k)) :
    ∃ ex ey,
      HasInfinityRepresentative _ 2 (s,(t-s)+s,t-(n-k:ℕ))
        (syntheticDeltaSourceLabel X n s t (n-k) x) ex ∧
      HasInfinityRepresentative _ 2 (s+(k+1),(t-s)+(s+(k+1)),t-(n-k:ℕ))
        (syntheticDeltaNuLabel X n k (n-k) s t (by omega) y) ey ∧
      TowerExtensionEquation (model.convergentMap (.quotient n (.nu X))
        (.shift (1,-(n:ℤ)) (.nu X)) (syntheticAbsoluteBoundary X n))
        (t-s,t-(n-k:ℕ)) s (k+1) ex ey :=
  syntheticDeltaExtension_absolute X n k (n-k) hn (by omega) (by omega) s t x y hd hy

/-- Proposition 4.6(1) for the actual finite δ_(n,m). -/
public theorem syntheticDeltaExtension_prop46_above_finite (X : ClassicalObject)
    (n m k : ℕ) (hn : 0<n) (hnm : n<m) (hnk : n≤k) (s t : ℤ)
    (x : Ambient model X (s,t)) (y : Ambient model X (s+k+1,t+k))
    (hd : HasDifferential (model.classical.obj (X.obj model.auxiliary))
      (k+1) (s,t) (s+k+1,t+k) x y)
    (hy : y∈permanentCycles model X (s+k+1,t+k)) :
    ∃ ex ey,
      HasInfinityRepresentative _ 2 (s,(t-s)+s,t-0)
        (syntheticDeltaSourceLabel X n s t 0 x) ex ∧
      HasInfinityRepresentative _ 2 (s+(k+1),(t-s)+(s+(k+1)),t-0)
        (syntheticDeltaFiniteLabel X n m k 0 s t (by omega) y) ey ∧
      TowerExtensionEquation (model.convergentMap (.quotient n (.nu X))
        (.shift (1,-(n:ℤ)) (.quotient (m-n) (.nu X)))
        (syntheticFiniteBoundary X n m hn hnm))
        (t-s,t-0) s (k+1) ex ey :=
  syntheticDeltaExtension_finite X n m k 0 hn (by omega) hnm (by omega) s t x y hd hy

/-- Proposition 4.6(2) for the actual finite δ_(n,m). -/
public theorem syntheticDeltaExtension_prop46_below_finite (X : ClassicalObject)
    (n m k : ℕ) (hn : 0<n) (hnm : n<m) (hkn : k<n) (s t : ℤ)
    (x : Ambient model X (s,t)) (y : Ambient model X (s+k+1,t+k))
    (hd : HasDifferential (model.classical.obj (X.obj model.auxiliary))
      (k+1) (s,t) (s+k+1,t+k) x y)
    (hy : y∈permanentCycles model X (s+k+1,t+k)) :
    ∃ ex ey,
      HasInfinityRepresentative _ 2 (s,(t-s)+s,t-(n-k:ℕ))
        (syntheticDeltaSourceLabel X n s t (n-k) x) ex ∧
      HasInfinityRepresentative _ 2 (s+(k+1),(t-s)+(s+(k+1)),t-(n-k:ℕ))
        (syntheticDeltaFiniteLabel X n m k (n-k) s t (by omega) y) ey ∧
      TowerExtensionEquation (model.convergentMap (.quotient n (.nu X))
        (.shift (1,-(n:ℤ)) (.quotient (m-n) (.nu X)))
        (syntheticFiniteBoundary X n m hn hnm))
        (t-s,t-(n-k:ℕ)) s (k+1) ex ey :=
  syntheticDeltaExtension_finite X n m k (n-k) hn (by omega) hnm (by omega) s t x y hd hy

end
end KIP126.ProofTools.Paper
