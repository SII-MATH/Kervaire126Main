module

import all KIP126.ProofTools.GeneralizedMahowald.FiniteLevelLabels
import all KIP126.ProofTools.GeneralizedMahowald.FiniteComparison
import all KIP126.ProofTools.GeneralizedMahowald.FiniteLevelSourceLabel
import all KIP126.ProofTools.GeneralizedMahowald.FiniteLevelConclusion
import all KIP126.ProofTools.GeneralizedMahowald.SphereLabels
import all KIP126.ProofTools.GeneralizedMahowald.Signs

/-! Forward finite-lambda labels for the common MH representative.
All maps and all detecting homotopy classes remain in the fixed quotients. -/

@[expose] section
namespace KIP126.ProofTools.Internal.Mahowald
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Standard
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Leibniz
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 200000
set_option Elab.async false

private def finiteLambdaLayerClass (X : ClassicalObject)
    (N A j : ℕ) (hA : 0 < A) (hAN : A < N) (s t : ℤ)
    (b : BiHom (t-s) (t-j)
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (N-A))) :
    BiHom (t-s) (t-(A+j))
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) N) :=
  homotopyRegrade (by simp) (by dsimp; omega)
    (shiftHomotopyClass (0,-(A:ℤ)) (t-s,t-j) b) ≫
    ((model.quotients.tower _).triangle hA hAN).lambdaMap

/-- The actual lambda transition carries every visible layer j to A+j.
No divided source label is guessed or chosen independently. -/
private theorem finite_lambda_layer_detects (X : ClassicalObject)
    (N A j : ℕ) (hA : 0 < A) (hAN : A < N) (hj : j < N-A)
    (s t : ℤ) (y : Ambient model X (s,t))
    (b : BiHom (t-s) (t-j)
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (N-A)))
    (hb : Detects (model.convergence (.quotient (N-A) (.nu X))) (s,t,t-j)
      (finiteTargetLabel model X (N-A) s t j y) b) :
    Detects (model.convergence (.quotient N (.nu X))) (s,t,t-(A+j))
      (finiteTargetLabel model X N s t (A+j) y)
      (finiteLambdaLayerClass X N A j hA hAN s t b) := by
  let L : ((SyntheticObject.shift (0,-(A:ℤ)) (.quotient (N-A) (.nu X))).obj
      model.nu model.auxiliary) ⟶
      ((SyntheticObject.quotient N (.nu X)).obj model.nu model.auxiliary) :=
    ((model.quotients.tower _).triangle hA hAN).lambdaMap
  have hsource : (s,t,t-j)=(s,(t-s)+s,t-j) := by simp
  have hb' := detects_transport hsource _ _ hb
  have hmap := shifted_map_detects (.quotient (N-A) (.nu X)) (.quotient N (.nu X))
    (0,-(A:ℤ)) (t-s,t-j) s L
    (regradeE2 hsource (finiteTargetLabel model X (N-A) s t j y)) b hb'
  have hindex : (s,((t-s,t-j)+(0,-(A:ℤ))).1+s,
      ((t-s,t-j)+(0,-(A:ℤ))).2)=(s,t,t-(A+j)) := by
    ext <;> dsimp <;> omega
  have hmap := detects_transport hindex _ _ hmap
  obtain ⟨e,he,ar,har,hgar⟩ := hmap
  obtain ⟨e0,he0,_⟩ := hb
  have heStem := representative_transport hsource _ _ he0
  have heMap := shifted_representative_map (.quotient (N-A) (.nu X)) (.quotient N (.nu X))
    (0,-(A:ℤ)) (t-s,t-j) s L _ _ heStem
  have heMap := representative_transport hindex _ _ heMap
  have heq := he.unique heMap
  have hJ : (s,t,t-j-A)=(s,t,t-(A+j)) := by ext <;> dsimp; omega
  let eLamRaw := KIP126.Literature.Standard.infinityFiniteLambda X N A hAN (s,t) (t-j) e0
  let eLam := (eqToHom (congrArg (fun q =>
    ((model.family.obj (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) N)).sequence.ssData q).eInfty)
      hJ)) eLamRaw
  have heq' : e=eLam := by
    convert heq using 1
    dsimp only [eLam,eLamRaw]
    simp only [KIP126.Literature.Standard.infinityFiniteLambda,
      InfinityShiftCoordinates.finiteLambdaMap,show A ≠ 0 by omega,↓reduceDIte,
      InfinityShiftCoordinates.shift,infinityShift,Iso.trans_hom,ModuleCat.comp_apply,
      eqToIso.hom,KIP126.Literature.Standard.infinityShiftData,
      KIP126.Literature.Standard.infinityShift_comparison]
    erw [infinity_map_regrade L hJ,infinity_map_regrade L hindex]
    simp only [←ModuleCat.comp_apply,Category.assoc,eqToHom_trans]
    rfl
  have hsourceLabel : nuWeightLabel model X s t (t-j) (by omega) y =
      targetNuLabel model X s t j y := by
    unfold nuWeightLabel
    have hk : (t-(t-j)).toNat=j := by omega
    have transport (k k' : ℕ) (h : k=k') (hp : (s,t,t-k)=(s,t,t-k')) :
        regradeE2 hp (targetNuLabel model X s t k y)=targetNuLabel model X s t k' y := by
      subst k'; rfl
    exact transport _ _ hk _
  have he0' : HasInfinityRepresentative _ 2 (s,t,t-j)
      (nuWeightLabel model X s t (t-j) (by omega) y |>
        familyPageMap model.family (XModLambdaN.incl _ (N-A)) 2 (s,t,t-j)) e0 := by
    rw [hsourceLabel]
    exact he0
  obtain ⟨hy,hyl⟩ := (KIP126.Literature.Standard.eInfinity_finite_labels X (N-A)
    (by omega) s t (t-j) (by omega) y e0).mp he0'
  have hraw : HasInfinityRepresentative _ 2 (s,t,t-j-A)
      (familyPageMap model.family (XModLambdaN.incl _ N) 2 (s,t,t-j-A)
        (nuWeightLabel model X s t (t-j-A) (by omega) y)) eLamRaw := by
    apply (KIP126.Literature.Standard.eInfinity_finite_labels X N (by omega)
      s t (t-j-A) (by omega) y eLamRaw).mpr
    refine ⟨by convert hy using 1; congr 1; omega,?_⟩
    dsimp only [eLamRaw]
    rw [KIP126.Literature.Standard.eInfinity_lambda_finite X N A hAN (s,t) (t-j)
      (by omega),hyl]
    rfl
  have hlabel := representative_transport hJ _ _ hraw
  have htargetLabel : regradeE2 hJ
      (familyPageMap model.family (XModLambdaN.incl _ N) 2 (s,t,t-j-A)
        (nuWeightLabel model X s t (t-j-A) (by omega) y)) =
      finiteTargetLabel model X N s t (A+j) y := by
    unfold nuWeightLabel
    rw [page_regrade]
    have hk : (t-(t-j-A)).toNat=A+j := by omega
    have labels (k k' : ℕ) (hk : k=k') (p : Tridegree)
        (h₁ : (s,t,t-k)=p) (h₂ : p=(s,t,t-k')) :
        regradeE2 h₂ (regradeE2 h₁ (targetNuLabel model X s t k y)) =
          targetNuLabel model X s t k' y := by
      subst k'
      subst p
      rfl
    exact congrArg (familyPageMap model.family (XModLambdaN.incl _ N) 2
      (s,t,t-(A+j))) (labels _ _ hk _ _ hJ)
  rw [htargetLabel] at hlabel
  have heFinal : HasInfinityRepresentative _ 2 (s,t,t-(A+j))
      (finiteTargetLabel model X N s t (A+j) y) e := by
    simpa only [heq',eLam,SyntheticObject.obj] using hlabel
  refine ⟨e,heFinal,ar,?_,hgar⟩
  convert har using 1
  simp only [finiteLambdaLayerClass,regrade_precomp,Category.assoc]
  simp only [←Category.assoc,eqToHom_trans]
  rfl


private theorem output_regrade_trans {U : SyntheticSpectrum} {m m' m'' w w' w'' : ℤ}
    (hm : m=m') (hw : w=w') (hm' : m'=m'') (hw' : w'=w'')
    (a : BiHom m w U) :
    homotopyRegrade hm' hw' (homotopyRegrade hm hw a) =
      homotopyRegrade (hm.trans hm') (hw.trans hw') a := by
  subst m'; subst m''; subst w'; subst w''; rfl

private theorem output_regrade_neg {U : SyntheticSpectrum} {m m' w w' : ℤ}
    (hm : m=m') (hw : w=w') (a : BiHom m w U) :
    homotopyRegrade hm hw (-a) = -homotopyRegrade hm hw a := by
  subst m'; subst w'; rfl

private def finiteLambdaSuspendedInputLabel (X : ClassicalObject)
    (D A j : ℕ) (s t : ℤ) (p : ℤ×ℤ)
    (hp : p.1=t-s+1) (hw : p.2=t-j-A) (y : Ambient model X (s,t)) :
    (model.family.obj ((SyntheticObject.shift (1,0)
      (.shift (0,-(A:ℤ)) (.quotient D (.nu X)))).obj model.nu model.auxiliary)).E₂
      (s,p.1+s,p.2) :=
  regradeE2 (by ext <;> dsimp <;> omega)
    (finiteConclusionShiftLabel (.shift (0,-(A:ℤ)) (.quotient D (.nu X))) (1,0)
      _
      (finiteConclusionShiftLabel (.quotient D (.nu X)) (0,-(A:ℤ)) (s,t,t-j)
        (finiteTargetLabel model X D s t j y)))

private def finiteLambdaSuspendedOutputLabel (X : ClassicalObject)
    (N A j : ℕ) (s t : ℤ) (p : ℤ×ℤ)
    (hp : p.1=t-s+1) (hw : p.2=t-j-A) (y : Ambient model X (s,t)) :
    (model.family.obj ((SyntheticObject.shift (1,0) (.quotient N (.nu X))).obj
      model.nu model.auxiliary)).E₂ (s,p.1+s,p.2) :=
  regradeE2 (by ext <;> dsimp <;> omega)
    (finiteConclusionShiftLabel (.quotient N (.nu X)) (1,0) (s,t,t-(A+j))
      (finiteTargetLabel model X N s t (A+j) y))

/-- The exact nested-shift input label detects the negative ordinary
suspension of the fixed finite lambda map at layer A+j. -/
private theorem finite_lambda_suspended_signed_detects (X : ClassicalObject)
    (N A j : ℕ) (hA : 0 < A) (hAN : A < N) (hj : j < N-A)
    (s t : ℤ) (p : ℤ×ℤ) (hp : p.1=t-s+1) (hw : p.2=t-j-A)
    (y : Ambient model X (s,t))
    (b : BiHom p.1 p.2
      ((((SyntheticCategory.biShift (0,-(A:ℤ))).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (N-A)))⟦(1:ℤ)⟧)))
    (hb : Detects (model.convergence (.shift (1,0)
        (.shift (0,-(A:ℤ)) (.quotient (N-A) (.nu X)))))
      (s,p.1+s,p.2) (finiteLambdaSuspendedInputLabel X (N-A) A j s t p hp hw y)
      (homotopyRegrade (by dsimp; omega) rfl
        (b≫(SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).inv.app _))) :
    Detects (model.convergence (.shift (1,0) (.quotient N (.nu X))))
      (s,p.1+s,p.2) (finiteLambdaSuspendedOutputLabel X N A j s t p hp hw y)
      (homotopyRegrade (by dsimp; omega) rfl
        ((-(b≫(shiftFunctor SyntheticSpectrum (1:ℤ)).map
          (((model.quotients.tower _).triangle hA hAN).lambdaMap)))≫
          (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).inv.app _)) := by
  let V : SyntheticObject := .quotient (N-A) (.nu X)
  let U : SyntheticObject := .shift (0,-(A:ℤ)) V
  let W : SyntheticObject := .quotient N (.nu X)
  let δ : ℤ×ℤ := (0,-(A:ℤ))
  let ε : ℤ×ℤ := (1,0)
  let p₀ : ℤ×ℤ := (t-s,t-j)
  let p₁ : ℤ×ℤ := p₀+δ
  let κ := SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1
  let L : U.obj model.nu model.auxiliary ⟶ W.obj model.nu model.auxiliary :=
    ((model.quotients.tower _).triangle hA hAN).lambdaMap
  have hP : p=p₁+ε := by ext <;> dsimp [p₁,p₀,δ,ε] <;> omega
  have hGrade : (s,p.1+s,p.2)=(s,(p₁+ε).1+s,(p₁+ε).2) := by rw [hP]
  have hSource : (s,t,t-j)=(s,p₀.1+s,p₀.2) := by dsimp [p₀]; simp
  have hMiddle : (s,t+(0:ℤ),t-j+(-(A:ℤ)))=(s,p₁.1+s,p₁.2) := by
    ext <;> dsimp [p₁,p₀,δ]; omega
  let y₀ := regradeE2 hSource (finiteTargetLabel model X (N-A) s t j y)
  let y₁ := ((essShift δ).page V 2 (by decide) p₀ s).hom y₀
  have hInput : regradeE2 hGrade
      (finiteLambdaSuspendedInputLabel X (N-A) A j s t p hp hw y) =
      ((essShift ε).page U 2 (by decide) p₁ s).hom y₁ := by
    unfold finiteLambdaSuspendedInputLabel
    rw [normalized_regrade_trans]
    rw [finite_conclusion_shift_label_to_page U ε p₁ s _ hMiddle]
    congr 1
    exact finite_conclusion_shift_label_to_page V δ p₀ s _ hSource _
  let bS := homotopyRegrade (congrArg Prod.fst hP) (congrArg Prod.snd hP)
    (b≫κ.inv.app (U.obj model.nu model.auxiliary))
  have hbS := detects_transport hGrade _ _ hb
  rw [hInput] at hbS
  obtain ⟨b₁,hb₁,hd₁⟩ := deshift_detected_representative U ε p₁ s y₁ bS
    (by simpa only [bS,regrade_precomp,←Category.assoc,eqToHom_trans,κ,U,V,ε,SyntheticObject.obj] using hbS)
  obtain ⟨b₀,hb₀,hd₀⟩ := deshift_detected_representative V δ p₀ s y₀ b₁ hd₁
  have hd₀' := detects_transport hSource.symm _ _ hd₀
  have hdNative : Detects (model.convergence V) (s,t,t-j)
      (finiteTargetLabel model X (N-A) s t j y) b₀ := by
    convert hd₀' using 1
    · simp only [y₀,normalized_regrade_trans]; rfl
    · simp only [p₀,regrade_precomp,←Category.assoc,eqToHom_trans,eqToHom_refl,Category.id_comp]
  have hd := finite_lambda_layer_detects X N A j hA hAN hj s t y b₀ hdNative
  have hTarget : (s,t,t-(A+j))=(s,p₁.1+s,p₁.2) := by
    ext <;> dsimp [p₁,p₀,δ] <;> omega
  let y₂ := regradeE2 hTarget (finiteTargetLabel model X N s t (A+j) y)
  have hd₂ : Detects (model.convergence W) (s,p₁.1+s,p₁.2) y₂
      (homotopyRegrade (by dsimp; omega) rfl (b₁≫L)) := by
    have H := detects_transport hTarget _ _ hd
    convert H using 1
    simp only [finiteLambdaLayerClass,regrade_comp,output_regrade_trans]
    rw [hb₀]
    rfl
  have hdS := detects_shift W ε p₁ s y₂ (b₁≫L) hd₂
  have heq : shiftHomotopyClass ε p₁ (b₁≫L) =
      homotopyRegrade (congrArg Prod.fst hP) (congrArg Prod.snd hP)
        (b≫(shiftFunctor SyntheticSpectrum (1:ℤ)).map L≫κ.inv.app _) := by
    rw [shift_class_comp,hb₁]
    simp only [bS,regrade_precomp,Category.assoc]
    rw [κ.inv.naturality L]
  rw [heq] at hdS
  have hdOut := detects_transport hGrade.symm _ _ hdS
  have hOutput : regradeE2 hGrade
      (finiteLambdaSuspendedOutputLabel X N A j s t p hp hw y) =
      ((essShift ε).page W 2 (by decide) p₁ s).hom y₂ := by
    unfold finiteLambdaSuspendedOutputLabel
    rw [normalized_regrade_trans]
    exact finite_conclusion_shift_label_to_page W ε p₁ s _ hTarget _
  have hdPositive : Detects (model.convergence (.shift (1,0) W)) (s,p.1+s,p.2)
      (finiteLambdaSuspendedOutputLabel X N A j s t p hp hw y)
      (homotopyRegrade (by dsimp; omega) rfl
        (b≫(shiftFunctor SyntheticSpectrum (1:ℤ)).map L≫κ.inv.app _)) := by
    convert hdOut using 1
    · rw [←hOutput,normalized_regrade_trans]; rfl
    · simp only [regrade_precomp,←Category.assoc,eqToHom_trans]
  have hn := detects_neg hdPositive
  have hnlabel : -(finiteLambdaSuspendedOutputLabel X N A j s t p hp hw y) =
      finiteLambdaSuspendedOutputLabel X N A j s t p hp hw y := by
    unfold finiteLambdaSuspendedOutputLabel finiteConclusionShiftLabel regradeE2
    rw [←map_neg,←map_neg,←map_neg,←map_neg,finite_target_neg]
  rw [hnlabel] at hn
  convert hn using 1
  rw [Preadditive.neg_comp,output_regrade_neg]
  simp only [L,κ,W,SyntheticObject.obj,Category.assoc]

/-- Move the entire detection function, including its actual source class,
through equality of the short quotient length. -/
private theorem finite_lambda_signed_transport_short_length
    (X : ClassicalObject) (N A j D E : ℕ) (hDE : D=E)
    (s t : ℤ) (p : ℤ×ℤ) (hp : p.1=t-s+1) (hw : p.2=t-j-A)
    (y : Ambient model X (s,t))
    (L : (SyntheticCategory.biShift (0,-(A:ℤ))).obj
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) D) ⟶
      XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) N)
    (H : ∀ (b : BiHom p.1 p.2
        ((((SyntheticCategory.biShift (0,-(A:ℤ))).obj
          (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) D))⟦(1:ℤ)⟧))),
      Detects (model.convergence (.shift (1,0) (.shift (0,-(A:ℤ)) (.quotient D (.nu X)))))
        (s,p.1+s,p.2) (finiteLambdaSuspendedInputLabel X D A j s t p hp hw y)
        (homotopyRegrade (by dsimp; omega) rfl
          (b≫(SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).inv.app _)) →
      Detects (model.convergence (.shift (1,0) (.quotient N (.nu X))))
        (s,p.1+s,p.2) (finiteLambdaSuspendedOutputLabel X N A j s t p hp hw y)
        (homotopyRegrade (by dsimp; omega) rfl
          ((-(b≫(shiftFunctor SyntheticSpectrum (1:ℤ)).map L))≫
            (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).inv.app _))) :
    let LE : (SyntheticCategory.biShift (0,-(A:ℤ))).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) E) ⟶
        XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) N :=
      Eq.mp (congrArg (fun d => (SyntheticCategory.biShift (0,-(A:ℤ))).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) d) ⟶
        XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) N) hDE) L
    ∀ (b : BiHom p.1 p.2
        ((((SyntheticCategory.biShift (0,-(A:ℤ))).obj
          (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) E))⟦(1:ℤ)⟧))),
      Detects (model.convergence (.shift (1,0) (.shift (0,-(A:ℤ)) (.quotient E (.nu X)))))
        (s,p.1+s,p.2) (finiteLambdaSuspendedInputLabel X E A j s t p hp hw y)
        (homotopyRegrade (by dsimp; omega) rfl
          (b≫(SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).inv.app _)) →
      Detects (model.convergence (.shift (1,0) (.quotient N (.nu X))))
        (s,p.1+s,p.2) (finiteLambdaSuspendedOutputLabel X N A j s t p hp hw y)
        (homotopyRegrade (by dsimp; omega) rfl
          ((-(b≫(shiftFunctor SyntheticSpectrum (1:ℤ)).map LE))≫
            (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).inv.app _)) := by
  subst E
  exact H

/-- The exact same detection theorem with the short quotient written B
and the lambda map transported in precisely the public statement's way. -/
private theorem finite_lambda_suspended_signed_detects_explicit_lengths
    (X : ClassicalObject) (A B j : ℕ) (hA : 0 < A) (hB : 0 < B) (hj : j < B)
    (s t : ℤ) (p : ℤ×ℤ) (hp : p.1=t-s+1) (hw : p.2=t-j-A)
    (y : Ambient model X (s,t)) :
    let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(A:ℤ))
    let LY := (model.quotients.tower (model.nu.functor.obj (X.obj model.auxiliary))).triangle
      hA (show A < A+B by omega)
    let lambdaY : F.obj (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) B) ⟶
        XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (A+B) := by
      simpa only [Nat.add_sub_cancel_left] using LY.lambdaMap
    ∀ (b : BiHom p.1 p.2
        ((F.obj (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) B))⟦(1:ℤ)⟧)),
      Detects (model.convergence (.shift (1,0) (.shift (0,-(A:ℤ)) (.quotient B (.nu X)))))
        (s,p.1+s,p.2) (finiteLambdaSuspendedInputLabel X B A j s t p hp hw y)
        (homotopyRegrade (by dsimp; omega) rfl
          (b≫(SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).inv.app _)) →
      Detects (model.convergence (.shift (1,0) (.quotient (A+B) (.nu X))))
        (s,p.1+s,p.2) (finiteLambdaSuspendedOutputLabel X (A+B) A j s t p hp hw y)
        (homotopyRegrade (by dsimp; omega) rfl
          ((-(b≫(shiftFunctor SyntheticSpectrum (1:ℤ)).map lambdaY))≫
            (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).inv.app _)) := by
  exact finite_lambda_signed_transport_short_length X (A+B) A j ((A+B)-A) B
    (Nat.add_sub_cancel_left A B) s t p hp hw y
    ((model.quotients.tower (model.nu.functor.obj (X.obj model.auxiliary))).triangle
      hA (show A < A+B by omega)).lambdaMap
    (finite_lambda_suspended_signed_detects X (A+B) A j hA (by omega) (by omega)
      s t p hp hw y)

end
end KIP126.ProofTools.Internal.Mahowald
