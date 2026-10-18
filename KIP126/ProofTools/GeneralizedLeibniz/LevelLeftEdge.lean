module
import all KIP126.ProofTools.GeneralizedLeibniz.LevelBoundary
import all KIP126.ProofTools.GeneralizedLeibniz.LevelSource
import all KIP126.ProofTools.GeneralizedLeibniz.LevelLanguage

/-! The actual left edge of the GL square at arbitrary retained lambda level. -/

@[expose] section
namespace KIP126.ProofTools.Internal.Leibniz
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Standard
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward false
set_option maxHeartbeats 800000
set_option Elab.async false

set_option backward.defeqAttrib.useBackward true

private theorem level_differential_absolute_boundary_labelled (X : ClassicalObject)
    (i k d : ℕ) (hdq : d < i) (hik : i-d ≤ k) (s t : ℤ)
    (x : Ambient model X (s,t)) (y : Ambient model X (s+k+1,t+k))
    (hd : HasDifferential (model.classical.obj (X.obj model.auxiliary))
      (k+1) (s,t) (s+k+1,t+k) x y)
    (hy : y ∈ permanentCycles model X (s+k+1,t+k)) :
    ∃ a : BiHom (t-s) (t-d) (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) i),
      Detects (model.convergence (.quotient i (.nu X))) (s,(t-s)+s,t-d)
        (regradeE2 (by simp) (finiteTargetLabel model X i s t d x))
        (homotopyRegrade (by dsimp; omega) rfl a) ∧
      Detects (model.convergence (.shift (1,-(i:ℤ)) (.nu X)))
        (s+k+1,(t-s)+(s+k+1),t-d)
        (regradeE2 (by ext <;> dsimp <;> omega)
          (((essShift (1,-(i:ℤ))).page (.nu X) 2 (by decide)
            ((t-s)-1,t-d+i) (s+k+1)).hom
              (regradeE2 (by ext <;> dsimp <;> omega)
                (nuWeightLabel model X (s+k+1) (t+k) (t-d+i) (by omega) y))))
        (homotopyRegrade (by dsimp; omega) rfl
          (a ≫ absoluteBoundary (model.nu.functor.obj (X.obj model.auxiliary)) i)) := by
  obtain ⟨a,ha,hδ⟩ := differential_absolute_boundary_level X i k d hdq hik s t x y hd hy
  refine ⟨a,?_,?_⟩
  · have hl : (model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) i).pageMap
          2 (s,t,t-d) (nuWeightLabel model X s t (t-d) (by omega) x) =
        finiteTargetLabel model X i s t d x := by
      unfold nuWeightLabel
      have transport (j : ℕ) (hj : j=d) (h : (s,t,t-j)=(s,t,t-d)) :
          familyPageMap model.family (XModLambdaN.incl _ i) 2 (s,t,t-d)
            (regradeE2 h (targetNuLabel model X s t j x)) =
          finiteTargetLabel model X i s t d x := by
        subst j
        rfl
      exact transport _ (by omega) _
    rw [hl] at ha
    have h := detects_transport (show (s,t,t-d)=(s,(t-s)+s,t-d) by simp) _ _ ha
    simpa only [regrade_precomp,←Category.assoc,eqToHom_trans] using h
  · let α := biSuspensionHomEquiv (t-s) (t-d) i
      (model.nu.functor.obj (X.obj model.auxiliary)) (a ≫ XModLambdaN.proj _ i)
    have hs : Detects (model.convergence (.nu X))
        (s+k+1,((t-s)-1)+(s+k+1),t-d+i)
        (regradeE2 (by ext <;> dsimp <;> omega)
          (nuWeightLabel model X (s+k+1) (t+k) (t-d+i) (by omega) y))
        (homotopyRegrade (by dsimp; omega) rfl α) := by
      have h := detects_transport
        (show (s+k+1,t+k,t-d+i)=(s+k+1,((t-s)-1)+(s+k+1),t-d+i) by
          ext <;> dsimp <;> omega) _ _ hδ
      simpa only [α,regrade_precomp,←Category.assoc,eqToHom_trans] using h
    have hb := detects_shift (.nu X) ((1:ℤ),-(i:ℤ)) ((t-s)-1,t-d+i) (s+k+1) _ α hs
    have hp : (s+k+1,(((t-s)-1,t-d+i)+((1:ℤ),-(i:ℤ))).1+(s+k+1),
          (((t-s)-1,t-d+i)+((1:ℤ),-(i:ℤ))).2)=(s+k+1,(t-s)+(s+k+1),t-d) := by
        ext <;> dsimp <;> omega
    have H := detects_transport hp _ _ hb
    rw [absolute_boundary_class_shift]
    simpa only [α,regrade_precomp,←Category.assoc,eqToHom_trans] using H

private def levelDifferentialBoundaryInfinity (X : ClassicalObject)
    (i k d : ℕ) (hdq : d < i) (hik : i-d ≤ k) (s t : ℤ)
    (z : ((model.family.nu model.nu (X.obj model.auxiliary)).sequence.ssData
      (s+k+1,((t-s)-1)+(s+k+1),t+k)).eInfty) :
    ((model.family.obj ((SyntheticObject.shift (1,-(i:ℤ)) (.nu X)).obj
      model.nu model.auxiliary)).sequence.ssData (s+k+1,(t-s)+(s+k+1),t-d)).eInfty :=
  (eqToHom (congrArg (fun p : ℤ×ℤ =>
    ((model.family.obj ((SyntheticObject.shift (1,-(i:ℤ)) (.nu X)).obj
      model.nu model.auxiliary)).sequence.ssData (s+k+1,p.1+(s+k+1),p.2)).eInfty)
      (show lambdaBoundaryPoint (k-(i-d)) i ((t-s)-1,t+k)=(t-s,t-d) by
        ext <;> dsimp [lambdaBoundaryPoint] <;> omega)))
    (lambdaBoundaryInfinity (.nu X) (k-(i-d)) i ((t-s)-1,t+k) (s+k+1) z)

set_option maxHeartbeats 200000 in
private theorem level_differential_boundary_infinity_representative (X : ClassicalObject)
    (i k d : ℕ) (hdq : d < i) (hik : i-d ≤ k) (s t : ℤ)
    (y : Ambient model X (s+k+1,t+k))
    (z : ((model.family.nu model.nu (X.obj model.auxiliary)).sequence.ssData
      (s+k+1,((t-s)-1)+(s+k+1),t+k)).eInfty)
    (hz : HasInfinityRepresentative _ 2 _
      (regradeE2 (by ext <;> dsimp <;> omega)
        (nuWeightLabel model X (s+k+1) (t+k) (t+k) (by omega) y)) z) :
    HasInfinityRepresentative _ 2 (s+k+1,(t-s)+(s+k+1),t-d)
      (regradeE2 (by ext <;> dsimp <;> omega)
        (((essShift (1,-(i:ℤ))).page (.nu X) 2 (by decide)
          ((t-s)-1,t-d+i) (s+k+1)).hom
            (regradeE2 (by ext <;> dsimp <;> omega)
              (nuWeightLabel model X (s+k+1) (t+k) (t-d+i) (by omega) y))))
      (levelDifferentialBoundaryInfinity X i k d hdq hik s t z) := by
  let p : ℤ×ℤ := ((t-s)-1,t+k)
  let p' : ℤ×ℤ := ((t-s)-1,t-d+i)
  have hp : p+((0:ℤ),-((k-(i-d):ℕ):ℤ))=p' := by ext <;> dsimp [p,p'] <;> omega
  let target : (model.family.nu model.nu (X.obj model.auxiliary)).E₂
      (s+k+1,p'.1+(s+k+1),p'.2) :=
    regradeE2 (by ext <;> dsimp [p']; omega)
      (nuWeightLabel model X (s+k+1) (t+k) (t-d+i) (by omega) y)
  let targetRaw : (model.family.nu model.nu (X.obj model.auxiliary)).E₂
      (s+k+1,(p+((0:ℤ),-((k-(i-d):ℕ):ℤ))).1+(s+k+1),
        (p+((0:ℤ),-((k-(i-d):ℕ):ℤ))).2) :=
    regradeE2 (congrArg (fun v : ℤ×ℤ => (s+k+1,v.1+(s+k+1),v.2)) hp.symm) target
  have htargetRaw : HEq targetRaw
      (nuWeightLabel model X (s+k+1) (t+k) (p.2-((k-(i-d):ℕ):ℤ)) (by dsimp [p]; omega) y) := by
    apply (regradeE2_heq _ target).trans
    apply (regradeE2_heq _ _).trans
    exact nuWeight_label_heq X _ _ _ _ _ _ rfl rfl (by dsimp [p]; omega) _ _ _ _ HEq.rfl
  have hraw := lambdaRawInfinity_nu_representative_regraded X (k-(i-d)) p (s+k+1) (t+k)
    (by dsimp [p]; omega) (by dsimp [p]; omega) y _ (regradeE2_heq _ _) z hz
    _ (by ext <;> dsimp [p] <;> omega) targetRaw htargetRaw
    (lambdaRawInfinity (.nu X) (k-(i-d)) p (s+k+1) z) HEq.rfl
  have hbound := ((essShift (1,-(i:ℤ))).representative_iff (.nu X) 2 (by decide)
    (p+((0:ℤ),-((k-(i-d):ℕ):ℤ))) (s+k+1) targetRaw
    (lambdaRawInfinity (.nu X) (k-(i-d)) p (s+k+1) z)).mp hraw
  have hpoint : (s+k+1,(lambdaBoundaryPoint (k-(i-d)) i p).1+(s+k+1),
      (lambdaBoundaryPoint (k-(i-d)) i p).2)=(s+k+1,(t-s)+(s+k+1),t-d) := by
    ext <;> dsimp [lambdaBoundaryPoint,p] <;> omega
  have hbound := representative_transport hpoint _ _ hbound
  have hshift (a b : ℤ×ℤ) (hab : a=b)
      (x : (model.family.nu model.nu (X.obj model.auxiliary)).E₂ (s+k+1,a.1+(s+k+1),a.2))
      (y : (model.family.nu model.nu (X.obj model.auxiliary)).E₂ (s+k+1,b.1+(s+k+1),b.2))
      (hxy : HEq x y) :
      HEq (((essShift (1,-(i:ℤ))).page (.nu X) 2 (by decide) a (s+k+1)).hom x)
        (((essShift (1,-(i:ℤ))).page (.nu X) 2 (by decide) b (s+k+1)).hom y) := by
    subst b
    cases hxy
    rfl
  let labelA := ((essShift (1,-(i:ℤ))).page (.nu X) 2 (by decide)
    (p+((0:ℤ),-((k-(i-d):ℕ):ℤ))) (s+k+1)).hom targetRaw
  let labelB := ((essShift (1,-(i:ℤ))).page (.nu X) 2 (by decide) p' (s+k+1)).hom target
  have hshiftxy := hshift (p+((0:ℤ),-((k-(i-d):ℕ):ℤ))) p' hp targetRaw target
    (regradeE2_heq _ target)
  have hlabel := (regradeE2_heq hpoint labelA).trans hshiftxy
  have hcan : (s+k+1,(p'+((1:ℤ),-(i:ℤ))).1+(s+k+1),
      (p'+((1:ℤ),-(i:ℤ))).2)=(s+k+1,(t-s)+(s+k+1),t-d) := by
    ext <;> dsimp [p'] <;> omega
  let finalLabel : (model.family.obj ((SyntheticObject.shift (1,-(i:ℤ)) (.nu X)).obj
      model.nu model.auxiliary)).E₂ (s+k+1,(t-s)+(s+k+1),t-d) :=
    regradeE2 hcan labelB
  have hfinal : HEq finalLabel labelB := regradeE2_heq hcan labelB
  have hlabel' := hlabel.trans hfinal.symm
  have hlabelEq := eq_of_heq hlabel'
  rw [hlabelEq] at hbound
  exact hbound

private theorem level_differential_absolute_boundary_extension (X : ClassicalObject)
    (i k d : ℕ) (hdq : d < i) (hik : i-d ≤ k) (s t : ℤ)
    (x : Ambient model X (s,t)) (y : Ambient model X (s+k+1,t+k))
    (hd : HasDifferential (model.classical.obj (X.obj model.auxiliary))
      (k+1) (s,t) (s+k+1,t+k) x y)
    (hy : y ∈ permanentCycles model X (s+k+1,t+k))
    (zF : ((model.family.obj ((SyntheticObject.quotient i (.nu X)).obj
      model.nu model.auxiliary)).sequence.ssData (s,(t-s)+s,t-d)).eInfty)
    (hzF : HasInfinityRepresentative _ 2 _
      (regradeE2 (show (s,t,t-d)=(s,(t-s)+s,t-d) by simp)
        (finiteTargetLabel model X i s t d x)) zF)
    (zI : ((model.family.nu model.nu (X.obj model.auxiliary)).sequence.ssData
      (s+k+1,((t-s)-1)+(s+k+1),t+k)).eInfty)
    (hzI : HasInfinityRepresentative _ 2 _
      (regradeE2 (by ext <;> dsimp <;> omega)
        (nuWeightLabel model X (s+k+1) (t+k) (t+k) (by omega) y)) zI) :
    TowerExtensionEquation
      (model.convergentMap (.quotient i (.nu X)) (.shift (1,-(i:ℤ)) (.nu X))
        (absoluteBoundary (model.nu.functor.obj (X.obj model.auxiliary)) i))
      (t-s,t-d) s (k+1) zF
      ((eqToHom (congrArg (fun p =>
        ((model.family.obj ((SyntheticObject.shift (1,-(i:ℤ)) (.nu X)).obj
          model.nu model.auxiliary)).sequence.ssData p).eInfty)
          (show (s+k+1,(t-s)+(s+k+1),t-d)=(s+(k+1),(t-s)+(s+(k+1)),t-d) by
            ext <;> dsimp <;> omega)))
        (levelDifferentialBoundaryInfinity X i k d hdq hik s t zI)) := by
  obtain ⟨a,ha,hδ⟩ := level_differential_absolute_boundary_labelled X i k d hdq hik s t x y hd hy
  have hp : (s+k+1,(t-s)+(s+k+1),t-d)=(s+(k+1),(t-s)+(s+(k+1)),t-d) := by
    ext <;> dsimp <;> omega
  have hδ' := detects_transport hp _ _ hδ
  have htarget := representative_transport hp _ _
    (level_differential_boundary_infinity_representative X i k d hdq hik s t y zI hzI)
  obtain ⟨z₀,z₁,hz₀,hz₁,heq⟩ := extension_equation_of_detected_pair
    (model.convergentMap (.quotient i (.nu X)) (.shift (1,-(i:ℤ)) (.nu X))
      (absoluteBoundary (model.nu.functor.obj (X.obj model.auxiliary)) i))
      (t-s,t-d) s (k+1) (by omega) _ _ a
      (a ≫ absoluteBoundary (model.nu.functor.obj (X.obj model.auxiliary)) i) ha
      (by simpa only [regrade_precomp,←Category.assoc,eqToHom_trans] using hδ') rfl
  rw [hz₀.unique hzF,hz₁.unique htarget] at heq
  exact heq


private def normalizedLevelDifferentialBoundaryInfinity (X : ClassicalObject)
    (e : ℤ) (i k d : ℕ) (hdq : d < i) (hik : i-d ≤ k) (s t : ℤ)
    (z : ((model.family.obj ((SyntheticObject.shift ((0:ℤ),e) (.nu X)).obj
      model.nu model.auxiliary)).sequence.ssData
        (s+k+1,(((t+k)-(s+k+1),t+k)+((0:ℤ),e)).1+(s+k+1),
          (((t+k)-(s+k+1),t+k)+((0:ℤ),e)).2)).eInfty) :
    ((model.family.obj ((SyntheticObject.shift (1,-(i:ℤ))
      (.shift ((0:ℤ),e) (.nu X))).obj model.nu model.auxiliary)).sequence.ssData
        (s+(k+1),(t-s)+(s+(k+1)),t+e-d)).eInfty :=
  (eqToHom (congrArg (fun j =>
    ((model.family.obj ((SyntheticObject.shift (1,-(i:ℤ))
      (.shift ((0:ℤ),e) (.nu X))).obj model.nu model.auxiliary)).sequence.ssData j).eInfty)
      (show (s+k+1,
          (lambdaBoundaryPoint (k-(i-d)) i (((t+k)-(s+k+1),t+k)+((0:ℤ),e))).1+(s+k+1),
          (lambdaBoundaryPoint (k-(i-d)) i (((t+k)-(s+k+1),t+k)+((0:ℤ),e))).2)=
          (s+(k+1),(t-s)+(s+(k+1)),t+e-d) by
        ext <;> dsimp [lambdaBoundaryPoint] <;> omega)))
    (lambdaBoundaryInfinity (.shift ((0:ℤ),e) (.nu X)) (k-(i-d)) i
      (((t+k)-(s+k+1),t+k)+((0:ℤ),e)) (s+k+1) z)

set_option maxHeartbeats 200000 in
private theorem level_differential_absolute_boundary_normalized_extension
    (X : ClassicalObject) (e : ℤ) (he : e=0 ∨ e=1)
    (i k d : ℕ) (hdq : d < i) (hik : i-d ≤ k) (s t : ℤ)
    (x : Ambient model X (s,t)) (y : Ambient model X (s+k+1,t+k))
    (hd : HasDifferential (model.classical.obj (X.obj model.auxiliary))
      (k+1) (s,t) (s+k+1,t+k) x y)
    (hy : y ∈ permanentCycles model X (s+k+1,t+k))
    (zFN : ((model.family.obj ((SyntheticObject.quotient i (.shift ((0:ℤ),e) (.nu X))).obj
      model.nu model.auxiliary)).sequence.ssData
        (s,(t-s)+s,t+e-d)).eInfty)
    (hzFN : HasInfinityRepresentative _ 2 _
      (levelFiniteSourceLabel X i e s t d x) zFN)
    (zIN : ((model.family.obj ((SyntheticObject.shift ((0:ℤ),e) (.nu X)).obj
      model.nu model.auxiliary)).sequence.ssData
        (s+k+1,(((t+k)-(s+k+1),t+k)+((0:ℤ),e)).1+(s+k+1),
          (((t+k)-(s+k+1),t+k)+((0:ℤ),e)).2)).eInfty)
    (hzIN : HasInfinityRepresentative _ 2 _
      (regradeE2 (by ext <;> simp) (model.comparison.nuE2 X e (s+k+1) (t+k) 0 y)) zIN) :
    TowerExtensionEquation
      (model.convergentMap (.quotient i (.shift ((0:ℤ),e) (.nu X)))
        (.shift (1,-(i:ℤ)) (.shift ((0:ℤ),e) (.nu X)))
        (absoluteBoundary ((SyntheticCategory.biShift ((0:ℤ),e)).obj
          (model.nu.functor.obj (X.obj model.auxiliary))) i))
      (t-s,t+e-d) s (k+1) zFN
      (normalizedLevelDifferentialBoundaryInfinity X e i k d hdq hik s t zIN) := by
  let A := model.nu.functor.obj (X.obj model.auxiliary)
  let E : ℤ×ℤ := (0,e)
  let D : ℤ×ℤ := (1,-(i:ℤ))
  let p : ℤ×ℤ := (t-s,t-d)
  let pI : ℤ×ℤ := ((t+k)-(s+k+1),t+k)
  obtain ⟨a,ha,_⟩ := level_differential_absolute_boundary_labelled X i k d hdq hik s t x y hd hy
  have ha := detects_transport (show (s,(t-s)+s,t-d)=(s,t,t-d) by simp) _ _ ha
  obtain ⟨zF,hzF,_⟩ := ha
  have hzF : HasInfinityRepresentative _ 2 (s,t,t-d)
      (finiteTargetLabel model X i s t d x) zF := by
    exact representative_heq_transport _ _ _ rfl _ _ _ _
      ((regradeE2_heq _ _).trans (regradeE2_heq _ _)) HEq.rfl hzF
  have hpF : (s,t,t-d)=(s,p.1+s,p.2) := by simp [p]
  let zFs := (eqToHom (congrArg (fun j =>
    ((model.family.obj (XModLambdaN A i)).sequence.ssData j).eInfty) hpF)) zF
  have hzFs := representative_transport hpF _ _ hzF
  let zI := (KIP126.Literature.Standard.infinityNuWindow X (s+k+1,t+k) (t+k) (by omega)).symm
    (subquotientClass (permanentCycles model X (s+k+1,t+k))
      (boundaries model X (1+(t+k)-(t+k)) (s+k+1,t+k)) ⟨y,hy⟩)
  have hzI : HasInfinityRepresentative _ 2 (s+k+1,t+k,t+k)
      (nuWeightLabel model X (s+k+1) (t+k) (t+k) (by omega) y) zI := by
    apply (KIP126.Literature.Standard.eInfinity_nu_labels X (s+k+1) (t+k) (t+k)
      (by omega) y zI).mpr
    exact ⟨hy,(KIP126.Literature.Standard.infinityNuWindow X (s+k+1,t+k) (t+k)
      (by omega)).apply_symm_apply _⟩
  have hpI : (s+k+1,t+k,t+k)=(s+k+1,pI.1+(s+k+1),pI.2) := by simp [pI]
  let zIs := (eqToHom (congrArg (fun j =>
    ((model.family.nu model.nu (X.obj model.auxiliary)).sequence.ssData j).eInfty) hpI)) zI
  have hzIs := representative_transport hpI _ _ hzI
  have hpI' : (s+k+1,t+k,t+k)=(s+k+1,((t-s)-1)+(s+k+1),t+k) := by
    ext <;> dsimp <;> omega
  let zIs' := (eqToHom (congrArg (fun j =>
    ((model.family.nu model.nu (X.obj model.auxiliary)).sequence.ssData j).eInfty) hpI')) zI
  have hzIs' := representative_transport hpI' _ _ hzI
  have hpB : (s+k+1,(t-s)+(s+k+1),t-d)=(s+(k+1),p.1+(s+(k+1)),p.2) := by
    ext <;> dsimp [p] <;> omega
  let zB := (eqToHom (congrArg (fun j =>
    ((model.family.obj ((SyntheticObject.shift D (.nu X)).obj
      model.nu model.auxiliary)).sequence.ssData j).eInfty) hpB))
        (levelDifferentialBoundaryInfinity X i k d hdq hik s t zIs')
  have hbase := level_differential_absolute_boundary_extension X i k d hdq hik s t x y hd hy
    zFs hzFs zIs' hzIs'
  have hshift := ((essShift E).towerExtensionEquation_iff
    (.quotient i (.nu X)) (.shift D (.nu X)) (absoluteBoundary A i)
    p s (k+1) _ _).mp hbase
  let Q := levelQuotientShiftIso X e i
  have hδ := level_quotient_shift_boundary X e i
  let N := (boundaryShiftNatIso e i).hom.app A
  have hsquare : (SyntheticCategory.biShift E).map (absoluteBoundary A i) ≫ N =
      Q.inv ≫ absoluteBoundary ((SyntheticCategory.biShift E).obj A) i := by
    have hδ' : Q.hom ≫ ((SyntheticCategory.biShift E).map (absoluteBoundary A i) ≫ N) =
        absoluteBoundary ((SyntheticCategory.biShift E).obj A) i := by
      exact hδ
    exact (Iso.inv_hom_id_assoc Q _).symm.trans (congrArg (fun z => Q.inv ≫ z) hδ')
  have hmap := tower_extension_map
    (model.convergentMap (.shift E (.quotient i (.nu X))) (.shift E (.shift D (.nu X)))
      ((SyntheticCategory.biShift E).map (absoluteBoundary A i)))
    (model.convergentMap (.quotient i (.shift E (.nu X))) (.shift D (.shift E (.nu X)))
      (absoluteBoundary ((SyntheticCategory.biShift E).obj A) i))
    (model.convergentMap (.shift E (.quotient i (.nu X))) (.quotient i (.shift E (.nu X))) Q.inv)
    (model.convergentMap (.shift E (.shift D (.nu X))) (.shift D (.shift E (.nu X))) N)
    hsquare (p+E) s (k+1) _ _ hshift
  have hsourceEq := level_finite_source_infinity_eq X i e s t d x zF hzF zFN hzFN
  have hsourceRaw : HEq
      ((model.family.map Q.inv).eInftyMap (s,(p+E).1+s,(p+E).2)
        ((towerInfinityIso (model.convergence (.quotient i (.nu X)))
          (model.convergence (.shift E (.quotient i (.nu X))))
          ((essShift E).filtered (.quotient i (.nu X)) p) s).hom zFs))
      (levelFiniteSourceInfinity X i e s t d zF) := by
    unfold levelFiniteSourceInfinity
    apply left_infinity_map_heq Q.inv _ _ (by ext <;> dsimp [p,E] <;> omega)
    exact (eqToHom_apply_heq _ _).symm
  have hsource := hsourceRaw.trans (heq_of_eq hsourceEq)
  have hsourceI := normalized_source_infinity_shift X e (s+k+1) (t+k) he y zI hzI zIN hzIN
  have hpointI : (s+k+1,t+k)=(s+k+1,pI.1+(s+k+1)) := by simp [pI]
  let yI : Ambient model X (s+k+1,pI.1+(s+k+1)) :=
    (eqToHom (congrArg (fun j => Ambient model X j) hpointI)) y
  have hyy : HEq y yI := (eqToHom_apply_heq _ y).symm
  have hwI : pI.2 ≤ pI.1+(s+k+1) := by dsimp [pI]; omega
  let labelI := nuWeightLabel model X (s+k+1) (pI.1+(s+k+1)) pI.2 hwI yI
  have hlabelI : HEq (nuWeightLabel model X (s+k+1) (t+k) (t+k) (by omega) y) labelI :=
    nuWeight_label_heq X _ _ _ _ _ _ rfl (by simp [pI]) rfl _ _ _ _ hyy
  have hzRaw : HasInfinityRepresentative (model.family.nu model.nu (X.obj model.auxiliary))
      2 (s+k+1,pI.1+(s+k+1),pI.2) labelI zIs := by
    exact representative_heq_transport _ _ _ rfl _ _ _ _
      ((regradeE2_heq hpI _).trans hlabelI) HEq.rfl hzIs
  have hraw := lambdaBoundaryInfinity_vertical_comm_nu X e (k-(i-d)) i pI (s+k+1)
    hwI yI zIs hzRaw
  have hbaseTarget : HEq zB (lambdaBoundaryInfinity (.nu X) (k-(i-d)) i pI (s+k+1) zIs) := by
    apply (eqToHom_apply_heq _ _).trans
    apply (eqToHom_apply_heq _ _).trans
    apply left_lambdaBoundaryInfinity_heq (.nu X) (k-(i-d)) (k-(i-d)) i i
      ((t-s)-1,t+k) pI (s+k+1) (s+k+1) rfl rfl (by ext <;> dsimp [pI] <;> omega) rfl
    exact (eqToHom_apply_heq _ zI).trans (eqToHom_apply_heq _ zI).symm
  have htargetShift := left_infinity_shift_heq (.shift D (.nu X)) E p
    (lambdaBoundaryPoint (k-(i-d)) i pI) (s+(k+1)) (s+k+1)
    (by ext <;> dsimp [p,pI,lambdaBoundaryPoint] <;> omega) (by omega)
    _ _ hbaseTarget
  have htargetMap := left_infinity_map_heq N _ _
    (by ext <;> dsimp [p,pI,E,lambdaBoundaryPoint] <;> omega) _ _ htargetShift
  have htargetRaw := htargetMap.trans hraw
  have htargetNorm := left_lambdaBoundaryInfinity_heq (.shift E (.nu X))
    (k-(i-d)) (k-(i-d)) i i (pI+E) (pI+E) (s+k+1) (s+k+1)
    rfl rfl rfl rfl _ _ (heq_of_eq hsourceI)
  have hcast : HEq (normalizedLevelDifferentialBoundaryInfinity X e i k d hdq hik s t zIN)
      (lambdaBoundaryInfinity (.shift E (.nu X)) (k-(i-d)) i (pI+E) (s+k+1) zIN) :=
    eqToHom_apply_heq _ _
  have htarget := (htargetRaw.trans htargetNorm).trans hcast.symm
  exact left_extension_heq (.quotient i (.shift E (.nu X)))
    (.shift D (.shift E (.nu X)))
    (absoluteBoundary ((SyntheticCategory.biShift E).obj A) i)
    (p+E) (t-s,t+e-d) (by ext <;> dsimp [p,E] <;> omega) s (k+1)
    _ zFN _ _ hsource htarget hmap

set_option maxHeartbeats 200000 in
/-- The actual left edge of the GL square for the two specified extension
witnesses. No crossing assumption is needed for this edge. -/
private theorem level_gl_left_edge (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (page level : ℕ) (r m l s t : ℤ) (hpage : 2 ≤ page) (hpr : (page:ℤ) ≤ r)
    {x : Ambient model X (s,t)} {y : Ambient model Y (s+m,t+m)}
    {xInfinity : Ambient model X (s+r,t+r-1)}
    {yInfinity : Ambient model Y (s+r+l,t+r-1+l)}
    (hd : HasDifferential (model.classical.obj (X.obj model.auxiliary))
      r (s,t) (s+r,t+r-1) x xInfinity)
    (hxInfinity : xInfinity ∈ permanentCycles model X (s+r,t+r-1))
    (WFinite : LevelFiniteExtensionWitness X Y f page level m s t x y)
    (WInfinity : InfiniteExtensionWitness model X Y f l (s+r) (t+r-1) xInfinity yInfinity) :
    TowerExtensionEquation
      (model.convergentMap (.quotient (page+level-1) (extensionSourceObject model X Y f))
        (.shift (1,-((page+level-1:ℕ):ℤ)) (extensionSourceObject model X Y f))
        (absoluteBoundary ((extensionSourceObject model X Y f).obj model.nu model.auxiliary) (page+level-1)))
      (t-s,t+normalizedExponent model.classicalTower f-level) s r WFinite.source
      (levelGLBottomSource X Y f page level r l s t hpage hpr WInfinity) := by
  obtain ⟨k,hkr⟩ : ∃ k : ℕ, r=(k:ℤ)+1 := by
    refine ⟨(r-1).toNat,?_⟩
    rw [Int.toNat_of_nonneg (by omega)]
    omega
  subst r
  let e : ℤ := normalizedExponent model.classicalTower f
  let E : ℤ×ℤ := (0,e)
  let p : ℤ×ℤ := (t-s,t-level)
  let pI : ℤ×ℤ := ((t+k)-(s+k+1),t+k)
  have he : e=0 ∨ e=1 := by
    have h := normalizedExponent_le_one model.classicalTower f
    dsimp [e]
    omega
  have hi : level < page+level-1 := by omega
  have hik : (page+level-1)-level ≤ k := by omega
  have hindex : (s+((k:ℤ)+1),t+((k:ℤ)+1)-1)=(s+k+1,t+k) := by
    ext <;> omega
  let xI : Ambient model X (s+k+1,t+k) :=
    (eqToHom (congrArg (fun v => Ambient model X v) hindex)) xInfinity
  have transport {a b : Bidegree} (hab : a=b) (z : Ambient model X a)
      (hz : z ∈ permanentCycles model X a)
      (hdz : HasDifferential (model.classical.obj (X.obj model.auxiliary)) (k+1) (s,t) a x z) :
      ((eqToHom (congrArg (fun v => Ambient model X v) hab)) z) ∈ permanentCycles model X b ∧
      HasDifferential (model.classical.obj (X.obj model.auxiliary)) (k+1) (s,t) b x
        ((eqToHom (congrArg (fun v => Ambient model X v) hab)) z) := by
    subst b
    exact ⟨hz,hdz⟩
  obtain ⟨hxI,hdI⟩ := transport hindex xInfinity hxInfinity hd
  have hI : (s+((k:ℤ)+1),((t+((k:ℤ)+1)-1)-(s+((k:ℤ)+1)))+(s+((k:ℤ)+1)),
      t+((k:ℤ)+1)-1+e)=(s+k+1,(pI+E).1+(s+k+1),(pI+E).2) := by
    ext <;> dsimp [pI,E] <;> omega
  let zIN := (eqToHom (congrArg (fun j =>
    ((model.family.obj ((SyntheticObject.shift E (.nu X)).obj model.nu model.auxiliary)).sequence.ssData j).eInfty)
      hI)) WInfinity.source
  have hzIN : HasInfinityRepresentative _ 2 _
      (regradeE2 (by ext <;> dsimp [pI,E] <;> omega)
        (model.comparison.nuE2 X e (s+k+1) (t+k) 0 xI)) zIN := by
    have h := representative_transport hI _ _ WInfinity.source_rep
    dsimp only [infiniteSourceForExtension] at h
    apply representative_heq_transport _ _ _ rfl _ _ _ _ _ HEq.rfl h
    apply (regradeE2_heq _ _).trans
    apply (regradeE2_heq _ _).trans
    apply HEq.trans _ (regradeE2_heq _ _).symm
    exact left_nuE2_heq X e _ _ _ _ (by omega) (by omega) xInfinity xI
      (eqToHom_apply_heq _ xInfinity).symm
  have hgen := level_differential_absolute_boundary_normalized_extension X e he
    (page+level-1) k level hi hik s t x xI hdI hxI WFinite.source WFinite.source_rep zIN hzIN
  have htarget : HEq (normalizedLevelDifferentialBoundaryInfinity X e (page+level-1) k level hi hik s t zIN)
      (levelGLBottomSource X Y f page level ((k:ℤ)+1) l s t hpage hpr WInfinity) := by
    apply (eqToHom_apply_heq _ _).trans
    apply HEq.trans _ (eqToHom_apply_heq _ _).symm
    apply left_lambdaBoundaryInfinity_heq (.shift E (.nu X))
      (k-((page+level-1)-level)) (((k:ℤ)+1-page).toNat) (page+level-1) (page+level-1)
      (pI+E) (((t+((k:ℤ)+1)-1)-(s+((k:ℤ)+1))),t+((k:ℤ)+1)-1+e)
      (s+k+1) (s+((k:ℤ)+1))
      (by omega) rfl (by ext <;> dsimp [pI,E] <;> omega) (by omega)
    exact eqToHom_apply_heq _ WInfinity.source
  exact left_extension_heq (.quotient (page+level-1) (.shift E (.nu X)))
    (.shift (1,-((page+level-1:ℕ):ℤ)) (.shift E (.nu X)))
    (absoluteBoundary ((SyntheticObject.shift E (.nu X)).obj model.nu model.auxiliary) (page+level-1))
    (t-s,t+e-level) (t-s,t+e-level) rfl s (k+1)
    WFinite.source WFinite.source _ _ HEq.rfl htarget hgen

end
end KIP126.ProofTools.Internal.Leibniz
