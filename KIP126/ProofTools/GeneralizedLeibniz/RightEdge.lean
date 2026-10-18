module
import all KIP126.ProofTools.GeneralizedLeibniz.Reverse
import all KIP126.ProofTools.StretchingRepresentatives
import all KIP126.ProofTools.DetectionOperations
import all KIP126.ProofTools.FiniteFiltration

/-! AimPaper, the last step of the Generalized Leibniz Rule: the actual
right-edge representative with high absolute boundary lifts through rho.
The finite E-infinity window reflects filtration and shows that the original
classical label is a later cycle, even when its weight is below its degree.
No division by lambda or exact first-label choice is required. -/

@[expose] section
namespace KIP126.ProofTools.Internal.Leibniz
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Standard
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2400000

private theorem rho_lift_detects (X : ClassicalObject)
    (i j : ℕ) (hi : 0 < i) (hij : i ≤ j) (s t w : ℤ)
    (hw : 0 ≤ t-w ∧ t-w < i) (y : Ambient model X (s,t))
    (a : BiHom (t-s) w (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) i))
    (ha : Detects (model.convergence (.quotient i (.nu X))) (s,t,w)
      ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) i).pageMap 2 (s,t,w)
        (nuWeightLabel model X s t w (by omega) y)) a)
    (b : BiHom (t-s) w (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) j))
    (hb : b ≫ (model.quotients.tower _).rho i j hij = a) :
    Detects (model.convergence (.quotient j (.nu X))) (s,t,w)
      ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) j).pageMap 2 (s,t,w)
        (nuWeightLabel model X s t w (by omega) y)) b := by
  let A := model.nu.functor.obj (X.obj model.auxiliary)
  let ρ := (model.quotients.tower A).rho i j hij
  let p : ℤ × ℤ := (t-s,w)
  have haf : FiltrationAtLeast model.syntheticTower s a :=
    detects_filtration (.quotient i (.nu X)) (s,t,w) _ a ha
  have hbf : FiltrationAtLeast model.syntheticTower s b := by
    have hb0 := filtration_at_zero model.syntheticTower _ (t-s) w b
    by_cases hs : s ≤ 0
    · exact model.syntheticTower.filtrationSubmodule_antitone _ p hs hb0
    · let L : ℤ → AddSubgroup (BiHom (t-s) w (XModLambdaN A j)) :=
        fun k => (model.syntheticTower.filtrationSubmodule (XModLambdaN A j) k p).toAddSubgroup
      let E : ℤ → AddSubgroup (BiHom (t-s) w (XModLambdaN A i)) :=
        fun k => (model.syntheticTower.filtrationSubmodule (XModLambdaN A i) k p).toAddSubgroup
      have hsN : (0:ℤ) + (s.toNat:ℤ) = s := by omega
      have hρb : (syntheticHomotopyMap ρ p).hom.toAddMonoidHom b ∈ E (0+s.toNat) := by
        change b ≫ ρ ∈ E (0+s.toNat)
        rw [hsN,hb]
        exact haf
      have hh := finite_filtration_reflection (syntheticHomotopyMap ρ p).hom.toAddMonoidHom L E
        (fun k l hkl z hz => model.syntheticTower.filtrationSubmodule_antitone _ p hkl hz)
        0 s.toNat (fun k hk hks z hz hρz =>
          next_filtration_of_infinity_injective
            (model.convergentMap (.quotient j (.nu X)) (.quotient i (.nu X)) ρ)
            p k (rho_infty_injective X i j hi hij k (p.1+k) p.2 (by dsimp [p]; omega))
            z hz hρz) b hb0 hρb
      rw [hsN] at hh
      exact hh
  obtain ⟨e,he,a',ha',hga⟩ := ha
  obtain ⟨b',hb'⟩ := filtration_representative_exists model.syntheticTower
    (XModLambdaN A j) p s b hbf
  let e' := ((model.convergence (.quotient j (.nu X))).identification (s,t,w)).inv
    ((model.syntheticTower.filtration (XModLambdaN A j)).toAssociatedGraded s p b')
  have hg := grade_natural (.quotient j (.nu X)) (.quotient i (.nu X)) ρ (s,t,w) b' a'
    (by exact (congrArg (fun z => z ≫ ρ) hb').trans (hb.trans ha'.symm))
  have heq : (model.family.map ρ).eInftyMap (s,t,w) e' = e := by
    have hiGrade : ((model.convergence (.quotient i (.nu X))).identification (s,t,w)).inv
        ((model.syntheticTower.filtration (XModLambdaN A i)).toAssociatedGraded s p a') = e := by
      exact (congrArg ((model.convergence (.quotient i (.nu X))).identification (s,t,w)).inv hga.symm).trans
        (((model.convergence (.quotient i (.nu X))).identification (s,t,w)).toLinearEquiv.symm_apply_apply e)
    exact hg.symm.trans hiGrade
  obtain ⟨hy,hycl⟩ := (KIP126.Literature.Standard.eInfinity_finite_labels X i hi s t w hw y e).mp he
  obtain ⟨z,hz⟩ := CrossingLabels.subquotient_rep
    (cycles model X (j-t+w) (s,t)) (boundaries model X (1+t-w) (s,t))
    (KIP126.Literature.Standard.infinityFiniteWindow X j (by omega) (s,t) w (by constructor <;> omega) e')
  have hr := KIP126.Literature.Standard.eInfinity_rho_finite X i j hi hij (s,t) w hw e'
  rw [heq,hycl,←hz] at hr
  have hzold : z.val ∈ cycles model X (i-t+w) (s,t) :=
    cycles_antitone model X (s,t) (by omega : (i:ℤ)-t+w ≤ (j:ℤ)-t+w) z.property
  have hclass : subquotientClass (cycles model X (i-t+w) (s,t))
      (boundaries model X (1+t-w) (s,t)) ⟨y,hy⟩ =
    subquotientClass (cycles model X (i-t+w) (s,t))
      (boundaries model X (1+t-w) (s,t)) ⟨z.val,hzold⟩ := hr
  have hzero : subquotientClass (cycles model X (i-t+w) (s,t))
      (boundaries model X (1+t-w) (s,t)) (⟨y,hy⟩-⟨z.val,hzold⟩) = 0 := by
    rw [map_sub,hclass,sub_self]
  have hboundary : y-z.val ∈ boundaries model X (1+t-w) (s,t) :=
    (CrossingLabels.subquotient_zero_iff _ _ _).mp hzero
  have hdiff := boundaries_le_cycles model X (s,t) (1+t-w) (j-t+w) hboundary
  have hylater : y ∈ cycles model X (j-t+w) (s,t) := by
    simpa only [sub_add_cancel] using
      (cycles model X (j-t+w) (s,t)).add_mem hdiff z.property
  have hyz : subquotientClass (cycles model X (j-t+w) (s,t))
      (boundaries model X (1+t-w) (s,t)) ⟨y,hylater⟩ =
      subquotientClass (cycles model X (j-t+w) (s,t))
        (boundaries model X (1+t-w) (s,t)) z := by
    apply sub_eq_zero.mp
    rw [←map_sub]
    exact (CrossingLabels.subquotient_zero_iff _ _ _).mpr hboundary
  have he' : HasInfinityRepresentative _ 2 (s,t,w)
      ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) j).pageMap 2 (s,t,w)
        (nuWeightLabel model X s t w (by omega) y)) e' := by
    apply (KIP126.Literature.Standard.eInfinity_finite_labels X j (by omega) s t w
      (by constructor <;> omega) y e').mpr
    exact ⟨hylater,hz.symm.trans hyz.symm⟩
  refine ⟨e',he',b',hb',?_⟩
  exact ((model.convergence (.quotient j (.nu X))).identification (s,t,w)).toLinearEquiv.apply_symm_apply _


private theorem rho_lift_detected_cycles (X : ClassicalObject)
    (i j : ℕ) (hi : 0 < i) (hij : i ≤ j) (s t w : ℤ)
    (hw : 0 ≤ t-w ∧ t-w < i) (y : Ambient model X (s,t))
    (a : BiHom (t-s) w (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) i))
    (ha : Detects (model.convergence (.quotient i (.nu X))) (s,t,w)
      ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) i).pageMap 2 (s,t,w)
        (nuWeightLabel model X s t w (by omega) y)) a)
    (b : BiHom (t-s) w (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) j))
    (hb : b ≫ (model.quotients.tower _).rho i j hij = a) :
    y ∈ cycles model X (j-t+w) (s,t) := by
  obtain ⟨e,he,_⟩ := rho_lift_detects X i j hi hij s t w hw y a ha b hb
  exact ((KIP126.Literature.Standard.eInfinity_finite_labels X j (by omega) s t w
    (by constructor <;> omega) y e).mp he).1


private theorem absolute_boundary_filtration_lift_weighted (X : ClassicalObject)
    (i j : ℕ) (hi : 0 < i) (hij : i < j) (m w : ℤ)
    (a : BiHom m w (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) i))
    (hfil : FiltrationAtLeast model.syntheticTower (w-m+j+1)
      (biSuspensionHomEquiv m w i (model.nu.functor.obj (X.obj model.auxiliary))
        (a ≫ XModLambdaN.proj _ i))) :
    ∃ b : BiHom m w (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) j),
      b ≫ (model.quotients.tower _).rho i j hij.le = a := by
  have hm : m = w-(w-m) := by omega
  generalize hs : w-m = s0 at *
  subst m
  exact absolute_boundary_filtration_lift X i j hi hij s0 w a hfil

private theorem absolute_boundary_detected_cycles_weighted (X : ClassicalObject)
    (i j : ℕ) (hi : 0 < i) (hij : i < j) (s t w : ℤ)
    (hw : 0 ≤ t-w ∧ t-w < i) (y : Ambient model X (s,t))
    (a : BiHom (t-s) w (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) i))
    (ha : Detects (model.convergence (.quotient i (.nu X))) (s,t,w)
      ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) i).pageMap 2 (s,t,w)
        (nuWeightLabel model X s t w (by omega) y)) a)
    (hfil : FiltrationAtLeast model.syntheticTower (w-(t-s)+j+1)
      (biSuspensionHomEquiv (t-s) w i (model.nu.functor.obj (X.obj model.auxiliary))
        (a ≫ XModLambdaN.proj _ i))) :
    y ∈ cycles model X (j-t+w) (s,t) := by
  obtain ⟨b,hb⟩ := absolute_boundary_filtration_lift_weighted X i j hi hij (t-s) w a hfil
  exact rho_lift_detected_cycles X i j hi hij.le s t w hw y a ha b hb


private theorem finite_extension_target_weight_label (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (q : ℕ) (n s t : ℤ) (hn : (normalizedExponent model.classicalTower f : ℤ) ≤ n)
    (y : Ambient model Y (s+n,t+n)) :
    regradeE2 (by ext <;> dsimp <;> omega)
      (finiteTargetForExtension model X Y f q n s t hn y) =
    (model.family.quotientProjection (model.nu.functor.obj (Y.obj model.auxiliary)) q).pageMap
      2 (s+n,t+n,t+normalizedExponent model.classicalTower f)
      (nuWeightLabel model Y (s+n) (t+n) (t+normalizedExponent model.classicalTower f) (by omega) y) := by
  have regrade_comp {E : SyntheticAdamsSS} {p₁ p₂ p₃ : Tridegree}
      (h₁ : p₁=p₂) (h₂ : p₂=p₃) (z : E.E₂ p₁) :
      regradeE2 h₂ (regradeE2 h₁ z) = regradeE2 (h₁.trans h₂) z := by
    subst p₂; subst p₃; rfl
  have hpow : ((t+n)-(t+normalizedExponent model.classicalTower f)).toNat =
      (n-normalizedExponent model.classicalTower f).toNat := by congr 1; omega
  unfold finiteTargetForExtension finiteTargetLabel nuWeightLabel
  rw [regrade_comp]
  change regradeE2 _ (familyPageMap model.family (XModLambdaN.incl _ q) 2 _ _) =
    familyPageMap model.family (XModLambdaN.incl _ q) 2 _ (regradeE2 _ _)
  rw [page_regrade]
  have labels (k k' : ℕ) (hk : k=k') (p : Tridegree)
      (h₁ : (s+n,t+n,t+n-k)=p) (h₂ : (s+n,t+n,t+n-k')=p) :
      regradeE2 h₁ (targetNuLabel model Y (s+n) (t+n) k y) =
        regradeE2 h₂ (targetNuLabel model Y (s+n) (t+n) k' y) := by
    subst k'; rfl
  exact congrArg (familyPageMap model.family (XModLambdaN.incl _ q) 2
    (s+n,t+n,t+normalizedExponent model.classicalTower f))
    (labels _ _ hpow.symm _ _ _)

private theorem gl1_right_edge_survival (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (page : ℕ) (r m l s t : ℤ) (hpage : 2 ≤ page) (hpr : (page:ℤ) ≤ r)
    (hm : (normalizedExponent model.classicalTower f : ℤ) ≤ m)
    (hmUpper : m ≤ (page:ℤ)-2+normalizedExponent model.classicalTower f)
    (hl : (normalizedExponent model.classicalTower f : ℤ) < l)
    (y : Ambient model Y (s+m,t+m))
    (a : BiHom ((t+m)-(s+m)) (t+normalizedExponent model.classicalTower f)
      (XModLambdaN (model.nu.functor.obj (Y.obj model.auxiliary)) (page-1)))
    (ha : Detects (model.convergence (.quotient (page-1) (.nu Y)))
      (s+m,t+m,t+normalizedExponent model.classicalTower f)
      (regradeE2 (by ext <;> dsimp <;> omega)
        (finiteTargetForExtension model X Y f (page-1) m s t hm y)) a)
    (hfil : FiltrationAtLeast model.syntheticTower (s+r+l)
      (biSuspensionHomEquiv ((t+m)-(s+m)) (t+normalizedExponent model.classicalTower f) ((page-1:ℕ):ℤ)
        (model.nu.functor.obj (Y.obj model.auxiliary)) (a ≫ XModLambdaN.proj _ (page-1)))) :
    IsCycle model Y (r+l-m-1) (s+m,t+m) y := by
  let j := (r+l-normalizedExponent model.classicalTower f-1).toNat
  have hj : (j:ℤ)=r+l-normalizedExponent model.classicalTower f-1 := by
    dsimp [j]; omega
  rw [finite_extension_target_weight_label] at ha
  have hfil' : FiltrationAtLeast model.syntheticTower
      ((t+normalizedExponent model.classicalTower f)-((t+m)-(s+m))+j+1)
      (biSuspensionHomEquiv ((t+m)-(s+m)) (t+normalizedExponent model.classicalTower f) ((page-1:ℕ):ℤ)
        (model.nu.functor.obj (Y.obj model.auxiliary)) (a ≫ XModLambdaN.proj _ (page-1))) := by
    convert hfil using 1
    omega
  have hcycle := absolute_boundary_detected_cycles_weighted Y (page-1) j (by omega) (by omega)
    (s+m) (t+m) (t+normalizedExponent model.classicalTower f) (by constructor <;> omega) y a ha hfil'
  refine ⟨by omega,?_⟩
  convert hcycle using 1
  congr 1
  omega

end
end KIP126.ProofTools.Internal.Leibniz
