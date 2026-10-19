module

import all KIP126.ProofTools.GeneralizedMahowald.FiniteLevelLabels
import all KIP126.ProofTools.GeneralizedMahowald.FiniteComparison
import all KIP126.ProofTools.GeneralizedLeibniz.LevelSource
import all KIP126.ProofTools.LevelLanguage
import all KIP126.ProofTools.GeneralizedLeibniz.LevelLanguage

/-! The conclusion bridge for finite-level MH. Actual source and target
detections are transported through the fixed ESS shift and quotient
comparisons. No Mahowald or Leibniz law supplies either conclusion. -/

@[expose] section
namespace KIP126.ProofTools.Internal.Mahowald
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Standard
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Leibniz
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward false
set_option maxHeartbeats 200000
set_option Elab.async false

/-- Deshift a pair of actual detections and their equation by the fixed ESS
comparison. The two detections refer to the same actual map equation. -/
private theorem detected_pair_unshift
    (A B : SyntheticObject)
    (f : A.obj model.nu model.auxiliary ⟶ B.obj model.nu model.auxiliary)
    (δ p : ℤ×ℤ) (s n : ℤ) (hn : 0 ≤ n)
    (x : (model.family.obj (A.obj model.nu model.auxiliary)).E₂ (s,p.1+s,p.2))
    (y : (model.family.obj (B.obj model.nu model.auxiliary)).E₂ (s+n,p.1+(s+n),p.2))
    (a : BiHom (p+δ).1 (p+δ).2 ((SyntheticObject.shift δ A).obj model.nu model.auxiliary))
    (b : BiHom (p+δ).1 (p+δ).2 ((SyntheticObject.shift δ B).obj model.nu model.auxiliary))
    (ha : Detects (model.convergence (.shift δ A)) (s,(p+δ).1+s,(p+δ).2)
      (((essShift δ).page A 2 (by decide) p s).hom x)
      (homotopyRegrade (by dsimp; omega) rfl a))
    (hb : Detects (model.convergence (.shift δ B)) (s+n,(p+δ).1+(s+n),(p+δ).2)
      (((essShift δ).page B 2 (by decide) p (s+n)).hom y)
      (homotopyRegrade (by dsimp; omega) rfl b))
    (hab : a ≫ (SyntheticCategory.biShift δ).map f = b) :
    ∃ source target, HasInfinityRepresentative _ 2 _ x source ∧
      HasInfinityRepresentative _ 2 _ y target ∧
      TowerExtensionEquation (model.convergentMap A B f) p s n source target := by
  obtain ⟨zs,zt,hzs,hzt,heq⟩ := extension_equation_of_detected_pair
    (model.convergentMap (.shift δ A) (.shift δ B) ((SyntheticCategory.biShift δ).map f))
    (p+δ) s n hn _ _ a b ha hb hab
  let Is := towerInfinityIso (model.convergence A) (model.convergence (.shift δ A))
    ((essShift δ).filtered A p) s
  let It := towerInfinityIso (model.convergence B) (model.convergence (.shift δ B))
    ((essShift δ).filtered B p) (s+n)
  have hsource : HasInfinityRepresentative _ 2 _ x (Is.inv zs) := by
    apply ((essShift δ).representative_iff A 2 (by decide) p s x (Is.inv zs)).mpr
    change HasInfinityRepresentative _ 2 _ _ (Is.hom (Is.inv zs))
    rw [show Is.hom (Is.inv zs)=zs from Is.toLinearEquiv.apply_symm_apply zs]
    exact hzs
  have htarget : HasInfinityRepresentative _ 2 _ y (It.inv zt) := by
    apply ((essShift δ).representative_iff B 2 (by decide) p (s+n) y (It.inv zt)).mpr
    change HasInfinityRepresentative _ 2 _ _ (It.hom (It.inv zt))
    rw [show It.hom (It.inv zt)=zt from It.toLinearEquiv.apply_symm_apply zt]
    exact hzt
  refine ⟨Is.inv zs,It.inv zt,hsource,htarget,?_⟩
  apply ((essShift δ).towerExtensionEquation_iff A B f p s n (Is.inv zs) (It.inv zt)).mpr
  change TowerExtensionEquation _ _ _ _ (Is.hom (Is.inv zs)) (It.hom (It.inv zt))
  rw [show Is.hom (Is.inv zs)=zs from Is.toLinearEquiv.apply_symm_apply zs,
    show It.hom (It.inv zt)=zt from It.toLinearEquiv.apply_symm_apply zt]
  exact heq

/-- Existence of the specified intrinsic finite source label at infinity
already certifies the original class's full finite cycle qualification. -/
private theorem level_finite_source_representative_cycles
    (X : ClassicalObject) (N K : ℕ) (hKN : K < N) (e s t : ℤ)
    (x : Ambient model X (s,t))
    (z : ((model.family.obj ((SyntheticObject.quotient N (.shift (0,e) (.nu X))).obj
      model.nu model.auxiliary)).sequence.ssData (s,(t-s)+s,t+e-K)).eInfty)
    (hz : HasInfinityRepresentative _ 2 _
      (KIP126.ProofTools.Standard.levelFiniteSourceLabel X N e s t K x) z) :
    KIP126.ProofTools.IsCycle model X ((N:ℤ)-K) (s,t) x := by
  let A : SyntheticObject := .quotient N (.nu X)
  let δ : ℤ×ℤ := (0,e)
  let p : ℤ×ℤ := (t-s,t-K)
  let ε := levelQuotientShiftIso X e N
  let i : Tridegree := (s,(t-s)+s,t+e-K)
  have hmap := family_infinity_representative_map ε.hom i
    (KIP126.ProofTools.Standard.levelFiniteSourceLabel X N e s t K x) z hz
  have he2 : familyPageMap model.family ε.hom 2 i
      (KIP126.ProofTools.Standard.levelFiniteSourceLabel X N e s t K x) =
      regradeE2 (by ext <;> dsimp [i,p,δ] <;> omega)
        (((essShift δ).page A 2 (by decide) p s).hom
          (regradeE2 (by simp [p]) (finiteTargetLabel model X N s t K x))) := by
    change (familyPageMap model.family ε.hom 2 i)
      ((familyPageMap model.family ε.inv 2 i) _) = _
    rw [←ModuleCat.comp_apply,family_page_comp,Iso.inv_hom_id]
    change ((model.family.map (𝟙 _)).pageMap 2 i) _ = _
    rw [SyntheticAdamsFamily.map_id,SpectralSequenceMorphism.pageMap_id]
    rfl
  rw [he2] at hmap
  have hi : i=(s,(p+δ).1+s,(p+δ).2) := by
    ext <;> dsimp [i,p,δ] <;> omega
  have hshift := representative_transport hi _ _ hmap
  let zs := (eqToHom (congrArg (fun j =>
    ((model.family.obj ((SyntheticObject.shift δ A).obj model.nu model.auxiliary)).sequence.ssData j).eInfty)
    hi)) ((model.family.map ε.hom).eInftyMap i z)
  let I := towerInfinityIso (model.convergence A) (model.convergence (.shift δ A))
    ((essShift δ).filtered A p) s
  have hnative : HasInfinityRepresentative _ 2 (s,p.1+s,p.2)
      (regradeE2 (by simp [p]) (finiteTargetLabel model X N s t K x)) (I.inv zs) := by
    apply ((essShift δ).representative_iff A 2 (by decide) p s _ (I.inv zs)).mpr
    change HasInfinityRepresentative _ 2 _ _ (I.hom (I.inv zs))
    rw [show I.hom (I.inv zs)=zs from I.toLinearEquiv.apply_symm_apply zs]
    convert hshift using 1
    all_goals try rfl
    change _ = regradeE2 hi (regradeE2 hi.symm _)
    have cancel {E : SyntheticAdamsSS} {i j : Tridegree}
        (h : i=j) (v : E.E₂ j) : regradeE2 h (regradeE2 h.symm v)=v := by
      subst j
      rfl
    exact (cancel hi _).symm
  have hi0 : (s,p.1+s,p.2)=(s,t,t-K) := by simp [p]
  have hz0 := representative_transport hi0 _ _ hnative
  simp only [regradeE2,←ModuleCat.comp_apply,eqToHom_trans,eqToHom_refl,ModuleCat.id_apply] at hz0
  have hlabel : finiteTargetLabel model X N s t K x =
      (model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) N).pageMap
        2 (s,t,t-K) (nuWeightLabel model X s t (t-K) (by omega) x) := by
    have hk : (t-(t-K)).toNat=K := by omega
    unfold nuWeightLabel
    have labels (k k' : ℕ) (h : k=k') (hp : (s,t,t-k)=(s,t,t-k')) :
        regradeE2 hp (targetNuLabel model X s t k x) = targetNuLabel model X s t k' x := by
      subst k'; rfl
    rw [labels _ K hk]
    rfl
  rw [hlabel] at hz0
  have hx := ((KIP126.Literature.Standard.eInfinity_finite_labels X N (by omega)
    s t (t-K) (by constructor <;> omega) x _).mp hz0).1
  refine ⟨by omega,?_⟩
  convert hx using 1
  congr 1
  omega

/-- The specified infinity representatives and their actual normalized-map
extension equation imply both terminal conclusions of finite-level MH.
The inverse-shift lemma above constructs this very input pair from the
same shifted actual representative and its image. -/
private theorem finite_level_conclusion_of_infinity_pair
    (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (N K J : ℕ) (hKN : K < N) (hJN : J < N) (n s t : ℤ)
    (hn : (normalizedExponent model.classicalTower f : ℤ) ≤ n)
    (hJ : (J:ℤ) = K+n-normalizedExponent model.classicalTower f)
    (x : Ambient model X (s,t)) (y : Ambient model Y (s+n,t+n))
    (source : ((model.family.obj ((SyntheticObject.quotient N
      (.shift (0,(normalizedExponent model.classicalTower f:ℤ)) (.nu X))).obj
      model.nu model.auxiliary)).sequence.ssData
        (s,(t-s)+s,t+normalizedExponent model.classicalTower f-K)).eInfty)
    (target : ((model.family.obj ((SyntheticObject.quotient N (.nu Y)).obj
      model.nu model.auxiliary)).sequence.ssData
        (s+n,(t-s)+(s+n),t+normalizedExponent model.classicalTower f-K)).eInfty)
    (hs : HasInfinityRepresentative _ 2 _
      (KIP126.ProofTools.Standard.levelFiniteSourceLabel X N
        (normalizedExponent model.classicalTower f) s t K x) source)
    (ht : HasInfinityRepresentative _ 2 _
      (levelFiniteTargetLabel X Y f N K n s t hn y) target)
    (heq : TowerExtensionEquation
      (model.convergentMap (.quotient N
        (.shift (0,(normalizedExponent model.classicalTower f:ℤ)) (.nu X)))
        (.quotient N (.nu Y)) (finiteExtensionMap model X Y f N))
      (t-s,t+normalizedExponent model.classicalTower f-K) s n source target) :
    KIP126.ProofTools.IsCycle model X ((N:ℤ)-K) (s,t) x ∧
      KIP126.ProofTools.Standard.LevelFiniteExtension X Y f (N-K+1) K n s t x y := by
  refine ⟨level_finite_source_representative_cycles X N K hKN
    (normalizedExponent model.classicalTower f) s t x source hs,?_⟩
  have hq : (N-K+1)+K-1=N := by omega
  unfold KIP126.ProofTools.Standard.LevelFiniteExtension
  rw [hq]
  exact ⟨by omega,hn,by omega,source,target,hs,ht,heq⟩

/-- The exact page-label convention used by the local let in the public
finite MH statement. -/
private def finiteConclusionShiftLabel (V : SyntheticObject) (δ : ℤ×ℤ)
    (q : Tridegree) (x : (model.family.obj (V.obj model.nu model.auxiliary)).E₂ q) :
    (model.family.obj ((SyntheticObject.shift δ V).obj model.nu model.auxiliary)).E₂
      (q.1,q.2.1+δ.1,q.2.2+δ.2) :=
  regradeE2 (by ext <;> dsimp; omega)
    ((shift_page δ V 2 (by decide) (q.2.1-q.1,q.2.2) q.1).hom
      (regradeE2 (by ext <;> simp) x))

private theorem finite_conclusion_shift_label_to_page
    (V : SyntheticObject) (δ p : ℤ×ℤ) (s : ℤ) (q : Tridegree)
    (hq : q=(s,p.1+s,p.2))
    (x : (model.family.obj (V.obj model.nu model.auxiliary)).E₂ q) :
    regradeE2 (by rw [hq]; ext <;> dsimp; omega)
      (finiteConclusionShiftLabel V δ q x) =
      ((essShift δ).page V 2 (by decide) p s).hom (regradeE2 hq x) := by
  subst q
  unfold finiteConclusionShiftLabel
  rw [normalized_regrade_trans]
  have point (p' : ℤ×ℤ) (hp : p'=p)
      (hi : (s,p.1+s,p.2)=(s,p'.1+s,p'.2))
      (ho : (s,(p'+δ).1+s,(p'+δ).2)=(s,(p+δ).1+s,(p+δ).2)) :
      regradeE2 ho
        (((essShift δ).page V 2 (by decide) p' s).hom (regradeE2 hi x)) =
          ((essShift δ).page V 2 (by decide) p s).hom x := by
    subst p'
    rfl
  exact point ((p.1+s-s),p.2) (by ext <;> simp) _ _

private def finiteConclusionSourceLabel (X : ClassicalObject)
    (N K : ℕ) (e s t : ℤ) (p : ℤ×ℤ)
    (hp : p.1=t-s+1) (hw : p.2=t+e-K) (x : Ambient model X (s,t)) :
    (model.family.obj ((SyntheticObject.shift (1,0)
      (.quotient N (.shift (0,e) (.nu X)))).obj model.nu model.auxiliary)).E₂
      (s,p.1+s,p.2) :=
  regradeE2 (by ext <;> dsimp <;> omega)
    (finiteConclusionShiftLabel (.quotient N (.shift (0,e) (.nu X))) (1,0)
      (s,(t-s)+s,t+e-K)
      (KIP126.ProofTools.Standard.levelFiniteSourceLabel X N e s t K x))

private def finiteConclusionTargetLabel (Y : ClassicalObject)
    (N J : ℕ) (s t n : ℤ) (p : ℤ×ℤ)
    (hp : p.1=t-s+1) (hw : p.2=t+n-J)
    (y : Ambient model Y (s+n,t+n)) :
    (model.family.obj ((SyntheticObject.shift (1,0) (.quotient N (.nu Y))).obj
      model.nu model.auxiliary)).E₂ (s+n,p.1+(s+n),p.2) :=
  regradeE2 (by ext <;> dsimp <;> omega)
    (finiteConclusionShiftLabel (.quotient N (.nu Y)) (1,0) (s+n,t+n,t+n-J)
      (finiteTargetLabel model Y N (s+n) (t+n) J y))

/-- Keep the exact target class when the public statement writes its
degree as `t+l+n-1` and the extension language writes `(t+l-1)+n`. -/
private theorem finite_conclusion_target_label_regrade
    (Y : ClassicalObject) (N J : ℕ) (s t n : ℤ) (p : ℤ×ℤ)
    (hp : p.1=t-s+1) (hw : p.2=t+n-J) (u : ℤ) (hu : u=t+n)
    (y : Ambient model Y (s+n,u))
    (y' : Ambient model Y (s+n,t+n)) (hy : HEq y y')
    (ho : (s+n,u+1,u-J+0)=(s+n,p.1+(s+n),p.2)) :
    @regradeE2 (model.family.obj ((SyntheticObject.shift (1,0) (.quotient N (.nu Y))).obj
      model.nu model.auxiliary)) (s+n,u+1,u-J+0) (s+n,p.1+(s+n),p.2) ho
      (finiteConclusionShiftLabel (.quotient N (.nu Y)) (1,0) (s+n,u,u-J)
      (finiteTargetLabel model Y N (s+n) u J y)) =
      finiteConclusionTargetLabel Y N J s t n p hp hw y' := by
  subst u
  cases hy
  rfl

/-- Complete source/image conclusion adapter in the exact shifted-label
convention of the public finite MH statement.  In that statement substitute
`s := s+l`, `t := t+l-1`; its stem/weight pair is exactly the `p` below. -/
private theorem finite_level_conclusion_of_suspended_detects
    (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (N K J : ℕ) (hKN : K < N) (hJN : J < N) (n s t : ℤ)
    (hn : (normalizedExponent model.classicalTower f : ℤ) ≤ n)
    (hJ : (J:ℤ) = K+n-normalizedExponent model.classicalTower f)
    (p : ℤ×ℤ) (hp : p.1=t-s+1)
    (hw : p.2=t+normalizedExponent model.classicalTower f-K)
    (x : Ambient model X (s,t)) (y : Ambient model Y (s+n,t+n))
    (ex : XModLambdaN (((SyntheticCategory.biShift (0,(normalizedExponent model.classicalTower f:ℤ))).obj
      (model.nu.functor.obj (X.obj model.auxiliary)))⟦(1:ℤ)⟧) N ≅
      (XModLambdaN ((SyntheticCategory.biShift (0,(normalizedExponent model.classicalTower f:ℤ))).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) N)⟦(1:ℤ)⟧)
    (ey : XModLambdaN ((model.nu.functor.obj (Y.obj model.auxiliary))⟦(1:ℤ)⟧) N ≅
      (XModLambdaN (model.nu.functor.obj (Y.obj model.auxiliary)) N)⟦(1:ℤ)⟧)
    (hex : XModLambdaN.incl _ N ≫ ex.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ N))
    (hey : XModLambdaN.incl _ N ≫ ey.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ N))
    (c : BiHom p.1 p.2 (XModLambdaN
      (((SyntheticCategory.biShift (0,(normalizedExponent model.classicalTower f:ℤ))).obj
        (model.nu.functor.obj (X.obj model.auxiliary)))⟦(1:ℤ)⟧) N))
    (hc : Detects (model.convergence (.shift (1,0) (.quotient N
      (.shift (0,(normalizedExponent model.classicalTower f:ℤ)) (.nu X)))))
      (s,p.1+s,p.2)
      (finiteConclusionSourceLabel X N K (normalizedExponent model.classicalTower f) s t p hp hw x)
      (homotopyRegrade (by dsimp; omega) rfl
        (c ≫ ex.hom ≫ (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).inv.app _)))
    (hf : Detects (model.convergence (.shift (1,0) (.quotient N (.nu Y))))
      (s+n,p.1+(s+n),p.2)
      (finiteConclusionTargetLabel Y N J s t n p hp (by omega) y)
      (homotopyRegrade (by dsimp; omega) rfl
        (c ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
          (model.normalizedMap X Y f).map) N ≫ ey.hom ≫
          (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).inv.app _))) :
    KIP126.ProofTools.IsCycle model X ((N:ℤ)-K) (s,t) x ∧
      KIP126.ProofTools.Standard.LevelFiniteExtension X Y f (N-K+1) K n s t x y := by
  let A : SyntheticObject := .quotient N (.shift (0,(normalizedExponent model.classicalTower f:ℤ)) (.nu X))
  let B : SyntheticObject := .quotient N (.nu Y)
  let p₀ : ℤ×ℤ := (t-s,t+normalizedExponent model.classicalTower f-K)
  let δ : ℤ×ℤ := (1,0)
  let source₀ : (model.family.obj (A.obj model.nu model.auxiliary)).E₂ (s,p₀.1+s,p₀.2) :=
    KIP126.ProofTools.Standard.levelFiniteSourceLabel X N
      (normalizedExponent model.classicalTower f) s t K x
  let target₀ : (model.family.obj (B.obj model.nu model.auxiliary)).E₂
      (s+n,p₀.1+(s+n),p₀.2) := levelFiniteTargetLabel X Y f N K n s t hn y
  have hP : p=p₀+δ := by ext <;> dsimp [p₀,δ] <;> omega
  let κ := SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1
  let a' : BiHom p.1 p.2 ((SyntheticObject.shift δ A).obj model.nu model.auxiliary) :=
    c ≫ ex.hom ≫ κ.inv.app _
  let b' : BiHom p.1 p.2 ((SyntheticObject.shift δ B).obj model.nu model.auxiliary) :=
    c ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
      (model.normalizedMap X Y f).map) N ≫ ey.hom ≫ κ.inv.app _
  let a := homotopyRegrade (congrArg Prod.fst hP) (congrArg Prod.snd hP) a'
  let b := homotopyRegrade (congrArg Prod.fst hP) (congrArg Prod.snd hP) b'
  have hsGrade : (s,p.1+s,p.2)=(s,(p₀+δ).1+s,(p₀+δ).2) := by rw [hP]
  have htGrade : (s+n,p.1+(s+n),p.2)=(s+n,(p₀+δ).1+(s+n),(p₀+δ).2) := by rw [hP]
  have hsLabel : regradeE2 hsGrade
      (finiteConclusionSourceLabel X N K (normalizedExponent model.classicalTower f) s t p hp hw x) =
      ((essShift δ).page A 2 (by decide) p₀ s).hom source₀ := by
    unfold finiteConclusionSourceLabel
    rw [normalized_regrade_trans]
    exact finite_conclusion_shift_label_to_page A δ p₀ s _ rfl _
  have htLabel : regradeE2 htGrade
      (finiteConclusionTargetLabel Y N J s t n p hp (by omega) y) =
      ((essShift δ).page B 2 (by decide) p₀ (s+n)).hom target₀ := by
    unfold finiteConclusionTargetLabel
    rw [normalized_regrade_trans]
    have hq : (s+n,t+n,t+n-J)=(s+n,p₀.1+(s+n),p₀.2) := by
      ext <;> dsimp [p₀] <;> omega
    rw [finite_conclusion_shift_label_to_page B δ p₀ (s+n) _ hq]
    rw [finite_level_target_label X Y f N K J n s t hn hJ y]
  have ha := detects_transport hsGrade _ _ hc
  rw [hsLabel] at ha
  have hb := detects_transport htGrade _ _ hf
  rw [htLabel] at hb
  have hmap := finite_suspension_normalized_map_on_spheres X Y
    (normalizedExponent model.classicalTower f) (normalizedExponent_le_one model.classicalTower f)
    N (by omega) (model.normalizedMap X Y f).map ex ey hex hey p.1 p.2 c
  have hpair : a' ≫ (SyntheticCategory.biShift δ).map (finiteExtensionMap model X Y f N) = b' := by
    dsimp only [a',δ]
    simp only [Category.assoc]
    rw [←κ.inv.naturality]
    exact (by simpa only [b',finiteExtensionMap,Category.assoc] using
      congrArg (fun z => z ≫ κ.inv.app _) hmap.symm)
  have hab : a ≫ (SyntheticCategory.biShift δ).map (finiteExtensionMap model X Y f N) = b := by
    simpa only [a,b,regrade_precomp,Category.assoc] using
      congrArg (homotopyRegrade (congrArg Prod.fst hP) (congrArg Prod.snd hP)) hpair
  obtain ⟨source,target,hs,ht,heq⟩ := detected_pair_unshift A B
    (finiteExtensionMap model X Y f N) δ p₀ s n (by omega) source₀ target₀ a b
    (by simpa only [a,a',regrade_precomp,←Category.assoc,eqToHom_trans] using ha)
    (by simpa only [b,b',regrade_precomp,←Category.assoc,eqToHom_trans] using hb) hab
  exact finite_level_conclusion_of_infinity_pair X Y f N K J hKN hJN n s t hn hJ
    x y source target hs ht heq

end
end KIP126.ProofTools.Internal.Mahowald
