module

public import KIP126.Def.ProofTools.Laws
import all KIP126.Def.ProofTools.GeneralizedMahowald.Coherence
import all KIP126.Def.ProofTools.DetectionOperations
import all KIP126.Def.ProofTools.StretchingRepresentatives
import all KIP126.Def.ProofTools.GeneralizedMahowald.Detection
import all KIP126.Def.ProofTools.GeneralizedMahowald.BoundaryLambda

/-! The proved sphere cases of generalized Mahowald, retained from
GeneralizedMahowald/Proofs.lean:1996–2940 at bbac1fc05843 (MIT).
Shared detection, filtration and coherence arguments use the same fixed system. -/

@[expose] section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 6000000
namespace KIP126.ProofTools.Internal.Mahowald
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Standard
noncomputable section

private theorem sphere_first_quotient_label  (s t : ℤ)
    (y : Ambient model .sphere (s,t)) :
    (sphereFirstQuotient model.nu model.quotients.functoriality model.firstQuotient) s t
      (firstLabel model .sphere s t y ≫ XModLambdaN.map
        ((SyntheticCategory.biShift_zero.hom.app _) ≫ model.nu.unitIso.hom) 1) = y := by
  let e := SyntheticCategory.biShift_zero.app (model.nu.functor.obj SphereSpectrum) ≪≫ model.nu.unitIso
  let Q := (model.quotients.functoriality.functor 1).mapIso e
  let c : BiHom (t-s) t (XModLambdaN (nuZero model .sphere) 1) ≃ₗ[ℤ] Ambient model .sphere (s,t) :=
    Eq.mp (congrArg (fun z : ℤ => BiHom (t-s) z
      (XModLambdaN (nuZero model .sphere) 1) ≃ₗ[ℤ] Ambient model .sphere (s,t))
      (Int.add_zero t)) (model.firstQuotient .sphere 0 s t)
  change c ((firstLabel model .sphere s t y ≫ Q.hom) ≫ Q.inv) = y
  rw [Category.assoc,Iso.hom_inv_id,Category.comp_id]
  have cast_symm (n m : ℤ) (h : n = m)
      (e : BiHom (t-s) n (XModLambdaN (nuZero model .sphere) 1) ≃ₗ[ℤ]
        Ambient model .sphere (s,t)) (z : Ambient model .sphere (s,t)) :
      (congrArg (fun w => BiHom (t-s) w (XModLambdaN (nuZero model .sphere) 1)) h).mp
          (e.symm z) =
        ((congrArg (fun w => BiHom (t-s) w (XModLambdaN (nuZero model .sphere) 1) ≃ₗ[ℤ]
          Ambient model .sphere (s,t)) h).mp e).symm z := by
    subst m
    rfl
  have hc : firstLabel model .sphere s t y = c.symm y := by
    exact cast_symm (t+0) t (Int.add_zero t) (model.firstQuotient .sphere 0 s t) y
  rw [hc,LinearEquiv.apply_symm_apply]

private theorem sphere_finite_lambda_detects 
    (q : ℕ) (_hq : 0 < q) (s t : ℤ) (k : ℕ)
    (y : Ambient model .sphere (s,t))
    (α : BiHom (t-s) t (model.nu.functor.obj SphereSpectrum))
    (hα : α ≫ XModLambdaN.incl _ 1 =
      firstLabel model .sphere s t y ≫
        XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1) :
    Detects (model.convergence (.quotient q (.nu .sphere))) (s,t,t-k)
      (finiteTargetLabel model .sphere q s t k y)
      (lambdaMultiply k α ≫ XModLambdaN.incl _ q) := by
  have family_page_id (X : SyntheticSpectrum) (r : ℤ) (i : Tridegree) :
      familyPageMap model.family (𝟙 X) r i = 𝟙 _ := by
    change (model.family.map (𝟙 X)).pageMap r i = 𝟙 _
    rw [SyntheticAdamsFamily.map_id,SpectralSequenceMorphism.pageMap_id]
  let a : BiHom (t-s) t (S_0_0 : SyntheticSpectrum) := α ≫ model.nu.unitIso.hom
  have hfirst : quotientClass 1 a =
      firstLabel model .sphere s t y ≫ XModLambdaN.map
        (SyntheticCategory.biShift_zero.hom.app _ ≫ model.nu.unitIso.hom) 1 := by
    dsimp only [quotientClass,a]
    rw [Category.assoc,XModLambdaN.incl_naturality,←Category.assoc,hα,
      Category.assoc,←model.quotients.functoriality.map_comp]
    rfl
  have hl : (sphereFirstQuotient model.nu model.quotients.functoriality model.firstQuotient) s t (quotientClass 1 a) = y := by
    rw [hfirst]
    exact sphere_first_quotient_label s t y
  have hs := model.sphereDetectionCompatible.homotopy_lambda s t k a
  rw [hl] at hs
  have hforw : familyPageMap model.family model.nu.unitIso.hom 2 (s,t,t-k)
      (targetNuLabel model .sphere s t k y) = model.comparison.sphereE2 s t k y := by
    let z : (model.family.obj (nuZero model .sphere)).E₂ (s,t,t-k) := by
      simpa [SyntheticAdamsSS.E₂] using model.comparison.nuE2 .sphere 0 s t k y
    exact (ConcreteCategory.congr_hom (family_page_comp
      (SyntheticCategory.biShift_zero.hom.app _) model.nu.unitIso.hom 2 (s,t,t-k)) z).trans
        (model.comparison.sphere_nu s t k y)
  have hback : familyPageMap model.family model.nu.unitIso.inv 2 (s,t,t-k)
      (model.comparison.sphereE2 s t k y) = targetNuLabel model .sphere s t k y := by
    rw [←hforw,←ModuleCat.comp_apply,family_page_comp,Iso.hom_inv_id,family_page_id]
    rfl
  have hc : lambdaMultiply k a ≫ model.nu.unitIso.inv = lambdaMultiply k α := by
    dsimp only [lambdaMultiply,a]
    simp only [Category.assoc,Iso.hom_inv_id,Category.comp_id]
  have hn := detects_map .sphere (.nu .sphere) model.nu.unitIso.inv
    (s,t,t-k) _ _ hs
  have hn' : Detects (model.convergence (.nu .sphere)) (s,t,t-k)
      (targetNuLabel model .sphere s t k y) (lambdaMultiply k α) := by
    exact (congrArg₂ (Detects (model.convergence (.nu .sphere)) (s,t,t-k)) hback hc).mp hn
  exact detects_map (.nu .sphere) (.quotient q (.nu .sphere))
    (XModLambdaN.incl _ q) (s,t,t-k) _ _ hn'

/-! The same finite λ detection on every selected classical object follows from
actual filtered shift transport and the fixed finite E∞ presentation. -/
open KIP126.ProofTools.Internal

private theorem shift_frame (A : SyntheticObject) (δ p : ℤ × ℤ) (s : ℤ)
    (e : ((model.family.obj (A.obj model.nu model.auxiliary)).sequence.ssData (s,p.1+s,p.2)).eInfty)
    (a : (Subobject.underlying.obj ((model.syntheticTower.filtration
      (A.obj model.nu model.auxiliary)).F s p) : ModuleCat ℤ))
    (ha : (model.syntheticTower.filtration (A.obj model.nu model.auxiliary)).toAssociatedGraded s p a =
      (infinityGradedIso (model.convergence A) p s).hom e) :
    ∃ b : (Subobject.underlying.obj ((model.syntheticTower.filtration
      ((SyntheticObject.shift δ A).obj model.nu model.auxiliary)).F s (p+δ)) : ModuleCat ℤ),
      ((model.syntheticTower.filtration ((SyntheticObject.shift δ A).obj model.nu model.auxiliary)).F
        s (p+δ)).arrow b = shiftHomotopyClass δ p
          (((model.syntheticTower.filtration (A.obj model.nu model.auxiliary)).F s p).arrow a) ∧
      (model.syntheticTower.filtration ((SyntheticObject.shift δ A).obj model.nu model.auxiliary)).toAssociatedGraded
        s (p+δ) b = (infinityGradedIso (model.convergence (.shift δ A)) (p+δ) s).hom
          ((towerInfinityIso (model.convergence A) (model.convergence (.shift δ A))
            ((essShift δ).filtered A p) s).hom e) := by
  let S := (essShift δ).filtered A p
  refine ⟨(S.level s).hom a,?_,?_⟩
  · exact (ConcreteCategory.congr_hom (S.level_arrow s) a).trans
      ((essShift δ).ambient_eq A p _)
  · have h := ConcreteCategory.congr_hom (S.projection_comm s) a
    simp only [ModuleCat.comp_apply] at h
    rw [ha] at h
    rw [←h]
    change (S.gradedIso s).hom ((towerGradedIso (model.convergence A) p s).hom e) =
      (towerGradedIso (model.convergence (.shift δ A)) (p+δ) s).hom
        ((towerInfinityIso (model.convergence A) (model.convergence (.shift δ A)) S s).hom e)
    simp only [towerInfinityIso, Iso.trans_hom, Iso.symm_hom, ←ModuleCat.comp_apply,
      Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem detects_shift (A : SyntheticObject) (δ p : ℤ × ℤ) (s : ℤ)
    (x : (model.family.obj (A.obj model.nu model.auxiliary)).E₂ (s,p.1+s,p.2))
    (a : BiHom p.1 p.2 (A.obj model.nu model.auxiliary))
    (ha : Detects (model.convergence A) (s,p.1+s,p.2) x
      (homotopyRegrade (by dsimp; omega) rfl a)) :
    Detects (model.convergence (.shift δ A)) (s,(p+δ).1+s,(p+δ).2)
      (((essShift δ).page A 2 (by decide) p s).hom x)
      (homotopyRegrade (by dsimp; omega) rfl (shiftHomotopyClass δ p a)) := by
  obtain ⟨e,he,a',ha',hga⟩ := frame_of_source_detects (model.convergence A) p s x a ha
  obtain ⟨b,hb,hgb⟩ := shift_frame A δ p s e a' hga
  have hdet := source_frame_detects (model.convergence (.shift δ A)) (p+δ) s _ _
    ((essShift δ).representative_iff A 2 (by decide) p s x e |>.mp he) b
    hgb
  rw [hb,ha'] at hdet
  exact hdet

private theorem regrade_comp {m m' w w' : ℤ} {A B : SyntheticSpectrum}
    (hm : m=m') (hw : w=w') (a : BiHom m w A) (f : A ⟶ B) :
    homotopyRegrade hm hw (a≫f) = homotopyRegrade hm hw a ≫ f := by
  subst m'; subst w'; rfl

private theorem shifted_map_detects (A B : SyntheticObject) (δ p : ℤ × ℤ) (s : ℤ)
    (g : (SyntheticObject.shift δ A).obj model.nu model.auxiliary ⟶ B.obj model.nu model.auxiliary)
    (x : (model.family.obj (A.obj model.nu model.auxiliary)).E₂ (s,p.1+s,p.2))
    (a : BiHom p.1 p.2 (A.obj model.nu model.auxiliary))
    (ha : Detects (model.convergence A) (s,p.1+s,p.2) x (homotopyRegrade (by dsimp; omega) rfl a)) :
    Detects (model.convergence B) (s,(p+δ).1+s,(p+δ).2)
      (familyPageMap model.family g 2 (s,(p+δ).1+s,(p+δ).2)
        (((essShift δ).page A 2 (by decide) p s).hom x))
      (homotopyRegrade (by dsimp; omega) rfl (shiftHomotopyClass δ p a) ≫ g) :=
  detects_map (.shift δ A) B g (s,(p+δ).1+s,(p+δ).2) _ _
    (detects_shift A δ p s x a ha)

private theorem shifted_representative_map (A B : SyntheticObject) (δ p : ℤ × ℤ) (s : ℤ)
    (g : (SyntheticObject.shift δ A).obj model.nu model.auxiliary ⟶ B.obj model.nu model.auxiliary)
    (x : (model.family.obj (A.obj model.nu model.auxiliary)).E₂ (s,p.1+s,p.2))
    (e : ((model.family.obj (A.obj model.nu model.auxiliary)).sequence.ssData (s,p.1+s,p.2)).eInfty)
    (he : HasInfinityRepresentative _ 2 (s,p.1+s,p.2) x e) :
    HasInfinityRepresentative _ 2 (s,(p+δ).1+s,(p+δ).2)
      (familyPageMap model.family g 2 (s,(p+δ).1+s,(p+δ).2)
        (((essShift δ).page A 2 (by decide) p s).hom x))
      ((model.family.map g).eInftyMap (s,(p+δ).1+s,(p+δ).2)
        ((towerInfinityIso (model.convergence A) (model.convergence (.shift δ A))
          ((essShift δ).filtered A p) s).hom e)) :=
  family_infinity_representative_map g (s,(p+δ).1+s,(p+δ).2) _ _
    (((essShift δ).representative_iff A 2 (by decide) p s x e).mp he)

private theorem detects_transport {A : SyntheticObject} {i j : Tridegree} (h : i=j)
    (x : (model.family.obj (A.obj model.nu model.auxiliary)).E₂ i)
    (a : BiHom (i.2.1-i.1) i.2.2 (A.obj model.nu model.auxiliary))
    (ha : Detects (model.convergence A) i x a) :
    Detects (model.convergence A) j (regradeE2 h x)
      (homotopyRegrade (congrArg (fun k : Tridegree => k.2.1-k.1) h)
        (congrArg (fun k : Tridegree => k.2.2) h) a) := by
  subst j
  exact ha

private theorem representative_transport {A : SyntheticAdamsSS.{0}} {i j : Tridegree} (h : i=j)
    (x : A.E₂ i) (e : (A.sequence.ssData i).eInfty)
    (he : HasInfinityRepresentative A 2 i x e) :
    HasInfinityRepresentative A 2 j (regradeE2 h x)
      ((eqToHom (congrArg (fun k => (A.sequence.ssData k).eInfty) h)) e) := by
  subst j
  exact he

private theorem map_regrade {A B : SyntheticSpectrum} (f : A ⟶ B) {i j : Tridegree} (h : i=j)
    (x : (model.family.obj A).E₂ i) :
    familyPageMap model.family f 2 j (regradeE2 h x) =
      regradeE2 h (familyPageMap model.family f 2 i x) := by
  subst j
  rfl

private theorem zero_weight_label (X : ClassicalObject) (q : ℕ) (s t : ℤ) (y : Ambient model X (s,t)) :
    (model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) q).pageMap 2 (s,t,t)
      (nuWeightLabel model X s t t (by omega) y) =
    regradeE2 (by simp) (finiteTargetLabel model X q s t 0 y) := by
  unfold nuWeightLabel
  have transport (j : ℕ) (hj : j=0) (h : (s,t,t-j)=(s,t,t)) :
      familyPageMap model.family (XModLambdaN.incl _ q) 2 (s,t,t)
        (regradeE2 h (targetNuLabel model X s t j y)) =
      regradeE2 (by simp) (finiteTargetLabel model X q s t 0 y) := by
    subst j
    exact map_regrade _ h _
  exact transport _ (by omega) _

private theorem infinity_map_regrade {A B : SyntheticSpectrum} (f : A ⟶ B) {i j : Tridegree} (h : i=j)
    (x : ((model.family.obj A).sequence.ssData i).eInfty) :
    ((eqToHom (congrArg (fun k => ((model.family.obj B).sequence.ssData k).eInfty) h)))
      ((model.family.map f).eInftyMap i x) =
    (model.family.map f).eInftyMap j
      ((eqToHom (congrArg (fun k => ((model.family.obj A).sequence.ssData k).eInfty) h)) x) := by
  subst j
  rfl

private theorem regrade_precomp {m m' w w' : ℤ} {A : SyntheticSpectrum}
    (hm : m=m') (hw : w=w') (a : BiHom m w A) :
    homotopyRegrade hm hw a =
      eqToHom (congrArg (fun p : ℤ × ℤ => Smn p.1 p.2 (Syn := SyntheticSpectrum))
        (show (m',w')=(m,w) by rw [hm,hw])) ≫ a := by
  subst m'; subst w'
  simp only [homotopyRegrade,eqToHom_refl,Category.id_comp]

/-- The actual λ-multiple of any permanent lift has the prescribed finite label.
The shift, finite quotient map and E∞ window all come from the same fixed model. -/
private theorem finite_lambda_detects (X : ClassicalObject) (q k : ℕ) (hk : 0 < k) (hkq : k < q)
    (s t : ℤ) (y : Ambient model X (s,t))
    (hy : y ∈ permanentCycles model X (s,t))
    (α : BiHom (t-s) t (model.nu.functor.obj (X.obj model.auxiliary)))
    (hα : α ≫ XModLambdaN.incl _ 1 = firstLabel model X s t y ≫
      XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1) :
    Detects (model.convergence (.quotient q (.nu X))) (s,t,t-k)
      (finiteTargetLabel model X q s t k y)
      (lambdaMultiply k α ≫ XModLambdaN.incl _ q) := by
  let A := model.nu.functor.obj (X.obj model.auxiliary)
  let n := q-k
  have hn : 0 < n := by dsimp [n]; omega
  let a := α ≫ XModLambdaN.incl A n
  have ha := first_label_detects_unshifted X n hn s t y a (by
    dsimp only [a]
    rw [Category.assoc,(model.quotients.tower A).rho_quotient]
    exact hα)
  have hsource : (s,t,t)=(s,(t-s)+s,t) := by simp
  have hstem := detects_transport hsource _ _ ha
  let L : ((SyntheticObject.shift (0,-(k:ℤ)) (.quotient n (.nu X))).obj model.nu model.auxiliary) ⟶
      ((SyntheticObject.quotient q (.nu X)).obj model.nu model.auxiliary) :=
    ((model.quotients.tower A).triangle hk hkq).lambdaMap
  have hmap := shifted_map_detects (.quotient n (.nu X)) (.quotient q (.nu X))
    (0,-(k:ℤ)) (t-s,t) s L
    (regradeE2 hsource (regradeE2 (by simp) (finiteTargetLabel model X n s t 0 y))) a hstem
  have hindex : (s,((t-s,t)+(0,-(k:ℤ))).1+s,((t-s,t)+(0,-(k:ℤ))).2) =
      (s,t,t-k) := by ext <;> simp [sub_eq_add_neg]
  have hmap := detects_transport hindex _ _ hmap
  obtain ⟨e,he,b,hb,hgb⟩ := hmap
  obtain ⟨e0,he0,_⟩ := ha
  have heStem := representative_transport hsource _ _ he0
  have heMap := shifted_representative_map (.quotient n (.nu X)) (.quotient q (.nu X))
    (0,-(k:ℤ)) (t-s,t) s L _ _ heStem
  have heMap := representative_transport hindex _ _ heMap
  have heq := he.unique heMap
  have heq' : e = KIP126.Literature.Standard.infinityFiniteLambda X q k hkq (s,t) t e0 := by
    convert heq using 1
    simp only [KIP126.Literature.Standard.infinityFiniteLambda,
      InfinityShiftCoordinates.finiteLambdaMap, show k ≠ 0 by omega, ↓reduceDIte,
      InfinityShiftCoordinates.shift, infinityShift, Iso.trans_hom, ModuleCat.comp_apply,
      eqToIso.hom, KIP126.Literature.Standard.infinityShiftData,
      KIP126.Literature.Standard.infinityShift_comparison]
    rw [infinity_map_regrade L hindex]
    rfl
  have hlabel : HasInfinityRepresentative _ 2 (s,t,t-k)
      (finiteTargetLabel model X q s t k y)
      (KIP126.Literature.Standard.infinityFiniteLambda X q k hkq (s,t) t e0) := by
    apply (finite_target_label_iff X q (by omega) s t k hkq
      ⟨y,permanentCycles_le_cycles model X (s,t) _ hy⟩ _).mpr
    rw [KIP126.Literature.Standard.eInfinity_lambda_finite X q k hkq (s,t) t (by dsimp [n] at hn; omega)]
    have he0' := (KIP126.Literature.Standard.eInfinity_finite_labels X n hn s t t
      (by constructor <;> dsimp [n] at * <;> omega) y e0).mp
      ((congrArg (fun z => HasInfinityRepresentative _ 2 (s,t,t) z e0)
        (zero_weight_label X n s t y)).mpr he0)
    rw [he0'.2]
    rfl
  have heFinal : HasInfinityRepresentative _ 2 (s,t,t-k)
      (finiteTargetLabel model X q s t k y) e := by
    simpa only [heq'] using hlabel
  refine ⟨e,heFinal,b,?_,hgb⟩
  convert hb using 1
  simp only [regrade_comp]
  simp only [regrade_precomp, L, a, shiftHomotopyClass, lambdaMultiply,
    Functor.map_comp, Category.assoc]
  rw [((model.quotients.tower A).triangle hk hkq).lambda_quotient,
    ←Category.assoc ((SyntheticCategory.biShift (0,-(k:ℤ))).map α), lambdaPow_naturality]
  simp only [←Category.assoc,eqToHom_trans]
  rfl
end
end KIP126.ProofTools.Internal.Mahowald
