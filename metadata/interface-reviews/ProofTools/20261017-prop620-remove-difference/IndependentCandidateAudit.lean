module

public import KIP126.ProofTools.Language
import all KIP126.ProofTools.Operations
import all KIP126.ProofTools.GeneralizedMahowald.ShortSource
import all KIP126.ProofTools.ConvergenceOperations

/-! Proposition 6.20 with the cycle-set exclusion removed and the fixed target retained. -/

@[expose] section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace KIP126.ProofTools.Paper
open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.ProofTools.Internal
noncomputable section
universe u v w

section Filtered
variable {Acat : Type u} [Category.{v} Acat] [Abelian Acat]
  {ι : Type w} {A B : ι → Acat} {F : Filtration A} {G : Filtration B}

/-- Inessentiality for a known equation means that the same target is a
homogeneous solution for the same filtered map. -/
private theorem inessential_iff_zero_source_same_target
    (f : FilteredMorphism F G) (k : ι) (s n : ℤ) {T : Acat}
    (x : T ⟶ F.associatedGraded s k)
    (y : T ⟶ G.associatedGraded (s+n) k)
    (h : FilteredMapExtension.Relation f k s n x y) :
    ¬ FilteredMapExtension.Essential f k s n x y ↔
      FilteredMapExtension.Relation f k s n 0 y := by
  classical
  constructor
  · intro hne
    have hz : FilteredMapExtension.Relation f k s n x 0 := by
      by_contra hnz
      exact hne ((FilteredMapExtension.essential_iff h).mpr hnz)
    simpa only [sub_self, sub_zero] using h.sub hz
  · intro hz he
    have hh : FilteredMapExtension.Relation f k s n x 0 := by
      simpa only [sub_zero, sub_self] using h.sub hz
    exact ((FilteredMapExtension.essential_iff h).mp he) hh

/-- This is the actual higher-source representative form: the specified
target is retained, with a source lift in filtration s+1. -/
private theorem inessential_iff_higher_source_same_target
    (f : FilteredMorphism F G) (k : ι) (s n : ℤ) {T : Acat}
    (x : T ⟶ F.associatedGraded s k)
    (y : T ⟶ G.associatedGraded (s+n) k)
    (h : FilteredMapExtension.Relation f k s n x y) :
    ¬ FilteredMapExtension.Essential f k s n x y ↔
      0 ≤ n ∧ ∃ (a : T ⟶ Subobject.underlying.obj (F.F (s+1) k))
        (b : T ⟶ Subobject.underlying.obj (G.F (s+n) k)),
        b ≫ G.toAssociatedGraded (s+n) k = y ∧
        a ≫ (F.F (s+1) k).arrow ≫ f.map k =
          b ≫ (G.F (s+n) k).arrow := by
  rw [inessential_iff_zero_source_same_target f k s n x y h]
  exact FilteredMapExtension.mem_indeterminacy_iff
end Filtered

section Tower
variable {Syn : Type u} [SyntheticCategory.{u,v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  {H : Syn} {unit : S_0_0 ⟶ H} {F : SyntheticAdamsFamily Syn}
  {P : SyntheticTowerPresentation unit F} {X Y : Syn} {g : X ⟶ Y}
  {cx : SyntheticTowerConvergence P X} {cy : SyntheticTowerConvergence P Y}

private theorem elementMap_zero {A : ModuleCat.{v} ℤ} :
    elementMap (0 : A) = 0 := by
  ext z
  simp [elementMap]

private theorem elementMap_one {A : ModuleCat.{v} ℤ} (a : A) :
    elementMap a (ULift.up (1 : ℤ)) = a := by
  simp [elementMap, one_smul]

/-- Same-map, same-degree, same-target criterion in the actual tower language. -/
private theorem tower_inessential_iff_zero_source_same_target
    (M : ConvergentMap F g cx.toConvergence cy.toConvergence)
    (p : ℤ × ℤ) (s n : ℤ)
    (x : ((F.obj X).sequence.ssData (s,p.1+s,p.2)).eInfty)
    (y : ((F.obj Y).sequence.ssData (s+n,p.1+(s+n),p.2)).eInfty)
    (h : TowerExtensionEquation M p s n x y) :
    ¬ TowerEssentialExtension M p s n x y ↔
      TowerExtensionEquation M p s n 0 y := by
  unfold TowerEssentialExtension TowerExtensionEquation
    ConvergentMap.EssentialExtension ConvergentMap.ExtensionEquation
  rw [elementMap_zero]
  simp only [toGraded, Limits.zero_comp]
  exact inessential_iff_zero_source_same_target _ _ _ _ _ _ h

/-- Actual homotopy representatives realizing the fixed target y, with the
source strictly above s. There is no arbitrary or unrelated target y'. -/
private theorem tower_inessential_iff_higher_source_same_target
    (M : ConvergentMap F g cx.toConvergence cy.toConvergence)
    (p : ℤ × ℤ) (s n : ℤ)
    (x : ((F.obj X).sequence.ssData (s,p.1+s,p.2)).eInfty)
    (y : ((F.obj Y).sequence.ssData (s+n,p.1+(s+n),p.2)).eInfty)
    (h : TowerExtensionEquation M p s n x y) :
    ¬ TowerEssentialExtension M p s n x y ↔
      0 ≤ n ∧ ∃
        (a : (Subobject.underlying.obj ((P.filtration X).F (s+1) p) : ModuleCat.{v} ℤ))
        (b : (Subobject.underlying.obj ((P.filtration Y).F (s+n) p) : ModuleCat.{v} ℤ)),
        ((P.filtration X).F (s+1) p).arrow a ≫ g =
          ((P.filtration Y).F (s+n) p).arrow b ∧
        (P.filtration Y).toAssociatedGraded (s+n) p b =
          (KIP126.ProofTools.Operations.infinityGradedIso cy p (s+n)).hom y := by
  have hrel : FilteredMapExtension.Relation M.filteredMap p s n
      (toGraded cx.toConvergence (by simp [SyntheticTowerConvergence.toConvergence])
        (elementMap x))
      (toGraded cy.toConvergence (by simp [SyntheticTowerConvergence.toConvergence])
        (elementMap y)) := h
  rw [show (¬ TowerEssentialExtension M p s n x y) ↔ _ from
    inessential_iff_higher_source_same_target _ _ _ _ _ _ hrel]
  simp only [KIP126.ProofTools.Internal.toGraded_element]
  constructor
  · rintro ⟨hn,a,b,hb,he⟩
    refine ⟨hn,a (ULift.up 1),b (ULift.up 1),?_,?_⟩
    · have hh := ConcreteCategory.congr_hom he (ULift.up (1 : ℤ))
      have hf := ConcreteCategory.congr_hom (M.filteredMap_map p)
        (((P.filtration X).F (s+1) p).arrow (a (ULift.up 1)))
      exact hf.symm.trans hh
    · have hh := ConcreteCategory.congr_hom hb (ULift.up (1 : ℤ))
      change (P.filtration Y).toAssociatedGraded (s+n) p (b (ULift.up 1)) =
        elementMap ((KIP126.ProofTools.Internal.infinityGradedIso cy p (s+n)).hom y)
          (ULift.up (1 : ℤ)) at hh
      rw [elementMap_one] at hh
      exact hh
  · rintro ⟨hn,a,b,he,hb⟩
    refine ⟨hn,elementMap a,elementMap b,?_,?_⟩
    · rw [← KIP126.AdamsSynthetic.elementMap_comp]
      exact congrArg elementMap hb
    · rw [← Category.assoc,← KIP126.AdamsSynthetic.elementMap_comp,
        ← KIP126.AdamsSynthetic.elementMap_comp,
        ← KIP126.AdamsSynthetic.elementMap_comp]
      have hf := ConcreteCategory.congr_hom (M.filteredMap_map p)
        (((P.filtration X).F (s+1) p).arrow a)
      exact congrArg elementMap (hf.trans he)
private theorem tower_extension_reindexed
    (M : ConvergentMap F g cx.toConvergence cy.toConvergence)
    (p : ℤ × ℤ) (k m target : ℤ) (h : target = k+m)
    (x : ((F.obj X).sequence.ssData (k,p.1+k,p.2)).eInfty)
    (y : ((F.obj Y).sequence.ssData (target,p.1+target,p.2)).eInfty) :
    TowerExtensionEquation M p k m x
      ((eqToHom (congrArg
        (fun d => ((F.obj Y).sequence.ssData (d,p.1+d,p.2)).eInfty) h)) y) ↔
      0 ≤ m ∧ ∃
        (a : (Subobject.underlying.obj ((P.filtration X).F k p) : ModuleCat.{v} ℤ))
        (b : (Subobject.underlying.obj ((P.filtration Y).F target p) : ModuleCat.{v} ℤ)),
        ((P.filtration X).F k p).arrow a ≫ g =
          ((P.filtration Y).F target p).arrow b ∧
        (P.filtration X).toAssociatedGraded k p a = (infinityGradedIso cx p k).hom x ∧
        (P.filtration Y).toAssociatedGraded target p b =
          (infinityGradedIso cy p target).hom y := by
  subst target
  simpa only [eqToHom_refl, ModuleCat.id_apply] using tower_extension_iff M p k m x y

end Tower

open KIP126.Classical.Adams KIP126.AdamsSynthetic.Standard KIP126.Literature
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
open KIP126.ProofTools.Internal.Leibniz

private noncomputable def correctionShiftIso (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary) (q : ℕ) :
    (SyntheticObject.quotient q (extensionSourceObject model X Y f)).obj model.nu model.auxiliary ≅
      (SyntheticObject.shift (0,(normalizedExponent model.classicalTower f : ℤ))
        (.quotient q (.nu X))).obj model.nu model.auxiliary := by
  letI := model.exactness.shiftCommShift (0,(normalizedExponent model.classicalTower f : ℤ))
  letI := model.exactness.shiftExact (0,(normalizedExponent model.classicalTower f : ℤ))
  exact (quotient_shift_exists model.quotients.coherence
    (0,(normalizedExponent model.classicalTower f : ℤ)) q
      (model.nu.functor.obj (X.obj model.auxiliary))).choose

private theorem correctionShiftIso_incl (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary) (q : ℕ) :
    XModLambdaN.incl ((extensionSourceObject model X Y f).obj model.nu model.auxiliary) q ≫
      (correctionShiftIso X Y f q).hom =
      (SyntheticCategory.biShift (0,(normalizedExponent model.classicalTower f : ℤ))).map
        (XModLambdaN.incl (model.nu.functor.obj (X.obj model.auxiliary)) q) := by
  letI := model.exactness.shiftCommShift (0,(normalizedExponent model.classicalTower f : ℤ))
  letI := model.exactness.shiftExact (0,(normalizedExponent model.classicalTower f : ℤ))
  exact (quotient_shift_exists model.quotients.coherence
    (0,(normalizedExponent model.classicalTower f : ℤ)) q
      (model.nu.functor.obj (X.obj model.auxiliary))).choose_spec.1

/-- The λ^a classical label in the actual normalized finite source quotient.
The shift comparison and quotient isomorphism transport the same actual class. -/
@[no_expose] public noncomputable def finiteExtensionCorrectionLabel (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary) (q : ℕ) (s t : ℤ) (a : ℕ)
    (x : Ambient model X (s+a,(t-s)+(s+a))) :
    (model.family.obj ((SyntheticObject.quotient q (extensionSourceObject model X Y f)).obj
      model.nu model.auxiliary)).E₂
      (s+a,(t-s)+(s+a),t+normalizedExponent model.classicalTower f) :=
  familyPageMap model.family (correctionShiftIso X Y f q).inv 2 _
    (regradeE2 (by ext <;> dsimp <;> omega)
      (((essShift (0,(normalizedExponent model.classicalTower f : ℤ))).page
        (.quotient q (.nu X)) 2 (by decide)
        (t-s,((t-s)+(s+a))-(a:ℤ)) (s+a)).hom
          (finiteTargetLabel model X q (s+a) ((t-s)+(s+a)) a x)))

private theorem correction_label_exists (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (q : ℕ) (hq : 0 < q) (s t : ℤ) (a : ℕ) (ha : a < q)
    (z : ((model.family.obj ((SyntheticObject.quotient q (extensionSourceObject model X Y f)).obj
      model.nu model.auxiliary)).sequence.ssData
      (s+a,(t-s)+(s+a),t+normalizedExponent model.classicalTower f)).eInfty) :
    ∃ x : Ambient model X (s+a,(t-s)+(s+a)),
      x ∈ cycles model X ((q:ℤ)-a) (s+a,(t-s)+(s+a)) ∧
      HasInfinityRepresentative _ 2 _ (finiteExtensionCorrectionLabel X Y f q s t a x) z := by
  let e : ℤ := normalizedExponent model.classicalTower f
  let u : ℤ := s+a
  let v : ℤ := (t-s)+(s+a)
  let p : ℤ × ℤ := (t-s,v-a)
  let Q := correctionShiftIso X Y f q
  let I := towerInfinityIso (model.convergence (.quotient q (.nu X)))
    (model.convergence (.shift (0,e) (.quotient q (.nu X))))
    ((essShift (0,e)).filtered (.quotient q (.nu X)) p) u
  let hdeg : (u,(p+(0,e)).1+u,(p+(0,e)).2) =
      (s+a,(t-s)+(s+a),t+normalizedExponent model.classicalTower f) := by
    ext <;> dsimp [p,u,v,e] <;> omega
  let zs := ((model.family.map Q.hom).eInftyMap _ z)
  let zu := I.inv ((eqToHom (congrArg (fun i =>
    ((model.family.obj ((SyntheticObject.shift (0,e) (.quotient q (.nu X))).obj
      model.nu model.auxiliary)).sequence.ssData i).eInfty) hdeg.symm)) zs)
  obtain ⟨x,hx,hrep,_⟩ := CrossingLabels.finite_grade_label X q hq u v (v-a)
    (by dsimp [v]; constructor <;> omega) zu
  have hlabel : nuWeightLabel model X u v (v-a) (by omega) x =
      targetNuLabel model X u v a x := by
    have hk : (v-(v-(a:ℤ))).toNat=a := by omega
    have transport (b c : ℕ) (he : b=c) (hi : (u,v,v-b)=(u,v,v-c)) :
        regradeE2 hi (targetNuLabel model X u v b x) = targetNuLabel model X u v c x := by
      subst c
      rfl
    exact transport _ a hk _
  rw [hlabel] at hrep
  refine ⟨x,?_,?_⟩
  · convert hx using 1 <;> dsimp [u,v] <;> congr 1 <;> omega
  have hs := ((essShift (0,e)).representative_iff (.quotient q (.nu X)) 2
    (by decide) p u (finiteTargetLabel model X q u v a x) zu).mp hrep
  have hs' := infinity_representative_regrade hdeg _ _ hs
  have hz : ((eqToHom (congrArg (fun i =>
      ((model.family.obj ((SyntheticObject.shift (0,e) (.quotient q (.nu X))).obj
        model.nu model.auxiliary)).sequence.ssData i).eInfty) hdeg)) (I.hom zu)) = zs := by
    dsimp only [zu]
    simp only [←ModuleCat.comp_apply,Category.assoc,Iso.inv_hom_id_assoc,
      eqToHom_trans,eqToHom_refl,ConcreteCategory.id_apply]
  rw [hz] at hs'
  have hm := family_infinity_representative_map Q.inv _ _ zs hs'
  have hc : (model.family.map Q.inv).eInftyMap _ zs = z := by
    dsimp only [zs]
    rw [←ModuleCat.comp_apply,←SpectralSequenceMorphism.eInftyMap_comp,
      ←SyntheticAdamsFamily.map_comp,Q.hom_inv_id,SyntheticAdamsFamily.map_id,
      SpectralSequenceMorphism.eInftyMap_id,ConcreteCategory.id_apply]
  rw [hc] at hm
  exact hm

private theorem earlier_target_nonzero (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (rEarlier rLater : ℕ) (n s t : ℤ) (x y)
    (Wlater : FiniteExtensionWitness model X Y f rLater n s t x y)
    (Wearly : FiniteExtensionWitness model X Y f rEarlier n s t x y)
    (hle : rEarlier ≤ rLater) (hess : Wlater.Essential) : Wearly.target ≠ 0 := by
  let rb := (model.quotients.tower (model.nu.functor.obj (Y.obj model.auxiliary))).rho
    (rEarlier-1) (rLater-1) (Nat.sub_le_sub_right hle 1)
  have hh := family_infinity_representative_map rb _ _ Wlater.target Wlater.target_rep
  rw [finite_target_rho] at hh
  have heq := hh.unique Wearly.target_rep
  have hlate : Wlater.target ≠ 0 := by
    intro hz
    apply ((tower_essential_iff_no_zero _ _ _ _ _ _ Wlater.equation).mp hess)
    simpa only [hz] using Wlater.equation
  intro hz
  apply hlate
  apply rho_infty_injective Y (rEarlier-1) (rLater-1)
    (by have := Wearly.page_ge_two; omega) (Nat.sub_le_sub_right hle 1)
    (s+n) ((t-s)+(s+n)) (t+normalizedExponent model.classicalTower f)
    (by have := Wearly.length_upper; omega)
  change (model.family.map rb).eInftyMap _ Wlater.target =
    (model.family.map rb).eInftyMap _ 0
  rw [heq,hz,map_zero]

private theorem inessential_length_strict (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (r : ℕ) (n s t : ℤ) (x y)
    (W : FiniteExtensionWitness model X Y f r n s t x y)
    (hy : W.target ≠ 0) (h : ¬ W.Essential) :
    (normalizedExponent model.classicalTower f : ℤ) < n := by
  by_contra hn
  apply h
  exact (tower_essential_iff_target_nonzero_of_no_crossing _ _ _ _ _ _ W.equation
    (minimal_length_finite_tower_no_crossing X Y f (r-1)
      (by have := W.page_ge_two; omega) s t n (by omega))).mpr hy

/-- Proposition 6.20 after removing the source cycle-set exclusion. The
original target is retained, with b=0. The shorter extension may itself be
inessential and its source class is allowed to vanish. -/
public theorem finiteExtension_inessential_iff_shorter (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (rEarlier rLater : ℕ) (n s t : ℤ) (x y)
    (Wlater : FiniteExtensionWitness model X Y f rLater n s t x y)
    (Wearly : FiniteExtensionWitness model X Y f rEarlier n s t x y)
    (hle : rEarlier ≤ rLater) (hess : Wlater.Essential) :
    ¬ Wearly.Essential ↔ ∃ a : ℕ, 0 < a ∧
      (a:ℤ) ≤ n-normalizedExponent model.classicalTower f ∧
      ∃ x' : Ambient model X (s+a,(t-s)+(s+a)),
        x' ∈ cycles model X (((rEarlier-1:ℕ):ℤ)- (a:ℤ)) (s+a,(t-s)+(s+a)) ∧
        ∃ z,
          HasInfinityRepresentative _ 2 _
            (finiteExtensionCorrectionLabel X Y f (rEarlier-1) s t a x') z ∧
          TowerExtensionEquation (model.convergentMap
            (.quotient (rEarlier-1) (extensionSourceObject model X Y f))
            (.quotient (rEarlier-1) (.nu Y)) (finiteExtensionMap model X Y f (rEarlier-1)))
            (t-s,t+normalizedExponent model.classicalTower f) (s+a) (n-a) z
            ((eqToHom (congrArg (fun d =>
              ((model.family.obj ((SyntheticObject.quotient (rEarlier-1) (.nu Y)).obj
                model.nu model.auxiliary)).sequence.ssData
                (d,(t-s)+d,t+normalizedExponent model.classicalTower f)).eInfty)
              (show s+n = (s+a)+(n-a) by omega))) Wearly.target) := by
  let A := (SyntheticObject.quotient (rEarlier-1) (extensionSourceObject model X Y f)).obj
    model.nu model.auxiliary
  let B := (SyntheticObject.quotient (rEarlier-1) (.nu Y)).obj model.nu model.auxiliary
  let p : ℤ × ℤ := (t-s,t+normalizedExponent model.classicalTower f)
  let M := model.convergentMap
    (.quotient (rEarlier-1) (extensionSourceObject model X Y f))
    (.quotient (rEarlier-1) (.nu Y)) (finiteExtensionMap model X Y f (rEarlier-1))
  have hy := earlier_target_nonzero X Y f rEarlier rLater n s t x y Wlater Wearly hle hess
  constructor
  · intro hne
    have hn := inessential_length_strict X Y f rEarlier n s t x y Wearly hy hne
    have hq : 1 < rEarlier-1 := by have := Wearly.length_upper; omega
    obtain ⟨hn0,ar,br,heq,hbr⟩ :=
      (tower_inessential_iff_higher_source_same_target M p s n
        Wearly.source Wearly.target Wearly.equation).mp hne
    let I := infinityGradedIso (model.convergence
      (.quotient (rEarlier-1) (extensionSourceObject model X Y f))) p (s+1)
    let z := I.inv ((model.syntheticTower.filtration A).toAssociatedGraded (s+1) p ar)
    obtain ⟨x',hx',hz⟩ := correction_label_exists X Y f (rEarlier-1)
      (by omega) s t 1 hq z
    refine ⟨1,by decide,by omega,x',hx',z,hz,?_⟩
    apply (tower_extension_reindexed M p (s+1) (n-1) (s+n) (by omega) z Wearly.target).mpr
    refine ⟨by omega,ar,br,heq,?_,hbr⟩
    exact (I.toLinearEquiv.apply_symm_apply _).symm
  · rintro ⟨a,ha,han,x',hx',z,hz,he⟩
    obtain ⟨_,ar,br,heq,_,hbr⟩ :=
      (tower_extension_reindexed M p (s+a) (n-a) (s+n) (by omega) z Wearly.target).mp he
    have hα : ((model.syntheticTower.filtration A).F (s+a) p).arrow ar ∈
        model.syntheticTower.filtrationSubmodule A (s+a) p := by
      have hm : ((model.syntheticTower.filtration A).F (s+a) p).arrow ar ∈
          ModuleCat.subobjectModule _ ((model.syntheticTower.filtration A).F (s+a) p) := ⟨ar,rfl⟩
      simpa only [SyntheticTowerPresentation.filtration,OrderIso.apply_symm_apply] using hm
    have hα' := model.syntheticTower.filtrationSubmodule_antitone A p
      (show s+1 ≤ s+a by omega) hα
    obtain ⟨ar',har'⟩ := filtration_representative_exists model.syntheticTower A p (s+1)
      (((model.syntheticTower.filtration A).F (s+a) p).arrow ar) hα'
    apply (tower_inessential_iff_higher_source_same_target M p s n
      Wearly.source Wearly.target Wearly.equation).mpr
    refine ⟨by have := Wearly.length_lower; omega,ar',br,?_,hbr⟩
    rw [har']
    exact heq

end
end KIP126.ProofTools.Paper


open Lean Elab Command in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  for root in #[`KIP126.ProofTools.Paper.finiteExtensionCorrectionLabel,
      `KIP126.ProofTools.Paper.finiteExtension_inessential_iff_shorter] do
    let some rootInfo := env.find? root | throwError "Missing root {root}"
    logInfo m!"KERNEL_TYPE {root}: {rootInfo.type}"
    let mut pending := #[root]
    let mut seen : NameSet := {}
    let mut project : Array String := #[]
    let mut holes : Array String := #[]
    let mut localHoles : Array String := #[]
    let mut main : Array String := #[]
    let mut projectAxioms : Array String := #[]
    while !pending.isEmpty do
      let name := pending.back!
      pending := pending.pop
      if seen.contains name then continue
      seen := seen.insert name
      let userName := (privateToUserName? name).getD name
      unless userName.toString.startsWith "KIP126." do continue
      let some info := env.find? name | throwError "Missing dependency {name}"
      project := project.push userName.toString
      let body := info.value? (allowOpaque := true)
      if info.type.hasSorry || body.any (·.hasSorry) then
        holes := holes.push userName.toString
        if userName.toString.startsWith "KIP126.ProofTools." then
          localHoles := localHoles.push userName.toString
      if userName.toString.startsWith "KIP126.Main." then
        main := main.push userName.toString
      if let .axiomInfo _ := info then
        projectAxioms := projectAxioms.push userName.toString
      pending := pending ++ info.type.getUsedConstants
      if let some value := body then pending := pending ++ value.getUsedConstants
    let axioms ← collectAxioms root
    logInfo m!"AUDIT_JSON {(Json.mkObj [
      ("root", toJson root.toString),
      ("level_params", toJson (rootInfo.levelParams.map Name.toString)),
      ("project_constant_count", toJson project.size),
      ("direct_sorry_dependencies", toJson holes),
      ("proof_tools_sorry_dependencies", toJson localHoles),
      ("main_dependencies", toJson main),
      ("project_axioms", toJson projectAxioms),
      ("axioms", toJson (axioms.map Name.toString))]).pretty}"
