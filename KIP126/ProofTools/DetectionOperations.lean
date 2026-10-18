module

public import KIP126.AdamsSynthetic
import all KIP126.ProofTools.ConvergenceOperations
import all KIP126.ProofTools.FiltrationOperations
import all KIP126.ProofTools.StretchingRepresentatives

/-! Detection transport used in the retained Mahowald proof.
Adapted from GeneralizedMahowald/Proofs.lean:354–479 at bbac1fc05843
(MIT; see the retained source LICENSE). All maps are the prescribed maps
on the fixed background, and every helper below is proved. -/

@[expose] section
set_option backward.isDefEq.respectTransparency false
namespace KIP126.ProofTools.Internal
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.Synthetic.SpectralSequence KIP126.AdamsSynthetic
open KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard
noncomputable section

public theorem grade_natural (A B : SyntheticObject)
    (f : A.obj model.nu model.auxiliary ⟶ B.obj model.nu model.auxiliary) (i : Tridegree)
    (a : (Subobject.underlying.obj ((model.syntheticTower.filtration
      (A.obj model.nu model.auxiliary)).F i.1 (i.2.1-i.1,i.2.2)) : ModuleCat ℤ))
    (b : (Subobject.underlying.obj ((model.syntheticTower.filtration
      (B.obj model.nu model.auxiliary)).F i.1 (i.2.1-i.1,i.2.2)) : ModuleCat ℤ))
    (hab : ((model.syntheticTower.filtration (A.obj model.nu model.auxiliary)).F
      i.1 (i.2.1-i.1,i.2.2)).arrow a ≫ f =
      ((model.syntheticTower.filtration (B.obj model.nu model.auxiliary)).F
        i.1 (i.2.1-i.1,i.2.2)).arrow b) :
    ((model.convergence B).identification i).inv
      ((model.syntheticTower.filtration (B.obj model.nu model.auxiliary)).toAssociatedGraded
        i.1 (i.2.1-i.1,i.2.2) b) =
      (model.family.map f).eInftyMap i (((model.convergence A).identification i).inv
        ((model.syntheticTower.filtration (A.obj model.nu model.auxiliary)).toAssociatedGraded
          i.1 (i.2.1-i.1,i.2.2) a)) := by
  let M := model.convergentMap A B f
  let FA := model.syntheticTower.filtration (A.obj model.nu model.auxiliary)
  let FB := model.syntheticTower.filtration (B.obj model.nu model.auxiliary)
  let p := (i.2.1-i.1,i.2.2)
  have hb : (M.filteredMap.compat i.1 p).choose a = b := by
    apply (ModuleCat.mono_iff_injective (FB.F i.1 p).arrow).mp inferInstance
    have h := ConcreteCategory.congr_hom (M.filteredMap.compat i.1 p).choose_spec a
    change (FB.F i.1 p).arrow ((M.filteredMap.compat i.1 p).choose a) =
      M.filteredMap.map p ((FA.F i.1 p).arrow a) at h
    have hm := ConcreteCategory.congr_hom (M.filteredMap_map p) ((FA.F i.1 p).arrow a)
    change M.filteredMap.map p ((FA.F i.1 p).arrow a) = (FA.F i.1 p).arrow a ≫ f at hm
    exact h.trans (hm.trans hab)
  have hp := graded_map_representative M.filteredMap i.1 p a
  rw [hb] at hp
  apply ((model.convergence B).identification i).toLinearEquiv.injective
  have hn := ConcreteCategory.congr_hom (M.infinity_action_graded i)
    (((model.convergence A).identification i).inv (FA.toAssociatedGraded i.1 p a))
  change M.filteredMap.inducedGrMap i.1 p
      (((model.convergence A).identification i).hom
        (((model.convergence A).identification i).inv (FA.toAssociatedGraded i.1 p a))) =
    ((model.convergence B).identification i).hom
      ((model.family.map f).eInftyMap i
        (((model.convergence A).identification i).inv (FA.toAssociatedGraded i.1 p a))) at hn
  have hA := ((model.convergence A).identification i).toLinearEquiv.apply_symm_apply
    (FA.toAssociatedGraded i.1 p a)
  have hB := ((model.convergence B).identification i).toLinearEquiv.apply_symm_apply
    (FB.toAssociatedGraded i.1 p b)
  exact hB.trans (hp.symm.trans
    ((congrArg (M.filteredMap.inducedGrMap i.1 p) hA.symm).trans hn))

public theorem detects_map (A B : SyntheticObject)
    (f : A.obj model.nu model.auxiliary ⟶ B.obj model.nu model.auxiliary) (i : Tridegree)
    (x : (model.family.obj (A.obj model.nu model.auxiliary)).E₂ i)
    (a : BiHom (i.2.1-i.1) i.2.2 (A.obj model.nu model.auxiliary))
    (ha : Detects (model.convergence A) i x a) :
    Detects (model.convergence B) i (familyPageMap model.family f 2 i x) (a ≫ f) := by
  obtain ⟨e,he,a',ha',hga⟩ := ha
  let M := model.convergentMap A B f
  let b := (M.filteredMap.compat i.1 (i.2.1-i.1,i.2.2)).choose a'
  have hb : ((model.syntheticTower.filtration (B.obj model.nu model.auxiliary)).F
      i.1 (i.2.1-i.1,i.2.2)).arrow b = a ≫ f := by
    have h := ConcreteCategory.congr_hom
      (M.filteredMap.compat i.1 (i.2.1-i.1,i.2.2)).choose_spec a'
    change _ = M.filteredMap.map (i.2.1-i.1,i.2.2) _ at h
    have hm := ConcreteCategory.congr_hom (M.filteredMap_map (i.2.1-i.1,i.2.2))
      (((model.syntheticTower.filtration (A.obj model.nu model.auxiliary)).F
        i.1 (i.2.1-i.1,i.2.2)).arrow a')
    change _ = _ ≫ f at hm
    exact h.trans (hm.trans (congrArg (fun z => z ≫ f) ha'))
  refine ⟨_,family_infinity_representative_map f i x e he,b,hb,?_⟩
  have h := grade_natural A B f i a' b (by rw [ha',hb])
  have haE : ((model.convergence A).identification i).inv
      ((model.syntheticTower.filtration (A.obj model.nu model.auxiliary)).toAssociatedGraded
        i.1 (i.2.1-i.1,i.2.2) a') = e := by
    rw [← hga]
    exact ((model.convergence A).identification i).toLinearEquiv.symm_apply_apply e
  rw [haE] at h
  exact (congrArg ((model.convergence B).identification i).hom h).symm.trans
    (((model.convergence B).identification i).toLinearEquiv.apply_symm_apply _)

public theorem detects_reflect (A B : SyntheticObject)
    (f : A.obj model.nu model.auxiliary ⟶ B.obj model.nu model.auxiliary) (i : Tridegree)
    (hf : Function.Injective ((model.family.map f).eInftyMap i).hom)
    (x : (model.family.obj (A.obj model.nu model.auxiliary)).E₂ i)
    (e : ((model.family.obj (A.obj model.nu model.auxiliary)).sequence.ssData i).eInfty)
    (he : HasInfinityRepresentative _ 2 i x e)
    (a : BiHom (i.2.1-i.1) i.2.2 (A.obj model.nu model.auxiliary))
    (ha : FiltrationAtLeast model.syntheticTower i.1 a)
    (hb : Detects (model.convergence B) i (familyPageMap model.family f 2 i x) (a ≫ f)) :
    Detects (model.convergence A) i x a := by
  obtain ⟨a',ha'⟩ := filtration_representative_exists model.syntheticTower
    (A.obj model.nu model.auxiliary) (i.2.1-i.1,i.2.2) i.1 a ha
  obtain ⟨eB,heB,b,hb,hgb⟩ := hb
  have huniq := heB.unique (family_infinity_representative_map f i x e he)
  have h := grade_natural A B f i a' b (by rw [ha',hb])
  have hB : ((model.convergence B).identification i).inv
      ((model.syntheticTower.filtration (B.obj model.nu model.auxiliary)).toAssociatedGraded
        i.1 (i.2.1-i.1,i.2.2) b) = (model.family.map f).eInftyMap i e := by
    rw [← hgb]
    exact (((model.convergence B).identification i).toLinearEquiv.symm_apply_apply eB).trans huniq
  have hA := hf (h.symm.trans hB)
  refine ⟨e,he,a',ha',?_⟩
  exact (congrArg ((model.convergence A).identification i).hom hA).symm.trans
    (((model.convergence A).identification i).toLinearEquiv.apply_symm_apply _)

section Frames
universe u v
variable {Syn : Type u} [SyntheticCategory.{u,v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  {H : Syn} {unit : S_0_0 ⟶ H} {F : SyntheticAdamsFamily Syn}
  {P : SyntheticTowerPresentation unit F} {X Y : Syn} {g : X ⟶ Y}
  {cx : SyntheticTowerConvergence P X} {cy : SyntheticTowerConvergence P Y}

/-- A filtration frame, reindexed by the same stem, gives detection. -/
theorem source_frame_detects (cx : SyntheticTowerConvergence P X)
    (p : ℤ × ℤ) (s : ℤ)
    (x : ((F.obj X).sequence.ssData (s,p.1+s,p.2)).eInfty)
    (x0 : (F.obj X).E₂ (s,p.1+s,p.2))
    (hx : HasInfinityRepresentative _ 2 _ x0 x)
    (a : (Subobject.underlying.obj ((P.filtration X).F s p) : ModuleCat.{v} ℤ))
    (ha : (P.filtration X).toAssociatedGraded s p a = (infinityGradedIso cx p s).hom x) :
    Detects cx (s,p.1+s,p.2) x0
      (homotopyRegrade (by dsimp; omega) rfl (((P.filtration X).F s p).arrow a)) := by
  have lift_frame (m m' w s : ℤ) (hm : m=m') {V : ModuleCat.{v} ℤ} (e : V)
      (I : V ≅ (P.filtration X).associatedGraded s (m',w))
      (a : (Subobject.underlying.obj ((P.filtration X).F s (m,w)) : ModuleCat.{v} ℤ))
      (ha : (P.filtration X).toAssociatedGraded s (m,w) a =
        (I ≪≫ eqToIso (congrArg
          (fun z => (P.filtration X).associatedGraded s (z,w)) hm.symm)).hom e) :
      ∃ a' : (Subobject.underlying.obj ((P.filtration X).F s (m',w)) : ModuleCat.{v} ℤ),
        ((P.filtration X).F s (m',w)).arrow a' =
          homotopyRegrade hm rfl (((P.filtration X).F s (m,w)).arrow a) ∧
        I.hom e = (P.filtration X).toAssociatedGraded s (m',w) a' := by
    subst m'
    refine ⟨a,rfl,?_⟩
    simpa only [eqToIso_refl, Iso.trans_refl] using ha.symm
  obtain ⟨a',ha',hga⟩ := lift_frame p.1 ((p.1+s)-s) p.2 s (by omega) x
    (cx.identification (s,p.1+s,p.2)) a ha
  exact ⟨x,hx,a',ha',hga⟩

/-- Detection supplies a frame in the original stem coordinates. -/
theorem frame_of_source_detects (cx : SyntheticTowerConvergence P X)
    (p : ℤ × ℤ) (s : ℤ) (x0 : (F.obj X).E₂ (s,p.1+s,p.2))
    (a0 : BiHom p.1 p.2 X)
    (ha0 : Detects cx (s,p.1+s,p.2) x0 (homotopyRegrade (by dsimp; omega) rfl a0)) :
    ∃ x : ((F.obj X).sequence.ssData (s,p.1+s,p.2)).eInfty,
      HasInfinityRepresentative _ 2 _ x0 x ∧
      ∃ a : (Subobject.underlying.obj ((P.filtration X).F s p) : ModuleCat.{v} ℤ),
        ((P.filtration X).F s p).arrow a = a0 ∧
        (P.filtration X).toAssociatedGraded s p a = (infinityGradedIso cx p s).hom x := by
  have lower_frame (m m' w s : ℤ) (hm : m=m') {V : ModuleCat.{v} ℤ} (e : V)
      (I : V ≅ (P.filtration X).associatedGraded s (m',w))
      (a0 : BiHom m w X)
      (a' : (Subobject.underlying.obj ((P.filtration X).F s (m',w)) : ModuleCat.{v} ℤ))
      (ha' : ((P.filtration X).F s (m',w)).arrow a' = homotopyRegrade hm rfl a0)
      (hga : I.hom e = (P.filtration X).toAssociatedGraded s (m',w) a') :
      ∃ a : (Subobject.underlying.obj ((P.filtration X).F s (m,w)) : ModuleCat.{v} ℤ),
        ((P.filtration X).F s (m,w)).arrow a = a0 ∧
        (P.filtration X).toAssociatedGraded s (m,w) a =
          (I ≪≫ eqToIso (congrArg
            (fun z => (P.filtration X).associatedGraded s (z,w)) hm.symm)).hom e := by
    subst m'
    exact ⟨a',ha',hga.symm⟩
  obtain ⟨e,he,a',ha',hga⟩ := ha0
  obtain ⟨a,ha,hg⟩ := lower_frame p.1 ((p.1+s)-s) p.2 s (by omega) e
    (cx.identification (s,p.1+s,p.2)) a0 a' ha' hga
  exact ⟨e,he,a,ha,hg⟩

/-- Exact representatives of two detected classes determine the extension
equation for this same map and pair of convergences. -/
theorem extension_equation_of_detected_pair
    (M : ConvergentMap F g cx.toConvergence cy.toConvergence)
    (p : ℤ × ℤ) (s n : ℤ) (hn : 0 ≤ n)
    (x0 : (F.obj X).E₂ (s,p.1+s,p.2))
    (y0 : (F.obj Y).E₂ (s+n,p.1+(s+n),p.2))
    (a : BiHom p.1 p.2 X) (b : BiHom p.1 p.2 Y)
    (ha : Detects cx (s,p.1+s,p.2) x0 (homotopyRegrade (by dsimp; omega) rfl a))
    (hb : Detects cy (s+n,p.1+(s+n),p.2) y0 (homotopyRegrade (by dsimp; omega) rfl b))
    (hab : a ≫ g = b) :
    ∃ x y, HasInfinityRepresentative _ 2 _ x0 x ∧
      HasInfinityRepresentative _ 2 _ y0 y ∧ TowerExtensionEquation M p s n x y := by
  obtain ⟨x,hx,a',ha',hax⟩ := frame_of_source_detects cx p s x0 a ha
  obtain ⟨y,hy,b',hb',hby⟩ := frame_of_source_detects cy p (s+n) y0 b hb
  exact ⟨x,y,hx,hy,(tower_extension_iff M p s n x y).mpr
    ⟨hn,a',b',by rw [ha',hb']; exact hab,hax,hby⟩⟩

end Frames

end
end KIP126.ProofTools.Internal
