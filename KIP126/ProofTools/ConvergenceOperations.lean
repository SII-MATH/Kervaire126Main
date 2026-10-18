module

public import KIP126.AdamsSynthetic
import all KIP126.ProofTools.FiltrationOperations

/-! Element-level operations used by the retained stretching and Mahowald proofs.
The prescribed convergence and the actual map determine every graded equation.
Adapted from the pinned Kervaire126 proof sources (MIT; see LICENSE). -/

@[expose] section
set_option backward.isDefEq.respectTransparency false
namespace KIP126.ProofTools.Internal
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.Synthetic.SpectralSequence KIP126.AdamsSynthetic
open KIP126.Core.SpectralSequence
noncomputable section
universe u v
variable {Syn : Type u} [SyntheticCategory.{u,v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  {H : Syn} {unit : S_0_0 ⟶ H} {F : SyntheticAdamsFamily Syn}
  {P : SyntheticTowerPresentation unit F} {X Y : Syn} {g : X ⟶ Y}
  {cx : SyntheticTowerConvergence P X} {cy : SyntheticTowerConvergence P Y}

def infinityGradedIso (c : SyntheticTowerConvergence P X) (p : ℤ × ℤ) (s : ℤ) :
    ((F.obj X).sequence.ssData (s,p.1+s,p.2)).eInfty ≅
      (P.filtration X).associatedGraded s p :=
  c.identification (s,p.1+s,p.2) ≪≫ eqToIso (by simp)

theorem elementMap_injective {A : ModuleCat.{v} ℤ} :
    Function.Injective (elementMap (A := A)) := by
  intro a b h
  have h' := ConcreteCategory.congr_hom h (ULift.up (1 : ℤ))
  simpa [elementMap, one_smul] using h'

theorem toGraded_element (c : SyntheticTowerConvergence P X) (p : ℤ × ℤ) (s : ℤ)
    (x : ((F.obj X).sequence.ssData (s,p.1+s,p.2)).eInfty) :
    toGraded c.toConvergence (by simp [SyntheticTowerConvergence.toConvergence])
      (elementMap x) = elementMap ((infinityGradedIso c p s).hom x) := by
  rw [elementMap_comp]
  rfl

theorem tower_extension_iff
    (M : ConvergentMap F g cx.toConvergence cy.toConvergence)
    (p : ℤ × ℤ) (s n : ℤ)
    (x : ((F.obj X).sequence.ssData (s,p.1+s,p.2)).eInfty)
    (y : ((F.obj Y).sequence.ssData (s+n,p.1+(s+n),p.2)).eInfty) :
    TowerExtensionEquation M p s n x y ↔
      0 ≤ n ∧ ∃ (a : (Subobject.underlying.obj ((P.filtration X).F s p) : ModuleCat.{v} ℤ))
        (b : (Subobject.underlying.obj ((P.filtration Y).F (s+n) p) : ModuleCat.{v} ℤ)),
        ((P.filtration X).F s p).arrow a ≫ g = ((P.filtration Y).F (s+n) p).arrow b ∧
        (P.filtration X).toAssociatedGraded s p a = (infinityGradedIso cx p s).hom x ∧
        (P.filtration Y).toAssociatedGraded (s+n) p b = (infinityGradedIso cy p (s+n)).hom y := by
  unfold TowerExtensionEquation
  rw [M.extensionEquation_iff]
  simp only [toGraded_element]
  constructor
  · rintro ⟨hn,a,b,ha,hb,he⟩
    refine ⟨hn,a (ULift.up 1),b (ULift.up 1),?_,?_,?_⟩
    · exact ConcreteCategory.congr_hom he (ULift.up 1)
    · simpa [elementMap, one_smul] using ConcreteCategory.congr_hom ha (ULift.up (1 : ℤ))
    · simpa [elementMap, one_smul] using ConcreteCategory.congr_hom hb (ULift.up (1 : ℤ))
  · rintro ⟨hn,a,b,he,ha,hb⟩
    refine ⟨hn,elementMap a,elementMap b,?_,?_,?_⟩
    · rw [← elementMap_comp,ha]
    · rw [← elementMap_comp,hb]
    · rw [← Category.assoc,← elementMap_comp,← elementMap_comp,← elementMap_comp]
      exact congrArg elementMap he

theorem filtration_representative_exists (P : SyntheticTowerPresentation unit F)
    (A : Syn) (p : ℤ × ℤ) (s : ℤ) (a : BiHom p.1 p.2 A)
    (ha : a ∈ P.filtrationSubmodule A s p) :
    ∃ a' : (Subobject.underlying.obj ((P.filtration A).F s p) : ModuleCat.{v} ℤ),
      ((P.filtration A).F s p).arrow a' = a := by
  have hm : a ∈ ModuleCat.subobjectModule _ ((P.filtration A).F s p) := by
    simpa [SyntheticTowerPresentation.filtration, syntheticHomotopy] using ha
  exact hm

theorem map_preserves_filtration
    (M : ConvergentMap F g cx.toConvergence cy.toConvergence)
    (p : ℤ × ℤ) (s : ℤ) (a : BiHom p.1 p.2 X)
    (ha : a ∈ P.filtrationSubmodule X s p) :
    a ≫ g ∈ P.filtrationSubmodule Y s p := by
  obtain ⟨a',ha'⟩ := filtration_representative_exists P X p s a ha
  have h := ConcreteCategory.congr_hom (M.filteredMap.compat s p).choose_spec a'
  have hm : a ≫ g ∈ ModuleCat.subobjectModule _ ((P.filtration Y).F s p) := by
    refine ⟨(M.filteredMap.compat s p).choose a',?_⟩
    change ((P.filtration Y).F s p).arrow ((M.filteredMap.compat s p).choose a') = a ≫ g
    change ((P.filtration Y).F s p).arrow ((M.filteredMap.compat s p).choose a') =
      M.filteredMap.map p (((P.filtration X).F s p).arrow a') at h
    have hh := ConcreteCategory.congr_hom (M.filteredMap_map p)
      (((P.filtration X).F s p).arrow a')
    change M.filteredMap.map p (((P.filtration X).F s p).arrow a') =
      ((P.filtration X).F s p).arrow a' ≫ g at hh
    exact h.trans (hh.trans (congrArg (fun z => z ≫ g) ha'))
  simpa [SyntheticTowerPresentation.filtration, syntheticHomotopy] using hm

theorem infinity_graded_naturality
    (M : ConvergentMap F g cx.toConvergence cy.toConvergence)
    (p : ℤ × ℤ) (s : ℤ) :
    (infinityGradedIso cx p s).hom ≫ M.filteredMap.inducedGrMap s p =
      (F.functor.map g).eInftyMap (s,p.1+s,p.2) ≫ (infinityGradedIso cy p s).hom := by
  have h := M.infinity_action_graded (s,p.1+s,p.2)
  have transport {ι : Type} (A B : ι → ModuleCat.{v} ℤ)
      (f : ∀ i, A i ⟶ B i) {i j : ι} (hij : i=j)
      {U V : ModuleCat.{v} ℤ} (a : U ⟶ A i) (b : V ⟶ B i)
      (q : U ⟶ V) (hq : a ≫ f i = q ≫ b) :
      (a ≫ eqToHom (congrArg A hij)) ≫ f j =
        q ≫ (b ≫ eqToHom (congrArg B hij)) := by
    subst j
    simpa only [eqToHom_refl,Category.comp_id] using hq
  exact transport
    (fun p => (P.filtration X).associatedGraded s p)
    (fun p => (P.filtration Y).associatedGraded s p)
    (fun p => M.filteredMap.inducedGrMap s p)
    (show (p.1+s-s,p.2)=p by ext <;> simp) _ _ _ h

theorem infinity_image_iff_lift
    (M : ConvergentMap F g cx.toConvergence cy.toConvergence)
    (p : ℤ × ℤ) (s : ℤ)
    (x : (Subobject.underlying.obj ((P.filtration Y).F s p) : ModuleCat.{v} ℤ)) :
    (infinityGradedIso cy p s).inv ((P.filtration Y).toAssociatedGraded s p x) ∈
      Set.range ((F.functor.map g).eInftyMap (s,p.1+s,p.2)).hom ↔
    ∃ a : BiHom p.1 p.2 X, a ∈ P.filtrationSubmodule X s p ∧
      @HSub.hSub (BiHom p.1 p.2 Y) (BiHom p.1 p.2 Y) (BiHom p.1 p.2 Y)
        inferInstance (((P.filtration Y).F s p).arrow x) (a ≫ g) ∈
        P.filtrationSubmodule Y (s+1) p := by
  have hn := infinity_graded_naturality M p s
  have hi : (∃ z, (F.functor.map g).eInftyMap (s,p.1+s,p.2) z =
      (infinityGradedIso cy p s).inv ((P.filtration Y).toAssociatedGraded s p x)) ↔
      ∃ z, M.filteredMap.inducedGrMap s p z = (P.filtration Y).toAssociatedGraded s p x := by
    constructor
    · rintro ⟨z,hz⟩
      refine ⟨(infinityGradedIso cx p s).hom z,?_⟩
      have he := ConcreteCategory.congr_hom hn z
      change M.filteredMap.inducedGrMap s p ((infinityGradedIso cx p s).hom z) =
        (infinityGradedIso cy p s).hom ((F.functor.map g).eInftyMap (s,p.1+s,p.2) z) at he
      rw [hz] at he
      exact he.trans ((infinityGradedIso cy p s).toLinearEquiv.apply_symm_apply _)
    · rintro ⟨z,hz⟩
      refine ⟨(infinityGradedIso cx p s).inv z,?_⟩
      apply (infinityGradedIso cy p s).toLinearEquiv.injective
      have he := ConcreteCategory.congr_hom hn ((infinityGradedIso cx p s).inv z)
      simp only [ModuleCat.comp_apply] at he
      have ha := (infinityGradedIso cx p s).toLinearEquiv.apply_symm_apply z
      change (infinityGradedIso cx p s).hom ((infinityGradedIso cx p s).inv z) = z at ha
      rw [ha,hz] at he
      exact he.symm.trans ((infinityGradedIso cy p s).toLinearEquiv.apply_symm_apply _).symm
  change (∃ z, _ = _) ↔ _
  refine hi.trans ((graded_image_iff_lift M.filteredMap s p x).trans ?_)
  simp only [ConvergentMap.filteredMap_map,SyntheticTowerPresentation.filtration,
    OrderIso.apply_symm_apply]
  rfl

theorem next_filtration_of_infinity_injective
    (M : ConvergentMap F g cx.toConvergence cy.toConvergence)
    (p : ℤ × ℤ) (s : ℤ)
    (hf : Function.Injective ((F.functor.map g).eInftyMap (s,p.1+s,p.2)).hom)
    (a : BiHom p.1 p.2 X) (ha : a ∈ P.filtrationSubmodule X s p)
    (hb : a ≫ g ∈ P.filtrationSubmodule Y (s+1) p) :
    a ∈ P.filtrationSubmodule X (s+1) p := by
  have hn := infinity_graded_naturality M p s
  have hmono : Mono (M.filteredMap.inducedGrMap s p) := by
    rw [ModuleCat.mono_iff_injective]
    intro x y hxy
    have he (z : (P.filtration X).associatedGraded s p) :
        M.filteredMap.inducedGrMap s p z =
        (infinityGradedIso cy p s).hom
          ((F.functor.map g).eInftyMap (s,p.1+s,p.2) ((infinityGradedIso cx p s).inv z)) := by
      have h := ConcreteCategory.congr_hom hn ((infinityGradedIso cx p s).inv z)
      simp only [ModuleCat.comp_apply] at h
      have hc := (infinityGradedIso cx p s).toLinearEquiv.apply_symm_apply z
      change (infinityGradedIso cx p s).hom ((infinityGradedIso cx p s).inv z) = z at hc
      rwa [hc] at h
    rw [he,he] at hxy
    exact (infinityGradedIso cx p s).symm.toLinearEquiv.injective
      (hf ((infinityGradedIso cy p s).toLinearEquiv.injective hxy))
  have h := next_filtration_mem_of_graded_mono M.filteredMap s p a
  simp only [SyntheticTowerPresentation.filtration,OrderIso.apply_symm_apply,
    ConvergentMap.filteredMap_map] at h
  exact h ha hb

theorem representative_grade_naturality
    (M : ConvergentMap F g cx.toConvergence cy.toConvergence)
    (p : ℤ × ℤ) (s : ℤ)
    (a : (Subobject.underlying.obj ((P.filtration X).F s p) : ModuleCat.{v} ℤ))
    (b : (Subobject.underlying.obj ((P.filtration Y).F s p) : ModuleCat.{v} ℤ))
    (hab : ((P.filtration X).F s p).arrow a ≫ g = ((P.filtration Y).F s p).arrow b) :
    (infinityGradedIso cy p s).inv ((P.filtration Y).toAssociatedGraded s p b) =
      (F.functor.map g).eInftyMap (s,p.1+s,p.2)
        ((infinityGradedIso cx p s).inv ((P.filtration X).toAssociatedGraded s p a)) := by
  have hb : (M.filteredMap.compat s p).choose a = b := by
    apply (ModuleCat.mono_iff_injective ((P.filtration Y).F s p).arrow).mp inferInstance
    have h := ConcreteCategory.congr_hom (M.filteredMap.compat s p).choose_spec a
    change ((P.filtration Y).F s p).arrow ((M.filteredMap.compat s p).choose a) =
      M.filteredMap.map p (((P.filtration X).F s p).arrow a) at h
    have hh := ConcreteCategory.congr_hom (M.filteredMap_map p)
      (((P.filtration X).F s p).arrow a)
    change M.filteredMap.map p (((P.filtration X).F s p).arrow a) =
      ((P.filtration X).F s p).arrow a ≫ g at hh
    exact h.trans (hh.trans hab)
  have hp := graded_map_representative M.filteredMap s p a
  rw [hb] at hp
  apply (infinityGradedIso cy p s).toLinearEquiv.injective
  have he := ConcreteCategory.congr_hom (infinity_graded_naturality M p s)
    ((infinityGradedIso cx p s).inv ((P.filtration X).toAssociatedGraded s p a))
  simp only [ModuleCat.comp_apply] at he
  have hA := (infinityGradedIso cx p s).toLinearEquiv.apply_symm_apply
    ((P.filtration X).toAssociatedGraded s p a)
  have hB := (infinityGradedIso cy p s).toLinearEquiv.apply_symm_apply
    ((P.filtration Y).toAssociatedGraded s p b)
  exact hB.trans (hp.symm.trans ((congrArg (M.filteredMap.inducedGrMap s p) hA.symm).trans he))

theorem grade_difference
    (M : ConvergentMap F g cx.toConvergence cy.toConvergence)
    (p : ℤ × ℤ) (s : ℤ)
    (a : (Subobject.underlying.obj ((P.filtration X).F s p) : ModuleCat.{v} ℤ))
    (b : (Subobject.underlying.obj ((P.filtration Y).F s p) : ModuleCat.{v} ℤ))
    (he : (F.functor.map g).eInftyMap (s,p.1+s,p.2)
      ((infinityGradedIso cx p s).inv ((P.filtration X).toAssociatedGraded s p a)) =
      (infinityGradedIso cy p s).inv ((P.filtration Y).toAssociatedGraded s p b)) :
    @HSub.hSub (BiHom p.1 p.2 Y) (BiHom p.1 p.2 Y) (BiHom p.1 p.2 Y)
      inferInstance (((P.filtration Y).F s p).arrow b)
      (((P.filtration X).F s p).arrow a ≫ g) ∈
      P.filtrationSubmodule Y (s+1) p := by
  let b' := (M.filteredMap.compat s p).choose a
  have hb' : ((P.filtration Y).F s p).arrow b' = ((P.filtration X).F s p).arrow a ≫ g := by
    have h := ConcreteCategory.congr_hom (M.filteredMap.compat s p).choose_spec a
    change ((P.filtration Y).F s p).arrow b' =
      M.filteredMap.map p (((P.filtration X).F s p).arrow a) at h
    rw [ConvergentMap.filteredMap_map] at h
    exact h
  have hh := representative_grade_naturality M p s a b' hb'.symm
  have heq := (infinityGradedIso cy p s).symm.toLinearEquiv.injective (he.symm.trans hh.symm)
  have hm := (element_grade_equal_iff (P.filtration Y) s p b b').mp heq
  rw [hb'] at hm
  simpa only [SyntheticTowerPresentation.filtration,OrderIso.apply_symm_apply,
    syntheticHomotopy] using hm

end
end KIP126.ProofTools.Internal
