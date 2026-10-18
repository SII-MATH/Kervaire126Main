module
import all KIP126.ProofTools.FiniteFiltration
import all KIP126.ProofTools.ConvergenceOperations
/-! Finite filtration correction and actual extension-square representatives.
ProofTools-private implementation of the representative argument in AimPaper
Proposition `prop:i8r47oe` and Corollary `cor:0012nik`;
no completion or bounded ESS is used. -/

@[expose] section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace KIP126.ProofTools.Internal.Leibniz
noncomputable section

/-- Raising the source filtration terminates at the target filtration.
The correction premise is exactly nonessentiality of the fixed target grade. -/
private theorem higher_source_image_of_nonessential
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (f : A →+ B) (F : ℤ → AddSubgroup A) (G : ℤ → AddSubgroup B)
    (hG : Antitone G)
    (hf : ∀ u a, a ∈ F u → f a ∈ G u)
    (s t : ℤ) (hst : s ≤ t)
    (hcorrect : ∀ u, s < u → u ≤ t → ∀ a, a ∈ F u → f a ∈ G t →
      ∃ b, b ∈ F u ∧ a - b ∈ F (u + 1) ∧ f b ∈ G (t + 1))
    (a : A) (ha : a ∈ F (s + 1)) (hfa : f a ∈ G t) :
    f a ∈ G (t + 1) := by
  have aux : ∀ N : ℕ, ∀ u : ℤ, s < u → u + N = t + 1 →
      ∀ a, a ∈ F u → f a ∈ G t → f a ∈ G (t + 1) := by
    intro N
    induction N with
    | zero =>
      intro u hu he a ha hfa
      have hut : u = t + 1 := by omega
      subst u
      exact hf _ _ ha
    | succ N ih =>
      intro u hu he a ha hfa
      obtain ⟨b, hb, hab, hfb⟩ := hcorrect u hu (by omega) a ha hfa
      have hsub : f (a - b) ∈ G t := by
        rw [map_sub]
        exact (G t).sub_mem hfa (hG (by omega) hfb)
      have hh := ih (u + 1) (by omega) (by omega) (a - b) hab hsub
      have h := (G (t + 1)).add_mem hh hfb
      simpa only [map_sub, sub_add_cancel] using h
  exact aux (t - s).toNat (s + 1) (by omega) (by omega) a ha hfa

/-- A finite interval of essential-crossing exclusions makes every higher-source
correction invisible at the selected target grade. No completion is used. -/
private theorem higher_source_image_of_no_crossing
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (f : A →+ B) (F : ℤ → AddSubgroup A) (G : ℤ → AddSubgroup B)
    (hG : Antitone G)
    (hf : ∀ u a, a ∈ F u → f a ∈ G u)
    (s n : ℤ) (hn : 0 ≤ n)
    (hcorrect : ∀ u v, s < u → u ≤ v → v ≤ s + n →
      ∀ a, a ∈ F u → f a ∈ G v →
        ∃ b, b ∈ F u ∧ a - b ∈ F (u + 1) ∧ f b ∈ G (v + 1))
    (a : A) (ha : a ∈ F (s + 1)) : f a ∈ G (s + n + 1) := by
  by_contra hnot
  obtain ⟨v, hv, hvn, hva, hvnext⟩ :=
    first_nonzero_filtration_grade G (s + 1) n.toNat (f a)
      (hf _ _ ha) (by simpa only [Int.toNat_of_nonneg hn, add_assoc, add_comm, add_left_comm] using hnot)
  apply hvnext
  exact higher_source_image_of_nonessential f F G hG hf s v (by omega)
    (fun u hsu huv => hcorrect u v hsu huv (by omega)) a ha hva

/-- The image of every representative has the same target grade once all
higher-source corrections have zero target grade. -/
private theorem image_same_target_of_no_crossing
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (f : A →+ B) (F : ℤ → AddSubgroup A) (G : ℤ → AddSubgroup B)
    (hG : Antitone G)
    (hf : ∀ u a, a ∈ F u → f a ∈ G u)
    (s n : ℤ) (hn : 0 ≤ n)
    (hcorrect : ∀ u v, s < u → u ≤ v → v ≤ s + n →
      ∀ a, a ∈ F u → f a ∈ G v →
        ∃ b, b ∈ F u ∧ a - b ∈ F (u + 1) ∧ f b ∈ G (v + 1))
    (a a₀ : A) (hrep : a - a₀ ∈ F (s + 1)) :
    f a - f a₀ ∈ G (s + n + 1) := by
  simpa only [map_sub] using
    higher_source_image_of_no_crossing f F G hG hf s n hn hcorrect (a-a₀) hrep

section Tower
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
universe u v
variable {Syn : Type u} [SyntheticCategory.{u,v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  {H : Syn} {unit : S_0_0 ⟶ H} {E : SyntheticAdamsFamily Syn}
  {P : SyntheticTowerPresentation unit E} {X Y : Syn} {g : X ⟶ Y}
  {cx : SyntheticTowerConvergence P X} {cy : SyntheticTowerConvergence P Y}

private theorem tower_essential_iff_no_zero
    (M : ConvergentMap E g cx.toConvergence cy.toConvergence)
    (p : ℤ × ℤ) (s n : ℤ)
    (x : ((E.obj X).sequence.ssData (s,p.1+s,p.2)).eInfty)
    (y : ((E.obj Y).sequence.ssData (s+n,p.1+(s+n),p.2)).eInfty)
    (he : TowerExtensionEquation M p s n x y) :
    TowerEssentialExtension M p s n x y ↔
      ¬TowerExtensionEquation M p s n x 0 := by
  have h0 {A : ModuleCat.{v} ℤ} : elementMap (0 : A) = 0 := by
    ext z
    simp [elementMap]
  simpa only [TowerEssentialExtension, TowerExtensionEquation, h0] using
    M.essential_iff_no_zero_target p s n
      (by simp [SyntheticTowerConvergence.toConvergence])
      (by simp [SyntheticTowerConvergence.toConvergence]) (elementMap x) (elementMap y) he

/-- Nonessentiality supplies a representative with the same leading source
and zero leading target; the difference raises the source filtration. -/
private theorem tower_correction_of_nonessential
    (M : ConvergentMap E g cx.toConvergence cy.toConvergence)
    (p : ℤ × ℤ) (s n : ℤ) (hn : 0 ≤ n)
    (hnot : ∀ x y, ¬TowerEssentialExtension M p s n x y)
    (a : BiHom p.1 p.2 X) (ha : a ∈ P.filtrationSubmodule X s p)
    (hfa : a ≫ g ∈ P.filtrationSubmodule Y (s+n) p) :
    ∃ b, b ∈ P.filtrationSubmodule X s p ∧
      a-b ∈ P.filtrationSubmodule X (s+1) p ∧
      b ≫ g ∈ P.filtrationSubmodule Y (s+n+1) p := by
  obtain ⟨ar, har⟩ := filtration_representative_exists P X p s a ha
  obtain ⟨br, hbr⟩ := filtration_representative_exists P Y p (s+n) (a≫g) hfa
  let x := (infinityGradedIso cx p s).inv ((P.filtration X).toAssociatedGraded s p ar)
  let y := (infinityGradedIso cy p (s+n)).inv ((P.filtration Y).toAssociatedGraded (s+n) p br)
  have hx : (P.filtration X).toAssociatedGraded s p ar = (infinityGradedIso cx p s).hom x :=
    ((infinityGradedIso cx p s).toLinearEquiv.apply_symm_apply _).symm
  have hy : (P.filtration Y).toAssociatedGraded (s+n) p br = (infinityGradedIso cy p (s+n)).hom y :=
    ((infinityGradedIso cy p (s+n)).toLinearEquiv.apply_symm_apply _).symm
  have he : TowerExtensionEquation M p s n x y :=
    (tower_extension_iff M p s n x y).mpr ⟨hn, ar, br, by rw [har,hbr], hx,hy⟩
  have he0 : TowerExtensionEquation M p s n x 0 := by
    by_contra hz
    exact hnot x y ((tower_essential_iff_no_zero M p s n x y he).mpr hz)
  obtain ⟨_,ar',br',he',hx',hy'⟩ := (tower_extension_iff M p s n x 0).mp he0
  let b := ((P.filtration X).F s p).arrow ar'
  refine ⟨b, ?_, ?_, ?_⟩
  · have hh : b ∈ ModuleCat.subobjectModule _ ((P.filtration X).F s p) := ⟨ar',rfl⟩
    simpa only [SyntheticTowerPresentation.filtration,OrderIso.apply_symm_apply] using hh
  · have hh := (element_grade_equal_iff (P.filtration X) s p ar ar').mp (hx.trans hx'.symm)
    rw [har] at hh
    simpa only [b,SyntheticTowerPresentation.filtration,OrderIso.apply_symm_apply] using hh
  · have hh := (element_grade_equal_iff (P.filtration Y) (s+n) p br' 0).mp (by
      rw [hy']; simp only [map_zero])
    have hz : ((P.filtration Y).F (s+n) p).arrow (0 : (Subobject.underlying.obj ((P.filtration Y).F (s+n) p) : ModuleCat.{v} ℤ)) = 0 := map_zero _
    rw [hz,sub_zero,←he'] at hh
    simpa only [b,SyntheticTowerPresentation.filtration,OrderIso.apply_symm_apply] using hh

/-- Absence of essential higher-source extensions on the finite triangle
forces all choices of a source representative to have the same target grade. -/
private theorem tower_image_same_target_of_no_crossing
    (M : ConvergentMap E g cx.toConvergence cy.toConvergence)
    (p : ℤ × ℤ) (s n : ℤ) (hn : 0 ≤ n)
    (hnot : ∀ u v : ℤ, s < u → u ≤ v → v ≤ s+n →
      ∀ x y, ¬TowerEssentialExtension M p u (v-u) x y)
    (a a₀ : BiHom p.1 p.2 X)
    (ha : a-a₀ ∈ P.filtrationSubmodule X (s+1) p) :
    a≫g - a₀≫g ∈ P.filtrationSubmodule Y (s+n+1) p := by
  let F : ℤ → AddSubgroup (BiHom p.1 p.2 X) := fun s => (P.filtrationSubmodule X s p).toAddSubgroup
  let G : ℤ → AddSubgroup (BiHom p.1 p.2 Y) := fun s => (P.filtrationSubmodule Y s p).toAddSubgroup
  let f : BiHom p.1 p.2 X →+ BiHom p.1 p.2 Y := (syntheticHomotopyMap g p).hom.toAddMonoidHom
  apply image_same_target_of_no_crossing f F G
    (fun i j hij a ha => P.filtrationSubmodule_antitone Y p hij ha)
    (fun u a ha => map_preserves_filtration M p u a ha) s n hn ?_ a a₀ ha
  intro u v hsu huv hvs a ha hfa
  have huv' : u + (v-u) = v := by omega
  change a ≫ g ∈ P.filtrationSubmodule Y v p at hfa
  change ∃ b, b ∈ P.filtrationSubmodule X u p ∧ a-b ∈ P.filtrationSubmodule X (u+1) p ∧ b ≫ g ∈ P.filtrationSubmodule Y (v+1) p
  have hh := tower_correction_of_nonessential M p u (v-u) (by omega)
    (hnot u v hsu huv hvs) a ha (by simpa only [huv', f, G, syntheticHomotopyMap] using hfa)
  simpa only [huv',f,F,G,syntheticHomotopyMap] using hh

/-- Every representative of a fixed source grade has the prescribed target
when the extension has no essential crossing. -/
private theorem tower_target_of_any_source_frame
    (M : ConvergentMap E g cx.toConvergence cy.toConvergence)
    (p : ℤ × ℤ) (s n : ℤ)
    (x : ((E.obj X).sequence.ssData (s,p.1+s,p.2)).eInfty)
    (y : ((E.obj Y).sequence.ssData (s+n,p.1+(s+n),p.2)).eInfty)
    (he : TowerExtensionEquation M p s n x y)
    (hnot : ∀ u v : ℤ, s < u → u ≤ v → v ≤ s+n →
      ∀ x y, ¬TowerEssentialExtension M p u (v-u) x y)
    (ar : (Subobject.underlying.obj ((P.filtration X).F s p) : ModuleCat.{v} ℤ))
    (har : (P.filtration X).toAssociatedGraded s p ar = (infinityGradedIso cx p s).hom x) :
    ∃ br : (Subobject.underlying.obj ((P.filtration Y).F (s+n) p) : ModuleCat.{v} ℤ),
      ((P.filtration X).F s p).arrow ar ≫ g = ((P.filtration Y).F (s+n) p).arrow br ∧
      (P.filtration Y).toAssociatedGraded (s+n) p br = (infinityGradedIso cy p (s+n)).hom y := by
  obtain ⟨hn,ar₀,br₀,he₀,hx₀,hy₀⟩ := (tower_extension_iff M p s n x y).mp he
  have hsource := (element_grade_equal_iff (P.filtration X) s p ar ar₀).mp (har.trans hx₀.symm)
  have hsource' : ((P.filtration X).F s p).arrow ar -
      ((P.filtration X).F s p).arrow ar₀ ∈ P.filtrationSubmodule X (s+1) p := by
    simpa only [SyntheticTowerPresentation.filtration,OrderIso.apply_symm_apply] using hsource
  have hdiff := tower_image_same_target_of_no_crossing M p s n hn hnot _ _ hsource'
  rw [he₀] at hdiff
  have hb₀ : ((P.filtration Y).F (s+n) p).arrow br₀ ∈ P.filtrationSubmodule Y (s+n) p := by
    have hh : ((P.filtration Y).F (s+n) p).arrow br₀ ∈
        ModuleCat.subobjectModule _ ((P.filtration Y).F (s+n) p) := ⟨br₀,rfl⟩
    simpa only [SyntheticTowerPresentation.filtration,OrderIso.apply_symm_apply] using hh
  have hb : ((P.filtration X).F s p).arrow ar ≫ g ∈ P.filtrationSubmodule Y (s+n) p := by
    have hh := (P.filtrationSubmodule Y (s+n) p).add_mem
      (P.filtrationSubmodule_antitone Y p (show s+n≤s+n+1 by omega) hdiff) hb₀
    simpa only [sub_add_cancel] using hh
  obtain ⟨br,hbr⟩ := filtration_representative_exists P Y p (s+n) _ hb
  refine ⟨br,hbr.symm,?_⟩
  have hdiff' : ((P.filtration Y).F (s+n) p).arrow br -
      ((P.filtration Y).F (s+n) p).arrow br₀ ∈
        ModuleCat.subobjectModule _ ((P.filtration Y).F (s+n+1) p) := by
    rw [hbr]
    simpa only [SyntheticTowerPresentation.filtration,OrderIso.apply_symm_apply] using hdiff
  exact ((element_grade_equal_iff (P.filtration Y) (s+n) p br br₀).mpr hdiff').trans hy₀

/-- The actual higher-source triangle of essential extensions, at fixed stem
and synthetic weight. -/
private def TowerNoCrossing
    (M : ConvergentMap E g cx.toConvergence cy.toConvergence)
    (p : ℤ × ℤ) (s n : ℤ) : Prop :=
  ∀ u v : ℤ, s < u → u ≤ v → v ≤ s+n →
    ∀ x y, ¬TowerEssentialExtension M p u (v-u) x y

/-- A correction with the same source grade and a higher target filtration
excludes every essential extension in the specified crossing triangle. -/
private theorem tower_no_crossing_of_correction
    (M : ConvergentMap E g cx.toConvergence cy.toConvergence)
    (p : ℤ × ℤ) (s n : ℤ)
    (hcorrect : ∀ u v : ℤ, s < u → u ≤ v → v ≤ s+n →
      ∀ a : BiHom p.1 p.2 X, a ∈ P.filtrationSubmodule X u p →
        a ≫ g ∈ P.filtrationSubmodule Y v p →
        ∃ b, b ∈ P.filtrationSubmodule X u p ∧
          a-b ∈ P.filtrationSubmodule X (u+1) p ∧
          b ≫ g ∈ P.filtrationSubmodule Y (v+1) p) :
    TowerNoCrossing M p s n := by
  intro u v hsu huv hvs x y hess
  have he : TowerExtensionEquation M p u (v-u) x y := hess.1
  apply (tower_essential_iff_no_zero M p u (v-u) x y he).mp hess
  obtain ⟨hn,ar,br,heq,hx,hy⟩ := (tower_extension_iff M p u (v-u) x y).mp he
  let a := ((P.filtration X).F u p).arrow ar
  have ha : a ∈ P.filtrationSubmodule X u p := by
    have hm : a ∈ ModuleCat.subobjectModule _ ((P.filtration X).F u p) := ⟨ar,rfl⟩
    simpa only [SyntheticTowerPresentation.filtration,OrderIso.apply_symm_apply] using hm
  have hfa : a ≫ g ∈ P.filtrationSubmodule Y (u+(v-u)) p := by
    have hm : a ≫ g ∈ ModuleCat.subobjectModule _ ((P.filtration Y).F (u+(v-u)) p) :=
      ⟨br,heq.symm⟩
    simpa only [SyntheticTowerPresentation.filtration,OrderIso.apply_symm_apply] using hm
  obtain ⟨b,hb,hab,hbg⟩ := hcorrect u (u+(v-u)) hsu (by omega) (by omega) a ha hfa
  obtain ⟨ar',har'⟩ := filtration_representative_exists P X p u b hb
  have hbg' := P.filtrationSubmodule_antitone Y p (show u+(v-u)≤u+(v-u)+1 by omega) hbg
  obtain ⟨br',hbr'⟩ := filtration_representative_exists P Y p (u+(v-u)) (b≫g) hbg'
  apply (tower_extension_iff M p u (v-u) x 0).mpr
  refine ⟨hn,ar',br',by rw [har',hbr'],?_,?_⟩
  · have hdiff : ((P.filtration X).F u p).arrow ar -
        ((P.filtration X).F u p).arrow ar' ∈
        ModuleCat.subobjectModule _ ((P.filtration X).F (u+1) p) := by
      rw [har']
      simpa only [a,SyntheticTowerPresentation.filtration,OrderIso.apply_symm_apply] using hab
    exact ((element_grade_equal_iff (P.filtration X) u p ar ar').mpr hdiff).symm.trans hx
  · rw [map_zero]
    have hdiff : ((P.filtration Y).F (u+(v-u)) p).arrow br' -
        ((P.filtration Y).F (u+(v-u)) p).arrow
          (0 : (Subobject.underlying.obj ((P.filtration Y).F (u+(v-u)) p) : ModuleCat.{v} ℤ)) ∈
        ModuleCat.subobjectModule _ ((P.filtration Y).F (u+(v-u)+1) p) := by
      rw [hbr',map_zero,sub_zero]
      simpa only [SyntheticTowerPresentation.filtration,OrderIso.apply_symm_apply] using hbg
    have hgrade := (element_grade_equal_iff (P.filtration Y) (u+(v-u)) p br' 0).mpr hdiff
    simpa only [map_zero] using hgrade

private theorem square_frames
    {Z W : Syn}
    {cz : SyntheticTowerConvergence P Z} {cw : SyntheticTowerConvergence P W}
    {f : X ⟶ Y} {h : X ⟶ Z} {j : Z ⟶ W} {k : Y ⟶ W}
    (Mf : ConvergentMap E f cx.toConvergence cy.toConvergence)
    (Mh : ConvergentMap E h cx.toConvergence cz.toConvergence)
    (Mj : ConvergentMap E j cz.toConvergence cw.toConvergence)
    (hcomm : f ≫ k = h ≫ j)
    (p : ℤ × ℤ) (s n m l : ℤ)
    (x : ((E.obj X).sequence.ssData (s,p.1+s,p.2)).eInfty)
    (y : ((E.obj Y).sequence.ssData (s+n,p.1+(s+n),p.2)).eInfty)
    (z : ((E.obj Z).sequence.ssData (s+m,p.1+(s+m),p.2)).eInfty)
    (w : ((E.obj W).sequence.ssData (s+m+l,p.1+(s+m+l),p.2)).eInfty)
    (hf : TowerExtensionEquation Mf p s n x y)
    (hh : TowerExtensionEquation Mh p s m x z)
    (hj : TowerExtensionEquation Mj p (s+m) l z w)
    (hnc : TowerNoCrossing Mf p s n ∨ TowerNoCrossing Mh p s m)
    (hncj : TowerNoCrossing Mj p (s+m) l) :
    ∃ (ar : (Subobject.underlying.obj ((P.filtration X).F s p) : ModuleCat.{v} ℤ))
      (br : (Subobject.underlying.obj ((P.filtration Y).F (s+n) p) : ModuleCat.{v} ℤ))
      (cr : (Subobject.underlying.obj ((P.filtration Z).F (s+m) p) : ModuleCat.{v} ℤ))
      (dr : (Subobject.underlying.obj ((P.filtration W).F (s+m+l) p) : ModuleCat.{v} ℤ)),
      (P.filtration X).toAssociatedGraded s p ar = (infinityGradedIso cx p s).hom x ∧
      (P.filtration Y).toAssociatedGraded (s+n) p br = (infinityGradedIso cy p (s+n)).hom y ∧
      (P.filtration Z).toAssociatedGraded (s+m) p cr = (infinityGradedIso cz p (s+m)).hom z ∧
      (P.filtration W).toAssociatedGraded (s+m+l) p dr = (infinityGradedIso cw p (s+m+l)).hom w ∧
      ((P.filtration X).F s p).arrow ar ≫ f = ((P.filtration Y).F (s+n) p).arrow br ∧
      ((P.filtration X).F s p).arrow ar ≫ h = ((P.filtration Z).F (s+m) p).arrow cr ∧
      ((P.filtration Z).F (s+m) p).arrow cr ≫ j = ((P.filtration W).F (s+m+l) p).arrow dr ∧
      ((P.filtration Y).F (s+n) p).arrow br ≫ k = ((P.filtration W).F (s+m+l) p).arrow dr := by
  have hthree : ∃ (ar : (Subobject.underlying.obj ((P.filtration X).F s p) : ModuleCat.{v} ℤ))
      (br : (Subobject.underlying.obj ((P.filtration Y).F (s+n) p) : ModuleCat.{v} ℤ))
      (cr : (Subobject.underlying.obj ((P.filtration Z).F (s+m) p) : ModuleCat.{v} ℤ)),
      (P.filtration X).toAssociatedGraded s p ar = (infinityGradedIso cx p s).hom x ∧
      (P.filtration Y).toAssociatedGraded (s+n) p br = (infinityGradedIso cy p (s+n)).hom y ∧
      (P.filtration Z).toAssociatedGraded (s+m) p cr = (infinityGradedIso cz p (s+m)).hom z ∧
      ((P.filtration X).F s p).arrow ar ≫ f = ((P.filtration Y).F (s+n) p).arrow br ∧
      ((P.filtration X).F s p).arrow ar ≫ h = ((P.filtration Z).F (s+m) p).arrow cr := by
    rcases hnc with hnf | hnh
    · obtain ⟨_,ar,cr,he,ha,hc⟩ := (tower_extension_iff Mh p s m x z).mp hh
      obtain ⟨br,he',hb⟩ := tower_target_of_any_source_frame Mf p s n x y hf hnf ar ha
      exact ⟨ar,br,cr,ha,hb,hc,he',he⟩
    · obtain ⟨_,ar,br,he,ha,hb⟩ := (tower_extension_iff Mf p s n x y).mp hf
      obtain ⟨cr,he',hc⟩ := tower_target_of_any_source_frame Mh p s m x z hh hnh ar ha
      exact ⟨ar,br,cr,ha,hb,hc,he,he'⟩
  obtain ⟨ar,br,cr,ha,hb,hc,haf,hah⟩ := hthree
  obtain ⟨dr,hcj,hd⟩ := tower_target_of_any_source_frame Mj p (s+m) l z w hj hncj cr hc
  refine ⟨ar,br,cr,dr,ha,hb,hc,hd,haf,hah,hcj,?_⟩
  rw [←haf,Category.assoc,hcomm,←Category.assoc,hah,hcj]

private theorem tower_map_frame
    (M : ConvergentMap E g cx.toConvergence cy.toConvergence)
    (p : ℤ × ℤ) (s : ℤ)
    (x : ((E.obj X).sequence.ssData (s,p.1+s,p.2)).eInfty)
    (ar : (Subobject.underlying.obj ((P.filtration X).F s p) : ModuleCat.{v} ℤ))
    (ha : (P.filtration X).toAssociatedGraded s p ar = (infinityGradedIso cx p s).hom x) :
    ∃ br : (Subobject.underlying.obj ((P.filtration Y).F s p) : ModuleCat.{v} ℤ),
      ((P.filtration X).F s p).arrow ar ≫ g = ((P.filtration Y).F s p).arrow br ∧
      (P.filtration Y).toAssociatedGraded s p br = (infinityGradedIso cy p s).hom
        ((E.functor.map g).eInftyMap (s,p.1+s,p.2) x) := by
  let br := (M.filteredMap.compat s p).choose ar
  have hab : ((P.filtration X).F s p).arrow ar ≫ g = ((P.filtration Y).F s p).arrow br := by
    have h := ConcreteCategory.congr_hom (M.filteredMap.compat s p).choose_spec ar
    change ((P.filtration Y).F s p).arrow br = M.filteredMap.map p (((P.filtration X).F s p).arrow ar) at h
    rw [ConvergentMap.filteredMap_map] at h
    exact h.symm
  refine ⟨br,hab,?_⟩
  have h := representative_grade_naturality M p s ar br hab
  rw [ha] at h
  have hx : (infinityGradedIso cx p s).inv ((infinityGradedIso cx p s).hom x) = x :=
    (infinityGradedIso cx p s).toLinearEquiv.symm_apply_apply x
  rw [hx] at h
  exact ((infinityGradedIso cy p s).toLinearEquiv.apply_symm_apply _).symm.trans
    (congrArg (infinityGradedIso cy p s).hom h)

private theorem tower_extension_map
    {X' Y' : Syn}
    {cx' : SyntheticTowerConvergence P X'} {cy' : SyntheticTowerConvergence P Y'}
    {g' : X' ⟶ Y'} {a : X ⟶ X'} {b : Y ⟶ Y'}
    (M : ConvergentMap E g cx.toConvergence cy.toConvergence)
    (M' : ConvergentMap E g' cx'.toConvergence cy'.toConvergence)
    (Ma : ConvergentMap E a cx.toConvergence cx'.toConvergence)
    (Mb : ConvergentMap E b cy.toConvergence cy'.toConvergence)
    (hcomm : g ≫ b = a ≫ g')
    (p : ℤ × ℤ) (s n : ℤ)
    (x : ((E.obj X).sequence.ssData (s,p.1+s,p.2)).eInfty)
    (y : ((E.obj Y).sequence.ssData (s+n,p.1+(s+n),p.2)).eInfty)
    (he : TowerExtensionEquation M p s n x y) :
    TowerExtensionEquation M' p s n
      ((E.functor.map a).eInftyMap (s,p.1+s,p.2) x)
      ((E.functor.map b).eInftyMap (s+n,p.1+(s+n),p.2) y) := by
  obtain ⟨hn,ar,br,hab,ha,hb⟩ := (tower_extension_iff M p s n x y).mp he
  obtain ⟨ar',haa,ha'⟩ := tower_map_frame Ma p s x ar ha
  obtain ⟨br',hbb,hb'⟩ := tower_map_frame Mb p (s+n) y br hb
  apply (tower_extension_iff M' p s n _ _).mpr
  refine ⟨hn,ar',br',?_,ha',hb'⟩
  rw [←haa,Category.assoc,←hcomm,←Category.assoc,hab,hbb]

end Tower
end
end KIP126.ProofTools.Internal.Leibniz
