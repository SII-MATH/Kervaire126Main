module

public import KIP126.ProofTools.FiniteFiltration
public import KIP126.ProofTools.Laws
import all KIP126.ProofTools.FiltrationOperations
import all KIP126.ProofTools.ConvergenceOperations
import all KIP126.ProofTools.StretchingRepresentatives

/-! Finite stretching: the proved finite correction argument from the pinned
PageExtensionStretching/Proofs.lean, using the public tower and convergence API.
The same correction proof includes zero length and zero representatives.
Source: bbac1fc05843 (MIT; see LICENSE and metadata/proof-tools-sources.json). -/

@[expose] section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace KIP126.ProofTools.Standard
open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.AdamsSynthetic.Standard
open KIP126.ProofTools.Internal
noncomputable section

/-- Finite stretching with the original layer-preserving no-crossing condition.
No infinite completion or compatible tower of strict lifts is asserted. -/
public theorem finitePageExtensionStretching
    (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary) :
    FinitePageExtensionStretchingLaw model X Y f := by
  classical
  intro rEarlier rLater n s t x y hr hle hn hnUpper hx hy hW hcross
  have hn0 : 0 ≤ n := le_trans (by exact_mod_cast Nat.zero_le (normalizedExponent model.classicalTower f)) hn
  let p : ℤ × ℤ := (t - s, t + normalizedExponent model.classicalTower f)
  let Aearly := (SyntheticObject.quotient (rEarlier - 1)
    (extensionSourceObject model X Y f)).obj model.nu model.auxiliary
  let Alater := (SyntheticObject.quotient (rLater - 1)
    (extensionSourceObject model X Y f)).obj model.nu model.auxiliary
  let Bearly := (SyntheticObject.quotient (rEarlier - 1) (.nu Y)).obj model.nu model.auxiliary
  let E : ℤ → AddSubgroup (BiHom p.1 p.2 Aearly) :=
    fun k => (model.syntheticTower.filtrationSubmodule Aearly k p).toAddSubgroup
  let L : ℤ → AddSubgroup (BiHom p.1 p.2 Alater) :=
    fun k => (model.syntheticTower.filtrationSubmodule Alater k p).toAddSubgroup
  let F : ℤ → AddSubgroup (BiHom p.1 p.2 Bearly) :=
    fun k => (model.syntheticTower.filtrationSubmodule Bearly k p).toAddSubgroup
  let T := F (s + n + 1)
  let ρ : BiHom p.1 p.2 Alater →+ BiHom p.1 p.2 Aearly :=
    (syntheticHomotopyMap
      ((model.quotients.tower ((extensionSourceObject model X Y f).obj model.nu model.auxiliary)).rho
        (rEarlier - 1) (rLater - 1) (Nat.sub_le_sub_right hle 1)) p).hom.toAddMonoidHom
  let g : BiHom p.1 p.2 Aearly →+ BiHom p.1 p.2 Bearly :=
    (syntheticHomotopyMap (finiteExtensionMap model X Y f (rEarlier - 1)) p).hom.toAddMonoidHom
  have hL : Antitone L := by
    intro i j hij z hz
    exact model.syntheticTower.filtrationSubmodule_antitone Alater p hij hz
  have actual_map_preserves (A B : SyntheticObject)
      (h : A.obj model.nu model.auxiliary ⟶ B.obj model.nu model.auxiliary) (k : ℤ)
      (z : BiHom p.1 p.2 (A.obj model.nu model.auxiliary))
      (hz : z ∈ model.syntheticTower.filtrationSubmodule (A.obj model.nu model.auxiliary) k p) :
      z ≫ h ∈ model.syntheticTower.filtrationSubmodule (B.obj model.nu model.auxiliary) k p :=
    map_preserves_filtration (model.convergentMap A B h) p k z hz
  have hg : ∀ k : ℤ, ∀ δ : BiHom p.1 p.2 Aearly, δ ∈ E k → g δ ∈ F k := by
    intro k δ hδ
    exact actual_map_preserves (.quotient (rEarlier-1) (extensionSourceObject model X Y f))
      (.quotient (rEarlier-1) (.nu Y)) (finiteExtensionMap model X Y f (rEarlier - 1)) k δ hδ
  have hstep : ∀ k : ℤ, s + 1 ≤ k → k < s + 1 + n.toNat →
      ∀ δ : BiHom p.1 p.2 Aearly, δ ∈ E k →
      (∃ ε : BiHom p.1 p.2 Alater, ε ∈ L k ∧ δ - ρ ε ∈ E (k + 1)) ∨ g δ ∈ T := by
    intro k hk hkn δ hδ
    by_cases hlift : ∃ ε : BiHom p.1 p.2 Alater, ε ∈ L k ∧ δ - ρ ε ∈ E (k + 1)
    · exact Or.inl hlift
    right
    by_contra hnot
    have hlast : k + ((s + n + 1 - k).toNat : ℤ) = s + n + 1 := by omega
    obtain ⟨l, hkl, hln, hgl, hgnext⟩ := first_nonzero_filtration_grade F k
      (s + n + 1 - k).toNat (g δ) (hg k δ hδ) (by simpa only [hlast] using hnot)
    apply hcross
    have module_map_zero {A B : ModuleCat ℤ} (f : A ⟶ B) : f (0 : A) = 0 := f.hom.map_zero
    have hln' : l ≤ s + n := by omega
    obtain ⟨a, hka⟩ : ∃ a : ℕ, k = s + a :=
      ⟨(k-s).toNat, by omega⟩
    subst k
    have ha : 0 < a := by omega
    obtain ⟨b, hl⟩ : ∃ b : ℕ, l = s + a + (n-a-b) :=
      ⟨(s+n-l).toNat, by omega⟩
    subst l
    have hab : (a : ℤ) + b ≤ n := by omega
    obtain ⟨da, hda⟩ := filtration_representative_exists model.syntheticTower Aearly p (s+a) δ hδ
    obtain ⟨db, hdb⟩ := filtration_representative_exists model.syntheticTower Bearly p
      (s+a+(n-a-b)) (g δ) hgl
    let u := (infinityGradedIso
      (model.convergence (.quotient (rEarlier-1) (extensionSourceObject model X Y f))) p (s+a)).inv
      ((model.syntheticTower.filtration Aearly).toAssociatedGraded (s+a) p da)
    let v := (infinityGradedIso
      (model.convergence (.quotient (rEarlier-1) (.nu Y))) p (s+a+(n-a-b))).inv
      ((model.syntheticTower.filtration Bearly).toAssociatedGraded (s+a+(n-a-b)) p db)
    have hu : u ∉ Set.range (((model.family.functor.map
        ((model.quotients.tower ((extensionSourceObject model X Y f).obj model.nu model.auxiliary)).rho
          (rEarlier-1) (rLater-1) (Nat.sub_le_sub_right hle 1))).eInftyMap
            (s+a,p.1+(s+a),p.2)).hom) := by
      intro hu
      obtain ⟨ε,hε,hres⟩ := (infinity_image_iff_lift (model.convergentMap
        (.quotient (rLater-1) (extensionSourceObject model X Y f))
        (.quotient (rEarlier-1) (extensionSourceObject model X Y f))
        ((model.quotients.tower ((extensionSourceObject model X Y f).obj model.nu model.auxiliary)).rho
          (rEarlier-1) (rLater-1) (Nat.sub_le_sub_right hle 1))) p (s+a) da).mp hu
      apply hlift
      refine ⟨ε,hε,?_⟩
      rw [hda] at hres
      exact hres
    have haupper : a ≤ rEarlier-2 := by
      by_contra ha'
      have hz := shifted_quotient_eInfty_zero X (rEarlier-1) (by omega)
        (normalizedExponent model.classicalTower f) (s+a) (p.1+(s+a)) p.2 (by
          dsimp only [p]
          omega)
      apply hu
      refine ⟨0, ?_⟩
      have hu0 : u = 0 := @Subsingleton.elim _ (ModuleCat.subsingleton_of_isZero hz) _ _
      exact (module_map_zero _).trans hu0.symm
    have hv : v ≠ 0 := by
      intro hv
      have hgrade : (model.syntheticTower.filtration Bearly).toAssociatedGraded
          (s+a+(n-a-b)) p db = 0 := by
        apply (infinityGradedIso
          (model.convergence (.quotient (rEarlier-1) (.nu Y))) p (s+a+(n-a-b))).toLinearEquiv.symm.injective
        exact hv.trans ((infinityGradedIso
          (model.convergence (.quotient (rEarlier-1) (.nu Y))) p (s+a+(n-a-b))).inv.hom.map_zero.symm)
      have hnext := (element_grade_equal_iff (model.syntheticTower.filtration Bearly)
        (s+a+(n-a-b)) p db 0).mp (by
          rw [module_map_zero]
          exact hgrade)
      change ((model.syntheticTower.filtration Bearly).F (s+a+(n-a-b)) p).arrow db -
        ((model.syntheticTower.filtration Bearly).F (s+a+(n-a-b)) p).arrow 0 ∈
        (ModuleCat.subobjectModule _) ((model.syntheticTower.filtration Bearly).F (s+a+(n-a-b)+1) p) at hnext
      rw [module_map_zero,sub_zero,hdb] at hnext
      have hnext' : g δ ∈ model.syntheticTower.filtrationSubmodule Bearly (s+a+(n-a-b)+1) p := by
        simpa only [SyntheticTowerPresentation.filtration, OrderIso.apply_symm_apply] using hnext
      exact hgnext hnext'
    refine ⟨hle,a,b,ha,haupper,hab,u,v,hu,?_,hv⟩
    apply (tower_extension_iff (model.convergentMap
      (.quotient (rEarlier-1) (extensionSourceObject model X Y f))
      (.quotient (rEarlier-1) (.nu Y)) (finiteExtensionMap model X Y f (rEarlier-1))) p (s+a) (n-a-b) u v).mpr
    refine ⟨by omega,da,db,?_,?_,?_⟩
    · change ((model.syntheticTower.filtration Aearly).F (s+a) p).arrow da ≫
        finiteExtensionMap model X Y f (rEarlier-1) =
        ((model.syntheticTower.filtration Bearly).F (s+a+(n-a-b)) p).arrow db
      rw [hda,hdb]
      rfl
    · exact ((infinityGradedIso
        (model.convergence (.quotient (rEarlier-1) (extensionSourceObject model X Y f))) p (s+a)).toLinearEquiv.apply_symm_apply _).symm
    · exact ((infinityGradedIso
        (model.convergence (.quotient (rEarlier-1) (.nu Y))) p (s+a+(n-a-b))).toLinearEquiv.apply_symm_apply _).symm
  have hcorrect (α₀ : BiHom p.1 p.2 Aearly) (α : BiHom p.1 p.2 Alater)
      (hδ : α₀ - ρ α ∈ E (s + 1)) :
      ∃ α' : BiHom p.1 p.2 Alater, α' - α ∈ L (s + 1) ∧
        g (α₀ - ρ α') ∈ T := by
    apply finite_filtration_correction ρ g E L T hL (s + 1) n.toNat hstep
    · intro δ hδ
      have hlast : s + 1 + (n.toNat : ℤ) = s + n + 1 := by omega
      exact hg (s + n + 1) δ (by simpa only [hlast] using hδ)
    · exact hδ
  obtain ⟨W⟩ := hW
  obtain ⟨xx,yy,hxx,hyy,hxxrho,hyyrho⟩ :=
    finite_representatives_lift X Y f
      rEarlier rLater n s t x y hr hle hn hnUpper hx hy W
  let Blater := (SyntheticObject.quotient (rLater-1) (.nu Y)).obj model.nu model.auxiliary
  let FL : ℤ → AddSubgroup (BiHom p.1 p.2 Blater) :=
    fun k => (model.syntheticTower.filtrationSubmodule Blater k p).toAddSubgroup
  let ra : Alater ⟶ Aearly := (model.quotients.tower ((extensionSourceObject model X Y f).obj model.nu model.auxiliary)).rho
    (rEarlier-1) (rLater-1) (Nat.sub_le_sub_right hle 1)
  let rb : Blater ⟶ Bearly := (model.quotients.tower (model.nu.functor.obj (Y.obj model.auxiliary))).rho
    (rEarlier-1) (rLater-1) (Nat.sub_le_sub_right hle 1)
  let ge : Aearly ⟶ Bearly := finiteExtensionMap model X Y f (rEarlier-1)
  let gl : Alater ⟶ Blater := finiteExtensionMap model X Y f (rLater-1)
  let IA := infinityGradedIso (model.convergence (.quotient (rLater-1)
    (extensionSourceObject model X Y f))) p s
  let IB := infinityGradedIso (model.convergence (.quotient (rLater-1) (.nu Y))) p (s+n)
  let IEA := infinityGradedIso (model.convergence (.quotient (rEarlier-1)
    (extensionSourceObject model X Y f))) p s
  let IEB := infinityGradedIso (model.convergence (.quotient (rEarlier-1) (.nu Y))) p (s+n)
  haveI : Epi ((model.syntheticTower.filtration Alater).toAssociatedGraded s p) :=
    inferInstanceAs (Epi (cokernel.π _))
  haveI : Epi ((model.syntheticTower.filtration Blater).toAssociatedGraded (s+n) p) :=
    inferInstanceAs (Epi (cokernel.π _))
  obtain ⟨ar,har⟩ := (ModuleCat.epi_iff_surjective
    ((model.syntheticTower.filtration Alater).toAssociatedGraded s p)).mp inferInstance (IA.hom xx)
  obtain ⟨br,hbr⟩ := (ModuleCat.epi_iff_surjective
    ((model.syntheticTower.filtration Blater).toAssociatedGraded (s+n) p)).mp inferInstance (IB.hom yy)
  let α : BiHom p.1 p.2 Alater := ((model.syntheticTower.filtration Alater).F s p).arrow ar
  let β : BiHom p.1 p.2 Blater := ((model.syntheticTower.filtration Blater).F (s+n) p).arrow br
  have hα : α ∈ L s := by
    have h : α ∈ (ModuleCat.subobjectModule _) ((model.syntheticTower.filtration Alater).F s p) := ⟨ar,rfl⟩
    simp only [SyntheticTowerPresentation.filtration, OrderIso.apply_symm_apply] at h
    exact h
  have hβ : β ∈ FL (s+n) := by
    have h : β ∈ (ModuleCat.subobjectModule _) ((model.syntheticTower.filtration Blater).F (s+n) p) := ⟨br,rfl⟩
    simp only [SyntheticTowerPresentation.filtration, OrderIso.apply_symm_apply] at h
    exact h
  obtain ⟨_,a0r,b0r,ha0b0,ha0,hb0⟩ :=
    (tower_extension_iff (model.convergentMap
      (.quotient (rEarlier-1) (extensionSourceObject model X Y f))
      (.quotient (rEarlier-1) (.nu Y)) ge) p s n W.source W.target).mp W.equation
  let α0 : BiHom p.1 p.2 Aearly := ((model.syntheticTower.filtration Aearly).F s p).arrow a0r
  let β0 : BiHom p.1 p.2 Bearly := ((model.syntheticTower.filtration Bearly).F (s+n) p).arrow b0r
  have iso_cancel {A B : ModuleCat ℤ} (e : A ≅ B) (a : A) : e.inv (e.hom a) = a :=
    e.toLinearEquiv.symm_apply_apply a
  have hδ : α0 - ρ α ∈ E (s+1) := by
    apply grade_difference (model.convergentMap (.quotient (rLater-1) (extensionSourceObject model X Y f))
      (.quotient (rEarlier-1) (extensionSourceObject model X Y f)) ra) p s ar a0r
    change (model.family.functor.map ra).eInftyMap (s,p.1+s,p.2)
      (IA.inv ((model.syntheticTower.filtration Alater).toAssociatedGraded s p ar)) =
      IEA.inv ((model.syntheticTower.filtration Aearly).toAssociatedGraded s p a0r)
    have ha0' : (model.syntheticTower.filtration Aearly).toAssociatedGraded s p a0r = IEA.hom W.source := ha0
    rw [har,ha0',iso_cancel,iso_cancel]
    exact hxxrho
  have hβδ : Sub.sub β0 (β ≫ rb) ∈ F (s+n+1) := by
    apply grade_difference (model.convergentMap (.quotient (rLater-1) (.nu Y)) (.quotient (rEarlier-1) (.nu Y))
      rb) p (s+n) br b0r
    change (model.family.functor.map rb).eInftyMap (s+n,p.1+(s+n),p.2)
      (IB.inv ((model.syntheticTower.filtration Blater).toAssociatedGraded (s+n) p br)) =
      IEB.inv ((model.syntheticTower.filtration Bearly).toAssociatedGraded (s+n) p b0r)
    have hb0' : (model.syntheticTower.filtration Bearly).toAssociatedGraded (s+n) p b0r = IEB.hom W.target := hb0
    rw [hbr,hb0',iso_cancel,iso_cancel]
    exact hyyrho
  obtain ⟨α',hα'diff,hres⟩ := hcorrect α0 α hδ
  have hn0 : 0 ≤ n := le_trans (by exact_mod_cast Nat.zero_le (normalizedExponent model.classicalTower f)) hn
  have hα' : α' ∈ L s := by
    have hd : α'-α ∈ L s := model.syntheticTower.filtrationSubmodule_antitone Alater p (show s ≤ s+1 by omega) hα'diff
    have h := (L s).add_mem hd hα
    simpa only [sub_add_cancel] using h
  have hsquare : ra ≫ ge = gl ≫ rb :=
    (model.quotients.natural (model.normalizedMap X Y f).map).rho_naturality (Nat.sub_le_sub_right hle 1)
  have hrhodiff : (Sub.sub (α' ≫ gl) β) ≫ rb ∈ F (s+n+1) := by
    have hh := (F (s+n+1)).sub_mem hβδ hres
    have he : (Sub.sub (α' ≫ gl) β) ≫ rb = (Sub.sub β0 (β ≫ rb)) - g (α0 - ρ α') := by
      change _ = (Sub.sub β0 (β ≫ rb)) - (Sub.sub α0 (α' ≫ ra)) ≫ ge
      have sub_comp_actual {A B C : SyntheticSpectrum} (a b : A ⟶ B) (c : B ⟶ C) :
          Sub.sub a b ≫ c = Sub.sub (a ≫ c) (b ≫ c) := Preadditive.sub_comp a b c
      simp only [sub_comp_actual,Category.assoc,hsquare]
      have he0 : α0 ≫ ge = β0 := ha0b0
      rw [he0]
      have algebra {G : Type} [AddCommGroup G] (a b c : G) :
          Sub.sub c b = Sub.sub a b - Sub.sub a c := by
        change c-b = (a-b)-(a-c)
        abel
      exact algebra β0 (β ≫ rb) (α' ≫ gl ≫ rb)
    rw [he]
    exact hh
  have hstart : Sub.sub (α' ≫ gl) β ∈ FL s :=
    (FL s).sub_mem (actual_map_preserves (.quotient (rLater-1) (extensionSourceObject model X Y f))
      (.quotient (rLater-1) (.nu Y)) gl s α' hα')
      (model.syntheticTower.filtrationSubmodule_antitone Blater p (by omega) hβ)
  have hreflect : Sub.sub (α' ≫ gl) β ∈ FL (s+n+1) := by
    have he : s + (((n+1).toNat : ℕ) : ℤ) = s+n+1 := by omega
    rw [←he]
    refine finite_filtration_reflection
      (syntheticHomotopyMap rb p).hom.toAddMonoidHom FL F
      (fun i j hij z hz => model.syntheticTower.filtrationSubmodule_antitone Bearly p hij hz)
      s (n+1).toNat ?_ (Sub.sub (α' ≫ gl) β) hstart ?_
    · intro k hk hkN z hz hrz
      exact next_filtration_of_infinity_injective
        (model.convergentMap (.quotient (rLater-1) (.nu Y)) (.quotient (rEarlier-1) (.nu Y)) rb)
        p k (rho_infty_injective Y (rEarlier-1) (rLater-1) (by omega)
          (Nat.sub_le_sub_right hle 1) k (p.1+k) p.2 (by dsimp only [p]; omega)) z hz hrz
    · rw [he]
      exact hrhodiff
  have hfinalmem : α' ≫ gl ∈ FL (s+n) := by
    have hd := model.syntheticTower.filtrationSubmodule_antitone Blater p (show s+n≤s+n+1 by omega) hreflect
    have hh := (FL (s+n)).add_mem hd hβ
    have he : Sub.sub (α' ≫ gl) β + β = α' ≫ gl := sub_add_cancel _ _
    exact he ▸ hh
  obtain ⟨ar',har'⟩ := filtration_representative_exists model.syntheticTower Alater p s α' hα'
  obtain ⟨br',hbr'⟩ := filtration_representative_exists model.syntheticTower Blater p (s+n) (α' ≫ gl) hfinalmem
  refine ⟨{
    page_ge_two := by omega
    length_lower := hn
    length_upper := by omega
    source_cycle := (isCycle_iff_reaches model X rLater (by omega) (s,t) x).mp hx
    target_cycle := (isCycle_iff_reaches model Y ((rLater : ℤ)-n+normalizedExponent model.classicalTower f)
      (by omega) (s+n,t+n) y).mp (by convert hy using 1 <;> omega)
    source := xx
    target := yy
    source_rep := hxx
    target_rep := hyy
    equation := ?_ }⟩
  apply (tower_extension_iff (model.convergentMap
    (.quotient (rLater-1) (extensionSourceObject model X Y f))
    (.quotient (rLater-1) (.nu Y)) gl) p s n xx yy).mpr
  refine ⟨hn0,ar',br',?_,?_,?_⟩
  ·
    rw [har',hbr']
  · rw [←har]
    apply (element_grade_equal_iff (model.syntheticTower.filtration Alater) s p ar' ar).mpr
    rw [har']
    simp only [SyntheticTowerPresentation.filtration,OrderIso.apply_symm_apply]
    exact hα'diff
  · rw [←hbr]
    apply (element_grade_equal_iff (model.syntheticTower.filtration Blater) (s+n) p br' br).mpr
    rw [hbr']
    simp only [SyntheticTowerPresentation.filtration,OrderIso.apply_symm_apply]
    exact hreflect

end
end KIP126.ProofTools.Standard
