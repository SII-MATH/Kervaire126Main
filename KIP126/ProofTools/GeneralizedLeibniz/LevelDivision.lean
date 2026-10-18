module
import all KIP126.ProofTools.GeneralizedLeibniz.CrossingLift
import all KIP126.ProofTools.GeneralizedLeibniz.CrossingFinite

/-! Conditional division in the actual finite lambda square.  The additional
crossing condition excludes essential smaller-layer extensions whose targets
lie in the kernel of the actual lambda map on E-infinity.  It is imposed only
strictly below the requested target grade and includes the original source
grade.  The target at the final grade is not asserted to have a unique lambda
preimage. -/

@[expose] section
namespace KIP126.ProofTools.Internal.Leibniz
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Standard
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2000000
set_option Elab.async false

/-- Kernel-sensitive corrections over the closed-source, open-target triangle
reflect the filtration of an actual image through a filtered homomorphism.
Only finitely many source and target grades occur. -/
private theorem filtered_image_reflection_of_kernel_correction
    {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    (f : A →+ B) (L : B →+ C)
    (F : ℤ → AddSubgroup A) (G : ℤ → AddSubgroup B) (H : ℤ → AddSubgroup C)
    (hG : Antitone G) (hH : Antitone H)
    (hf : ∀ u a, a ∈ F u → f a ∈ G u)
    (hL : ∀ u b, b ∈ G u → L b ∈ H u)
    (s N : ℤ) (hsN : s ≤ N)
    (hcorrect : ∀ u v, s ≤ u → u ≤ v → v < N →
      ∀ a, a ∈ F u → f a ∈ G v → L (f a) ∈ H (v + 1) →
        ∃ b, b ∈ F u ∧ a - b ∈ F (u + 1) ∧ f b ∈ G (v + 1))
    (a : A) (ha : a ∈ F s) (hLfa : L (f a) ∈ H N) :
    f a ∈ G N := by
  have raise : ∀ v : ℤ, s ≤ v → v < N →
      ∀ a, a ∈ F s → f a ∈ G v → L (f a) ∈ H (v + 1) →
        f a ∈ G (v + 1) := by
    intro v hsv hvN
    have aux : ∀ k : ℕ, ∀ u : ℤ, s ≤ u → u + k = v + 1 →
        ∀ a, a ∈ F u → f a ∈ G v → L (f a) ∈ H (v + 1) →
          f a ∈ G (v + 1) := by
      intro k
      induction k with
      | zero =>
        intro u hsu he a ha hfa hLfa
        have hu : u = v + 1 := by omega
        subst u
        exact hf _ _ ha
      | succ k ih =>
        intro u hsu he a ha hfa hLfa
        obtain ⟨b, hb, hab, hfb⟩ :=
          hcorrect u v hsu (by omega) hvN a ha hfa hLfa
        have hsub : f (a - b) ∈ G v := by
          rw [map_sub]
          exact (G v).sub_mem hfa (hG (by omega) hfb)
        have hLsub : L (f (a - b)) ∈ H (v + 1) := by
          rw [map_sub, map_sub]
          exact (H (v + 1)).sub_mem hLfa (hL _ _ hfb)
        have hh := ih (u + 1) (by omega) (by omega) (a - b) hab hsub hLsub
        have hh' := (G (v + 1)).add_mem hh hfb
        simpa only [map_sub, sub_add_cancel] using hh'
    exact aux (v + 1 - s).toNat s le_rfl (by omega)
  have climb : ∀ k : ℕ, s + k ≤ N → f a ∈ G (s + k) := by
    intro k
    induction k with
    | zero =>
      intro hk
      simpa only [Nat.cast_zero, add_zero] using hf s a ha
    | succ k ih =>
      intro hk
      have hprev := ih (by omega)
      have hh := raise (s + k) (by omega) (by omega) a ha hprev
        (hH (by omega) hLfa)
      simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using hh
  have hh := climb (N - s).toNat (by omega)
  simpa only [Int.toNat_of_nonneg (show 0 ≤ N - s by omega), add_sub_cancel] using hh

section Tower
universe u v
variable {Syn : Type u} [SyntheticCategory.{u,v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  {H : Syn} {unit : S_0_0 ⟶ H} {E : SyntheticAdamsFamily Syn}
  {P : SyntheticTowerPresentation unit E} {X Y Z : Syn} {g : X ⟶ Y} {l : Y ⟶ Z}
  {cx : SyntheticTowerConvergence P X} {cy : SyntheticTowerConvergence P Y}
  {cz : SyntheticTowerConvergence P Z}

/-- A finite lower triangle of actual essential extensions has no target
killed by the selected comparison map.  The same-source row is included. -/
private def TowerKernelNoCrossing
    (M : ConvergentMap E g cx.toConvergence cy.toConvergence)
    (_L : ConvergentMap E l cy.toConvergence cz.toConvergence)
    (p : ℤ × ℤ) (s N : ℤ) : Prop :=
  ∀ u v : ℤ, s ≤ u → u ≤ v → v < N → ∀ x y,
    TowerEssentialExtension M p u (v-u) x y →
      (E.functor.map l).eInftyMap (u+(v-u),p.1+(u+(v-u)),p.2) y ≠ 0

/-- If the selected target grade is killed by the comparison, the kernel
crossing exclusion supplies a correction with zero target grade. -/
private theorem tower_correction_of_kernel_exclusion
    (M : ConvergentMap E g cx.toConvergence cy.toConvergence)
    (L : ConvergentMap E l cy.toConvergence cz.toConvergence)
    (p : ℤ × ℤ) (s n : ℤ) (hn : 0 ≤ n)
    (hnot : ∀ x y, TowerEssentialExtension M p s n x y →
      (E.functor.map l).eInftyMap (s+n,p.1+(s+n),p.2) y ≠ 0)
    (a : BiHom p.1 p.2 X) (ha : a ∈ P.filtrationSubmodule X s p)
    (hfa : a ≫ g ∈ P.filtrationSubmodule Y (s+n) p)
    (hLfa : (a ≫ g) ≫ l ∈ P.filtrationSubmodule Z (s+n+1) p) :
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
  obtain ⟨cr, hbc, hc⟩ := tower_map_frame L p (s+n) y br hy
  have hcnext : ((P.filtration Z).F (s+n) p).arrow cr ∈
      ModuleCat.subobjectModule _ ((P.filtration Z).F (s+n+1) p) := by
    rw [←hbc,hbr]
    simpa only [SyntheticTowerPresentation.filtration,OrderIso.apply_symm_apply] using hLfa
  have hc0 : (P.filtration Z).toAssociatedGraded (s+n) p cr = 0 := by
    have h := (element_grade_equal_iff (P.filtration Z) (s+n) p cr 0).mpr (by
      simpa only [map_zero,sub_zero] using hcnext)
    simpa only [map_zero] using h
  have hLy : (E.functor.map l).eInftyMap (s+n,p.1+(s+n),p.2) y = 0 := by
    apply (infinityGradedIso cz p (s+n)).toLinearEquiv.injective
    change (infinityGradedIso cz p (s+n)).hom _ = (infinityGradedIso cz p (s+n)).hom 0
    rw [←hc,hc0,map_zero]
  have he0 : TowerExtensionEquation M p s n x 0 := by
    by_contra hz
    exact hnot x y ((tower_essential_iff_no_zero M p s n x y he).mpr hz) hLy
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

/-- The kernel crossing condition reflects a high target filtration for the
same actual source and image.  No representative is replaced in the result. -/
private theorem tower_image_filtration_of_kernel_no_crossing
    (M : ConvergentMap E g cx.toConvergence cy.toConvergence)
    (L : ConvergentMap E l cy.toConvergence cz.toConvergence)
    (p : ℤ × ℤ) (s N : ℤ) (hsN : s ≤ N)
    (hcross : TowerKernelNoCrossing M L p s N)
    (a : BiHom p.1 p.2 X) (ha : a ∈ P.filtrationSubmodule X s p)
    (hLa : (a ≫ g) ≫ l ∈ P.filtrationSubmodule Z N p) :
    a ≫ g ∈ P.filtrationSubmodule Y N p := by
  let Fa : ℤ → AddSubgroup (BiHom p.1 p.2 X) :=
    fun u => (P.filtrationSubmodule X u p).toAddSubgroup
  let Fb : ℤ → AddSubgroup (BiHom p.1 p.2 Y) :=
    fun u => (P.filtrationSubmodule Y u p).toAddSubgroup
  let Fc : ℤ → AddSubgroup (BiHom p.1 p.2 Z) :=
    fun u => (P.filtrationSubmodule Z u p).toAddSubgroup
  apply filtered_image_reflection_of_kernel_correction
    (syntheticHomotopyMap g p).hom.toAddMonoidHom
    (syntheticHomotopyMap l p).hom.toAddMonoidHom Fa Fb Fc
    (fun u v huv b hb => P.filtrationSubmodule_antitone Y p huv hb)
    (fun u v huv b hb => P.filtrationSubmodule_antitone Z p huv hb)
    (fun u a ha => map_preserves_filtration M p u a ha)
    (fun u b hb => map_preserves_filtration L p u b hb)
    s N hsN ?_ a ha hLa
  intro u v hsu huv hvN b hb hgb hlgb
  change BiHom p.1 p.2 X at b
  change b ≫ g ∈ P.filtrationSubmodule Y v p at hgb
  change (b ≫ g) ≫ l ∈ P.filtrationSubmodule Z (v+1) p at hlgb
  change ∃ c, c ∈ P.filtrationSubmodule X u p ∧
    b-c ∈ P.filtrationSubmodule X (u+1) p ∧
    c ≫ g ∈ P.filtrationSubmodule Y (v+1) p
  have huv' : u+(v-u)=v := by omega
  have h := tower_correction_of_kernel_exclusion M L p u (v-u) (by omega)
    (hcross u v hsu huv hvN) b hb
    (by simpa only [huv'] using hgb)
    (by simpa only [huv'] using hlgb)
  simpa only [huv'] using h

end Tower

section Square
universe u v
variable {Syn : Type u} [SyntheticCategory.{u,v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  {H : Syn} {unit : S_0_0 ⟶ H} {E : SyntheticAdamsFamily Syn}
  {P : SyntheticTowerPresentation unit E} {X Y X' Y' : Syn}
  {g : X ⟶ Y} {g' : X' ⟶ Y'} {a : X ⟶ X'} {b : Y ⟶ Y'}
  {cx : SyntheticTowerConvergence P X} {cy : SyntheticTowerConvergence P Y}
  {cx' : SyntheticTowerConvergence P X'} {cy' : SyntheticTowerConvergence P Y'}

/-- An actual filtered source lift in a commuting square lifts an essential
extension when the lower kernel-crossing triangle is excluded. The two smaller
labels are the grades of the same lifted source and its actual image. -/
private theorem tower_essential_division_from_actual_lift
    (M : ConvergentMap E g cx.toConvergence cy.toConvergence)
    (M' : ConvergentMap E g' cx'.toConvergence cy'.toConvergence)
    (Ma : ConvergentMap E a cx.toConvergence cx'.toConvergence)
    (Mb : ConvergentMap E b cy.toConvergence cy'.toConvergence)
    (hcomm : g ≫ b = a ≫ g')
    (p : ℤ × ℤ) (s n : ℤ) (hn : 0 ≤ n)
    (hcross : TowerKernelNoCrossing M Mb p s (s+n))
    (x' : ((E.obj X').sequence.ssData (s,p.1+s,p.2)).eInfty)
    (y' : ((E.obj Y').sequence.ssData (s+n,p.1+(s+n),p.2)).eInfty)
    (ar' : (Subobject.underlying.obj ((P.filtration X').F s p) : ModuleCat.{v} ℤ))
    (br' : (Subobject.underlying.obj ((P.filtration Y').F (s+n) p) : ModuleCat.{v} ℤ))
    (he' : ((P.filtration X').F s p).arrow ar' ≫ g' =
      ((P.filtration Y').F (s+n) p).arrow br')
    (hx' : (P.filtration X').toAssociatedGraded s p ar' =
      (infinityGradedIso cx' p s).hom x')
    (hy' : (P.filtration Y').toAssociatedGraded (s+n) p br' =
      (infinityGradedIso cy' p (s+n)).hom y')
    (α : BiHom p.1 p.2 X) (hα : α ∈ P.filtrationSubmodule X s p)
    (hlift : α ≫ a = ((P.filtration X').F s p).arrow ar')
    (hess : TowerEssentialExtension M' p s n x' y') :
    ∃ x y, TowerEssentialExtension M p s n x y ∧
      (E.functor.map a).eInftyMap (s,p.1+s,p.2) x = x' ∧
      (E.functor.map b).eInftyMap (s+n,p.1+(s+n),p.2) y = y' := by
  have hbig : ((P.filtration Y').F (s+n) p).arrow br' ∈
      P.filtrationSubmodule Y' (s+n) p := by
    have hh : ((P.filtration Y').F (s+n) p).arrow br' ∈
        ModuleCat.subobjectModule _ ((P.filtration Y').F (s+n) p) := ⟨br',rfl⟩
    simpa only [SyntheticTowerPresentation.filtration,OrderIso.apply_symm_apply] using hh
  have hmap : (α ≫ g) ≫ b = ((P.filtration Y').F (s+n) p).arrow br' := by
    rw [Category.assoc,hcomm,←Category.assoc,hlift,he']
  have himage := tower_image_filtration_of_kernel_no_crossing M Mb p s (s+n)
    (by omega) hcross α hα (by rw [hmap]; exact hbig)
  obtain ⟨ar,har⟩ := filtration_representative_exists P X p s α hα
  obtain ⟨br,hbr⟩ := filtration_representative_exists P Y p (s+n) (α≫g) himage
  let x := (infinityGradedIso cx p s).inv ((P.filtration X).toAssociatedGraded s p ar)
  let y := (infinityGradedIso cy p (s+n)).inv ((P.filtration Y).toAssociatedGraded (s+n) p br)
  have hx : (P.filtration X).toAssociatedGraded s p ar = (infinityGradedIso cx p s).hom x :=
    ((infinityGradedIso cx p s).toLinearEquiv.apply_symm_apply _).symm
  have hy : (P.filtration Y).toAssociatedGraded (s+n) p br = (infinityGradedIso cy p (s+n)).hom y :=
    ((infinityGradedIso cy p (s+n)).toLinearEquiv.apply_symm_apply _).symm
  have he : TowerExtensionEquation M p s n x y :=
    (tower_extension_iff M p s n x y).mpr ⟨hn,ar,br,by rw [har,hbr],hx,hy⟩
  have hxa : (E.functor.map a).eInftyMap (s,p.1+s,p.2) x = x' := by
    have hh := representative_grade_naturality Ma p s ar ar' (by rw [har]; exact hlift)
    rw [hx'] at hh
    exact hh.symm.trans ((infinityGradedIso cx' p s).toLinearEquiv.symm_apply_apply x')
  have hyb : (E.functor.map b).eInftyMap (s+n,p.1+(s+n),p.2) y = y' := by
    have hh := representative_grade_naturality Mb p (s+n) br br' (by rw [hbr]; exact hmap)
    rw [hy'] at hh
    exact hh.symm.trans ((infinityGradedIso cy' p (s+n)).toLinearEquiv.symm_apply_apply y')
  refine ⟨x,y,?_,hxa,hyb⟩
  exact tower_essential_of_mapped_extension M M' Ma Mb hcomm p s n x y he
    (by rw [hxa,hyb]; exact hess)

end Square

/-- The divided normalized source has its expected bottom filtration. -/
private theorem normalized_divided_source_bottom
    (X : ClassicalObject) (e : ℤ) (q i : ℕ) (hiq : i < q) (s t : ℤ)
    (b : BiHom (t-s) (t+e) ((SyntheticCategory.biShift (0,-(i:ℤ))).obj
      (XModLambdaN ((SyntheticCategory.biShift (0,e)).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) (q-i)))) :
    FiltrationAtLeast model.syntheticTower (s+i) b := by
  let A := model.nu.functor.obj (X.obj model.auxiliary)
  letI := model.exactness.shiftCommShift (0,e)
  letI := model.exactness.shiftExact (0,e)
  obtain ⟨ε,_,_⟩ := quotient_shift_exists model.quotients.coherence (0,e) (q-i) A
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(i:ℤ))
  let I : F.obj (XModLambdaN ((SyntheticCategory.biShift (0,e)).obj A) (q-i)) ≅
      (SyntheticCategory.biShift (0,e-i)).obj (XModLambdaN A (q-i)) :=
    F.mapIso ε ≪≫
      (SyntheticCategory.biShift_comp (0,e) (0,-(i:ℤ))).app _ ≪≫
      eqToIso (congrArg (fun p => (SyntheticCategory.biShift p).obj (XModLambdaN A (q-i)))
        (by ext <;> simp [sub_eq_add_neg]))
  have hbottom := shifted_quotient_bottom_filtration X (q-i) (by omega) (e-i)
    (t-s) (t+e) (b≫I.hom)
  have hbottom' : FiltrationAtLeast model.syntheticTower (s+i) (b≫I.hom) := by
    convert hbottom using 1; omega
  have hbf := map_preserves_filtration (model.convergentMap
    (.shift (0,e-i) (.quotient (q-i) (.nu X)))
    (.shift (0,-(i:ℤ)) (.quotient (q-i) (.shift (0,e) (.nu X)))) I.inv)
    (t-s,t+e) (s+i) (b≫I.hom) hbottom'
  change FiltrationAtLeast model.syntheticTower (s+i) ((b≫I.hom)≫I.inv) at hbf
  simpa only [FiltrationAtLeast,Category.assoc,Iso.hom_inv_id,Category.comp_id] using hbf

/-- Extra crossings excluded for division by `lambda^i`: the condition uses
the actual shifted smaller-quotient map and the actual target lambda arrow. -/
private def FiniteLambdaKernelNoCrossing (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (q i : ℕ) (hi : 0 < i) (hiq : i < q) (s t N : ℤ) : Prop :=
  TowerKernelNoCrossing
    (model.convergentMap
      (.shift (0,-(i:ℤ)) (.quotient (q-i) (extensionSourceObject model X Y f)))
      (.shift (0,-(i:ℤ)) (.quotient (q-i) (.nu Y)))
      ((SyntheticCategory.biShift (0,-(i:ℤ))).map (finiteExtensionMap model X Y f (q-i))))
    (model.convergentMap (.shift (0,-(i:ℤ)) (.quotient (q-i) (.nu Y))) (.quotient q (.nu Y))
      ((model.quotients.tower _).triangle hi hiq).lambdaMap)
    (t-s,t+normalizedExponent model.classicalTower f) (s+i) N

/-- Conditional finite lambda division preserves the actual source and image
equations and reflects the requested target filtration.  The smaller source
class is the class of the constructed `b`, not an independently chosen lift. -/
private theorem normalized_finite_division_of_kernel_no_crossing
    (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (q i : ℕ) (hi : 0 < i) (hiq : i < q) (s t N : ℤ) (hsN : s+i ≤ N)
    (hcross : FiniteLambdaKernelNoCrossing X Y f q i hi hiq s t N)
    (a : BiHom (t-s) (t+normalizedExponent model.classicalTower f)
      (XModLambdaN ((extensionSourceObject model X Y f).obj model.nu model.auxiliary) q))
    (ha : FiltrationAtLeast model.syntheticTower (s+i) a)
    (hfa : FiltrationAtLeast model.syntheticTower N (a ≫ finiteExtensionMap model X Y f q)) :
    ∃ b : BiHom (t-s) (t+normalizedExponent model.classicalTower f)
        ((SyntheticCategory.biShift (0,-(i:ℤ))).obj
          (XModLambdaN ((extensionSourceObject model X Y f).obj model.nu model.auxiliary) (q-i))),
      b ≫ ((model.quotients.tower _).triangle hi hiq).lambdaMap = a ∧
      FiltrationAtLeast model.syntheticTower (s+i) b ∧
      (b ≫ (SyntheticCategory.biShift (0,-(i:ℤ))).map
        (finiteExtensionMap model X Y f (q-i))) ≫
          ((model.quotients.tower _).triangle hi hiq).lambdaMap =
        a ≫ finiteExtensionMap model X Y f q ∧
      FiltrationAtLeast model.syntheticTower N
        (b ≫ (SyntheticCategory.biShift (0,-(i:ℤ))).map
          (finiteExtensionMap model X Y f (q-i))) := by
  obtain ⟨b,hb,himage,_⟩ := normalized_finite_source_image_division X Y f q i hi hiq s t a ha
  have hbfil := normalized_divided_source_bottom X (normalizedExponent model.classicalTower f)
    q i hiq s t b
  refine ⟨b,hb,hbfil,himage,?_⟩
  exact tower_image_filtration_of_kernel_no_crossing _ _ _ (s+i) N hsN hcross b hbfil
    (by
      change FiltrationAtLeast model.syntheticTower N
        ((b ≫ (SyntheticCategory.biShift (0,-(i:ℤ))).map
          (finiteExtensionMap model X Y f (q-i))) ≫
            ((model.quotients.tower (model.nu.functor.obj (Y.obj model.auxiliary))).triangle hi hiq).lambdaMap)
      rw [himage]
      exact hfa)

/-- An actual essential extension in the larger quotient descends to an
essential extension in the shifted smaller quotient under the kernel crossing
condition. Both smaller classes map to the specified larger classes exactly;
neither smaller class is prescribed independently of the actual source lift. -/
private theorem finite_essential_division_of_kernel_no_crossing
    (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (q i : ℕ) (hi : 0 < i) (hiq : i < q) (s t n : ℤ)
    (hcross : FiniteLambdaKernelNoCrossing X Y f q i hi hiq s t (s+i+n))
    (x : ((model.family.obj ((SyntheticObject.quotient q
      (extensionSourceObject model X Y f)).obj model.nu model.auxiliary)).sequence.ssData
      (s+i,(t-s)+(s+i),t+normalizedExponent model.classicalTower f)).eInfty)
    (y : ((model.family.obj ((SyntheticObject.quotient q (.nu Y)).obj
      model.nu model.auxiliary)).sequence.ssData
      (s+i+n,(t-s)+(s+i+n),t+normalizedExponent model.classicalTower f)).eInfty)
    (hess : TowerEssentialExtension (model.convergentMap
      (.quotient q (extensionSourceObject model X Y f)) (.quotient q (.nu Y))
      (finiteExtensionMap model X Y f q))
      (t-s,t+normalizedExponent model.classicalTower f) (s+i) n x y) :
    ∃ (x₀ : ((model.family.obj ((SyntheticObject.shift (0,-(i:ℤ))
        (.quotient (q-i) (extensionSourceObject model X Y f))).obj
        model.nu model.auxiliary)).sequence.ssData
        (s+i,(t-s)+(s+i),t+normalizedExponent model.classicalTower f)).eInfty)
      (y₀ : ((model.family.obj ((SyntheticObject.shift (0,-(i:ℤ))
        (.quotient (q-i) (.nu Y))).obj model.nu model.auxiliary)).sequence.ssData
        (s+i+n,(t-s)+(s+i+n),t+normalizedExponent model.classicalTower f)).eInfty),
      TowerEssentialExtension (model.convergentMap
        (.shift (0,-(i:ℤ)) (.quotient (q-i) (extensionSourceObject model X Y f)))
        (.shift (0,-(i:ℤ)) (.quotient (q-i) (.nu Y)))
        ((SyntheticCategory.biShift (0,-(i:ℤ))).map (finiteExtensionMap model X Y f (q-i))))
        (t-s,t+normalizedExponent model.classicalTower f) (s+i) n x₀ y₀ ∧
      (model.family.functor.map ((model.quotients.tower
        ((extensionSourceObject model X Y f).obj model.nu model.auxiliary)).triangle hi hiq).lambdaMap).eInftyMap
        (s+i,(t-s)+(s+i),t+normalizedExponent model.classicalTower f) x₀ = x ∧
      (model.family.functor.map ((model.quotients.tower
        (model.nu.functor.obj (Y.obj model.auxiliary))).triangle hi hiq).lambdaMap).eInftyMap
        (s+i+n,(t-s)+(s+i+n),t+normalizedExponent model.classicalTower f) y₀ = y := by
  let A := extensionSourceObject model X Y f
  let B := SyntheticObject.nu Y
  let δ : ℤ × ℤ := (0,-(i:ℤ))
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) δ
  let p : ℤ × ℤ := (t-s,t+normalizedExponent model.classicalTower f)
  let LA := ((model.quotients.tower (A.obj model.nu model.auxiliary)).triangle hi hiq).lambdaMap
  let LB := ((model.quotients.tower (B.obj model.nu model.auxiliary)).triangle hi hiq).lambdaMap
  let M := model.convergentMap (.shift δ (.quotient (q-i) A))
    (.shift δ (.quotient (q-i) B)) (F.map (finiteExtensionMap model X Y f (q-i)))
  let M' := model.convergentMap (.quotient q A) (.quotient q B) (finiteExtensionMap model X Y f q)
  let Ma := model.convergentMap (.shift δ (.quotient (q-i) A)) (.quotient q A) LA
  let Mb := model.convergentMap (.shift δ (.quotient (q-i) B)) (.quotient q B) LB
  obtain ⟨hn,ar,br,he,hx,hy⟩ := (tower_extension_iff M' p (s+i) n x y).mp hess.1
  let a := ((model.syntheticTower.filtration ((SyntheticObject.quotient q A).obj
    model.nu model.auxiliary)).F (s+i) p).arrow ar
  have ha : FiltrationAtLeast model.syntheticTower (s+i) a := by
    have hh : a ∈ ModuleCat.subobjectModule _ ((model.syntheticTower.filtration
      ((SyntheticObject.quotient q A).obj model.nu model.auxiliary)).F (s+i) p) := ⟨ar,rfl⟩
    simpa only [SyntheticTowerPresentation.filtration,OrderIso.apply_symm_apply,FiltrationAtLeast] using hh
  obtain ⟨b,hb,_,_⟩ := normalized_finite_source_image_division X Y f q i hi hiq s t a ha
  have hbfil := normalized_divided_source_bottom X (normalizedExponent model.classicalTower f)
    q i hiq s t b
  have hcomm := (model.quotients.natural (model.normalizedMap X Y f).map).lambda_naturality hi hiq
  change F.map (finiteExtensionMap model X Y f (q-i)) ≫ LB =
    LA ≫ finiteExtensionMap model X Y f q at hcomm
  exact tower_essential_division_from_actual_lift M M' Ma Mb hcomm p (s+i) n hn
    hcross x y ar br he hx hy b hbfil hb hess

end
end KIP126.ProofTools.Internal.Leibniz
