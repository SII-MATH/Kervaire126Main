module

import all KIP126.ProofTools.GeneralizedMahowald.Filtration
import all KIP126.ProofTools.GeneralizedLeibniz.CrossingLabels
import all KIP126.ProofTools.ConvergenceOperations
import all KIP126.ProofTools.DetectionOperations
import all KIP126.ProofTools.GeneralizedMahowald.SuspensionClassLabels
import KIP126.ProofTools.MahowaldLeibniz

/-! Actual finite-window bridges for the Mahowald--Leibniz comparison.
All maps and filtrations below are those of the fixed model.  The label
naturality proof is adapted from AdamsSynthetic.Standard.Operations using
its public comparison fields; it does not import that module's private API.
These local results do not assert the full classical composition theorem.
-/

@[expose] section
namespace KIP126.ProofTools.Internal.MahowaldLeibniz
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard KIP126.Literature
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

private theorem familyPageMap_comp
    (F : SyntheticAdamsFamily SyntheticSpectrum) {X Y Z : SyntheticSpectrum}
    (f : X ⟶ Y) (g : Y ⟶ Z) (r : ℤ) (i : Tridegree) :
    F.pageMap (f ≫ g) r i = F.pageMap f r i ≫ F.pageMap g r i := by
  change (F.map (f ≫ g)).pageMap r i =
    (F.map f).pageMap r i ≫ (F.map g).pageMap r i
  rw [F.map_comp, SpectralSequenceMorphism.pageMap_comp]

private theorem familyPageMapCast
    {U V : SyntheticSpectrum} (g : U ⟶ V) {p q : Tridegree} (h : p = q)
    (x : (model.family.obj U).E₂ p) :
    model.family.pageMap g 2 q
      (Eq.mp (congrArg (fun a : Tridegree => ((model.family.obj U).E₂ a : Type)) h) x) =
      Eq.mp (congrArg (fun a : Tridegree => ((model.family.obj V).E₂ a : Type)) h)
        (model.family.pageMap g 2 p x) := by
  subst q
  rfl

private theorem targetNuLabelNatural
    (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (s t : ℤ) (k : ℕ) (x : (model.classical.obj (X.obj model.auxiliary)).Page 2 (s,t)) :
    model.family.pageMap (model.nu.functor.map f) 2 (s,t,t-k)
      (targetNuLabel model X s t k x) =
    targetNuLabel model Y s t k ((model.classical.map f).pageMap 2 (s,t) x) := by
  let p : Tridegree := (s,t,t-k)
  let nuf := model.nu.functor.map f
  let x₀ : (model.family.obj ((SyntheticCategory.biShift (0,0)).obj
      (model.nu.functor.obj (X.obj model.auxiliary)))).E₂ p := by
    simpa only [add_zero] using model.comparison.nuE2 X 0 s t k x
  let y₀ : (model.family.obj ((SyntheticCategory.biShift (0,0)).obj
      (model.nu.functor.obj (Y.obj model.auxiliary)))).E₂ p := by
    simpa only [add_zero] using model.comparison.nuE2 Y 0 s t k
      ((model.classical.map f).pageMap 2 (s,t) x)
  have hxy : model.family.pageMap ((SyntheticCategory.biShift (0,0)).map nuf) 2 p x₀ = y₀ := by
    have hdeg : (s,t,t+0-(k : ℤ)) = p := by dsimp [p]; simp only [add_zero]
    have hraw := model.comparison.nu_natural X Y f 0 s t k x
    have hc := familyPageMapCast ((SyntheticCategory.biShift (0,0)).map nuf) hdeg
      (model.comparison.nuE2 X 0 s t k x)
    exact hc.trans (congrArg
      (fun z => Eq.mp (congrArg (fun a : Tridegree =>
        ((model.family.obj ((SyntheticCategory.biShift (0,0)).obj
          (model.nu.functor.obj (Y.obj model.auxiliary)))).E₂ a : Type)) hdeg) z) hraw)
  let zx := SyntheticCategory.biShift_zero.hom.app
    (model.nu.functor.obj (X.obj model.auxiliary))
  let zy := SyntheticCategory.biShift_zero.hom.app
    (model.nu.functor.obj (Y.obj model.auxiliary))
  have hn : (SyntheticCategory.biShift (0,0)).map nuf ≫ zy = zx ≫ nuf :=
    SyntheticCategory.biShift_zero.hom.naturality nuf
  change model.family.pageMap nuf 2 p (model.family.pageMap zx 2 p x₀) =
    model.family.pageMap zy 2 p y₀
  calc
    _ = model.family.pageMap (zx ≫ nuf) 2 p x₀ :=
      (ConcreteCategory.congr_hom (familyPageMap_comp model.family zx nuf 2 p) x₀).symm
    _ = model.family.pageMap ((SyntheticCategory.biShift (0,0)).map nuf ≫ zy) 2 p x₀ :=
      congrArg (fun g => model.family.pageMap g 2 p x₀) hn.symm
    _ = model.family.pageMap zy 2 p
        (model.family.pageMap ((SyntheticCategory.biShift (0,0)).map nuf) 2 p x₀) :=
      ConcreteCategory.congr_hom
        (familyPageMap_comp model.family ((SyntheticCategory.biShift (0,0)).map nuf) zy 2 p) x₀
    _ = _ := congrArg (model.family.pageMap zy 2 p) hxy

private theorem familyPageMapRegrade
    {U V : SyntheticSpectrum} (g : U ⟶ V) {p q : Tridegree} (h : p = q)
    (x : (model.family.obj U).E₂ p) :
    model.family.pageMap g 2 q (regradeE2 h x) =
      regradeE2 h (model.family.pageMap g 2 p x) := by
  subst q
  rfl

private theorem weightLabelNatural
    (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (s t w : ℤ) (hw : w ≤ t)
    (x : (model.classical.obj (X.obj model.auxiliary)).Page 2 (s,t)) :
    model.family.pageMap (model.nu.functor.map f) 2 (s,t,w)
      (nuWeightLabel model X s t w hw x) =
    nuWeightLabel model Y s t w hw ((model.classical.map f).pageMap 2 (s,t) x) := by
  unfold nuWeightLabel
  rw [familyPageMapRegrade, targetNuLabelNatural]


/-- Vanishing of a complete classical cycle quotient kills the actual finite
infinity grade, not just one chosen representative. -/
private theorem finite_infinity_zero_of_cycles_le_boundaries
    (X : ClassicalObject) (q : ℕ) (hq : 0 < q) (s t w : ℤ)
    (hw : 0 ≤ t-w ∧ t-w < q)
    (hzero : cycles model X ((q:ℤ)-t+w) (s,t) ≤
      boundaries model X (1+t-w) (s,t)) :
    IsZero (((model.family.quotient (model.nu.functor.obj (X.obj model.auxiliary)) q).sequence.ssData
      (s,t,w)).eInfty) := by
  have he (e : ((model.family.quotient
      (model.nu.functor.obj (X.obj model.auxiliary)) q).sequence.ssData (s,t,w)).eInfty) : e=0 := by
    obtain ⟨x,hx,_,hz⟩ := CrossingLabels.finite_grade_label X q hq s t w hw e
    exact hz.mp (hzero hx)
  haveI : Subsingleton (((model.family.quotient
      (model.nu.functor.obj (X.obj model.auxiliary)) q).sequence.ssData (s,t,w)).eInfty) :=
    ⟨fun a b => (he a).trans (he b).symm⟩
  exact ModuleCat.isZero_of_subsingleton _

/-- The PDF middle-layer conditions collapse the actual source filtration
onto its final visible layer.  The layer c is retained throughout. -/
private theorem finite_filtration_collapse_of_middle_conditions
    (X : ClassicalObject) (c K : ℕ) (hK : 2 ≤ K) (S T : ℤ)
    (hmid : ∀ j : ℕ, 1 ≤ j → j < K-1 →
      cycles model X ((K:ℤ)-j) (S+j,T+j) ≤
        boundaries model X ((c:ℤ)+j+1) (S+j,T+j))
    (a : BiHom (T-S) (T-c)
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (c+K))) :
    FiltrationAtLeast model.syntheticTower (S+1) a ↔
      FiltrationAtLeast model.syntheticTower (S+K-1) a := by
  apply filtration_iff_of_infinity_zero (model.convergence (.quotient (c+K) (.nu X)))
    (S+1) (S+K-1) (T-S) (T-c) (by omega)
  intro k hk hk'
  let j := (k-S).toNat
  have hj : (j:ℤ)=k-S := by dsimp [j]; omega
  have hj1 : 1 ≤ j := by omega
  have hjK : j < K-1 := by omega
  have hzero := finite_infinity_zero_of_cycles_le_boundaries X (c+K) (by omega)
    (S+j) (T+j) (T-c) (by omega) (by
      convert hmid j hj1 hjK using 1 <;> congr 1 <;> omega)
  have hks : S+(j:ℤ)=k := by omega
  have hkt : T+(j:ℤ)=T-S+k := by omega
  simpa only [hks,hkt,SyntheticAdamsFamily.quotient,SyntheticObject.obj] using hzero

/-- The terminal subgroup at the end of this finite level window is zero. -/
private theorem finite_composition_tail_zero
    (X : ClassicalObject) (c K : ℕ) (hK : 0 < K) (S T : ℤ)
    (a : BiHom (T-S) (T-c)
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (c+K)))
    (ha : FiltrationAtLeast model.syntheticTower (S+K) a) : a=0 := by
  exact finite_high_filtration_zero X (c+K) (by omega) (T-S) (T-c)
    (S+K) (by omega) a ha

/-- Naturality of the actual finite quotient label under an ordinary
classical map.  No separate E∞ matrix is supplied. -/
private theorem finite_weight_label_natural
    (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (q : ℕ) (s t w : ℤ) (hw : w ≤ t)
    (x : Ambient model X (s,t)) :
    familyPageMap model.family (XModLambdaN.map (model.nu.functor.map f) q) 2 (s,t,w)
      ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) q).pageMap 2 (s,t,w)
        (nuWeightLabel model X s t w hw x)) =
    (model.family.quotientProjection (model.nu.functor.obj (Y.obj model.auxiliary)) q).pageMap 2 (s,t,w)
      (nuWeightLabel model Y s t w hw ((model.classical.map f).pageMap 2 (s,t) x)) := by
  change model.family.pageMap (XModLambdaN.map (model.nu.functor.map f) q) 2 (s,t,w)
    (model.family.pageMap (XModLambdaN.incl _ q) 2 (s,t,w) _) =
    model.family.pageMap (XModLambdaN.incl _ q) 2 (s,t,w) _
  rw [←ModuleCat.comp_apply,←familyPageMap_comp,←XModLambdaN.incl_naturality,
    familyPageMap_comp,ModuleCat.comp_apply,weightLabelNatural]

/-- Complete cycle surjectivity modulo the precise boundary denominator
induces surjectivity of the actual finite E∞ map. -/
private theorem finite_infinity_surjective_of_cycle_surjective
    (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (q : ℕ) (hq : 0 < q) (s t w : ℤ)
    (hw : 0 ≤ t-w ∧ t-w < q)
    (hsurj : ∀ y : Ambient model Y (s,t),
      y ∈ cycles model Y ((q:ℤ)-t+w) (s,t) →
      ∃ x : Ambient model X (s,t), x ∈ cycles model X ((q:ℤ)-t+w) (s,t) ∧
        y-(model.classical.map f).pageMap 2 (s,t) x ∈
          boundaries model Y (1+t-w) (s,t)) :
    Function.Surjective ((model.family.map
      (XModLambdaN.map (model.nu.functor.map f) q)).eInftyMap (s,t,w)).hom := by
  intro e
  obtain ⟨y,hy,hey,_⟩ := CrossingLabels.finite_grade_label Y q hq s t w hw e
  obtain ⟨x,hx,hxy⟩ := hsurj y hy
  let ex := (KIP126.Literature.Standard.infinityFiniteWindow X q hq (s,t) w hw).symm
    (subquotientClass (cycles model X ((q:ℤ)-t+w) (s,t))
      (boundaries model X (1+t-w) (s,t)) ⟨x,hx⟩)
  have hex : HasInfinityRepresentative _ 2 (s,t,w)
      ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) q).pageMap 2 (s,t,w)
        (nuWeightLabel model X s t w (by omega) x)) ex := by
    apply (KIP126.Literature.Standard.eInfinity_finite_labels X q hq s t w hw x ex).mpr
    exact ⟨hx,AddEquiv.apply_symm_apply _ _⟩
  have hmap := family_infinity_representative_map
    (XModLambdaN.map (model.nu.functor.map f) q) (s,t,w) _ ex hex
  rw [finite_weight_label_natural X Y f q s t w (by omega) x] at hmap
  obtain ⟨hfc,hfl⟩ := (KIP126.Literature.Standard.eInfinity_finite_labels Y q hq s t w hw
    ((model.classical.map f).pageMap 2 (s,t) x) _).mp hmap
  obtain ⟨_,hyl⟩ := (KIP126.Literature.Standard.eInfinity_finite_labels Y q hq s t w hw y e).mp hey
  refine ⟨ex,?_⟩
  apply (KIP126.Literature.Standard.infinityFiniteWindow Y q hq (s,t) w hw).injective
  rw [hfl,hyl]
  symm
  apply sub_eq_zero.mp
  rw [←map_sub]
  exact (CrossingLabels.subquotient_zero_iff _ _ _).mpr hxy

/-- Graded cycle surjectivity at every remaining finite layer gives an
actual filtered preimage under the same quotient map.  This is a finite
induction, so it introduces no inverse-limit lifting assumption. -/
private theorem finite_filtered_surjective_of_cycle_surjective
    (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (q : ℕ) (hq : 0 < q) (m w u : ℤ) (hwindow : 0 ≤ m+u-w)
    (hsurj : ∀ s : ℤ, u ≤ s → s < (q:ℤ)+w-m →
      ∀ y : Ambient model Y (s,m+s),
        y ∈ cycles model Y ((q:ℤ)-(m+s)+w) (s,m+s) →
        ∃ x : Ambient model X (s,m+s),
          x ∈ cycles model X ((q:ℤ)-(m+s)+w) (s,m+s) ∧
          y-(model.classical.map f).pageMap 2 (s,m+s) x ∈
            boundaries model Y (1+(m+s)-w) (s,m+s))
    (z : BiHom m w (XModLambdaN (model.nu.functor.obj (Y.obj model.auxiliary)) q))
    (hz : FiltrationAtLeast model.syntheticTower u z) :
    ∃ a : BiHom m w (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q),
      FiltrationAtLeast model.syntheticTower u a ∧
      a ≫ XModLambdaN.map (model.nu.functor.map f) q = z := by
  let SX : SyntheticObject := .quotient q (.nu X)
  let SY : SyntheticObject := .quotient q (.nu Y)
  let fq := XModLambdaN.map (model.nu.functor.map f) q
  let M := model.convergentMap SX SY fq
  let top : ℤ := q+w-m
  induction hd : (top-u).toNat using Nat.strong_induction_on generalizing u z with
  | h d ih =>
    by_cases htop : top ≤ u
    · have hzero : z=0 := finite_high_filtration_zero Y q hq m w u
        (by dsimp [top] at htop; omega) z hz
      refine ⟨0,?_,?_⟩
      · exact (model.syntheticTower.filtrationSubmodule _ u (m,w)).zero_mem
      · simpa only [Limits.zero_comp] using hzero.symm
    · obtain ⟨zr,hzr⟩ := filtration_representative_exists model.syntheticTower
        (SY.obj model.nu model.auxiliary) (m,w) u z hz
      have hepi := finite_infinity_surjective_of_cycle_surjective X Y f q hq
        u (m+u) w (by dsimp [top] at htop; omega)
        (hsurj u le_rfl (by dsimp [top] at htop; omega))
      have hrange : (infinityGradedIso (model.convergence SY) (m,w) u).inv
          ((model.syntheticTower.filtration (SY.obj model.nu model.auxiliary)).toAssociatedGraded
            u (m,w) zr) ∈ Set.range ((model.family.functor.map fq).eInftyMap
              (u,m+u,w)).hom := hepi _
      obtain ⟨a,ha,hrem⟩ := (infinity_image_iff_lift M (m,w) u zr).mp hrange
      change BiHom m w (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q) at a
      rw [hzr] at hrem
      have hd' : (top-(u+1)).toNat < d := by omega
      obtain ⟨a',ha',heq⟩ := ih (top-(u+1)).toNat hd' (u+1) (by omega)
        (fun s hs ht => hsurj s (by omega) ht) (z-a≫fq) hrem rfl
      refine ⟨a+a',?_,?_⟩
      · exact (model.syntheticTower.filtrationSubmodule _ u (m,w)).add_mem ha
          (model.syntheticTower.filtrationSubmodule_antitone _ (m,w) (by omega) ha')
      · change (a+a')≫fq=z
        rw [Preadditive.add_comp,heq]
        abel

/-- Every suspended classical E2 label has a desuspension in the fixed
comparison; the construction uses its actual raw Adams representatives. -/
private theorem exists_desuspendsClass (X : ClassicalObject) (s t : ℤ)
    (sx : Ambient model (.shift 1 X) (s,t)) :
    ∃ x : Ambient model X (s,t-1),
      (model.classicalSuspension X).DesuspendsClass s t sx x := by
  let S := model.classicalSuspension X
  let DX := (model.classical.obj (X.obj model.auxiliary)).ssData (s,t-1)
  let DU := (model.classical.obj ((X.obj model.auxiliary)⟦(1:ℤ)⟧)).ssData (s,t)
  let PX := model.classicalTower.sequence (X.obj model.auxiliary)
  let PU := model.classicalTower.sequence ((X.obj model.auxiliary)⟦(1:ℤ)⟧)
  let TX := model.classicalTower.tower (X.obj model.auxiliary)
  let qu : Subobject.underlying.obj (DU.Z 0) ⟶ Ambient model (.shift 1 X) (s,t) := DU.pageπ 0 ≫
    eqToHom (by simp only [Ambient,DU,ClassicalObject.obj,KIP126.Core.SpectralSequence.Page,
      model.classical.firstPage,sub_self,Int.toNat_zero,Nat.cast_zero])
  haveI : Epi (DU.pageπ 0) := inferInstanceAs (Epi (cokernel.π _))
  haveI : Epi qu := by dsimp only [qu]; infer_instance
  obtain ⟨a,ha⟩ := (ModuleCat.epi_iff_surjective qu).mp inferInstance sx
  let sa := ((PU.ambient (s,t)).hom ((DU.Z 0).arrow a)).val
  let xb := S.desuspendFirstPage s t sa
  have hb_cycle : xb∈TX.cycles 2 (by omega) (s,t-1) :=
    desuspend_mem_raw_cycles X 2 (by omega) s t sa
      (((PU.ambient (s,t)).hom ((DU.Z 0).arrow a)).property)
  let v := (PX.ambient (s,t-1)).inv ⟨xb,hb_cycle⟩
  have hv : v ∈ (ModuleCat.subobjectModule DX.V) (DX.Z 0) := by
    apply (PX.cycles (s,t-1) 0 v).mpr
    have he : (PX.ambient (s,t-1)).hom v = ⟨xb,hb_cycle⟩ := by
      change ((PX.ambient (s,t-1)).inv ≫ (PX.ambient (s,t-1)).hom) _ = _
      rw [Iso.inv_hom_id]
      rfl
    rw [he]
    exact hb_cycle
  obtain ⟨b,hb⟩ := hv
  let qx : Subobject.underlying.obj (DX.Z 0) ⟶ Ambient model X (s,t-1) := DX.pageπ 0 ≫
    eqToHom (by simp only [Ambient,DX,KIP126.Core.SpectralSequence.Page,
      model.classical.firstPage,sub_self,Int.toNat_zero,Nat.cast_zero])
  refine ⟨qx b,a,b,ha,rfl,?_⟩
  have heb : (PX.ambient (s,t-1)).hom ((DX.Z 0).arrow b)=⟨xb,hb_cycle⟩ := by
    rw [hb]
    change ((PX.ambient (s,t-1)).inv ≫ (PX.ambient (s,t-1)).hom) _ = _
    rw [Iso.inv_hom_id]
    rfl
  change xb=((PX.ambient (s,t-1)).hom ((DX.Z 0).arrow b)).val
  rw [heb]

private theorem initial_cycle_class_iff (D : SSData (ModuleCat.{0} ℤ))
    (n : WithTop ℕ) (z : (Subobject.underlying.obj (D.Z 0) : ModuleCat ℤ)) :
    (∃ v : (Subobject.underlying.obj (D.Z n) : ModuleCat ℤ),
      (Subobject.ofLE (D.Z n) (D.Z 0) (D.Z_anti bot_le) ≫ D.pageπ 0) v=D.pageπ 0 z) ↔
      (D.Z 0).arrow z∈(ModuleCat.subobjectModule D.V) (D.Z n) := by
  let i := Subobject.ofLE (D.Z n) (D.Z 0) (D.Z_anti bot_le)
  constructor
  · rintro ⟨v,hv⟩
    have hz : D.pageπ 0 (z-i v)=0 := by
      rw [map_sub]
      exact sub_eq_zero.mpr hv.symm
    have hb := (subobject_cokernel_π_eq_zero_iff (D.B 0) (D.Z 0) (D.B_le_Z 0) _).mp hz
    have hb' : (D.Z 0).arrow (z-i v)∈(ModuleCat.subobjectModule D.V) (D.Z n) :=
      (ModuleCat.subobjectModule D.V).monotone
        ((D.B_mono le_top).trans ((D.B_le_Z ⊤).trans (D.Z_anti le_top))) hb
    have hv' : (D.Z 0).arrow (i v)∈(ModuleCat.subobjectModule D.V) (D.Z n) := by
      change (i≫(D.Z 0).arrow) v∈_
      rw [Subobject.ofLE_arrow]
      exact ⟨v,rfl⟩
    have h := ((ModuleCat.subobjectModule D.V) (D.Z n)).add_mem hb' hv'
    rw [map_sub,sub_add_cancel] at h
    exact h
  · rintro ⟨v,hv⟩
    refine ⟨v,?_⟩
    have he : i v=z := by
      apply (ModuleCat.mono_iff_injective (D.Z 0).arrow).mp inferInstance
      change (i≫(D.Z 0).arrow) v=(D.Z 0).arrow z
      rw [Subobject.ofLE_arrow]
      exact hv
    change D.pageπ 0 (i v)=D.pageπ 0 z
    rw [he]

private theorem initial_cycle_label_iff (X : ClassicalObject) (c : ℤ) (p : ℤ×ℤ)
    (z : (Subobject.underlying.obj (((model.classical.obj (X.obj model.auxiliary)).ssData p).Z 0) : ModuleCat ℤ)) :
    cycleLabel model X 0 p z∈cycles model X c p ↔
      ((((model.classicalTower.sequence (X.obj model.auxiliary)).ambient p).hom
        ((((model.classical.obj (X.obj model.auxiliary)).ssData p).Z 0).arrow z)).val)∈
          (model.classicalTower.tower (X.obj model.auxiliary)).cycles ((c-1).toNat+2) (by omega) p := by
  let D := (model.classical.obj (X.obj model.auxiliary)).ssData p
  rw [←(model.classicalTower.sequence (X.obj model.auxiliary)).cycles p (c-1).toNat]
  rw [←initial_cycle_class_iff D (↑(c-1).toNat) z]
  change (∃v, cycleLabel model X (↑(c-1).toNat) p v=cycleLabel model X 0 p z) ↔ _
  simp only [cycleLabel,Subobject.ofLE_refl,Category.id_comp]
  constructor
  · rintro ⟨v,hv⟩
    refine ⟨v,?_⟩
    apply (ModuleCat.mono_iff_injective (eqToHom _)).mp inferInstance
    exact hv
  · rintro ⟨v,hv⟩
    refine ⟨v,?_⟩
    exact congrArg (fun a=>(eqToHom _ : D.page 0 ⟶ (model.classical.obj (X.obj model.auxiliary)).Page 2 p) a) hv

/-- The fixed tower suspension preserves exactly the paper cycle index. -/
private theorem desuspendsClass_cycle_iff (X : ClassicalObject) (k s t : ℤ)
    (sx : Ambient model (.shift 1 X) (s,t)) (x : Ambient model X (s,t-1))
    (h : (model.classicalSuspension X).DesuspendsClass s t sx x) :
    sx∈cycles model (.shift 1 X) k (s,t) ↔ x∈cycles model X k (s,t-1) := by
  obtain ⟨a,b,ha,hb,hab⟩ := h
  have ha' : cycleLabel model (.shift 1 X) 0 (s,t) a=sx := by
    simpa only [cycleLabel,Subobject.ofLE_refl,Category.id_comp,ClassicalObject.obj] using ha
  have hb' : cycleLabel model X 0 (s,t-1) b=x := by
    simpa only [cycleLabel,Subobject.ofLE_refl,Category.id_comp] using hb
  rw [←ha',←hb',initial_cycle_label_iff,initial_cycle_label_iff,←hab]
  exact (desuspend_mem_raw_cycles_iff X ((k-1).toNat+2) (by omega) s t _).symm

/-- The existing public Surj condition supplies complete ordinary h cycle
coverage, including j=K-1 and its full denominator R+K-2. -/
private theorem finite_layer_surj_ordinary_h_cycles
    (T : TriangleData model.auxiliary) (R K : ℕ) (s t : ℤ)
    (hsurj : KIP126.ProofTools.Standard.MahowaldLeibnizFiniteLayerSurjectivity T R K s t)
    (j : ℕ) (hj : 1≤j) (hjK : j<K)
    (y : Ambient model (.shift 1 T.X) (s+R+j,t+R+j))
    (hy : y∈cycles model (.shift 1 T.X) ((K:ℤ)-j) (s+R+j,t+R+j)) :
    ∃ z : Ambient model T.Z (s+R+j,t+R+j),
      z∈cycles model T.Z ((K:ℤ)-j) (s+R+j,t+R+j) ∧
      y-(model.classical.map T.h).pageMap 2 (s+R+j,t+R+j) z ∈
        boundaries model (.shift 1 T.X) ((R:ℤ)+j-1) (s+R+j,t+R+j) := by
  obtain ⟨a,ha⟩ := exists_desuspendsClass T.X (s+R+j) (t+R+j) y
  have hac : IsCycle model T.X ((K:ℤ)-j) (s+R+j,t+R+j-1) a :=
    ⟨by omega,(desuspendsClass_cycle_iff T.X _ _ _ y a ha).mp hy⟩
  obtain ⟨z,hz,b,hb,hab⟩ := hsurj j hj hjK a hac
  refine ⟨z,hz.2,?_⟩
  exact (desuspendsClass_boundary_iff T.X _ _ _ _ _
    (suspension_desuspends_sub T.X _ _ _ _ _ _ ha hb)).mpr hab.2

/-- The public finite-layer surjectivity hypothesis yields actual filtered
preimages under Q_(c+K)(nu h), without a separate matrix or lift assumption. -/
private theorem finite_layer_surj_ordinary_h_filtered
    (T : TriangleData model.auxiliary) (c K : ℕ) (hK : 2≤K) (S V : ℤ)
    (hsurj : KIP126.ProofTools.Standard.MahowaldLeibnizFiniteLayerSurjectivity
      T (c+2) K (S-(c+2:ℕ)) (V-(c+2:ℕ)+1))
    (a : BiHom (V-S+1) (V-c+1)
      (XModLambdaN (model.nu.functor.obj ((ClassicalObject.shift 1 T.X).obj model.auxiliary)) (c+K)))
    (ha : FiltrationAtLeast model.syntheticTower (S+1) a) :
    ∃ b : BiHom (V-S+1) (V-c+1)
      (XModLambdaN (model.nu.functor.obj (T.Z.obj model.auxiliary)) (c+K)),
      FiltrationAtLeast model.syntheticTower (S+1) b ∧
      b≫XModLambdaN.map (model.nu.functor.map T.h) (c+K)=a := by
  apply finite_filtered_surjective_of_cycle_surjective T.Z (.shift 1 T.X) T.h
    (c+K) (by omega) (V-S+1) (V-c+1) (S+1) (by omega) ?_ a ha
  intro k hk hktop
  let j := (k-S).toNat
  have hj : (j:ℤ)=k-S := by dsimp [j]; omega
  have hj1 : 1≤j := by omega
  have hjK : j<K := by omega
  have h := finite_layer_surj_ordinary_h_cycles T (c+2) K
    (S-(c+2:ℕ)) (V-(c+2:ℕ)+1) hsurj j hj1 hjK
  have hs : S-(c+2:ℕ)+(c+2:ℕ)+(j:ℤ)=k := by omega
  have ht : V-(c+2:ℕ)+1+(c+2:ℕ)+(j:ℤ)=V-S+1+k := by omega
  have hc : (c+K:ℕ)-(V-S+1+k)+(V-(c:ℤ)+1)=(K:ℤ)-j := by omega
  have hb : 1+(V-S+1+k)-(V-(c:ℤ)+1)=(c+2:ℕ)+(j:ℤ)-1 := by omega
  rw [hs,ht] at h
  rw [hc,hb]
  exact h

end
end KIP126.ProofTools.Internal.MahowaldLeibniz
