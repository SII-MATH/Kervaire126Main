module

public import KIP126.Main.Conditions
public import KIP126.ProofTools.Operations

/-! Sphere and finite-quotient label transports used in the Section 7 proof.
Adapted from NuTargetHelpers.lean:321–524, 614–628, 739–775 at the fixed
Kervaire126 source bbac1fc05843 (MIT). All data belong to the fixed system. -/

@[expose] section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace KIP126.Main.Internal
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard KIP126.Literature
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
noncomputable section

abbrev sphereLabel (s t : ℤ) (k : ℕ) (x : model.classical.sphere.Page 2 (s,t)) :=
  model.comparison.sphereE2 s t k x

abbrev quotientLabel (q : ℕ) (s t : ℤ) (k : ℕ)
    (x : model.classical.sphere.Page 2 (s,t)) :=
  (model.family.quotientProjection (S_0_0 : SyntheticSpectrum) q).pageMap 2 (s,t,t-k)
    (sphereLabel s t k x)

theorem family_page_id (A : SyntheticSpectrum) (r : ℤ) (i : Tridegree) :
    familyPageMap model.family (𝟙 A) r i = 𝟙 _ := by
  change (model.family.map (𝟙 A)).pageMap r i = 𝟙 _
  rw [SyntheticAdamsFamily.map_id,SpectralSequenceMorphism.pageMap_id]

theorem sphere_label_from_nu (k : ℕ) (s t : ℤ)
    (x : model.classical.sphere.Page 2 (s,t)) :
    familyPageMap model.family model.nu.unitIso.hom 2 (s,t,t-k)
      (targetNuLabel model .sphere s t k x) = sphereLabel s t k x := by
  let z : (model.family.obj (nuZero model .sphere)).E₂ (s,t,t-k) := by
    simpa [SyntheticAdamsSS.E₂] using model.comparison.nuE2 .sphere 0 s t k x
  exact (ConcreteCategory.congr_hom (family_page_comp
    (SyntheticCategory.biShift_zero.hom.app _) model.nu.unitIso.hom 2 (s,t,t-k)) z).trans
      (model.comparison.sphere_nu s t k x)

theorem sphere_label_to_nu (k : ℕ) (s t : ℤ)
    (x : model.classical.sphere.Page 2 (s,t)) :
    familyPageMap model.family model.nu.unitIso.inv 2 (s,t,t-k)
      (sphereLabel s t k x) = targetNuLabel model .sphere s t k x := by
  rw [←sphere_label_from_nu k s t x,←ModuleCat.comp_apply,family_page_comp,
    Iso.hom_inv_id,family_page_id]
  rfl

theorem sphere_quotient_label_to_nu (q k : ℕ) (s t : ℤ)
    (x : model.classical.sphere.Page 2 (s,t)) :
    familyPageMap model.family (XModLambdaN.map model.nu.unitIso.inv q) 2 (s,t,t-k)
      (quotientLabel q s t k x) = finiteTargetLabel model .sphere q s t k x := by
  change familyPageMap model.family (XModLambdaN.map model.nu.unitIso.inv q) 2 (s,t,t-k)
    (familyPageMap model.family (XModLambdaN.incl _ q) 2 (s,t,t-k) (sphereLabel s t k x)) = _
  rw [←ModuleCat.comp_apply,family_page_comp,←XModLambdaN.incl_naturality,
    ←family_page_comp,ModuleCat.comp_apply,sphere_label_to_nu]
  rfl

theorem sphere_quotient_label_from_nu (q k : ℕ) (s t : ℤ)
    (x : model.classical.sphere.Page 2 (s,t)) :
    familyPageMap model.family (XModLambdaN.map model.nu.unitIso.hom q) 2 (s,t,t-k)
      (finiteTargetLabel model .sphere q s t k x) = quotientLabel q s t k x := by
  rw [←sphere_quotient_label_to_nu q k s t x,←ModuleCat.comp_apply,family_page_comp,
    ←model.quotients.functoriality.map_comp,Iso.inv_hom_id,
    model.quotients.functoriality.map_id,family_page_id]
  rfl

theorem finite_sphere_infinity_cycle_label_exists
    (q k : ℕ) (hq : 0 < q) (hkq : k < q) (s t : ℤ)
    (e : ((model.family.quotient (S_0_0 : SyntheticSpectrum) q).sequence.ssData (s,t,t-k)).eInfty) :
    ∃ x : model.classical.sphere.Page 2 (s,t),
      x ∈ cycles model .sphere ((q:ℤ)-k) (s,t) ∧
      HasInfinityRepresentative (model.family.quotient (S_0_0 : SyntheticSpectrum) q) 2 (s,t,t-k)
        (quotientLabel q s t k x) e := by
  let P := KIP126.Literature.Standard.infinityFiniteWindow .sphere q hq (s,t) (t-k)
    (by constructor <;> omega)
  let f := XModLambdaN.map model.nu.unitIso.hom q
  let g := XModLambdaN.map model.nu.unitIso.inv q
  have hgf : g ≫ f = 𝟙 _ := by
    dsimp only [f,g]
    rw [←model.quotients.functoriality.map_comp,Iso.inv_hom_id,model.quotients.functoriality.map_id]
  have heq : (model.family.map f).eInftyMap (s,t,t-k)
      ((model.family.map g).eInftyMap (s,t,t-k) e) = e := by
    change ((model.family.map g).eInftyMap (s,t,t-k) ≫
      (model.family.map f).eInftyMap (s,t,t-k)) e = e
    rw [←SpectralSequenceMorphism.eInftyMap_comp,←SyntheticAdamsFamily.map_comp,hgf,
      SyntheticAdamsFamily.map_id,SpectralSequenceMorphism.eInftyMap_id]
    rfl
  obtain ⟨c,hc⟩ := Quotient.exists_rep (P ((model.family.map g).eInftyMap (s,t,t-k) e))
  have hn := (finite_target_label_iff .sphere q hq s t k hkq c _).mpr hc.symm
  have h := family_infinity_representative_map f (s,t,t-k) _ _ hn
  rw [sphere_quotient_label_from_nu,heq] at h
  refine ⟨c.val,?_,h⟩
  have hc' := c.property
  change c.val ∈ cycles model .sphere ((q:ℤ)-t+(t-k)) (s,t) at hc'
  exact (congrArg (fun j : ℤ => c.val ∈ cycles model .sphere j (s,t))
    (show (q:ℤ)-t+(t-k)=(q:ℤ)-k by omega)).mp hc'

theorem finite_sphere_filtration_has_cycle_label
    (q k : ℕ) (hq : 0 < q) (hkq : k < q) (s t : ℤ)
    (a : BiHom (t-s) (t-k) (XModLambdaN (S_0_0 : SyntheticSpectrum) q))
    (ha : FiltrationAtLeast model.syntheticTower s a) :
    ∃ x : model.classical.sphere.Page 2 (s,t),
      x ∈ cycles model .sphere ((q:ℤ)-k) (s,t) ∧
      Detects (model.convergence (.quotient q .sphere)) (s,t,t-k) (quotientLabel q s t k x) a := by
  let F := model.syntheticTower.filtration (XModLambdaN (S_0_0 : SyntheticSpectrum) q)
  obtain ⟨a',ha'⟩ := filtration_representative_exists model.syntheticTower _ (t-s,t-k) s a ha
  let gr := F.toAssociatedGraded s (t-s,t-k) a'
  let e := ((model.convergence (.quotient q .sphere)).identification (s,t,t-k)).inv gr
  have he : ((model.convergence (.quotient q .sphere)).identification (s,t,t-k)).hom e = gr :=
    ConcreteCategory.congr_hom ((model.convergence (.quotient q .sphere)).identification (s,t,t-k)).inv_hom_id gr
  obtain ⟨x,hc,hx⟩ := finite_sphere_infinity_cycle_label_exists q k hq hkq s t e
  exact ⟨x,hc,e,hx,a',ha',he⟩

theorem permanent_cycle_iff_mem (X : ClassicalObject) (p : ℤ × ℤ)
    (x : (model.classical.obj (X.obj model.auxiliary)).Page 2 p) :
    IsPermanentCycle (model.classical.obj (X.obj model.auxiliary)) p x ↔
      x ∈ permanentCycles model X p := by
  let E := model.classical.obj (X.obj model.auxiliary)
  let P := E.ssData p
  have normalize (P : SSData (ModuleCat ℤ)) (n : WithTop ℕ) (hn : n=0) :
      Subobject.ofLE (P.Z ⊤) (P.Z n) (P.Z_anti le_top) ≫ P.pageπ n =
        Subobject.ofLE (P.Z ⊤) (P.Z 0) (P.Z_anti le_top) ≫ P.pageπ 0 ≫
          eqToHom (congrArg P.page hn.symm) := by
    subst n
    simp only [eqToHom_refl,Category.comp_id]
  have h := normalize P (↑(2-E.r₀).toNat) (by dsimp only [E]; rw [model.classical.firstPage]; rfl)
  constructor
  · rintro ⟨z,hz⟩
    refine ⟨z,?_⟩
    exact (congrArg (fun f => f z) h).symm.trans hz
  · rintro ⟨z,hz⟩
    refine ⟨z,?_⟩
    exact (congrArg (fun f => f z) h).trans hz

theorem sphere_permanent_first_quotient_lift (s t : ℤ)
    (x : model.classical.sphere.Page 2 (s,t))
    (hx : IsPermanentCycle model.classical.sphere (s,t) x) :
    ∃ a : BiHom (t-s) t (S_0_0 : SyntheticSpectrum),
      (KIP126.Literature.sphereFirstQuotient model) s t (quotientClass 1 a) = x := by
  obtain ⟨a,ha⟩ := (KIP126.Literature.Standard.selected_permanent_lift .sphere s t x).mp hx
  let f := SyntheticCategory.biShift_zero.hom.app (model.nu.functor.obj SphereSpectrum) ≫ model.nu.unitIso.hom
  refine ⟨a ≫ f,?_⟩
  have hc : quotientClass 1 (a ≫ f) = quotientClass 1 a ≫ XModLambdaN.map f 1 := by
    unfold quotientClass
    simp only [Category.assoc]
    exact congrArg (fun h => a ≫ h) (XModLambdaN.incl_naturality f 1)
  rw [hc,ha]
  exact sphere_first_quotient_label s t x


theorem sphere_quotient_high_filtration_zero (q : ℕ) (hq : 0 < q)
    (m w s : ℤ) (hs : (q:ℤ) ≤ m+s-w)
    (a : BiHom m w (XModLambdaN (S_0_0 : SyntheticSpectrum) q))
    (ha : FiltrationAtLeast model.syntheticTower s a) : a = 0 := by
  let g : XModLambdaN (S_0_0 : SyntheticSpectrum) q ⟶ XModLambdaN (model.nu.functor.obj SphereSpectrum) q :=
    XModLambdaN.map model.nu.unitIso.inv q
  let f : XModLambdaN (model.nu.functor.obj SphereSpectrum) q ⟶ XModLambdaN (S_0_0 : SyntheticSpectrum) q :=
    XModLambdaN.map model.nu.unitIso.hom q
  have hm := map_preserves_filtration
    (model.convergentMap (.quotient q .sphere) (.quotient q (.nu .sphere)) g)
    (m,w) s a ha
  have hz := finite_high_filtration_zero .sphere q hq m w s hs (a ≫ g) hm
  have hgf : g ≫ f = 𝟙 _ := by
    dsimp only [f,g]
    rw [←model.quotients.functoriality.map_comp,Iso.inv_hom_id,model.quotients.functoriality.map_id]
    rfl
  have he := congrArg (fun z => z ≫ f) hz
  change (a ≫ g) ≫ f = 0 ≫ f at he
  rw [Category.assoc,hgf,Category.comp_id,zero_comp] at he
  exact he

theorem finite_sphere_frame (q k : ℕ) (hq : 0 < q) (hkq : k < q) (s t : ℤ)
    (c : cycles model .sphere ((q:ℤ)-t+(t-k)) (s,t))
    (hframe : ∀ y : CycleQuotient model .sphere ((q:ℤ)-t+(t-k)) (1+t-(t-k)) (s,t),
      y = 0 ∨ y = subquotientClass _ _ c) :
    ∀ e : ((model.family.quotient (S_0_0 : SyntheticSpectrum) q).sequence.ssData (s,t,t-k)).eInfty,
      e = 0 ∨ HasInfinityRepresentative (model.family.quotient (S_0_0 : SyntheticSpectrum) q)
        2 (s,t,t-k) (quotientLabel q s t k c.val) e := by
  intro e
  let P := KIP126.Literature.Standard.infinityFiniteWindow .sphere q hq (s,t) (t-k)
    (by constructor <;> omega)
  let f := XModLambdaN.map model.nu.unitIso.hom q
  let g := XModLambdaN.map model.nu.unitIso.inv q
  have hgf : g ≫ f = 𝟙 _ := by
    dsimp only [f,g]
    rw [←model.quotients.functoriality.map_comp,Iso.inv_hom_id,model.quotients.functoriality.map_id]
  have heq : (model.family.map f).eInftyMap (s,t,t-k)
      ((model.family.map g).eInftyMap (s,t,t-k) e) = e := by
    change ((model.family.map g).eInftyMap (s,t,t-k) ≫
      (model.family.map f).eInftyMap (s,t,t-k)) e = e
    rw [←SpectralSequenceMorphism.eInftyMap_comp,←SyntheticAdamsFamily.map_comp,hgf,
      SyntheticAdamsFamily.map_id,SpectralSequenceMorphism.eInftyMap_id]
    rfl
  rcases hframe (P ((model.family.map g).eInftyMap (s,t,t-k) e)) with hz | hz
  · left
    have hzero : (model.family.map g).eInftyMap (s,t,t-k) e = 0 :=
      P.injective (hz.trans (map_zero P).symm)
    rw [hzero,map_zero] at heq
    exact heq.symm
  · right
    have hn := (finite_target_label_iff .sphere q hq s t k hkq c _).mpr hz
    have h := family_infinity_representative_map f (s,t,t-k) _ _ hn
    rw [sphere_quotient_label_from_nu,heq] at h
    exact h

theorem finite_detection_peel (q : ℕ) (i : Tridegree)
    (x : (model.family.quotient (S_0_0 : SyntheticSpectrum) q).E₂ i)
    (hframe : ∀ e : ((model.family.quotient (S_0_0 : SyntheticSpectrum) q).sequence.ssData i).eInfty,
      e = 0 ∨ HasInfinityRepresentative (model.family.quotient (S_0_0 : SyntheticSpectrum) q) 2 i x e)
    (c : BiHom (i.2.1-i.1) i.2.2 (XModLambdaN (S_0_0 : SyntheticSpectrum) q))
    (hc : Detects (model.convergence (.quotient q .sphere)) i x c)
    (a : BiHom (i.2.1-i.1) i.2.2 (XModLambdaN (S_0_0 : SyntheticSpectrum) q))
    (ha : FiltrationAtLeast model.syntheticTower i.1 a) :
    ∃ b : Bool, FiltrationAtLeast model.syntheticTower (i.1+1) (a-(if b then c else 0)) := by
  let F := model.syntheticTower.filtration (XModLambdaN (S_0_0 : SyntheticSpectrum) q)
  obtain ⟨a',ha'⟩ := filtration_representative_exists model.syntheticTower _
    (i.2.1-i.1,i.2.2) i.1 a ha
  let gr := F.toAssociatedGraded i.1 (i.2.1-i.1,i.2.2) a'
  let e := ((model.convergence (.quotient q .sphere)).identification i).inv gr
  have he : ((model.convergence (.quotient q .sphere)).identification i).hom e = gr :=
    ConcreteCategory.congr_hom ((model.convergence (.quotient q .sphere)).identification i).inv_hom_id gr
  rcases hframe e with hz | hz
  · refine ⟨false,?_⟩
    have hdet : Detects (model.convergence (.quotient q .sphere)) i 0 a :=
      ⟨0,HasInfinityRepresentative.zero _ 2 (by decide) i,a',ha',by rw [←hz]; exact he⟩
    simpa only [Bool.false_eq_true, ↓reduceIte,sub_zero] using
      detects_zero_filtration (model.convergence (.quotient q .sphere)) i hdet
  · refine ⟨true,?_⟩
    have hdet : Detects (model.convergence (.quotient q .sphere)) i x a := ⟨e,hz,a',ha',he⟩
    simpa only [↓reduceIte] using detects_sub_filtration
      (model.convergence (.quotient q .sphere)) i hdet hc

end
end KIP126.Main.Internal
