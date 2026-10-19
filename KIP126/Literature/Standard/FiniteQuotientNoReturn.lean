module

import all KIP126.Literature.Standard
import KIP126.AdamsSynthetic.Standard.Operations
import KIP126.AdamsSynthetic.Standard.Separation

/-! Spherewise no-return for the actual finite λ quotients.

The finite-window argument is adapted from Kervaire126 bbac1fc05843
(MIT), retained in GeneralizedMahowald/Filtration.lean and NoReturn.lean;
the filtered-map and cofiber arguments are copied as foundational proofs.
Only the owning upstream modules are consumed here. The separation and
infinity-page presentations remain their existing upstream responsibilities.
Vanishing after sphere precomposition is the conclusion: no inference to
vanishing of an arbitrary synthetic morphism is made.
-/

@[expose] section
namespace KIP126.Literature.Standard.Internal

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.Synthetic.SpectralSequence KIP126.AdamsSynthetic
open KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option Elab.async false

section GeneralFiltration
universe u v
variable {Syn : Type u} [SyntheticCategory.{u,v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  {H : Syn} {unit : S_0_0 ⟶ H} {F : SyntheticAdamsFamily Syn}
  {P : SyntheticTowerPresentation unit F} {X Y : Syn} {g : X ⟶ Y}
  {cx : SyntheticTowerConvergence P X} {cy : SyntheticTowerConvergence P Y}

private theorem filtration_at_zero (P : SyntheticTowerPresentation unit F)
    (X : Syn) (m w : ℤ) (a : BiHom m w X) : FiltrationAtLeast P 0 a := by
  refine ⟨a ≫ (P.tower X).zeroIso.inv, ?_⟩
  change (a ≫ (P.tower X).zeroIso.inv) ≫ (P.tower X).projection 0 = a
  simp only [AbstractAdamsTower.projection, Int.toNat_zero, (P.tower X).map_self]
  erw [Category.assoc, Category.id_comp, Iso.inv_hom_id, Category.comp_id]

private theorem filtration_iff_of_infinity_zero (c : SyntheticTowerConvergence P X)
    (s t m w : ℤ) (hst : s ≤ t)
    (hz : ∀ j, s ≤ j → j < t → IsZero (((F.obj X).sequence.ssData (j,m+j,w)).eInfty))
    (a : BiHom m w X) : FiltrationAtLeast P s a ↔ FiltrationAtLeast P t a := by
  have hgraded (j : ℤ) (hj : s ≤ j) (hjt : j < t) :
      IsZero ((P.filtration X).associatedGraded j (m,w)) :=
    (hz j hj hjt).of_iso (towerGradedIso c (m,w) j).symm
  have he := (P.filtration X).eq_of_associatedGraded_isZero s t (m,w) hst hgraded
  have he' := congrArg (fun Q => a ∈
    (ModuleCat.subobjectModule (syntheticHomotopy X (m,w))) Q) he
  simpa only [SyntheticTowerPresentation.filtration, OrderIso.apply_symm_apply,
    FiltrationAtLeast] using Iff.of_eq he'

private theorem filtration_representative_exists (P : SyntheticTowerPresentation unit F)
    (A : Syn) (p : ℤ × ℤ) (s : ℤ) (a : BiHom p.1 p.2 A)
    (ha : a ∈ P.filtrationSubmodule A s p) :
    ∃ a' : (Subobject.underlying.obj ((P.filtration A).F s p) : ModuleCat.{v} ℤ),
      ((P.filtration A).F s p).arrow a' = a := by
  have hm : a ∈ ModuleCat.subobjectModule _ ((P.filtration A).F s p) := by
    simpa [SyntheticTowerPresentation.filtration, syntheticHomotopy] using ha
  exact hm

private theorem map_preserves_filtration
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

end GeneralFiltration

private theorem finite_infinity_zero_outside (X : ClassicalObject) (q : ℕ) (hq : 0 < q)
    (s t w : ℤ) (hw : ¬ (0 ≤ t-w ∧ t-w < q)) :
    IsZero (((model.family.quotient (model.nu.functor.obj (X.obj model.auxiliary)) q).sequence.ssData
      (s,t,w)).eInfty) := by
  haveI : Subsingleton (KIP126.Literature.finiteEInftyModel model X q (s,t) w) := by
    simp only [KIP126.Literature.finiteEInftyModel, hw, ite_false]
    infer_instance
  haveI : Subsingleton (((model.family.quotient
      (model.nu.functor.obj (X.obj model.auxiliary)) q).sequence.ssData (s,t,w)).eInfty) :=
    (KIP126.Literature.Standard.eInfinity_finite X q hq (s,t) w).injective.subsingleton
  exact ModuleCat.isZero_of_subsingleton _

private theorem finite_high_filtration_zero (X : ClassicalObject) (q : ℕ) (hq : 0 < q)
    (m w s : ℤ) (hs : (q:ℤ) ≤ m+s-w)
    (a : BiHom m w (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
    (ha : FiltrationAtLeast model.syntheticTower s a) : a = 0 := by
  apply synthetic_homotopy_separated (.nu X) q m w a
  intro j
  by_cases hj : s ≤ (j:ℤ)
  · exact (filtration_iff_of_infinity_zero (model.convergence (.quotient q (.nu X)))
      s j m w hj (fun k hk _ => finite_infinity_zero_outside X q hq k (m+k) w (by omega)) a).mp ha
  · exact model.syntheticTower.filtrationSubmodule_antitone _ (m,w) (by omega) ha

private theorem nu_infinity_zero_above (X : ClassicalObject) (s t w : ℤ) (hw : t < w) :
    IsZero (((model.family.nu model.nu (X.obj model.auxiliary)).sequence.ssData (s,t,w)).eInfty) := by
  haveI : Subsingleton (KIP126.Literature.nuEInftyModel model X (s,t) w) := by
    simp only [KIP126.Literature.nuEInftyModel, not_le.mpr hw, ite_false]
    infer_instance
  haveI : Subsingleton (((model.family.nu model.nu (X.obj model.auxiliary)).sequence.ssData
      (s,t,w)).eInfty) :=
    (KIP126.Literature.Standard.eInfinity_nu X (s,t) w).injective.subsingleton
  exact ModuleCat.isZero_of_subsingleton _

private theorem nonreturn_at_window_end (X Y : ClassicalObject)
    (j : ℕ) (hj : 0 < j) (d : ℤ) (hd : d ≤ -(j:ℤ)) (m w : ℤ)
    (c : BiHom m w ((SyntheticCategory.biShift (0,d)).obj
      (model.nu.functor.obj (X.obj model.auxiliary))))
    (z : (SyntheticCategory.biShift (0,d)).obj
      (model.nu.functor.obj (X.obj model.auxiliary)) ⟶
        XModLambdaN (model.nu.functor.obj (Y.obj model.auxiliary)) j) : c ≫ z = 0 := by
  let A : SyntheticObject := .shift (0,d) (.nu X)
  let B : SyntheticObject := .quotient j (.nu Y)
  let L : ℤ := w-m-d
  have hzA (k : ℤ) (hk : k < L) :
      IsZero (((model.family.obj (A.obj model.nu model.auxiliary)).sequence.ssData
        (k,m+k,w)).eInfty) := by
    have hz := nu_infinity_zero_above X k (m+k) (w-d) (by dsimp [L] at hk; omega)
    let e := towerInfinityIso (model.convergence (.nu X)) (model.convergence A)
      ((essShift (0,d)).filtered (.nu X) (m,w-d)) k
    have he := hz.of_iso e.symm
    have hw : w-d+d=w := by omega
    simpa only [e, A, Prod.fst_add, Prod.snd_add, add_zero, hw] using he
  have hc0 := filtration_at_zero model.syntheticTower _ m w c
  have hcL : FiltrationAtLeast model.syntheticTower L c := by
    by_cases hL : L ≤ 0
    · exact model.syntheticTower.filtrationSubmodule_antitone _ (m,w) hL hc0
    · exact (filtration_iff_of_infinity_zero (model.convergence A) 0 L m w
        (by omega) (fun k _ hk => hzA k hk) c).mp hc0
  have hcz : FiltrationAtLeast model.syntheticTower L (c ≫ z) :=
    map_preserves_filtration (model.convergentMap A B z) (m,w) L c hcL
  exact finite_high_filtration_zero Y j hj m w L (by dsimp [L]; omega) (c ≫ z) hcz

private theorem negative_shift_nu_to_quotient_zero (X Y : ClassicalObject)
    (j : ℕ) (hj : 0 < j) (m w : ℤ)
    (c : BiHom m w ((SyntheticCategory.biShift (0,-(j:ℤ)-1)).obj
      (model.nu.functor.obj (X.obj model.auxiliary))))
    (z : (SyntheticCategory.biShift (0,-(j:ℤ)-1)).obj
      (model.nu.functor.obj (X.obj model.auxiliary)) ⟶
        XModLambdaN (model.nu.functor.obj (Y.obj model.auxiliary)) j) : c ≫ z = 0 := by
  exact nonreturn_at_window_end X Y j hj (-(j:ℤ)-1) (by omega) m w c z

section CofiberExactness
universe u v
variable {Syn : Type u} [SyntheticCategory.{u,v} Syn]
  [HasFunctorialCofiber (C := Syn)]

private theorem quotient_maps_difference_factors {A B : Syn} (j : ℕ)
    (a b : XModLambdaN A j ⟶ B)
    (hab : XModLambdaN.incl A j ≫ a = XModLambdaN.incl A j ≫ b) :
    ∃ z : ((SyntheticCategory.biShift (0,-(j:ℤ))).obj A)⟦(1:ℤ)⟧ ⟶ B,
      a-b = XModLambdaN.proj A j ≫ z := by
  apply Triangle.yoneda_exact₃ (XModLambdaN.cofiberTriangle A j)
    (XModLambdaN.cofiberTriangle_distinguished A j) (a-b)
  change XModLambdaN.incl A j ≫ (a-b) = 0
  rw [Preadditive.comp_sub,hab,sub_self]

private theorem quotient_maps_equal_on_spheres_of_no_return {A B : Syn} (j : ℕ)
    (a b : XModLambdaN A j ⟶ B)
    (hab : XModLambdaN.incl A j ≫ a = XModLambdaN.incl A j ≫ b)
    (hzero : ∀ (m w : ℤ)
      (c : BiHom m w (((SyntheticCategory.biShift (0,-(j:ℤ))).obj A)⟦(1:ℤ)⟧))
      (z : ((SyntheticCategory.biShift (0,-(j:ℤ))).obj A)⟦(1:ℤ)⟧ ⟶ B), c ≫ z = 0) :
    ∀ (m w : ℤ) (c : BiHom m w (XModLambdaN A j)), c ≫ a = c ≫ b := by
  obtain ⟨z,hz⟩ := quotient_maps_difference_factors j a b hab
  intro m w c
  apply sub_eq_zero.mp
  rw [←Preadditive.comp_sub,hz,←Category.assoc]
  exact hzero m w (c ≫ XModLambdaN.proj A j) z

end CofiberExactness

/-- Agreement on the actual quotient inclusion forces agreement after every
bigraded sphere precomposition. -/
private theorem quotient_nu_maps_equal_on_spheres
    (X Y : ClassicalObject) (j : ℕ) (hj : 0 < j)
    (a b : XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) j ⟶
      XModLambdaN (model.nu.functor.obj (Y.obj model.auxiliary)) j)
    (hab : XModLambdaN.incl _ j ≫ a = XModLambdaN.incl _ j ≫ b) :
    ∀ (m w : ℤ)
      (c : BiHom m w (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) j)),
      c ≫ a = c ≫ b := by
  apply quotient_maps_equal_on_spheres_of_no_return j a b hab
  intro m w c z
  let V := model.nu.functor.obj (X.obj model.auxiliary)
  let ε : ((SyntheticCategory.biShift (0,-(j:ℤ))).obj V)⟦(1:ℤ)⟧ ≅
      (SyntheticCategory.biShift (0,-(j:ℤ)-1)).obj
        (model.nu.functor.obj ((ClassicalObject.shift 1 X).obj model.auxiliary)) :=
    (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).symm.app _ ≪≫
      (SyntheticCategory.biShift_comp (0,-(j:ℤ)) (1,0)).app V ≪≫
      eqToIso (congrArg (fun p => (SyntheticCategory.biShift p).obj V)
        (show (0,-(j:ℤ))+(1,0)=(1,1)+(0,-(j:ℤ)-1) by ext <;> simp)) ≪≫
      (SyntheticCategory.biShift_comp (1,1) (0,-(j:ℤ)-1)).symm.app V ≪≫
      (SyntheticCategory.biShift (0,-(j:ℤ)-1)).mapIso (model.nu.suspensionIso _).symm
  have h := negative_shift_nu_to_quotient_zero (.shift 1 X) Y j hj m w
    (c ≫ ε.hom) (ε.inv ≫ z)
  simpa only [Category.assoc,Iso.hom_inv_id_assoc] using h

/-- An endomorphism killed by the actual inclusion is a sphere ghost. -/
private theorem quotient_nu_endomorphism_sphere_ghost
    (X : ClassicalObject) (j : ℕ) (hj : 0 < j)
    (a : XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) j ⟶
      XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) j)
    (ha : XModLambdaN.incl _ j ≫ a = 0) :
    ∀ (m w : ℤ)
      (c : BiHom m w (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) j)),
      c ≫ a = 0 := by
  intro m w c
  simpa only [comp_zero] using
    quotient_nu_maps_equal_on_spheres X X j hj a 0 (by simpa using ha) m w c

end
end KIP126.Literature.Standard.Internal
