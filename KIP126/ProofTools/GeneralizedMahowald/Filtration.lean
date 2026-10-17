module
public import KIP126.ProofTools.Laws
public import KIP126.AdamsSynthetic.Standard.Separation

/-! The finite-window filtration arguments in the retained Mahowald proof.
Separation is the original upstream tower responsibility; no tool conclusion
or new geometric input is assumed here. Source bbac1fc05843 (MIT). -/
@[expose] section
namespace KIP126.ProofTools.Internal.Mahowald
open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence KIP126.AdamsSynthetic
open KIP126.Core.SpectralSequence KIP126.Kervaire.Route
noncomputable section
set_option backward.isDefEq.respectTransparency false

section General
universe u v
variable {Syn : Type u} [SyntheticCategory.{u,v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  {H : Syn} {unit : S_0_0 ⟶ H} {F : SyntheticAdamsFamily Syn}
  {P : SyntheticTowerPresentation unit F} {X : Syn}

theorem filtration_at_zero (P : SyntheticTowerPresentation unit F)
    (X : Syn) (m w : ℤ) (a : BiHom m w X) : FiltrationAtLeast P 0 a := by
  refine ⟨a ≫ (P.tower X).zeroIso.inv, ?_⟩
  change (a ≫ (P.tower X).zeroIso.inv) ≫ (P.tower X).projection 0 = a
  simp only [AbstractAdamsTower.projection, Int.toNat_zero, (P.tower X).map_self]
  erw [Category.assoc, Category.id_comp, Iso.inv_hom_id, Category.comp_id]

theorem filtration_iff_of_infinity_zero (c : SyntheticTowerConvergence P X)
    (s t m w : ℤ) (hst : s ≤ t)
    (hz : ∀ j, s ≤ j → j < t → IsZero (((F.obj X).sequence.ssData (j,m+j,w)).eInfty))
    (a : BiHom m w X) : FiltrationAtLeast P s a ↔ FiltrationAtLeast P t a := by
  have hgraded (j : ℤ) (hj : s ≤ j) (hjt : j < t) :
      IsZero ((P.filtration X).associatedGraded j (m,w)) :=
    (hz j hj hjt).of_iso (towerGradedIso c (m,w) j).symm
  have he := (P.filtration X).eq_of_associatedGraded_isZero s t (m,w) hst hgraded
  have he' := congrArg (fun Q => a ∈ (ModuleCat.subobjectModule (syntheticHomotopy X (m,w))) Q) he
  simpa only [SyntheticTowerPresentation.filtration, OrderIso.apply_symm_apply,
    FiltrationAtLeast] using Iff.of_eq he'
end General

open KIP126.AdamsSynthetic.Standard

/- The shift comparison transports actual filtration levels, so separation on
   a finite quotient also holds after the specified bigraded shift. -/
section ShiftSeparation
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w,v} Syn]
  [HasFunctorialCofiber (C := Syn)]
private theorem homotopySeparated_shift (D : Model C Syn) (X : SyntheticObject) (δ : ℤ × ℤ)
    (S : SyntheticESSShiftComparison D δ)
    (hsep : HomotopySeparated D.syntheticTower (X.obj D.nu D.auxiliary)) :
    HomotopySeparated D.syntheticTower ((SyntheticCategory.biShift δ).obj
      (X.obj D.nu D.auxiliary)) := by
  intro m w a ha
  let p : ℤ × ℤ := (m-δ.1,w-δ.2)
  have hp : p+δ=(m,w) := by ext <;> simp [p]
  let e : FilteredPieceIso (D.convergence X).filtration
      (D.convergence (.shift δ X)).filtration p (m,w) :=
    hp ▸ S.filtered X p
  have hb : e.ambient.inv a = 0 := by
    apply hsep p.1 p.2 (e.ambient.inv a)
    intro s
    have hmem : a ∈ ModuleCat.subobjectModule _
        ((D.convergence (.shift δ X)).filtration.F s (m,w)) := by
      simpa only [SyntheticTowerConvergence.filtration,
        SyntheticTowerPresentation.filtration, OrderIso.apply_symm_apply,
        FiltrationAtLeast, SyntheticObject.obj] using ha s
    obtain ⟨x,hx⟩ := hmem
    have hcomm := ConcreteCategory.congr_hom (e.symm.level_arrow s) x
    simp only [ModuleCat.comp_apply, FilteredPieceIso.symm] at hcomm
    have hm : e.ambient.inv a ∈ ModuleCat.subobjectModule _
        ((D.convergence X).filtration.F s p) := by
      refine ⟨(e.level s).inv x,?_⟩
      change ((D.convergence X).filtration.F (s:ℤ) p).arrow ((e.level s).inv x) = e.ambient.inv a
      simpa only [hx, Iso.symm_hom] using hcomm
    simpa only [SyntheticTowerConvergence.filtration,
      SyntheticTowerPresentation.filtration, OrderIso.apply_symm_apply,
      FiltrationAtLeast] using hm
  apply (ModuleCat.mono_iff_injective e.ambient.inv).mp inferInstance
  simpa only [map_zero] using hb

end ShiftSeparation

private theorem shifted_quotient_homotopy_separated
    (X : SyntheticObject) (q : ℕ) (δ : ℤ × ℤ) :
    HomotopySeparated model.syntheticTower
      ((SyntheticCategory.biShift δ).obj (XModLambdaN (X.obj model.nu model.auxiliary) q)) :=
  homotopySeparated_shift model (.quotient q X) δ (essShift δ)
    (synthetic_homotopy_separated X q)

theorem finite_infinity_zero_outside (X : ClassicalObject) (q : ℕ) (hq : 0 < q)
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

theorem finite_high_filtration_zero (X : ClassicalObject) (q : ℕ) (hq : 0 < q)
    (m w s : ℤ) (hs : (q:ℤ) ≤ m+s-w)
    (a : BiHom m w (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
    (ha : FiltrationAtLeast model.syntheticTower s a) : a = 0 := by
  apply synthetic_homotopy_separated (.nu X) q m w a
  intro j
  by_cases hj : s ≤ (j:ℤ)
  · exact (filtration_iff_of_infinity_zero (model.convergence (.quotient q (.nu X)))
      s j m w hj (fun k hk _ => finite_infinity_zero_outside X q hq k (m+k) w (by omega)) a).mp ha
  · exact model.syntheticTower.filtrationSubmodule_antitone _ (m,w) (by omega) ha

theorem finite_top_detection_unique (X : ClassicalObject) (q : ℕ) (hq : 0 < q)
    (s t w : ℤ) (hwindow : (q:ℤ) ≤ t+1-w)
    (x : (model.family.quotient (model.nu.functor.obj (X.obj model.auxiliary)) q).E₂ (s,t,w))
    (a b : BiHom (t-s) w (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
    (ha : Detects (model.convergence (.quotient q (.nu X))) (s,t,w) x a)
    (hb : Detects (model.convergence (.quotient q (.nu X))) (s,t,w) x b) : a = b := by
  apply sub_eq_zero.mp
  exact finite_high_filtration_zero X q hq (t-s) w (s+1) (by omega) (a-b)
    (detects_sub_filtration (model.convergence (.quotient q (.nu X))) (s,t,w) ha hb)

theorem finite_bottom_filtration (X : ClassicalObject) (q : ℕ) (hq : 0 < q)
    (s t : ℤ)
    (a : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q)) :
    FiltrationAtLeast model.syntheticTower s a := by
  have hzero := filtration_at_zero model.syntheticTower _ (t-s) t a
  by_cases hs : s ≤ 0
  · exact model.syntheticTower.filtrationSubmodule_antitone _ (t-s,t) hs hzero
  · exact (filtration_iff_of_infinity_zero (model.convergence (.quotient q (.nu X)))
      0 s (t-s) t (by omega)
      (fun k _ hk => finite_infinity_zero_outside X q hq k (t-s+k) t (by omega)) a).mp hzero

theorem shifted_finite_high_filtration_zero (X : ClassicalObject) (q : ℕ) (hq : 0 < q)
    (i m w s : ℤ) (hs : (q:ℤ) ≤ m+s-(w-i))
    (a : BiHom m w ((SyntheticCategory.biShift (0,i)).obj
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q)))
    (ha : FiltrationAtLeast model.syntheticTower s a) : a = 0 := by
  let B : SyntheticObject := .shift (0,i) (.quotient q (.nu X))
  have hz (j : ℤ) (hj : s ≤ j) :
      IsZero (((model.family.obj (B.obj model.nu model.auxiliary)).sequence.ssData (j,m+j,w)).eInfty) := by
    have hbase := finite_infinity_zero_outside X q hq j (m+j) (w-i) (by omega)
    let e := towerInfinityIso (model.convergence (.quotient q (.nu X)))
      (model.convergence (.shift (0,i) (.quotient q (.nu X))))
      ((essShift (0,i)).filtered (.quotient q (.nu X)) (m,w-i)) j
    have he := hbase.of_iso e.symm
    simpa only [e, B, Prod.fst_add, Prod.snd_add, add_zero, sub_add_cancel] using he
  apply shifted_quotient_homotopy_separated (.nu X) q (0,i) m w a
  intro j
  by_cases hj : s ≤ (j:ℤ)
  · exact (filtration_iff_of_infinity_zero (model.convergence B) s j m w hj
      (fun k hk _ => hz k hk) a).mp ha
  · exact model.syntheticTower.filtrationSubmodule_antitone _ (m,w) (by omega) ha

end
end KIP126.ProofTools.Internal.Mahowald
