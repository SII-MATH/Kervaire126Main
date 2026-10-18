module

public import KIP126.ProofTools.Laws
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! Proved shift and quotient operations retained from the pinned Mahowald
proof and Synthetic/Sphere/Shift files at bbac1fc05843 (MIT). -/
@[expose] section
namespace KIP126.ProofTools.Internal.Mahowald
open CategoryTheory CategoryTheory.Pretriangulated CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context
universe u v
variable {Syn : Type u} [SyntheticCategory.{u,v} Syn]
noncomputable section
set_option backward.isDefEq.respectTransparency false
/-- Compare the combined bigraded shift with the ordinary suspension of the
specified vertical shift, using the existing composition and compatibility. -/
noncomputable def biSuspensionIso (q : ℤ) (Q : Syn) :
    (SyntheticCategory.biShift (1, -q)).obj Q ≅
      ((SyntheticCategory.biShift (0, -q)).obj Q)⟦(1 : ℤ)⟧ := by
  have h : ((0 : ℤ), -q) + (1, 0) = (1, -q) := by
    ext <;> simp
  simpa only [h] using
    ((SyntheticCategory.biShift_comp (0, -q) (1, 0)).symm.app Q ≪≫
      (SyntheticCategory.biShift_compat (Syn := Syn) 1).app
        ((SyntheticCategory.biShift (0, -q)).obj Q))

/-- The underlying equivalence for the Bockstein landing degree. It is the
inverse of the existing suspension invariance, followed by the specified
ordinary-suspension comparison and the integer degree equalities. -/
noncomputable def biSuspensionHomEquivRaw (n w q : ℤ) (Q : Syn) :
    BiHom n w (((SyntheticCategory.biShift (0, -q)).obj Q)⟦(1 : ℤ)⟧) ≃
      BiHom (n - 1) (w + q) Q := by
  let e : BiHom (n - 1) (w + q) Q ≃
      BiHom n w (((SyntheticCategory.biShift (0, -q)).obj Q)⟦(1 : ℤ)⟧) := by
    simpa only [sub_add_cancel, add_neg_cancel_right] using
      ((susp_invariance (n - 1) (w + q) 1 (-q) Q).trans
        (Iso.homCongr (Iso.refl _) (biSuspensionIso q Q)))
  exact e.symm

/-- The existing bigraded shift preserves addition. -/
theorem biShift_additive (p : ℤ × ℤ) :
    (SyntheticCategory.biShift (Syn := Syn) p).Additive := by
  letI : (SyntheticCategory.biShift (Syn := Syn) p).IsEquivalence :=
    Functor.IsEquivalence.mk' (SyntheticCategory.biShift (-p))
      (SyntheticCategory.biShift_zero.symm ≪≫
        eqToIso (congrArg SyntheticCategory.biShift
          (by simp : (0 : ℤ × ℤ) = p + -p)) ≪≫
        (SyntheticCategory.biShift_comp p (-p)).symm)
      (SyntheticCategory.biShift_comp (-p) p ≪≫
        eqToIso (congrArg SyntheticCategory.biShift
          (by simp : -p + p = (0 : ℤ × ℤ))) ≪≫
        SyntheticCategory.biShift_zero)
  exact Functor.additive_of_preserves_binary_products _

attribute [instance] biShift_additive

/-- Additivity of the already defined suspension-invariance function. -/
theorem susp_invariance_add (m n k l : ℤ) (X : Syn)
    (f g : BiHom m n X) :
    susp_invariance m n k l X (f + g) =
      susp_invariance m n k l X f + susp_invariance m n k l X g := by
  simp [susp_invariance, Functor.map_add, Preadditive.comp_add]

/-- The specified inverse reindexing map is additive. -/
theorem biSuspensionHomEquivRaw_add (n w q : ℤ) (Q : Syn)
    (f g : BiHom n w (((SyntheticCategory.biShift (0, -q)).obj Q)⟦(1 : ℤ)⟧)) :
    biSuspensionHomEquivRaw n w q Q (f + g) =
      biSuspensionHomEquivRaw n w q Q f + biSuspensionHomEquivRaw n w q Q g := by
  let e := biSuspensionHomEquivRaw n w q Q
  have h : ∀ a b, e.symm (a + b) = e.symm a + e.symm b := by
    intro a b
    let e0 := (susp_invariance (n - 1) (w + q) 1 (-q) Q).trans
      (Iso.homCongr (Iso.refl _) (biSuspensionIso q Q))
    have h0 : e0 (a + b) = e0 a + e0 b := by
      simp [e0, susp_invariance_add, Preadditive.comp_add, Preadditive.add_comp]
    have hc (n' w' : ℤ) (hn : n' = n) (hw : w' = w)
        (e' : BiHom (n - 1) (w + q) Q ≃
          BiHom n' w' (((SyntheticCategory.biShift (0, -q)).obj Q)⟦(1 : ℤ)⟧))
        (he' : e' (a + b) = e' a + e' b)
        (ht : (BiHom (n - 1) (w + q) Q ≃
          BiHom n' w' (((SyntheticCategory.biShift (0, -q)).obj Q)⟦(1 : ℤ)⟧)) =
          (BiHom (n - 1) (w + q) Q ≃
          BiHom n w (((SyntheticCategory.biShift (0, -q)).obj Q)⟦(1 : ℤ)⟧))) :
        (cast ht e') (a + b) = (cast ht e') a + (cast ht e') b := by
      subst n'
      subst w'
      exact he'
    dsimp only [e, biSuspensionHomEquivRaw, Equiv.symm_symm]
    exact hc (n - 1 + 1) (w + q + -q) (sub_add_cancel n 1)
      (add_neg_cancel_right w q) e0 h0 _
  apply e.symm.injective
  rw [h]
  simp [e]

/-- Additive enhancement of the existing `susp_invariance`, with exactly
the same underlying equivalence. -/
noncomputable def suspInvarianceAddEquiv (m n k l : ℤ) (X : Syn) :
    BiHom m n X ≃+
      BiHom (m + k) (n + l) ((SyntheticCategory.biShift (k, l)).obj X) where
  toEquiv := susp_invariance m n k l X
  map_add' := susp_invariance_add m n k l X

/-- The additive reindexing of an ordinary suspension of a vertical shift:
`[S^(n,w), Σ Σ^(0,-q) Q] ≃+ [S^(n-1,w+q), Q]`. -/
noncomputable def biSuspensionHomEquiv (n w q : ℤ) (Q : Syn) :
    BiHom n w (((SyntheticCategory.biShift (0, -q)).obj Q)⟦(1 : ℤ)⟧) ≃+
      BiHom (n - 1) (w + q) Q where
  toEquiv := biSuspensionHomEquivRaw n w q Q
  map_add' := biSuspensionHomEquivRaw_add n w q Q

theorem biSuspensionIso_natural (i : ℤ) {A B : Syn} (f : A ⟶ B) :
    (SyntheticCategory.biShift (1,-i)).map f ≫ (biSuspensionIso i B).hom =
      (biSuspensionIso i A).hom ≫
        (shiftFunctor Syn (1:ℤ)).map ((SyntheticCategory.biShift (0,-i)).map f) := by
  let e : (SyntheticCategory.biShift ((0,-i)+(1,0)) : Syn ⥤ Syn) ≅
      SyntheticCategory.biShift (0,-i) ⋙ shiftFunctor Syn (1:ℤ) :=
    (SyntheticCategory.biShift_comp (0,-i) (1,0)).symm ≪≫
      Functor.isoWhiskerLeft (SyntheticCategory.biShift (0,-i)) (SyntheticCategory.biShift_compat 1)
  have cast_natural (p p' : ℤ×ℤ) (hp : p=p')
      (E : (SyntheticCategory.biShift p : Syn ⥤ Syn) ≅
        SyntheticCategory.biShift (0,-i) ⋙ shiftFunctor Syn (1:ℤ))
      (hA : ((SyntheticCategory.biShift p).obj A ≅
        (shiftFunctor Syn (1:ℤ)).obj ((SyntheticCategory.biShift (0,-i)).obj A)) =
        ((SyntheticCategory.biShift p').obj A ≅
        (shiftFunctor Syn (1:ℤ)).obj ((SyntheticCategory.biShift (0,-i)).obj A)))
      (hB : ((SyntheticCategory.biShift p).obj B ≅
        (shiftFunctor Syn (1:ℤ)).obj ((SyntheticCategory.biShift (0,-i)).obj B)) =
        ((SyntheticCategory.biShift p').obj B ≅
        (shiftFunctor Syn (1:ℤ)).obj ((SyntheticCategory.biShift (0,-i)).obj B))) :
      (SyntheticCategory.biShift p').map f ≫ (cast hB (E.app B)).hom =
        (cast hA (E.app A)).hom ≫
          (shiftFunctor Syn (1:ℤ)).map ((SyntheticCategory.biShift (0,-i)).map f) := by
    subst p'
    exact E.hom.naturality f
  unfold biSuspensionIso
  exact cast_natural ((0,-i)+(1,0)) (1,-i) (by ext <;> simp) e _ _

theorem shifted_representative_zero_iff (n w i : ℤ) (Q B : Syn)
    (L : (SyntheticCategory.biShift (0,-i)).obj Q ⟶ B)
    (c : BiHom (n-1) (w+i) Q) :
    (biSuspensionHomEquiv n w i Q).symm c ≫ (shiftFunctor Syn (1:ℤ)).map L = 0 ↔
      (SyntheticCategory.biShift (0,-i)).map c ≫ L = 0 := by
  let e0 := (susp_invariance (n-1) (w+i) 1 (-i) Q).trans
    (Iso.homCongr (Iso.refl _) (biSuspensionIso i Q))
  have h0 : e0 c ≫ (shiftFunctor Syn (1:ℤ)).map L = 0 ↔
      (SyntheticCategory.biShift (0,-i)).map c ≫ L = 0 := by
    change (𝟙 _ ≫ ((SyntheticCategory.biShift_comp (n-1,w+i) (1,-i)).inv.app S_0_0 ≫
      (SyntheticCategory.biShift (1,-i)).map c ≫ 𝟙 _) ≫ (biSuspensionIso i Q).hom) ≫
        (shiftFunctor Syn (1:ℤ)).map L = 0 ↔ _
    simp only [Category.id_comp,Category.comp_id,Category.assoc]
    rw [← Category.assoc ((SyntheticCategory.biShift (1,-i)).map c),
      biSuspensionIso_natural]
    simp only [Category.assoc]
    rw [←Functor.map_comp]
    constructor
    · intro h
      apply (shiftFunctor Syn (1:ℤ)).map_injective
      rw [Functor.map_zero]
      apply (cancel_epi (biSuspensionIso i (Smn (n-1) (w+i))).hom).mp
      apply (cancel_epi ((SyntheticCategory.biShift_comp (n-1,w+i) (1,-i)).inv.app S_0_0)).mp
      simpa only [comp_zero,Category.assoc] using h
    · intro h
      simp only [h,Functor.map_zero,comp_zero]
  have cast_equiv (n' w' : ℤ) (hn:n'=n) (hw:w'=w)
      (e' : BiHom (n-1) (w+i) Q ≃
        BiHom n' w' (((SyntheticCategory.biShift (0,-i)).obj Q)⟦(1:ℤ)⟧))
      (he' : e' c ≫ (shiftFunctor Syn (1:ℤ)).map L = 0 ↔
        (SyntheticCategory.biShift (0,-i)).map c ≫ L = 0)
      (ht : (BiHom (n-1) (w+i) Q ≃
        BiHom n' w' (((SyntheticCategory.biShift (0,-i)).obj Q)⟦(1:ℤ)⟧)) =
        (BiHom (n-1) (w+i) Q ≃
        BiHom n w (((SyntheticCategory.biShift (0,-i)).obj Q)⟦(1:ℤ)⟧))) :
      (cast ht e') c ≫ (shiftFunctor Syn (1:ℤ)).map L = 0 ↔
        (SyntheticCategory.biShift (0,-i)).map c ≫ L = 0 := by
    subst n'
    subst w'
    exact he'
  change (biSuspensionHomEquivRaw n w i Q).symm c ≫ _ = 0 ↔ _
  dsimp only [biSuspensionHomEquivRaw,Equiv.symm_symm]
  exact cast_equiv (n-1+1) (w+i+-i) (sub_add_cancel n 1)
    (add_neg_cancel_right w i) e0 h0 _

theorem shifted_composite_zero_of_conjugate
    (i : ℤ) {A Q B Y : Syn} (c : A ⟶ Q) (h : Q ⟶ B)
    (L : (SyntheticCategory.biShift (0,-i)).obj Q ⟶ Y)
    (ε : (SyntheticCategory.biShift (0,-i)).obj B ≅ Y)
    (hL : (SyntheticCategory.biShift (0,-i)).map h ≫ ε.hom = L) :
    (SyntheticCategory.biShift (0,-i)).map c ≫ L = 0 ↔ c ≫ h = 0 := by
  letI := (SyntheticCategory.biShift_fullyFaithful (Syn:=Syn) (0,-i)).faithful
  rw [←hL,←Category.assoc,←Functor.map_comp]
  constructor
  · intro hz
    apply (SyntheticCategory.biShift (0,-i)).map_injective
    rw [Functor.map_zero]
    apply (cancel_mono ε.hom).mp
    simpa only [zero_comp] using hz
  · intro hz
    rw [hz,Functor.map_zero,zero_comp]

theorem inverse_associativity (coh : BiShiftCoherence Syn)
    (a b c ab bc total : ℤ×ℤ) (hab : a+b=ab) (hbc : b+c=bc)
    (ht : ab+c=total) (ht' : a+bc=total) (X : Syn) :
    (biShiftAddIso a bc total ht').inv.app X ≫
        (biShiftAddIso b c bc hbc).inv.app ((SyntheticCategory.biShift a).obj X) =
      (biShiftAddIso ab c total ht).inv.app X ≫
        (SyntheticCategory.biShift c).map ((biShiftAddIso a b ab hab).inv.app X) := by
  have he : (SyntheticCategory.biShift c).mapIso ((biShiftAddIso a b ab hab).app X) ≪≫
        (biShiftAddIso ab c total ht).app X =
      (biShiftAddIso b c bc hbc).app ((SyntheticCategory.biShift a).obj X) ≪≫
        (biShiftAddIso a bc total ht').app X := by
    apply Iso.ext
    exact coh.associativity a b c ab bc total hab hbc ht ht' X
  have h := congrArg Iso.inv he
  simpa only [Iso.trans_inv,Functor.mapIso_inv,Iso.app_inv] using h.symm

theorem shift_hom_associativity (coh : BiShiftCoherence Syn)
    (a b c ab bc total : ℤ×ℤ) (hab : a+b=ab) (hbc : b+c=bc)
    (ht : ab+c=total) (ht' : a+bc=total) {A : Syn}
    (α : (SyntheticCategory.biShift a).obj (S_0_0 : Syn) ⟶ A) :
    (biShiftAddIso a bc total ht').inv.app S_0_0 ≫
        (SyntheticCategory.biShift bc).map α ≫ (biShiftAddIso b c bc hbc).inv.app A =
      (biShiftAddIso ab c total ht).inv.app S_0_0 ≫
        (SyntheticCategory.biShift c).map
          ((biShiftAddIso a b ab hab).inv.app S_0_0 ≫ (SyntheticCategory.biShift b).map α) := by
  rw [(biShiftAddIso b c bc hbc).inv.naturality α]
  change _ ≫ _ ≫ (SyntheticCategory.biShift c).map ((SyntheticCategory.biShift b).map α) = _
  rw [←Category.assoc,inverse_associativity coh,Functor.map_comp,Category.assoc]

theorem susp_regrade_eq (n u k l m w : ℤ) (hm : n+k=m) (hw : u+l=w)
    (A : Syn) (α : BiHom n u A) :
    homotopyRegrade hm hw (susp_invariance n u k l A α) =
      (biShiftAddIso (n,u) (k,l) (m,w) (Prod.ext hm hw)).inv.app S_0_0 ≫
        (SyntheticCategory.biShift (k,l)).map α := by
  subst m
  subst w
  simp [homotopyRegrade,susp_invariance,biShiftAddIso]

theorem bi_susp_symm_eq (m w q : ℤ) (A : Syn) (α : BiHom (m-1) (w+q) A) :
    (biSuspensionHomEquiv m w q A).symm α =
      homotopyRegrade (sub_add_cancel m 1) (add_neg_cancel_right w q)
        (susp_invariance (m-1) (w+q) 1 (-q) A α) ≫ (biSuspensionIso q A).hom := by
  have hc (m' w' : ℤ) (hm : m'=m) (hw : w'=w)
      (e : BiHom (m-1) (w+q) A ≃ BiHom m' w' (((SyntheticCategory.biShift (0,-q)).obj A)⟦(1:ℤ)⟧))
      (he : (BiHom (m-1) (w+q) A ≃ BiHom m' w' (((SyntheticCategory.biShift (0,-q)).obj A)⟦(1:ℤ)⟧)) =
        (BiHom (m-1) (w+q) A ≃ BiHom m w (((SyntheticCategory.biShift (0,-q)).obj A)⟦(1:ℤ)⟧))) :
      (he.mp e) α = homotopyRegrade hm hw (e α) := by
    subst m'; subst w'; rfl
  have regrade_comp {m' w' : ℤ} (hm : m'=m) (hw : w'=w) {B C : Syn}
      (a : BiHom m' w' B) (f : B ⟶ C) :
      homotopyRegrade hm hw (a≫f) = homotopyRegrade hm hw a ≫ f := by
    subst m'; subst w'; rfl
  change (biSuspensionHomEquivRaw m w q A).symm α = _
  simp only [biSuspensionHomEquivRaw,Equiv.symm_symm]
  rw [hc (m-1+1) (w+q+-q) (by omega) (by omega)]
  simp only [Equiv.trans_apply,Iso.homCongr_apply,Iso.refl_inv,Category.id_comp,regrade_comp]

theorem bi_susp_iso_hom_eq (q : ℤ) (A : Syn) :
    (biSuspensionIso q A).hom =
      (biShiftAddIso (0,-q) (1,0) (1,-q) (by ext <;> simp)).inv.app A ≫
        (SyntheticCategory.biShift_compat 1).hom.app ((SyntheticCategory.biShift (0,-q)).obj A) := by
  have hc {X X' Y : Syn} (h : X=X') (e : X ≅ Y) (he : (X ≅ Y)=(X' ≅ Y)) :
      (he.mp e).hom = eqToHom h.symm ≫ e.hom := by
    subst X'; simp
  unfold biSuspensionIso
  rw [hc (congrArg (fun p : ℤ×ℤ => (SyntheticCategory.biShift p).obj A) (by ext <;> simp))]
  simp only [biShiftAddIso,Iso.trans_hom,Iso.trans_inv,
    NatTrans.comp_app,eqToIso.inv,eqToHom_app,Category.assoc]
  rfl

def vertical_hom (n w q : ℤ) (A : Syn) (α : BiHom n (w+q) A) :
    BiHom n w ((SyntheticCategory.biShift (0,-q)).obj A) :=
  (biShiftAddIso (n,w+q) (0,-q) (n,w) (by ext <;> simp)).inv.app S_0_0 ≫
    (SyntheticCategory.biShift (0,-q)).map α

theorem bi_susp_symm_vertical (coh : BiShiftCoherence Syn)
    (m w q : ℤ) (A : Syn) (α : BiHom (m-1) (w+q) A) :
    (biSuspensionHomEquiv m w q A).symm α =
      (biShiftAddIso (m-1,w) (1,0) (m,w) (by ext <;> simp)).inv.app S_0_0 ≫
        (SyntheticCategory.biShift_compat 1).hom.app (Smn (m-1) w) ≫
          (shiftFunctor Syn (1:ℤ)).map (vertical_hom (m-1) w q A α) := by
  rw [bi_susp_symm_eq,susp_regrade_eq,bi_susp_iso_hom_eq]
  have h := shift_hom_associativity coh
    (m-1,w+q) (0,-q) (1,0) (m-1,w) (1,-q) (m,w)
    (by ext <;> simp) (by ext <;> simp) (by ext <;> simp) (by ext <;> simp) α
  have h' := congrArg (fun f => f ≫ (SyntheticCategory.biShift_compat 1).hom.app
    ((SyntheticCategory.biShift (0,-q)).obj A)) h
  calc
    _ = (biShiftAddIso (m-1,w) (1,0) (m,w) (by ext <;> simp)).inv.app S_0_0 ≫
        (SyntheticCategory.biShift (1,0)).map (vertical_hom (m-1) w q A α) ≫
          (SyntheticCategory.biShift_compat 1).hom.app ((SyntheticCategory.biShift (0,-q)).obj A) := by
      simpa only [vertical_hom,Category.assoc] using h'
    _ = _ := by
      rw [(SyntheticCategory.biShift_compat 1).hom.naturality]
      rfl

theorem lambda_regrade_eq (n u : ℤ) (d : ℕ) (v : ℤ) (hv : u-(d:ℤ)=v)
    (A : Syn) (α : BiHom n u A) :
    homotopyRegrade rfl hv (lambdaMultiply d α) =
      (biShiftAddIso (n,u) (0,-(d:ℤ)) (n,v) (by ext <;> dsimp <;> omega)).inv.app S_0_0 ≫
        lambdaPow d (Smn n u) ≫ α := by
  subst v
  simp only [homotopyRegrade,lambdaMultiply,biShiftAddIso,Iso.trans_inv,NatTrans.comp_app,
    eqToIso.inv,eqToHom_app,Category.assoc]

theorem vertical_hom_lambda (coh : BiShiftCoherence Syn)
    (i k : ℕ) (hik : i ≤ k) (n w : ℤ) (A : Syn) (α : BiHom n (w+k) A) :
    vertical_hom n w (k:ℤ) A α ≫ lambdaRestrictionSourceMap i k hik A =
      vertical_hom n w (i:ℤ) A
        (homotopyRegrade rfl (by omega) (lambdaMultiply (k-i) α)) := by
  dsimp only [vertical_hom,lambdaRestrictionSourceMap,lambdaShiftAddIso,KIP126.Synthetic.Context.lambdaDegree]
  rw [lambda_regrade_eq]
  have h := shift_hom_associativity coh
    (n,w+k) (0,-((k-i:ℕ):ℤ)) (0,-(i:ℤ)) (n,w+i) (0,-(k:ℤ)) (n,w)
    (by ext <;> dsimp <;> omega) (by ext <;> dsimp; omega)
    (by ext <;> dsimp <;> omega) (by ext <;> dsimp <;> omega) α
  have h' := congrArg (fun f => f ≫ (SyntheticCategory.biShift (0,-(i:ℤ))).map
    (lambdaPow (k-i) A)) h
  simpa only [Smn,Category.assoc,←Functor.map_comp,lambdaPow_naturality] using h'

theorem bi_susp_lambda_transition (coh : BiShiftCoherence Syn)
    (i k : ℕ) (hik : i ≤ k) (m w : ℤ) (A : Syn)
    (α : BiHom (m-1) (w+k) A) :
    biSuspensionHomEquiv m w (i:ℤ) A
      ((biSuspensionHomEquiv m w (k:ℤ) A).symm α ≫
        (shiftFunctor Syn (1:ℤ)).map (lambdaRestrictionSourceMap i k hik A)) =
      homotopyRegrade rfl (by omega) (lambdaMultiply (k-i) α) := by
  apply (biSuspensionHomEquiv m w (i:ℤ) A).symm.injective
  rw [AddEquiv.symm_apply_apply,bi_susp_symm_vertical coh,bi_susp_symm_vertical coh]
  simp only [Category.assoc]
  rw [←Functor.map_comp,vertical_hom_lambda coh]

theorem bi_susp_natural (coh : BiShiftCoherence Syn)
    (m w i : ℤ) {A B : Syn} (f : A ⟶ B)
    (a : BiHom m w (((SyntheticCategory.biShift (0,-i)).obj A)⟦(1:ℤ)⟧)) :
    biSuspensionHomEquiv m w i B
      (a ≫ (shiftFunctor Syn (1:ℤ)).map ((SyntheticCategory.biShift (0,-i)).map f)) =
      biSuspensionHomEquiv m w i A a ≫ f := by
  obtain ⟨α,rfl⟩ := (biSuspensionHomEquiv m w i A).symm.surjective a
  rw [AddEquiv.apply_symm_apply]
  apply (biSuspensionHomEquiv m w i B).symm.injective
  rw [AddEquiv.symm_apply_apply,bi_susp_symm_vertical coh,bi_susp_symm_vertical coh]
  simp only [vertical_hom,Functor.map_comp,Category.assoc]

theorem lambda_transition_evaluation [HasFunctorialCofiber (C := Syn)]
    (coh : BiShiftCoherence Syn) (i k : ℕ) (hik : i ≤ k) (q : ℕ)
    (m w : ℤ) (A : Syn) (α : BiHom (m-1) (w+k) A) :
    biSuspensionHomEquiv m w (i:ℤ) (XModLambdaN A q)
      ((biSuspensionHomEquiv m w (k:ℤ) A).symm α ≫
        (shiftFunctor Syn (1:ℤ)).map
          (lambdaRestrictionSourceMap i k hik A ≫
            (SyntheticCategory.biShift (0,-(i:ℤ))).map (XModLambdaN.incl A q))) =
      homotopyRegrade rfl (by omega) (lambdaMultiply (k-i) α ≫ XModLambdaN.incl A q) := by
  have regrade_comp {n n' v v' : ℤ} (hn : n=n') (hv : v=v')
      {A B : Syn} (a : BiHom n v A) (f : A ⟶ B) :
      homotopyRegrade hn hv (a≫f) = homotopyRegrade hn hv a ≫ f := by
    subst n'; subst v'; rfl
  rw [Functor.map_comp,←Category.assoc,bi_susp_natural coh,
    bi_susp_lambda_transition coh,regrade_comp]

variable [HasFunctorialCofiber (C := Syn)]

theorem quotient_maps_difference_factors {A B : Syn} (j : ℕ)
    (a b : XModLambdaN A j ⟶ B)
    (hab : XModLambdaN.incl A j ≫ a = XModLambdaN.incl A j ≫ b) :
    ∃ z : ((SyntheticCategory.biShift (0,-(j:ℤ))).obj A)⟦(1:ℤ)⟧ ⟶ B,
      a-b = XModLambdaN.proj A j ≫ z := by
  apply Triangle.yoneda_exact₃ (XModLambdaN.cofiberTriangle A j)
    (XModLambdaN.cofiberTriangle_distinguished A j) (a-b)
  change XModLambdaN.incl A j ≫ (a-b) = 0
  rw [Preadditive.comp_sub,hab,sub_self]

theorem quotient_maps_equal_on_spheres_of_no_return {A B : Syn} (j : ℕ)
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


end
end KIP126.ProofTools.Internal.Mahowald
