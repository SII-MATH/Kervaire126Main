module

public import KIP126.Def.ProofTools.Laws
import all KIP126.Def.ProofTools.GeneralizedMahowald.Coherence
import all KIP126.Def.ProofTools.GeneralizedMahowald.PageCalculus
import all KIP126.Def.ProofTools.GeneralizedMahowald.Filtration
import all KIP126.Def.ProofTools.GeneralizedMahowald.NoReturn
import all KIP126.Def.ProofTools.GeneralizedMahowald.KernelTriangles
import all KIP126.Def.ProofTools.GeneralizedMahowald.Adjacent
import all KIP126.Def.ProofTools.GeneralizedMahowald.Detection
import all KIP126.Def.ProofTools.GeneralizedMahowald.SphereLabels
import all KIP126.Def.ProofTools.DetectionOperations
import all KIP126.Def.ProofTools.StretchingRepresentatives

/-! Boundary lifts for every selected classical object, generalized from
GeneralizedMahowald/Proofs.lean:1996–2940 at bbac1fc05843 (MIT).
The original sphere argument extends using finite_lambda_detects on the same
fixed system; no assumption identifying the object with the sphere is needed. -/

@[expose] section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 6000000
namespace KIP126.ProofTools.Internal.Mahowald
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Standard
noncomputable section

/-- The boundary square for the same quotient restriction. Retained proof from
Synthetic/QuotientRestrictions/Proofs.lean:33–42 at the pinned baseline. -/
private theorem quotient_restriction_boundary (coh : BiShiftCoherence SyntheticSpectrum)
    (X : SyntheticSpectrum) (i j : ℕ) (hij : i ≤ j) :
    XModLambdaN.restriction coh X i j hij ≫ XModLambdaN.proj X i =
      XModLambdaN.proj X j ≫
        (shiftFunctor SyntheticSpectrum (1 : ℤ)).map (lambdaRestrictionSourceMap i j hij X) :=
  HasFunctorialCofiber.cofibMap_δ (lambdaPow j X) (lambdaPow i X)
    (lambdaRestrictionSourceMap i j hij X) (𝟙 X)
    (by simpa only [lambdaDegree, Category.comp_id] using
      lambdaRestrictionSourceMap_commutes coh i j hij X)

private theorem selected_boundary_nonadjacent (X : ClassicalObject)
    (i k : ℕ) (hi : 0 < i) (hik : i < k) (s t : ℤ)
    (x : Ambient model X (s,t))
    (y : Ambient model X (s+k+1,t+k))
    (hd : HasDifferential (model.classical.obj (X.obj model.auxiliary))
      (k+1) (s,t) (s+k+1,t+k) x y)
    (hy : y ∈ KIP126.Literature.permanentCycles model X (s+k+1,t+k))
 :
    ∃ a : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) i),
      a ≫ (model.quotients.tower _).rho 1 i hi =
        firstLabel model X s t x ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1 ∧
      Detects (model.convergence (.quotient (k+1-i) (.nu X)))
        (s+k+1,t+k,t+k-(k-i:ℕ))
        (finiteTargetLabel model X (k+1-i) (s+k+1) (t+k) (k-i) y)
        (homotopyRegrade (by dsimp; omega) (by dsimp; omega)
          (biSuspensionHomEquiv (t-s) t (i:ℤ) (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (k+1-i))
            (a ≫ ((model.quotients.tower _).triangle hi (show i < k+1 by omega)).delta))) := by
  have adjacent_selected_representative_and_target_lift
      
      (i k : ℕ) (hi : 0 < i) (hik : i ≤ k) (s t : ℤ)
      (x : Ambient model X (s,t))
      (y : Ambient model X (s+k+1,t+k))
      (hd : HasDifferential (model.classical.obj (X.obj model.auxiliary))
        (k+1) (s,t) (s+k+1,t+k) x y)
      (hy : y ∈ KIP126.Literature.permanentCycles model X (s+k+1,t+k)) :
      let A := model.nu.functor.obj (X.obj model.auxiliary)
      let δ : XModLambdaN A k ⟶
          ((SyntheticCategory.biShift (0,-(k:ℤ))).obj (XModLambdaN A 1))⟦(1:ℤ)⟧ := by
        simpa only [show k.succ-k=1 by omega] using
          ((model.quotients.tower A).triangle (show 0<k by omega) (Nat.lt_succ_self k)).delta
      ∃ (a : BiHom (t-s) t (XModLambdaN A k))
          (α : BiHom ((t+k)-(s+k+1)) (t+k) A),
        a ≫ (model.quotients.tower A).rho 1 k (by omega) =
          firstLabel model X s t x ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app A) 1 ∧
        α ≫ XModLambdaN.incl A 1 =
          firstLabel model X (s+k+1) (t+k) y ≫
            XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app A) 1 ∧
        homotopyRegrade (by omega) rfl
            (biSuspensionHomEquiv (t-s) t (k:ℤ) (XModLambdaN A 1) (a ≫ δ)) =
          α ≫ XModLambdaN.incl A 1 ∧
        (a ≫ (model.quotients.tower A).rho i k hik) ≫ (model.quotients.tower A).rho 1 i hi =
          firstLabel model X s t x ≫
            XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app A) 1 := by
    dsimp only
    let A := model.nu.functor.obj (X.obj model.auxiliary)
    obtain ⟨a,ha,had⟩ := adjacent_mahowald_case X k (by omega) s t x y hd
    obtain ⟨α0,hα0⟩ := (KIP126.Literature.Standard.selected_permanent_lift X (s+k+1) (t+k) y).mp (by
      obtain ⟨z,hz⟩ := hy
      refine ⟨z, ?_⟩
      have h := normalizeInitialProjection
        ((model.classical.obj (X.obj model.auxiliary)).ssData (s+k+1,t+k))
        (↑(2-(model.classical.obj (X.obj model.auxiliary)).r₀).toNat)
        ⊤ (by rw [model.classical.firstPage]; rfl) le_top
      exact (congrArg (fun f => f z) h).trans hz)
    let α : BiHom ((t+k)-(s+k+1)) (t+k) A :=
      α0 ≫ SyntheticCategory.biShift_zero.hom.app A
    have hα : α ≫ XModLambdaN.incl A 1 =
        firstLabel model X (s+k+1) (t+k) y ≫
          XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app A) 1 := by
      dsimp only [α]
      rw [Category.assoc,XModLambdaN.incl_naturality,←Category.assoc]
      exact congrArg (fun z => z ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app A) 1) hα0
    have hαρ : (α ≫ XModLambdaN.incl A 1) ≫ (model.quotients.tower A).rho 1 1 (by decide) =
        firstLabel model X (s+k+1) (t+k) y ≫
          XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app A) 1 := by
      rw [(model.quotients.tower A).rho_id,Category.comp_id]
      exact hα
    have hαd := first_label_detects_unshifted X 1 (by decide)
      (s+k+1) (t+k) y (α ≫ XModLambdaN.incl A 1) hαρ
    refine ⟨a,α,ha,hα,?_,?_⟩
    · exact finite_top_detection_unique X 1 (by decide)
        (s+k+1) (t+k) (t+k) (by omega) _ _ _ had hαd
    · rw [Category.assoc,(model.quotients.tower A).rho_comp hi hik]
      exact ha

  have selected_delta_cross_index_of_inclusion_square
       (X : ClassicalObject)
      (i k j : ℕ) (hi : 0 < i) (hik : i ≤ k) (hkj : k < j)
      (v : (SyntheticCategory.biShift (0,-(k:ℤ))).obj
          (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (j-k)) ⟶
        (SyntheticCategory.biShift (0,-(i:ℤ))).obj
          (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (j-i)))
      (hv : (SyntheticCategory.biShift (0,-(k:ℤ))).map
          (XModLambdaN.incl (model.nu.functor.obj (X.obj model.auxiliary)) (j-k)) ≫ v =
        lambdaRestrictionSourceMap i k hik (model.nu.functor.obj (X.obj model.auxiliary)) ≫
          (SyntheticCategory.biShift (0,-(i:ℤ))).map
            (XModLambdaN.incl (model.nu.functor.obj (X.obj model.auxiliary)) (j-i)))
      (m w : ℤ)
      (a : BiHom m w (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) k)) :
      (a ≫ (model.quotients.tower (model.nu.functor.obj (X.obj model.auxiliary))).rho i k hik) ≫
          ((model.quotients.tower (model.nu.functor.obj (X.obj model.auxiliary))).triangle hi
            (show i < j by omega)).delta =
        (a ≫ ((model.quotients.tower (model.nu.functor.obj (X.obj model.auxiliary))).triangle
          (show 0 < k by omega) hkj).delta) ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map v := by
    let A := model.nu.functor.obj (X.obj model.auxiliary)
    rw [selected_delta_evaluation_eq_cofiber X i j,
      selected_delta_evaluation_eq_cofiber X k j]
    simp only [Category.assoc]
    rw [model.quotients.restriction]
    rw [←Category.assoc (XModLambdaN.restriction model.quotients.coherence A i k hik),
      quotient_restriction_boundary]
    simp only [Category.assoc]
    rw [←Functor.map_comp,←hv,Functor.map_comp]

  have canonical_finite_lambda_transition_exists {X : SyntheticSpectrum}
      (Q : FiniteLambdaQuotientTower X) (i k q : ℕ) (hik : i < k) (hdq : k-i < q) :
      ∃ v : (SyntheticCategory.biShift (0,-(k:ℤ))).obj (XModLambdaN X (q-(k-i))) ⟶
          (SyntheticCategory.biShift (0,-(i:ℤ))).obj (XModLambdaN X q),
        (SyntheticCategory.biShift (0,-(k:ℤ))).map (XModLambdaN.incl X (q-(k-i))) ≫ v =
          lambdaRestrictionSourceMap i k hik.le X ≫
            (SyntheticCategory.biShift (0,-(i:ℤ))).map (XModLambdaN.incl X q) ∧
        v = (lambdaShiftAddIso (k-i) i k (Nat.sub_add_cancel hik.le)).inv.app
            (XModLambdaN X (q-(k-i))) ≫
          (SyntheticCategory.biShift (0,-(i:ℤ))).map
            (Q.triangle (by omega : 0 < k-i) hdq).lambdaMap := by
    let l := (Q.triangle (by omega : 0 < k-i) hdq).lambdaMap
    have hl : (SyntheticCategory.biShift (0,-((k-i:ℕ):ℤ))).map
        (XModLambdaN.incl X (q-(k-i))) ≫ l = lambdaPow (k-i) X ≫ XModLambdaN.incl X q :=
      (Q.triangle (by omega : 0 < k-i) hdq).lambda_quotient
    refine ⟨(lambdaShiftAddIso (k-i) i k (Nat.sub_add_cancel hik.le)).inv.app
        (XModLambdaN X (q-(k-i))) ≫ (SyntheticCategory.biShift (0,-(i:ℤ))).map l,?_,rfl⟩
    rw [←Category.assoc,NatTrans.naturality,Category.assoc]
    change (lambdaShiftAddIso (k-i) i k (Nat.sub_add_cancel hik.le)).inv.app X ≫
        (SyntheticCategory.biShift (0,-(i:ℤ))).map
          ((SyntheticCategory.biShift (0,-((k-i:ℕ):ℤ))).map (XModLambdaN.incl X (q-(k-i)))) ≫
            (SyntheticCategory.biShift (0,-(i:ℤ))).map l = _
    rw [←Functor.map_comp,hl,Functor.map_comp]
    simp only [lambdaRestrictionSourceMap,KIP126.Synthetic.Context.lambdaDegree,Category.assoc]

  have selected_cross_index_normalized
      
      (i k : ℕ) (hi : 0 < i) (hik : i < k) :
      ∃ v : (SyntheticCategory.biShift (0,-(k:ℤ))).obj
          (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) 1) ⟶
        (SyntheticCategory.biShift (0,-(i:ℤ))).obj
          (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (k+1-i)),
        (SyntheticCategory.biShift (0,-(k:ℤ))).map (XModLambdaN.incl _ 1) ≫ v =
          lambdaRestrictionSourceMap i k hik.le _ ≫
            (SyntheticCategory.biShift (0,-(i:ℤ))).map (XModLambdaN.incl _ (k+1-i)) ∧
        ∀ (m w : ℤ) (a : BiHom m w (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) k)),
          (a ≫ (model.quotients.tower _).rho i k hik.le) ≫
            ((model.quotients.tower _).triangle hi (show i < k+1 by omega)).delta =
          (a ≫ (by simpa only [show k.succ-k=1 by omega] using
            ((model.quotients.tower _).triangle (show 0 < k by omega) (Nat.lt_succ_self k)).delta)) ≫
            (shiftFunctor SyntheticSpectrum (1:ℤ)).map v := by
    let A := model.nu.functor.obj (X.obj model.auxiliary)
    let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(k:ℤ))
    have hv_exists : ∃ v : F.obj (XModLambdaN A 1) ⟶
        (SyntheticCategory.biShift (0,-(i:ℤ))).obj (XModLambdaN A (k+1-i)),
        F.map (XModLambdaN.incl A 1) ≫ v =
          lambdaRestrictionSourceMap i k hik.le A ≫
            (SyntheticCategory.biShift (0,-(i:ℤ))).map (XModLambdaN.incl A (k+1-i)) := by
      have raw : ∃ v : F.obj (XModLambdaN A ((k+1-i)-(k-i))) ⟶
          (SyntheticCategory.biShift (0,-(i:ℤ))).obj (XModLambdaN A (k+1-i)),
          F.map (XModLambdaN.incl A ((k+1-i)-(k-i))) ≫ v =
            lambdaRestrictionSourceMap i k hik.le A ≫
              (SyntheticCategory.biShift (0,-(i:ℤ))).map (XModLambdaN.incl A (k+1-i)) := by
        obtain ⟨v,hv,_⟩ := canonical_finite_lambda_transition_exists
          (model.quotients.tower A) i k (k+1-i) hik (by omega)
        exact ⟨v,hv⟩
      exact (congrArg (fun n => ∃ v : F.obj (XModLambdaN A n) ⟶
          (SyntheticCategory.biShift (0,-(i:ℤ))).obj (XModLambdaN A (k+1-i)),
          F.map (XModLambdaN.incl A n) ≫ v =
            lambdaRestrictionSourceMap i k hik.le A ≫
              (SyntheticCategory.biShift (0,-(i:ℤ))).map (XModLambdaN.incl A (k+1-i)))
        (show (k+1-i)-(k-i)=1 by omega)).mp raw
    obtain ⟨v,hv⟩ := hv_exists
    have hn : k.succ-k=1 := by omega
    let c : XModLambdaN A (k+1-k) ⟶ XModLambdaN A 1 :=
      eqToHom (congrArg (fun n => XModLambdaN A n) hn)
    have incl_cast (n n' : ℕ) (h : n=n') :
        XModLambdaN.incl A n ≫ eqToHom (congrArg (fun n => XModLambdaN A n) h) =
          XModLambdaN.incl A n' := by
      subst n'
      simp only [eqToHom_refl,Category.comp_id]
    have hvraw : F.map (XModLambdaN.incl A (k+1-k)) ≫ (F.map c ≫ v) =
        lambdaRestrictionSourceMap i k hik.le A ≫
          (SyntheticCategory.biShift (0,-(i:ℤ))).map (XModLambdaN.incl A (k+1-i)) := by
      rw [←Category.assoc,←Functor.map_comp]
      dsimp only [c]
      rw [incl_cast (k+1-k) 1 hn]
      exact hv
    have cast_delta (Q : ℕ → SyntheticSpectrum) (F G : SyntheticSpectrum ⥤ SyntheticSpectrum) (B : SyntheticSpectrum)
        (n n' : ℕ) (h : n=n') (δ : B ⟶ G.obj (F.obj (Q n)))
        (ht : (B ⟶ G.obj (F.obj (Q n))) = (B ⟶ G.obj (F.obj (Q n')))) :
        δ ≫ G.map (F.map (eqToHom (congrArg Q h))) = ht.mp δ := by
      subst n'
      simp only [eqToHom_refl,CategoryTheory.Functor.map_id,Category.comp_id]
      rfl
    refine ⟨v,hv,?_⟩
    intro m w a
    have hc := selected_delta_cross_index_of_inclusion_square X
      i k (k+1) hi hik.le (Nat.lt_succ_self k) (F.map c ≫ v) hvraw m w a
    have hδ : ((model.quotients.tower A).triangle (show 0 < k by omega) (Nat.lt_succ_self k)).delta ≫
          (shiftFunctor SyntheticSpectrum (1:ℤ)).map (F.map c) =
        (by simpa only [show k.succ-k=1 by omega] using
          ((model.quotients.tower A).triangle (show 0 < k by omega) (Nat.lt_succ_self k)).delta) := by
      exact cast_delta (fun n => XModLambdaN A n) F (shiftFunctor SyntheticSpectrum (1:ℤ)) (XModLambdaN A k)
        (k+1-k) 1 hn _ _
    refine hc.trans ?_
    rw [Functor.map_comp]
    have h := congrArg (fun z => (a ≫ z) ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map v) hδ
    simpa only [Category.assoc,A,ClassicalObject.obj] using h

  have selected_boundary_of_normalized_cross
      
      (i k : ℕ) (hi : 0 < i) (hik : i < k) (s t : ℤ)
      (x : Ambient model X (s,t))
      (y : Ambient model X (s+k+1,t+k))
      (hd : HasDifferential (model.classical.obj (X.obj model.auxiliary))
        (k+1) (s,t) (s+k+1,t+k) x y)
      (hy : y ∈ KIP126.Literature.permanentCycles model X (s+k+1,t+k))
      (v : (SyntheticCategory.biShift (0,-(k:ℤ))).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) 1) ⟶
        (SyntheticCategory.biShift (0,-(i:ℤ))).obj
          (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (k+1-i)))
      (hv : (SyntheticCategory.biShift (0,-(k:ℤ))).map (XModLambdaN.incl _ 1) ≫ v =
        lambdaRestrictionSourceMap i k hik.le _ ≫
          (SyntheticCategory.biShift (0,-(i:ℤ))).map (XModLambdaN.incl _ (k+1-i)))
      (hc : ∀ (a : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) k)),
        (a ≫ (model.quotients.tower _).rho i k hik.le) ≫
          ((model.quotients.tower _).triangle hi (show i < k+1 by omega)).delta =
        (a ≫ (by simpa only [show k.succ-k=1 by omega] using
          ((model.quotients.tower _).triangle (show 0 < k by omega) (Nat.lt_succ_self k)).delta)) ≫
          (shiftFunctor SyntheticSpectrum (1:ℤ)).map v) :
      ∃ a : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) i),
        a ≫ (model.quotients.tower _).rho 1 i hi =
          firstLabel model X s t x ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1 ∧
        Detects (model.convergence (.quotient (k+1-i) (.nu X)))
          (s+k+1,t+k,t+k-(k-i:ℕ))
          (finiteTargetLabel model X (k+1-i) (s+k+1) (t+k) (k-i) y)
          (homotopyRegrade (by dsimp; omega) (by dsimp; omega)
            (biSuspensionHomEquiv (t-s) t (i:ℤ) (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (k+1-i))
              (a ≫ ((model.quotients.tower _).triangle hi (show i < k+1 by omega)).delta))) := by
    let A := model.nu.functor.obj (X.obj model.auxiliary)
    let δ : XModLambdaN A k ⟶
        ((SyntheticCategory.biShift (0,-(k:ℤ))).obj (XModLambdaN A 1))⟦(1:ℤ)⟧ := by
      simpa only [show k.succ-k=1 by omega] using
        ((model.quotients.tower A).triangle (show 0 < k by omega) (Nat.lt_succ_self k)).delta
    obtain ⟨ak,α,ha,hα,hδ,hfirst⟩ := adjacent_selected_representative_and_target_lift
      i k hi hik.le s t x y hd hy
    let α' : BiHom ((t-s)-1) (t+k) A := homotopyRegrade (by omega) rfl α
    have regrade_comp {m m' w w' : ℤ} (hm : m=m') (hw : w=w')
        {A B : SyntheticSpectrum} (a : BiHom m w A) (f : A ⟶ B) :
        homotopyRegrade hm hw (a≫f) = homotopyRegrade hm hw a ≫ f := by
      subst m'; subst w'; rfl
    have regrade_compose {m m' m'' w w' w'' : ℤ}
        (hm : m=m') (hw : w=w') (hm' : m'=m'') (hw' : w'=w'')
        {B : SyntheticSpectrum} (b : BiHom m w B) :
        homotopyRegrade hm' hw' (homotopyRegrade hm hw b) =
          homotopyRegrade (hm.trans hm') (hw.trans hw') b := by
      subst m'; subst w'; subst m''; subst w''; rfl
    have undo_regrade {n n' w : ℤ} (hn : n=n') {B C : SyntheticSpectrum}
        (a : BiHom n w B) (b : BiHom n' w C) (f : C ⟶ B)
        (h : homotopyRegrade hn rfl a = b ≫ f) :
        a = homotopyRegrade hn.symm rfl b ≫ f := by
      subst n'
      exact h
    have hδ' : biSuspensionHomEquiv (t-s) t (k:ℤ) (XModLambdaN A 1) (ak≫δ) =
        α' ≫ XModLambdaN.incl A 1 := by
      exact undo_regrade (by omega) _ α (XModLambdaN.incl A 1) hδ
    have hδactual : ak≫δ =
        (biSuspensionHomEquiv (t-s) t (k:ℤ) A).symm α' ≫
          (shiftFunctor SyntheticSpectrum (1:ℤ)).map ((SyntheticCategory.biShift (0,-(k:ℤ))).map
            (XModLambdaN.incl A 1)) := by
      apply (biSuspensionHomEquiv (t-s) t (k:ℤ) (XModLambdaN A 1)).injective
      rw [hδ',bi_susp_natural model.quotients.coherence,AddEquiv.apply_symm_apply]
    have heval : biSuspensionHomEquiv (t-s) t (i:ℤ) (XModLambdaN A (k+1-i))
        ((ak ≫ (model.quotients.tower A).rho i k hik.le) ≫
          ((model.quotients.tower A).triangle hi (show i < k+1 by omega)).delta) =
        homotopyRegrade rfl (by omega)
          (lambdaMultiply (k-i) α' ≫ XModLambdaN.incl A (k+1-i)) := by
      rw [hc,hδactual,Category.assoc,←Functor.map_comp,hv]
      exact lambda_transition_evaluation model.quotients.coherence i k hik.le (k+1-i) (t-s) t A α'
    refine ⟨ak ≫ (model.quotients.tower A).rho i k hik.le,hfirst,?_⟩
    rw [heval]
    have hcal := finite_lambda_detects X (k+1-i) (k-i) (by omega) (by omega)
      (s+k+1) (t+k) y hy α hα
    have cancel_lambda_regrade {n n' w w' : ℤ} (hn : n=n') (d : ℕ)
        (hw : w-(d:ℤ)=w') {B C : SyntheticSpectrum} (a : BiHom n w B) (f : B ⟶ C) :
        homotopyRegrade hn.symm hw.symm
          (homotopyRegrade rfl hw
            (lambdaMultiply d (homotopyRegrade hn rfl a) ≫ f)) =
          lambdaMultiply d a ≫ f := by
      subst n'
      subst w'
      rfl
    have hlast := cancel_lambda_regrade
      (show (t+k)-(s+k+1)=(t-s)-1 by omega) (k-i)
      (show (t+k)-(k-i:ℕ)=t+i by omega) α (XModLambdaN.incl A (k+1-i))
    exact (congrArg (Detects (model.convergence (.quotient (k+1-i) (.nu X)))
      (s+k+1,t+k,t+k-(k-i:ℕ))
      (finiteTargetLabel model X (k+1-i) (s+k+1) (t+k) (k-i) y)) hlast).mpr hcal

  obtain ⟨v,hv,hc⟩ := selected_cross_index_normalized i k hi hik
  exact selected_boundary_of_normalized_cross i k hi hik s t x y hd hy
    v hv (hc (t-s) t)

private theorem selected_mahowald_case (X : ClassicalObject)
    (i q : ℕ) (hi : 0 < i) (hq : 0 < q) (s t : ℤ)
    (x : Ambient model X (s,t))
    (y : Ambient model X (s+i+q,t+i+q-1))
    (hd : HasDifferential (model.classical.obj (X.obj model.auxiliary))
      (i+q) (s,t) (s+i+q,t+i+q-1) x y)
    (hy : y ∈ KIP126.Literature.permanentCycles model X (s+i+q,t+i+q-1)) :
    let A := model.nu.functor.obj (X.obj model.auxiliary)
    let δ : XModLambdaN A i ⟶
        ((SyntheticCategory.biShift (0,-(i:ℤ))).obj (XModLambdaN A q))⟦(1:ℤ)⟧ := by
      simpa only [Nat.add_sub_cancel_left] using
        ((model.quotients.tower A).triangle hi (show i < i+q by omega)).delta
    ∃ a : BiHom (t-s) t (XModLambdaN A i),
      a ≫ (model.quotients.tower A).rho 1 i hi =
        firstLabel model X s t x ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app A) 1 ∧
      Detects (model.convergence (.quotient q (.nu X))) (s+i+q,t+i+q-1,t+i)
        (regradeE2 (by exact congrArg (fun w : ℤ => (s+i+q,t+i+q-1,w)) (by omega))
          (finiteTargetLabel model X q (s+i+q) (t+i+q-1) (q-1) y))
        (homotopyRegrade (by dsimp; omega) rfl
          (biSuspensionHomEquiv (t-s) t (i:ℤ) (XModLambdaN A q) (a≫δ))) := by
  have selected_boundary_nonadjacent_reindexed
      
      (i k j q d : ℕ) (hi : 0 < i) (hik : i < k)
      (hj : j=k+1) (hq : j-i=q) (hdexp : d=k-i)
      (s t S T : ℤ) (hS : S=s+k+1) (hT : T=t+k)
      (x : Ambient model X (s,t)) (y : Ambient model X (S,T))
      (hd : HasDifferential (model.classical.obj (X.obj model.auxiliary))
        j (s,t) (S,T) x y)
      (hy : y ∈ KIP126.Literature.permanentCycles model X (S,T)) :
      let A := model.nu.functor.obj (X.obj model.auxiliary)
      let δ : XModLambdaN A i ⟶
          ((SyntheticCategory.biShift (0,-(i:ℤ))).obj (XModLambdaN A q))⟦(1:ℤ)⟧ := by
        simpa only [hq] using
          ((model.quotients.tower A).triangle hi (show i < j by omega)).delta
      ∃ a : BiHom (t-s) t (XModLambdaN A i),
        a ≫ (model.quotients.tower A).rho 1 i hi =
          firstLabel model X s t x ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app A) 1 ∧
        Detects (model.convergence (.quotient q (.nu X))) (S,T,t+i)
          (regradeE2 (by exact congrArg (fun w : ℤ => (S,T,w)) (by omega)) (finiteTargetLabel model X q S T d y))
          (homotopyRegrade (by dsimp; omega) rfl
            (biSuspensionHomEquiv (t-s) t (i:ℤ) (XModLambdaN A q) (a≫δ))) := by
    subst j
    subst q
    subst d
    subst S
    subst T
    dsimp only
    obtain ⟨a,ha,had⟩ := selected_boundary_nonadjacent X i k hi hik s t x y hd hy
    refine ⟨a,ha,?_⟩
    have change_weight {X : SyntheticObject} (S T w w' m bweight : ℤ)
        (hw : w=w') (hm : m=T-S) (hb : bweight=w)
        (z : (model.family.obj (X.obj model.nu model.auxiliary)).E₂ (S,T,w))
        (b : BiHom m bweight (X.obj model.nu model.auxiliary))
        (h : Detects (model.convergence X) (S,T,w) z (homotopyRegrade hm hb b)) :
        Detects (model.convergence X) (S,T,w')
          (regradeE2 (congrArg (fun v => (S,T,v)) hw) z)
          (homotopyRegrade hm (hb.trans hw) b) := by
      subst w'
      simpa only [regradeE2,eqToHom_refl,ModuleCat.id_apply] using h
    exact change_weight (s+k+1) (t+k) (t+k-(k-i:ℕ)) (t+i) ((t-s)-1) (t+i)
      (by omega) (by omega) (by omega) _ _ had

  have selected_boundary_adjacent_reindexed
      
      (i : ℕ) (hi : 0 < i) (s t S T : ℤ) (hS : S=s+i+1) (hT : T=t+i)
      (x : Ambient model X (s,t)) (y : Ambient model X (S,T))
      (hd : HasDifferential (model.classical.obj (X.obj model.auxiliary))
        (i+1) (s,t) (S,T) x y) :
      let A := model.nu.functor.obj (X.obj model.auxiliary)
      let δ : XModLambdaN A i ⟶
          ((SyntheticCategory.biShift (0,-(i:ℤ))).obj (XModLambdaN A 1))⟦(1:ℤ)⟧ := by
        simpa only [show i.succ-i=1 by omega] using
          ((model.quotients.tower A).triangle hi (Nat.lt_succ_self i)).delta
      ∃ a : BiHom (t-s) t (XModLambdaN A i),
        a ≫ (model.quotients.tower A).rho 1 i hi =
          firstLabel model X s t x ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app A) 1 ∧
        Detects (model.convergence (.quotient 1 (.nu X))) (S,T,t+i)
          (regradeE2 (by exact congrArg (fun w : ℤ => (S,T,w)) (by omega)) (finiteTargetLabel model X 1 S T 0 y))
          (homotopyRegrade (by dsimp; omega) rfl
            (biSuspensionHomEquiv (t-s) t (i:ℤ) (XModLambdaN A 1) (a≫δ))) := by
    subst S
    subst T
    exact adjacent_mahowald_case X i hi s t x y hd

  by_cases hq1 : q=1
  · subst q
    exact selected_boundary_adjacent_reindexed i hi s t
      (s+i+1) (t+i+1-1) (by omega) (by omega) x y hd
  · exact selected_boundary_nonadjacent_reindexed
      i (i+q-1) (i+q) q (q-1) hi (by omega) (by omega) (by omega) (by omega)
      s t (s+i+q) (t+i+q-1) (by omega) (by omega) x y hd hy


end
end KIP126.ProofTools.Internal.Mahowald
