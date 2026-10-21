module

import all KIP126.ProofTools.MahowaldLeibniz.TerminalSquare
import all KIP126.ProofTools.MahowaldLeibniz.CoreAtLevel
import all KIP126.ProofTools.MahowaldLeibniz.Bockstein
import all KIP126.ProofTools.GeneralizedMahowald.FiniteComparison
import all KIP126.ProofTools.GeneralizedLeibniz.LeftEdge
import all KIP126.ProofTools.GeneralizedLeibniz.LevelSource
import all KIP126.ProofTools.GeneralizedLeibniz.LevelBoundary
import all KIP126.ProofTools.GeneralizedLeibniz.BoundaryDivision
import KIP126.AdamsSynthetic.Standard.FirstQuotientCompatibility

/-! The first classical differential produces the specified source of the
actual finite Mahowald--Leibniz comparison. The quotient, boundary, shift,
and normalization arrows are those of the selected model. -/

@[expose] section
namespace KIP126.ProofTools.Internal.MahowaldLeibniz
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard KIP126.Literature
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
open KIP126.ProofTools.Internal.Leibniz
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2000000

private def boundaryPositiveSuspIso (e : ℤ) (q : ℕ) (A : SyntheticSpectrum) :
    (SyntheticCategory.biShift (0,e)).obj
      (((SyntheticCategory.biShift (0,-(q:ℤ))).obj A)⟦(1:ℤ)⟧) ≅
    ((SyntheticCategory.biShift (0,-(q:ℤ))).obj
      ((SyntheticCategory.biShift (0,e)).obj A))⟦(1:ℤ)⟧ := by
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,e)
  letI := model.exactness.shiftCommShift (0,e)
  exact (F.commShiftIso (1:ℤ)).app _ ≪≫
    (shiftFunctor SyntheticSpectrum (1:ℤ)).mapIso
      ((shiftCommIso (0,e) (0,-(q:ℤ))).symm.app A)

private theorem boundaryPositiveSuspIso_natural (e : ℤ) (q : ℕ)
    {A B : SyntheticSpectrum} (f : A ⟶ B) :
    (SyntheticCategory.biShift (0,e)).map
        ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
          ((SyntheticCategory.biShift (0,-(q:ℤ))).map f)) ≫
      (boundaryPositiveSuspIso e q B).hom =
      (boundaryPositiveSuspIso e q A).hom ≫
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map
          ((SyntheticCategory.biShift (0,-(q:ℤ))).map
            ((SyntheticCategory.biShift (0,e)).map f)) := by
  letI := model.exactness.shiftCommShift (0,e)
  simp only [boundaryPositiveSuspIso,Iso.trans_hom,Functor.mapIso_hom,Iso.app_hom]
  rw [←Category.assoc,Functor.commShiftIso_hom_naturality]
  simp only [Category.assoc,←Functor.map_comp]
  congr 1
  exact congrArg ((shiftFunctor SyntheticSpectrum (1:ℤ)).map)
    ((shiftCommIso (0,e) (0,-(q:ℤ))).inv.naturality f)

private theorem vertical_translate_symm_comp {A B : SyntheticSpectrum}
    (f : A ⟶ B) (e m w : ℤ)
    (a : BiHom m (w+e) ((SyntheticCategory.biShift (0,e)).obj A)) :
    (verticalTranslate B e m w).symm
        (a ≫ (SyntheticCategory.biShift (0,e)).map f) =
      (verticalTranslate A e m w).symm a ≫ f := by
  apply (verticalTranslate B e m w).injective
  rw [AddEquiv.apply_symm_apply,←vertical_translate_comp,AddEquiv.apply_symm_apply]

private def positiveBoundaryReindex (e : ℤ) (q : ℕ) (m w : ℤ)
    (A : SyntheticSpectrum) : BiHom (m-1) (w+q) A ≃+ BiHom (m-1) (w+q) A :=
  (biSuspensionHomEquiv m w q A).symm |>.trans
    (verticalTranslate _ e m w) |>.trans
    (homPostcompAddEquiv (boundaryPositiveSuspIso e q A)) |>.trans
    (biSuspensionHomEquiv m (w+e) q ((SyntheticCategory.biShift (0,e)).obj A)) |>.trans
    (regradeAddEquiv rfl (by omega)) |>.trans
    (verticalTranslate A e (m-1) (w+q)).symm

private theorem positiveBoundaryReindex_natural (e : ℤ) (q : ℕ) (m w : ℤ)
    {A B : SyntheticSpectrum} (f : A ⟶ B) (a : BiHom (m-1) (w+q) A) :
    positiveBoundaryReindex e q m w B (a≫f) =
      positiveBoundaryReindex e q m w A a ≫ f := by
  dsimp only [positiveBoundaryReindex,AddEquiv.trans_apply,regradeAddEquiv,
    homPostcompAddEquiv,AddEquiv.coe_mk,Equiv.coe_fn_mk]
  rw [bi_susp_symm_natural,←vertical_translate_comp,Category.assoc,
    boundaryPositiveSuspIso_natural,←Category.assoc,
    bi_susp_natural model.quotients.coherence,homotopyRegrade_comp,
    vertical_translate_symm_comp]

private def positiveBoundarySourceIso (e : ℤ) (q : ℕ) (m w : ℤ) :
    Smn (m-1) (w+q) ≅ (Smn (m-1) (w+q) : SyntheticSpectrum) where
  hom := positiveBoundaryReindex e q m w _ (𝟙 _)
  inv := (positiveBoundaryReindex e q m w _).symm (𝟙 _)
  hom_inv_id := by
    rw [←positiveBoundaryReindex_natural,Category.id_comp,AddEquiv.apply_symm_apply]
  inv_hom_id := by
    apply (positiveBoundaryReindex e q m w _).injective
    rw [positiveBoundaryReindex_natural,AddEquiv.apply_symm_apply,Category.id_comp]

private theorem positiveBoundaryReindex_eq_precomp (e : ℤ) (q : ℕ) (m w : ℤ)
    (A : SyntheticSpectrum) (a : BiHom (m-1) (w+q) A) :
    positiveBoundaryReindex e q m w A a =
      (positiveBoundarySourceIso e q m w).hom ≫ a := by
  simpa only [Category.id_comp,positiveBoundarySourceIso] using
    positiveBoundaryReindex_natural e q m w a (𝟙 _)


private theorem positive_quotient_proj_square (X : ClassicalObject) (e : ℤ) (q : ℕ) :
    (levelQuotientShiftIso X e q).hom ≫
      (SyntheticCategory.biShift (0,e)).map
        (XModLambdaN.proj (model.nu.functor.obj (X.obj model.auxiliary)) q) ≫
      (boundaryPositiveSuspIso e q (model.nu.functor.obj (X.obj model.auxiliary))).hom =
      XModLambdaN.proj ((SyntheticCategory.biShift (0,e)).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) q := by
  let A := model.nu.functor.obj (X.obj model.auxiliary)
  have h := congrArg (fun z => z ≫
    (biSuspensionIso q ((SyntheticCategory.biShift (0,e)).obj A)).hom)
    (level_quotient_shift_boundary X e q)
  rw [show (boundaryShiftNatIso e q).hom.app A =
    ((boundaryShiftNatIso e q).app A).hom from rfl,boundaryShiftNatIso_app] at h
  simpa only [A,absoluteBoundary,boundaryPositiveSuspIso,Iso.trans_hom,Iso.symm_hom,
    Functor.mapIso_hom,Functor.map_comp,Category.assoc,Iso.inv_hom_id,
    Category.comp_id,Iso.map_inv_hom_id_assoc] using h

private theorem shifted_absolute_boundary_eq_precomp
    (X : ClassicalObject) (e : ℤ) (q : ℕ) (m w : ℤ)
    (a : BiHom m w (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q)) :
    verticalTranslate _ e (m-1) (w+q)
      ((positiveBoundarySourceIso e q m w).hom ≫
        biSuspensionHomEquiv m w q (model.nu.functor.obj (X.obj model.auxiliary))
          (a ≫ XModLambdaN.proj _ q)) =
    homotopyRegrade rfl (by omega)
      (biSuspensionHomEquiv m (w+e) q
        ((SyntheticCategory.biShift (0,e)).obj
          (model.nu.functor.obj (X.obj model.auxiliary)))
        ((verticalTranslate _ e m w a ≫ (levelQuotientShiftIso X e q).inv) ≫
          XModLambdaN.proj _ q)) := by
  rw [←positiveBoundaryReindex_eq_precomp]
  dsimp only [positiveBoundaryReindex,AddEquiv.trans_apply,regradeAddEquiv,
    homPostcompAddEquiv,AddEquiv.coe_mk,Equiv.coe_fn_mk]
  rw [AddEquiv.apply_symm_apply,AddEquiv.symm_apply_apply]
  have h := congrArg (fun z => (levelQuotientShiftIso X e q).inv ≫ z)
    (positive_quotient_proj_square X e q)
  simp only [Iso.inv_hom_id_assoc] at h
  rw [Category.assoc,←h,←Category.assoc,vertical_translate_comp]

private theorem positive_first_label_shift (X : ClassicalObject) (s t : ℤ)
    (x : Ambient model X (s,t)) :
    verticalTranslate _ 1 (t-s) t (nativeFirstLabel X s t x) ≫
      (levelQuotientShiftIso X 1 1).inv = (model.firstQuotient X 1 s t).symm x := by
  have h := KIP126.AdamsSynthetic.Standard.firstQuotient_positive_shift X s t x
    (levelQuotientShiftIso X 1 1) (level_quotient_shift_incl X 1 1)
  rw [nativeFirstLabel_eq_regrade]
  simpa [verticalTranslate,regradeAddEquiv,
    suspInvarianceAddEquiv,susp_invariance,shiftHomotopyClass,Iso.homCongr,
    regrade_precomp,Category.assoc] using h

private theorem vertical_selected_delta_evaluation_eq_cofiber
    (X : ClassicalObject) (e : ℤ) (i j : ℕ)
    (T : LambdaRhoDeltaTriangle ((SyntheticCategory.biShift (0,e)).obj
      (model.nu.functor.obj (X.obj model.auxiliary))) i j)
    (m w : ℤ)
    (a : BiHom m w (XModLambdaN ((SyntheticCategory.biShift (0,e)).obj
      (model.nu.functor.obj (X.obj model.auxiliary))) i)) :
    a ≫ T.delta = a ≫ XModLambdaN.proj _ i ≫
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map
        ((SyntheticCategory.biShift (0,-(i:ℤ))).map (XModLambdaN.incl _ (j-i))) := by
  let A := (SyntheticCategory.biShift (0,e)).obj
    (model.nu.functor.obj (X.obj model.auxiliary))
  let base := XModLambdaN.cofiberTriangle A i
  obtain ⟨c,hc,hδ⟩ := complete_distinguished_triangle_morphism
    base (Triangle.mk T.lambdaMap T.rho T.delta)
    (XModLambdaN.cofiberTriangle_distinguished A i) T.distinguished
    ((SyntheticCategory.biShift (0,-(i:ℤ))).map (XModLambdaN.incl A (j-i)))
    (XModLambdaN.incl A j) T.lambda_quotient.symm
  change XModLambdaN A i ⟶ XModLambdaN A i at c
  change XModLambdaN.incl A i ≫ c = XModLambdaN.incl A j ≫ T.rho at hc
  have hc' : XModLambdaN.incl A i ≫ c = XModLambdaN.incl A i ≫ 𝟙 _ := by
    rw [hc,T.rho_quotient,Category.comp_id]
  have hac : a ≫ c = a := by
    simpa only [Category.comp_id] using
      vertical_quotient_maps_equal_on_spheres X e i i T.i_pos le_rfl c (𝟙 _) hc' m w a
  change XModLambdaN.proj A i ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map
      ((SyntheticCategory.biShift (0,-(i:ℤ))).map (XModLambdaN.incl A (j-i))) =
    c ≫ T.delta at hδ
  calc
    a ≫ T.delta = (a ≫ c) ≫ T.delta := by rw [hac]
    _ = a ≫ XModLambdaN.proj A i ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map
        ((SyntheticCategory.biShift (0,-(i:ℤ))).map (XModLambdaN.incl A (j-i))) := by
      rw [Category.assoc,←hδ]


/-- The first classical differential supplies a full native representative
of its target whose positive shift is the actual boundary of the fixed
positive first-quotient label. The comparison automorphism is constructed
internally and preserves the specified nu label. -/
private theorem first_differential_positive_absolute_source
    (X : ClassicalObject) (k : ℕ) (hk : 0<k) (s t : ℤ)
    (x : Ambient model X (s,t)) (y : Ambient model X (s+k+1,t+k))
    (hd : HasDifferential (model.classical.obj (X.obj model.auxiliary))
      (k+1) (s,t) (s+k+1,t+k) x y) :
    ∃ α : BiHom (t-s-1) (t+(1:ℕ))
        (model.nu.functor.obj (X.obj model.auxiliary)),
      Detects (model.convergence (.nu X)) (s+k+1,t+k,t+(1:ℕ))
        (nuWeightLabel model X (s+k+1) (t+k) (t+(1:ℕ)) (by omega) y)
        (homotopyRegrade (by dsimp; omega) rfl α) ∧
      verticalTranslate _ 1 (t-s-1) (t+(1:ℕ)) α =
        homotopyRegrade rfl (by omega)
          (biSuspensionHomEquiv (t-s) (t+1) (1:ℕ)
            ((SyntheticCategory.biShift (0,1)).obj
              (model.nu.functor.obj (X.obj model.auxiliary)))
            ((model.firstQuotient X 1 s t).symm x ≫ XModLambdaN.proj _ 1)) := by
  obtain ⟨a,_,hay⟩ := adjacent_absolute_boundary X k hk s t x y hd
  have hy := first_label_lift_permanent X (s+k+1) (t+k) y
    (boundaryRepresentative X k s t a) hay
  obtain ⟨b,hb,hbd⟩ := differential_absolute_boundary X 1 k (by decide) (by omega)
    s t x y hd hy
  have hb' : b = nativeFirstLabel X s t x := by
    simpa only [nativeFirstLabel,(model.quotients.tower _).rho_id,Category.comp_id] using hb
  subst b
  let β := biSuspensionHomEquiv (t-s) t (1:ℕ)
    (model.nu.functor.obj (X.obj model.auxiliary))
    (nativeFirstLabel X s t x ≫ XModLambdaN.proj _ 1)
  let u := positiveBoundarySourceIso 1 1 (t-s) t
  refine ⟨u.hom ≫ β,?_,?_⟩
  · exact level_regraded_automorphism_detects X (s+k+1) (t+k) (t+(1:ℕ))
      (by omega) (t-s-1) (by omega) y u β hbd
  · have h := shifted_absolute_boundary_eq_precomp X 1 1 (t-s) t (nativeFirstLabel X s t x)
    rw [positive_first_label_shift] at h
    exact h


private theorem firstFiniteBoundaryRepresentative_vertical_eq
    (X : ClassicalObject) (e : ℤ) (N : ℕ) (hN : 0<N) (m w : ℤ)
    (a : BiHom m w (XModLambdaN ((SyntheticCategory.biShift (0,e)).obj
      (model.nu.functor.obj (X.obj model.auxiliary))) 1)) :
    firstFiniteBoundaryRepresentative _ N hN m w a =
      biSuspensionHomEquiv m w (1:ℕ) ((SyntheticCategory.biShift (0,e)).obj
        (model.nu.functor.obj (X.obj model.auxiliary)))
        (a ≫ XModLambdaN.proj _ 1) ≫ XModLambdaN.incl _ N := by
  let A := (SyntheticCategory.biShift (0,e)).obj
    (model.nu.functor.obj (X.obj model.auxiliary))
  have h := vertical_selected_delta_evaluation_eq_cofiber X e 1 (1+N)
    ((model.quotients.tower A).triangle (show 0<1 by decide) (show 1 < 1+N by omega)) m w a
  have transport (n : ℕ) (hn : n=N)
      (δ : XModLambdaN A 1 ⟶
        ((SyntheticCategory.biShift (0,-(1:ℕ))).obj (XModLambdaN A n))⟦(1:ℤ)⟧)
      (hδ : a ≫ δ = a ≫ XModLambdaN.proj A 1 ≫
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map
          ((SyntheticCategory.biShift (0,-(1:ℕ))).map (XModLambdaN.incl A n))) :
      biSuspensionHomEquiv m w (1:ℕ) (XModLambdaN A N)
        (a ≫ Eq.mp (congrArg (fun j => XModLambdaN A 1 ⟶
          ((SyntheticCategory.biShift (0,-(1:ℕ))).obj (XModLambdaN A j))⟦(1:ℤ)⟧) hn) δ) =
      biSuspensionHomEquiv m w (1:ℕ) A (a ≫ XModLambdaN.proj A 1) ≫
        XModLambdaN.incl A N := by
    subst n
    change biSuspensionHomEquiv m w (1:ℕ) (XModLambdaN A N) (a ≫ δ) = _
    rw [hδ,←Category.assoc,bi_susp_natural model.quotients.coherence]
  exact transport (1+N-1) (by omega) _ h

/-- This raw finite source is the finite projection of its actual full
absolute boundary after ordinary suspension. -/
private theorem suspendedFirstFiniteBoundary_full_projection
    (X : ClassicalObject) (e : ℤ) (N : ℕ) (hN : 0<N) (m w : ℤ)
    (ex : XModLambdaN (((SyntheticCategory.biShift (0,e)).obj
      (model.nu.functor.obj (X.obj model.auxiliary)))⟦(1:ℤ)⟧) N ≅
      (XModLambdaN ((SyntheticCategory.biShift (0,e)).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) N)⟦(1:ℤ)⟧)
    (hex : XModLambdaN.incl _ N ≫ ex.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ N))
    (a : BiHom m w (XModLambdaN ((SyntheticCategory.biShift (0,e)).obj
      (model.nu.functor.obj (X.obj model.auxiliary))) 1)) :
    suspendedFirstFiniteBoundary _ N hN m w ex a =
      ordinarySuspendedRepresentative _ m (w+(1:ℕ))
        (biSuspensionHomEquiv m w (1:ℕ) ((SyntheticCategory.biShift (0,e)).obj
          (model.nu.functor.obj (X.obj model.auxiliary)))
          (a ≫ XModLambdaN.proj _ 1)) ≫ XModLambdaN.incl _ N := by
  dsimp only [suspendedFirstFiniteBoundary]
  rw [firstFiniteBoundaryRepresentative_vertical_eq,
    ordinarySuspendedRepresentative_natural,←hex]
  simp only [Category.assoc,Iso.hom_inv_id,Category.comp_id]


private def positiveSuspensionIso (A : SyntheticSpectrum) :
    ((SyntheticCategory.biShift (0,1)).obj A)⟦(1:ℤ)⟧ ≅
      (SyntheticCategory.biShift (1,1)).obj A :=
  (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).symm.app _ ≪≫
    (biShiftAddIso (0,1) (1,0) (1,1) (by ext <;> simp)).app A

private theorem positive_ordinary_suspension_class
    (A : SyntheticSpectrum) (m w : ℤ) (a : BiHom (m-1) w A) :
    ordinarySuspendedRepresentative _ m (w+1)
        (verticalTranslate A 1 (m-1) w a) ≫ (positiveSuspensionIso A).hom =
      homotopyRegrade (by dsimp; omega) (by simp)
        (shiftHomotopyClass (1,1) (m-1,w) a) := by
  have h := shift_hom_associativity model.quotients.coherence
    (m-1,w) (0,1) (1,0) (m-1,w+1) (1,1) (m,w+1)
    (by ext <;> simp) (by ext <;> simp) (by ext <;> simp) (by ext <;> simp) a
  have hh := congrArg (fun z => z ≫
    (biShiftAddIso (0,1) (1,0) (1,1) (by ext <;> simp)).hom.app A) h.symm
  simp only [Category.assoc,Iso.inv_hom_id_app,Category.comp_id] at hh
  simpa [ordinarySuspendedRepresentative,verticalTranslate,regradeAddEquiv,
    suspInvarianceAddEquiv,susp_invariance,shiftHomotopyClass,Iso.homCongr,
    positiveSuspensionIso,Iso.trans_hom,Iso.symm_hom,Iso.app_inv,
    biShiftAddIso,regrade_precomp,Functor.map_comp,Category.assoc] using hh


private theorem quotient_unshift_projected_shift
    (X : ClassicalObject) (δ p : ℤ×ℤ) (N : ℕ)
    (ε : XModLambdaN ((SyntheticCategory.biShift δ).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) N ≅
      (SyntheticCategory.biShift δ).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) N))
    (hε : XModLambdaN.incl _ N ≫ ε.hom =
      (SyntheticCategory.biShift δ).map (XModLambdaN.incl _ N))
    (a : BiHom p.1 p.2 (model.nu.functor.obj (X.obj model.auxiliary))) :
    quotientUnshift X δ p N ε
      (shiftHomotopyClass δ p a ≫ XModLambdaN.incl _ N) =
      a ≫ XModLambdaN.incl _ N := by
  apply (SyntheticCategory.biShift_fullyFaithful δ).map_injective
  simp [quotientUnshift,shiftHomotopyClass,Category.assoc,hε,Functor.map_comp]

private theorem projected_suspended_positive_unshift
    (X : ClassicalObject) (N : ℕ) (m w : ℤ)
    (ε : XModLambdaN ((SyntheticCategory.biShift (1,1)).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) N ≅
      (SyntheticCategory.biShift (1,1)).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) N))
    (hε : XModLambdaN.incl _ N ≫ ε.hom =
      (SyntheticCategory.biShift (1,1)).map (XModLambdaN.incl _ N))
    (a : BiHom (m-1) w (model.nu.functor.obj (X.obj model.auxiliary))) :
    quotientUnshift X (1,1) (m-1,w) N ε
      (homotopyRegrade (by dsimp; omega) (by simp)
        (ordinarySuspendedRepresentative _ m (w+1)
          (verticalTranslate _ 1 (m-1) w a) ≫ XModLambdaN.incl _ N ≫
          XModLambdaN.map (positiveSuspensionIso _).hom N)) =
      a ≫ XModLambdaN.incl _ N := by
  rw [←XModLambdaN.incl_naturality (positiveSuspensionIso (model.nu.functor.obj (X.obj model.auxiliary))).hom N,←Category.assoc,positive_ordinary_suspension_class]
  simp only [homotopyRegrade_comp,normalized_homotopy_regrade_trans]
  exact quotient_unshift_projected_shift X (1,1) (m-1,w) N ε hε a


private theorem positive_first_finite_boundary_unshift_eq
    (X : ClassicalObject) (N : ℕ) (hN : 0<N) (m w : ℤ)
    (ex : XModLambdaN (((SyntheticCategory.biShift (0,1)).obj
      (model.nu.functor.obj (X.obj model.auxiliary)))⟦(1:ℤ)⟧) N ≅
      (XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) N)⟦(1:ℤ)⟧)
    (hex : XModLambdaN.incl _ N ≫ ex.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ N))
    (ε : XModLambdaN ((SyntheticCategory.biShift (1,1)).obj
      (model.nu.functor.obj (X.obj model.auxiliary))) N ≅
      (SyntheticCategory.biShift (1,1)).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) N))
    (hε : XModLambdaN.incl _ N ≫ ε.hom =
      (SyntheticCategory.biShift (1,1)).map (XModLambdaN.incl _ N))
    (a : BiHom m (w+1) (XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
      (model.nu.functor.obj (X.obj model.auxiliary))) 1))
    (α : BiHom (m-1) (w+1) (model.nu.functor.obj (X.obj model.auxiliary)))
    (hα : verticalTranslate _ 1 (m-1) (w+1) α =
      biSuspensionHomEquiv m (w+1) (1:ℕ) ((SyntheticCategory.biShift (0,1)).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) (a ≫ XModLambdaN.proj _ 1)) :
    quotientUnshift X (1,1) (m-1,w+1) N ε
      (homotopyRegrade (by dsimp; omega) (by simp)
        (suspendedFirstFiniteBoundary _ N hN m (w+1) ex a ≫
          XModLambdaN.map (positiveSuspensionIso _).hom N)) =
      α ≫ XModLambdaN.incl _ N := by
  rw [suspendedFirstFiniteBoundary_full_projection X 1 N hN m (w+1) ex hex,←hα]
  simpa [Category.assoc] using projected_suspended_positive_unshift X N m (w+1) ε hε α

/-- The exact finite source from the first classical differential, in native
X coordinates after the selected normalization and quotient comparison. -/
private theorem positive_first_finite_boundary_source_detects
    (X : ClassicalObject) (k N : ℕ) (hk : 0<k) (hN : 0<N) (s t : ℤ)
    (x : Ambient model X (s,t)) (y : Ambient model X (s+k+1,t+k))
    (hd : HasDifferential (model.classical.obj (X.obj model.auxiliary))
      (k+1) (s,t) (s+k+1,t+k) x y)
    (ex : XModLambdaN (((SyntheticCategory.biShift (0,1)).obj
      (model.nu.functor.obj (X.obj model.auxiliary)))⟦(1:ℤ)⟧) N ≅
      (XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) N)⟦(1:ℤ)⟧)
    (hex : XModLambdaN.incl _ N ≫ ex.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ N))
    (ε : XModLambdaN ((SyntheticCategory.biShift (1,1)).obj
      (model.nu.functor.obj (X.obj model.auxiliary))) N ≅
      (SyntheticCategory.biShift (1,1)).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) N))
    (hε : XModLambdaN.incl _ N ≫ ε.hom =
      (SyntheticCategory.biShift (1,1)).map (XModLambdaN.incl _ N)) :
    Detects (model.convergence (.quotient N (.nu X))) (s+k+1,t+k,t+(1:ℕ))
      ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) N).pageMap
        2 (s+k+1,t+k,t+(1:ℕ))
        (nuWeightLabel model X (s+k+1) (t+k) (t+(1:ℕ)) (by omega) y))
      (homotopyRegrade (by dsimp; omega) rfl
        (quotientUnshift X (1,1) (t-s-1,t+1) N ε
          (homotopyRegrade (by dsimp; omega) (by simp)
            (suspendedFirstFiniteBoundary _ N hN (t-s) (t+1) ex
              ((model.firstQuotient X 1 s t).symm x) ≫
                XModLambdaN.map (positiveSuspensionIso _).hom N)))) := by
  obtain ⟨α,hα,hshift⟩ := first_differential_positive_absolute_source X k hk s t x y hd
  have heq := positive_first_finite_boundary_unshift_eq X N hN (t-s) t
    ex hex ε hε ((model.firstQuotient X 1 s t).symm x) α hshift
  rw [heq]
  have hd := detects_map (.nu X) (.quotient N (.nu X)) (XModLambdaN.incl _ N)
    (s+k+1,t+k,t+(1:ℕ)) _ _ hα
  change Detects (model.convergence (.quotient N (.nu X))) (s+k+1,t+k,t+(1:ℕ))
    ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) N).pageMap
      2 (s+k+1,t+k,t+(1:ℕ))
      (nuWeightLabel model X (s+k+1) (t+k) (t+(1:ℕ)) (by omega) y))
    ((homotopyRegrade (by dsimp; omega) rfl α) ≫ XModLambdaN.incl _ N) at hd
  simpa only [homotopyRegrade_comp] using hd

private theorem normalized_suspension_native_comparison
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g +
      normalizedExponent model.classicalTower T.h = 1)
    (hf : normalizedExponent model.classicalTower T.f = 1) :
    HEq ((normalizedSuspensionNativeIso T he hf).hom ≫
        (model.nu.suspensionIso (T.X.obj model.auxiliary)).hom)
      ((SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).inv.app
          ((SyntheticCategory.biShift (0,1)).obj
            (model.nu.functor.obj (T.X.obj model.auxiliary))) ≫
        (biShiftAddIso (0,1) (1,0) (1,1) (by ext <;> simp)).hom.app
          (model.nu.functor.obj (T.X.obj model.auxiliary))) := by
  simp only [normalizedSuspensionNativeIso,Iso.trans_hom,Iso.symm_hom,
    Category.assoc,Iso.inv_hom_id,Category.comp_id]
  dsimp only [biShiftAddIso,normalizedTriangle,Triangle.mk]
  have general (A : SyntheticSpectrum) (k : ℕ) (hk : k=1)
      (hdeg : (0,(k:ℤ))+(1,0)=(1,1)) :
      HEq ((SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).inv.app
          ((SyntheticCategory.biShift (0,(k:ℤ))).obj A) ≫
        (SyntheticCategory.biShift_comp (0,(k:ℤ)) (1,0)).hom.app A ≫
        eqToHom (congrArg (fun j : ℤ×ℤ => (SyntheticCategory.biShift j).obj A) hdeg))
      ((SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).inv.app
          ((SyntheticCategory.biShift (0,1)).obj A) ≫
        (biShiftAddIso (0,1) (1,0) (1,1) (by ext <;> simp)).hom.app A) := by
    subst k
    rfl
  exact general _ _ hf (by ext <;> dsimp; omega)



private theorem quotient_unshift_regrade
    (X : ClassicalObject) (δ p p' : ℤ×ℤ) (N : ℕ)
    (ε : XModLambdaN ((SyntheticCategory.biShift δ).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) N ≅
      (SyntheticCategory.biShift δ).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) N))
    (hm : p.1=p'.1) (hw : p.2=p'.2)
    (a : BiHom (p.1+δ.1) (p.2+δ.2)
      (XModLambdaN ((SyntheticCategory.biShift δ).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) N)) :
    quotientUnshift X δ p' N ε
      (homotopyRegrade (by dsimp; omega) (by dsimp; omega) a) =
      homotopyRegrade hm hw (quotientUnshift X δ p N ε a) := by
  have hp : p=p' := Prod.ext hm hw
  subst p'
  rfl

private theorem finite_projected_weight_label_detects
    (X : ClassicalObject) (N c : ℕ) (S V w : ℤ) (hw : w=V-c)
    (hwt : w≤V) (y : Ambient model X (S,V))
    (a : BiHom (V-S) w (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) N))
    (ha : Detects (model.convergence (.quotient N (.nu X))) (S,V,w)
      ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) N).pageMap
        2 (S,V,w) (nuWeightLabel model X S V w hwt y)) a) :
    Detects (model.convergence (.quotient N (.nu X))) (S,V,V-c)
      (finiteTargetLabel model X N S V c y) (homotopyRegrade rfl hw a) := by
  subst w
  have hl : nuWeightLabel model X S V (V-c) hwt y = targetNuLabel model X S V c y := by
    unfold nuWeightLabel
    have labels (j : ℕ) (hj : j=c) (h : (S,V,V-j)=(S,V,V-c)) :
        regradeE2 h (targetNuLabel model X S V j y) = targetNuLabel model X S V c y := by
      subst j
      rfl
    exact labels _ (by omega) _
  rw [hl] at ha
  exact ha


private theorem positive_first_finite_boundary_target_detects
    (X : ClassicalObject) (k N c : ℕ) (hk : 0<k) (hN : 0<N)
    (hc : (c:ℤ)=k-1) (s t : ℤ)
    (x : Ambient model X (s,t)) (y : Ambient model X (s+k+1,t+k))
    (hd : HasDifferential (model.classical.obj (X.obj model.auxiliary))
      (k+1) (s,t) (s+k+1,t+k) x y)
    (ex : XModLambdaN (((SyntheticCategory.biShift (0,1)).obj
      (model.nu.functor.obj (X.obj model.auxiliary)))⟦(1:ℤ)⟧) N ≅
      (XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) N)⟦(1:ℤ)⟧)
    (hex : XModLambdaN.incl _ N ≫ ex.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ N))
    (ε : XModLambdaN ((SyntheticCategory.biShift (1,1)).obj
      (model.nu.functor.obj (X.obj model.auxiliary))) N ≅
      (SyntheticCategory.biShift (1,1)).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) N))
    (hε : XModLambdaN.incl _ N ≫ ε.hom =
      (SyntheticCategory.biShift (1,1)).map (XModLambdaN.incl _ N)) :
    Detects (model.convergence (.quotient N (.nu X))) (s+k+1,t+k,(t+k)-c)
      (finiteTargetLabel model X N (s+k+1) (t+k) c y)
      (quotientUnshift X (1,1) ((t+k)-(s+k+1),(t+k)-c) N ε
        (homotopyRegrade (by dsimp; omega) (by dsimp; omega)
          (suspendedFirstFiniteBoundary _ N hN (t-s) (t+1) ex
            ((model.firstQuotient X 1 s t).symm x) ≫
              XModLambdaN.map (positiveSuspensionIso _).hom N))) := by
  have h := positive_first_finite_boundary_source_detects X k N hk hN s t x y hd ex hex ε hε
  have ht := finite_projected_weight_label_detects X N c (s+k+1) (t+k) (t+(1:ℕ))
    (by omega) (by omega) y _ h
  have hr := quotient_unshift_regrade X (1,1) (t-s-1,t+1)
    ((t+k)-(s+k+1),(t+k)-c) N ε (by dsimp; omega) (by dsimp; omega)
    (homotopyRegrade (by dsimp; omega) (by simp)
      (suspendedFirstFiniteBoundary _ N hN (t-s) (t+1) ex
        ((model.firstQuotient X 1 s t).symm x) ≫
          XModLambdaN.map (positiveSuspensionIso _).hom N))
  simp only [normalized_homotopy_regrade_trans] at hr ht
  rw [hr]
  exact ht


private def positiveNormalizedSourceIso
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g +
      normalizedExponent model.classicalTower T.h = 1)
    (hf : normalizedExponent model.classicalTower T.f = 1) :
    (normalizedTriangle model T he).obj₁ ≅
      (SyntheticCategory.biShift (0,1)).obj
        (model.nu.functor.obj (T.X.obj model.auxiliary)) :=
  eqToIso (congrArg (fun k : ℕ => (SyntheticCategory.biShift (0,(k:ℤ))).obj
    (model.nu.functor.obj (T.X.obj model.auxiliary))) hf)

private theorem positive_normalized_source_arrow
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g +
      normalizedExponent model.classicalTower T.h = 1)
    (hf : normalizedExponent model.classicalTower T.f = 1) :
    (positiveNormalizedSourceIso T he hf).hom ≫ normalizedFirstMap T hf =
      (normalizedTriangle model T he).mor₁ := by
  have transport (A A' B : SyntheticSpectrum) (h : A=A')
      (ht : (A ⟶ B)=(A' ⟶ B)) (f : A ⟶ B) :
      eqToHom h ≫ ht.mp f = f := by
    subst A'
    simp
  dsimp only [positiveNormalizedSourceIso,normalizedFirstMap,normalizedTriangle,Triangle.mk]
  exact transport _ _ _ (congrArg (fun k : ℕ => (SyntheticCategory.biShift (0,(k:ℤ))).obj
    (model.nu.functor.obj (T.X.obj model.auxiliary))) hf) _ _


private theorem positive_normalized_source_suspension
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g +
      normalizedExponent model.classicalTower T.h = 1)
    (hf : normalizedExponent model.classicalTower T.f = 1) :
    (shiftFunctor SyntheticSpectrum (1:ℤ)).map (positiveNormalizedSourceIso T he hf).inv ≫
      (normalizedSuspensionNativeIso T he hf).hom ≫
        (model.nu.suspensionIso (T.X.obj model.auxiliary)).hom =
      (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).inv.app
          ((SyntheticCategory.biShift (0,1)).obj
            (model.nu.functor.obj (T.X.obj model.auxiliary))) ≫
        (biShiftAddIso (0,1) (1,0) (1,1) (by ext <;> simp)).hom.app
          (model.nu.functor.obj (T.X.obj model.auxiliary)) := by
  have transport (A A' B : SyntheticSpectrum) (h : A=A')
      (f : A⟦(1:ℤ)⟧ ⟶ B) (g : A'⟦(1:ℤ)⟧ ⟶ B) (hfg : HEq f g) :
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (eqToIso h).inv ≫ f = g := by
    subst A'
    simpa using eq_of_heq hfg
  exact transport _ _ _ (congrArg (fun k : ℕ => (SyntheticCategory.biShift (0,(k:ℤ))).obj
    (model.nu.functor.obj (T.X.obj model.auxiliary))) hf) _ _
      (normalized_suspension_native_comparison T he hf)

private theorem positive_normalized_source_inv_arrow
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g +
      normalizedExponent model.classicalTower T.h = 1)
    (hf : normalizedExponent model.classicalTower T.f = 1) :
    (positiveNormalizedSourceIso T he hf).inv ≫ (normalizedTriangle model T he).mor₁ =
      normalizedFirstMap T hf := by
  rw [←positive_normalized_source_arrow T he hf,←Category.assoc,Iso.inv_hom_id,Category.id_comp]

private theorem positive_normalized_source_raw_image
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g +
      normalizedExponent model.classicalTower T.h = 1)
    (hf : normalizedExponent model.classicalTower T.f = 1)
    (N : ℕ) (m w : ℤ)
    (a : BiHom m w (XModLambdaN (((SyntheticCategory.biShift (0,1)).obj
      (model.nu.functor.obj (T.X.obj model.auxiliary)))⟦(1:ℤ)⟧) N)) :
    (a ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
        (positiveNormalizedSourceIso T he hf).inv) N) ≫
      XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
        (normalizedTriangle model T he).mor₁) N =
    a ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
      (normalizedFirstMap T hf)) N := by
  rw [Category.assoc,←model.quotients.functoriality.map_comp,←Functor.map_comp,
    positive_normalized_source_inv_arrow]


private def actualNormalizedFirstFiniteBoundary
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g +
      normalizedExponent model.classicalTower T.h = 1)
    (hf : normalizedExponent model.classicalTower T.f = 1)
    (N : ℕ) (hN : 0<N) (s t : ℤ)
    (ex : XModLambdaN (((SyntheticCategory.biShift (0,1)).obj
      (model.nu.functor.obj (T.X.obj model.auxiliary)))⟦(1:ℤ)⟧) N ≅
      (XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
        (model.nu.functor.obj (T.X.obj model.auxiliary))) N)⟦(1:ℤ)⟧)
    (x : Ambient model T.X (s,t)) :
    BiHom (t-s) ((t+1)+(1:ℕ))
      (XModLambdaN ((normalizedTriangle model T he).obj₁⟦(1:ℤ)⟧) N) :=
  suspendedFirstFiniteBoundary _ N hN (t-s) (t+1) ex
    ((model.firstQuotient T.X 1 s t).symm x) ≫
    XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
      (positiveNormalizedSourceIso T he hf).inv) N

private theorem actual_first_finite_boundary_source_detects
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g +
      normalizedExponent model.classicalTower T.h = 1)
    (hf : normalizedExponent model.classicalTower T.f = 1)
    (k N c : ℕ) (hk : 0<k) (hN : 0<N) (hc : (c:ℤ)=k-1) (s t : ℤ)
    (x : Ambient model T.X (s,t)) (y : Ambient model T.X (s+k+1,t+k))
    (hd : HasDifferential (model.classical.obj (T.X.obj model.auxiliary))
      (k+1) (s,t) (s+k+1,t+k) x y)
    (ex : XModLambdaN (((SyntheticCategory.biShift (0,1)).obj
      (model.nu.functor.obj (T.X.obj model.auxiliary)))⟦(1:ℤ)⟧) N ≅
      (XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
        (model.nu.functor.obj (T.X.obj model.auxiliary))) N)⟦(1:ℤ)⟧)
    (hex : XModLambdaN.incl _ N ≫ ex.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ N))
    (ε : XModLambdaN ((SyntheticCategory.biShift (1,1)).obj
      (model.nu.functor.obj (T.X.obj model.auxiliary))) N ≅
      (SyntheticCategory.biShift (1,1)).obj
        (XModLambdaN (model.nu.functor.obj (T.X.obj model.auxiliary)) N))
    (hε : XModLambdaN.incl _ N ≫ ε.hom =
      (SyntheticCategory.biShift (1,1)).map (XModLambdaN.incl _ N)) :
    Detects (model.convergence (.quotient N (.nu T.X))) (s+k+1,t+k,(t+k)-c)
      (finiteTargetLabel model T.X N (s+k+1) (t+k) c y)
      (rawMaySourceDesuspend T he hf N c (s+k+1) (t+k) ε
        (homotopyRegrade (by omega) (by omega)
          (actualNormalizedFirstFiniteBoundary T he hf N hN s t ex x))) := by
  have h := positive_first_finite_boundary_target_detects T.X k N c hk hN hc s t
    x y hd ex hex ε hε
  dsimp only [rawMaySourceDesuspend,actualNormalizedFirstFiniteBoundary]
  simp only [homotopyRegrade_comp,normalized_homotopy_regrade_trans,Category.assoc]
  rw [←model.quotients.functoriality.map_comp,
    ←model.quotients.functoriality.map_comp,positive_normalized_source_suspension]
  simpa [positiveSuspensionIso,homotopyRegrade_comp] using h

end
end KIP126.ProofTools.Internal.MahowaldLeibniz
