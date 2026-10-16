module
import all KIP126.Def.ProofTools.GeneralizedLeibniz.Boundary
import all KIP126.Def.ProofTools.GeneralizedLeibniz.Square

/-! Strict finite-quotient source division for the absolute-boundary crossing
comparison in AimPaper Proposition `prop:cross-dr-En`. Filtration above the
smaller quotient window kills restriction; exactness gives an actual λ lift.
The boundary formula uses the selected λ arrow, with its sphere evaluation
identified by finite no-return. It does not assert λ division for an arbitrary
normalized-map extension. -/

@[expose] section
namespace KIP126.ProofTools.Internal.Leibniz
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Standard
open KIP126.ProofTools.Internal.Mahowald
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

private theorem finite_source_division (X : ClassicalObject)
    (i q : ℕ) (hi : 0 < i) (hiq : i < q) (m w s : ℤ)
    (hs : (i : ℤ) ≤ m+s-w)
    (a : BiHom m w (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
    (ha : FiltrationAtLeast model.syntheticTower s a) :
    ∃ b : BiHom m w ((SyntheticCategory.biShift (0,-(i:ℤ))).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (q-i))),
      b ≫ ((model.quotients.tower _).triangle hi hiq).lambdaMap = a := by
  let A := model.nu.functor.obj (X.obj model.auxiliary)
  let T := (model.quotients.tower A).triangle hi hiq
  have harho : FiltrationAtLeast model.syntheticTower s (a ≫ T.rho) := by
    exact map_preserves_filtration (model.convergentMap
      (.quotient q (.nu X)) (.quotient i (.nu X)) T.rho) (m,w) s a ha
  have hz : a ≫ T.rho = 0 := finite_high_filtration_zero X i hi m w s hs _ harho
  obtain ⟨b,hb⟩ := (Triangle.mk T.lambdaMap T.rho T.delta).coyoneda_exact₂
    T.distinguished a hz
  exact ⟨b,hb.symm⟩


private theorem shifted_quotient_maps_equal_on_spheres
    (X Y : ClassicalObject) (i q : ℕ) (hiq : i < q)
    (a b : (SyntheticCategory.biShift (0,-(i:ℤ))).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (q-i)) ⟶
      XModLambdaN (model.nu.functor.obj (Y.obj model.auxiliary)) q)
    (hab : (SyntheticCategory.biShift (0,-(i:ℤ))).map (XModLambdaN.incl _ (q-i)) ≫ a =
      (SyntheticCategory.biShift (0,-(i:ℤ))).map (XModLambdaN.incl _ (q-i)) ≫ b)
    (m w : ℤ)
    (c : BiHom m w ((SyntheticCategory.biShift (0,-(i:ℤ))).obj
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (q-i)))) :
    c ≫ a = c ≫ b := by
  letI := model.exactness.shiftCommShift (0,-(i:ℤ))
  letI := model.exactness.shiftExact (0,-(i:ℤ))
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(i:ℤ))
  let V := model.nu.functor.obj (X.obj model.auxiliary)
  let T := XModLambdaN.cofiberTriangle V (q-i)
  have hzero : (F.mapTriangle.obj T).mor₂ ≫ (a-b) = 0 := by
    change F.map (XModLambdaN.incl V (q-i)) ≫ (a-b) = 0
    rw [Preadditive.comp_sub,hab,sub_self]
  obtain ⟨z,hz⟩ := Triangle.yoneda_exact₃ (F.mapTriangle.obj T)
    (F.map_distinguished T (XModLambdaN.cofiberTriangle_distinguished V (q-i))) (a-b) hzero
  let ε : (F.obj ((SyntheticCategory.biShift (0,-((q-i:ℕ):ℤ))).obj V))⟦(1:ℤ)⟧ ≅
      (SyntheticCategory.biShift (0,-(q:ℤ)-1)).obj
        (model.nu.functor.obj ((ClassicalObject.shift 1 X).obj model.auxiliary)) :=
    (shiftFunctor SyntheticSpectrum (1:ℤ)).mapIso
      ((lambdaShiftAddIso (q-i) i q (Nat.sub_add_cancel hiq.le)).app V) ≪≫
    (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).symm.app _ ≪≫
    (SyntheticCategory.biShift_comp (0,-(q:ℤ)) (1,0)).app V ≪≫
    eqToIso (congrArg (fun p => (SyntheticCategory.biShift p).obj V)
      (show (0,-(q:ℤ))+(1,0)=(1,1)+(0,-(q:ℤ)-1) by ext <;> simp)) ≪≫
    (SyntheticCategory.biShift_comp (1,1) (0,-(q:ℤ)-1)).symm.app V ≪≫
    (SyntheticCategory.biShift (0,-(q:ℤ)-1)).mapIso (model.nu.suspensionIso _).symm
  have h := negative_shift_nu_to_quotient_zero (.shift 1 X) Y q (by omega) m w
    ((c ≫ (F.mapTriangle.obj T).mor₃) ≫ ε.hom) (ε.inv ≫ z)
  have hcz : (c ≫ (F.mapTriangle.obj T).mor₃) ≫ z = 0 := by
    simpa only [Category.assoc,Iso.hom_inv_id_assoc] using h
  apply sub_eq_zero.mp
  rw [←Preadditive.comp_sub,hz,←Category.assoc]
  exact hcz

private theorem lambda_cofiber_map_exists (A : SyntheticSpectrum)
    (i q : ℕ) (hiq : i ≤ q) :
    let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(i:ℤ))
    letI := model.exactness.shiftCommShift (0,-(i:ℤ))
    ∃ c : F.obj (XModLambdaN A (q-i)) ⟶ XModLambdaN A q,
      F.map (XModLambdaN.incl A (q-i)) ≫ c = lambdaPow i A ≫ XModLambdaN.incl A q ∧
      c ≫ XModLambdaN.proj A q =
        F.map (XModLambdaN.proj A (q-i)) ≫ (F.commShiftIso (1:ℤ)).hom.app _ ≫
          (shiftFunctor SyntheticSpectrum (1:ℤ)).map
            ((lambdaShiftAddIso (q-i) i q (Nat.sub_add_cancel hiq)).hom.app A) := by
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(i:ℤ))
  letI := model.exactness.shiftCommShift (0,-(i:ℤ))
  letI := model.exactness.shiftExact (0,-(i:ℤ))
  let T := XModLambdaN.cofiberTriangle A (q-i)
  let U := XModLambdaN.cofiberTriangle A q
  have hs : F.map (lambdaPow (q-i) A) ≫ lambdaPow i A =
      (lambdaShiftAddIso (q-i) i q (Nat.sub_add_cancel hiq)).hom.app A ≫ lambdaPow q A :=
    (lambdaPow_add_comparison model.quotients.coherence (q-i) i q
      (Nat.sub_add_cancel hiq) A).symm
  obtain ⟨c,hc,hd⟩ := complete_distinguished_triangle_morphism
    (F.mapTriangle.obj T) U
    (F.map_distinguished T (XModLambdaN.cofiberTriangle_distinguished A (q-i)))
    (XModLambdaN.cofiberTriangle_distinguished A q)
    ((lambdaShiftAddIso (q-i) i q (Nat.sub_add_cancel hiq)).hom.app A) (lambdaPow i A) hs
  refine ⟨c,hc,?_⟩
  change (F.map (XModLambdaN.proj A (q-i)) ≫ (F.commShiftIso (1:ℤ)).hom.app _) ≫
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map
        ((lambdaShiftAddIso (q-i) i q (Nat.sub_add_cancel hiq)).hom.app A) =
    c ≫ XModLambdaN.proj A q at hd
  simpa only [Category.assoc] using hd.symm

private theorem lambda_proj_evaluation
    (X : ClassicalObject) (i q : ℕ) (hi : 0 < i) (hiq : i < q)
    (m w : ℤ) (b : BiHom m w ((SyntheticCategory.biShift (0,-(i:ℤ))).obj
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (q-i)))) :
    let A := model.nu.functor.obj (X.obj model.auxiliary)
    let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(i:ℤ))
    letI := model.exactness.shiftCommShift (0,-(i:ℤ))
    b ≫ ((model.quotients.tower A).triangle hi hiq).lambdaMap ≫ XModLambdaN.proj A q =
      b ≫ F.map (XModLambdaN.proj A (q-i)) ≫ (F.commShiftIso (1:ℤ)).hom.app _ ≫
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map
          ((lambdaShiftAddIso (q-i) i q (Nat.sub_add_cancel hiq.le)).hom.app A) := by
  letI := model.exactness.shiftCommShift (0,-(i:ℤ))
  let A := model.nu.functor.obj (X.obj model.auxiliary)
  let T := (model.quotients.tower A).triangle hi hiq
  obtain ⟨c,hc,hp⟩ := lambda_cofiber_map_exists A i q hiq.le
  have he := shifted_quotient_maps_equal_on_spheres X X i q hiq
    T.lambdaMap c (T.lambda_quotient.trans hc.symm) m w b
  change b ≫ T.lambdaMap ≫ XModLambdaN.proj A q = _
  rw [←Category.assoc,he,Category.assoc,hp]


private def boundaryDivisionIso (X : ClassicalObject) (i q : ℕ) (hiq : i ≤ q) :
    (SyntheticCategory.biShift (0,-(i:ℤ))).obj
      ((SyntheticCategory.biShift (1,-((q-i:ℕ):ℤ))).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) ≅
    (SyntheticCategory.biShift (1,-(q:ℤ))).obj
      (model.nu.functor.obj (X.obj model.auxiliary)) := by
  let A := model.nu.functor.obj (X.obj model.auxiliary)
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(i:ℤ))
  letI := model.exactness.shiftCommShift (0,-(i:ℤ))
  exact F.mapIso (biSuspensionIso ((q-i:ℕ):ℤ) A) ≪≫
    (F.commShiftIso (1:ℤ)).app _ ≪≫
    (shiftFunctor SyntheticSpectrum (1:ℤ)).mapIso
      ((lambdaShiftAddIso (q-i) i q (Nat.sub_add_cancel hiq)).app A) ≪≫
    (biSuspensionIso q A).symm

private theorem absolute_boundary_division_evaluation
    (X : ClassicalObject) (i q : ℕ) (hi : 0 < i) (hiq : i < q)
    (m w : ℤ) (b : BiHom m w ((SyntheticCategory.biShift (0,-(i:ℤ))).obj
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (q-i)))) :
    b ≫ ((model.quotients.tower _).triangle hi hiq).lambdaMap ≫
        absoluteBoundary (model.nu.functor.obj (X.obj model.auxiliary)) q =
      b ≫ (SyntheticCategory.biShift (0,-(i:ℤ))).map
        (absoluteBoundary (model.nu.functor.obj (X.obj model.auxiliary)) (q-i)) ≫
        (boundaryDivisionIso X i q hiq.le).hom := by
  letI := model.exactness.shiftCommShift (0,-(i:ℤ))
  have h := congrArg (fun z => z ≫
    (biSuspensionIso q (model.nu.functor.obj (X.obj model.auxiliary))).inv)
    (lambda_proj_evaluation X i q hi hiq m w b)
  simpa only [absoluteBoundary,boundaryDivisionIso,Iso.trans_hom,Functor.mapIso_hom,
    Iso.symm_hom,Functor.map_comp,Category.assoc,Iso.map_inv_hom_id_assoc,Iso.app_hom] using h


private theorem iso_filtration_iff (A B : SyntheticObject)
    (e : A.obj model.nu model.auxiliary ≅ B.obj model.nu model.auxiliary)
    (m w s : ℤ) (a : BiHom m w (A.obj model.nu model.auxiliary)) :
    FiltrationAtLeast model.syntheticTower s (a ≫ e.hom) ↔
      FiltrationAtLeast model.syntheticTower s a := by
  constructor
  · intro h
    have he := map_preserves_filtration (model.convergentMap B A e.inv)
      (m,w) s (a ≫ e.hom) h
    simpa only [FiltrationAtLeast,Category.assoc,e.hom_inv_id,Category.comp_id] using he
  · exact map_preserves_filtration (model.convergentMap A B e.hom) (m,w) s a

private theorem shift_filtration_iff (A : SyntheticObject) (δ p : ℤ × ℤ)
    (s : ℤ) (a : BiHom p.1 p.2 (A.obj model.nu model.auxiliary)) :
    FiltrationAtLeast model.syntheticTower s (shiftHomotopyClass δ p a) ↔
      FiltrationAtLeast model.syntheticTower s a := by
  let e := (essShift δ).filtered A p
  have forward {A B : SyntheticSpectrum} {p q : ℤ × ℤ}
      (e : FilteredPieceIso (model.syntheticTower.filtration A)
        (model.syntheticTower.filtration B) p q)
      (a : BiHom p.1 p.2 A) (ha : FiltrationAtLeast model.syntheticTower s a) :
      FiltrationAtLeast model.syntheticTower s (e.ambient.hom a) := by
    obtain ⟨ar,har⟩ := filtration_representative_exists model.syntheticTower A p s a ha
    have hh := ConcreteCategory.congr_hom (e.level_arrow s) ar
    have hm : e.ambient.hom a ∈ ModuleCat.subobjectModule _
        ((model.syntheticTower.filtration B).F s q) := by
      refine ⟨(e.level s).hom ar,?_⟩
      simpa only [ModuleCat.comp_apply,har] using hh
    simpa only [SyntheticTowerPresentation.filtration,OrderIso.apply_symm_apply,
      FiltrationAtLeast] using hm
  rw [←(essShift δ).ambient_eq A p a]
  constructor
  · intro ha
    have h := forward e.symm _ ha
    change FiltrationAtLeast model.syntheticTower s (e.ambient.inv (e.ambient.hom a)) at h
    have he : e.ambient.inv (e.ambient.hom a) = a :=
      ConcreteCategory.congr_hom e.ambient.hom_inv_id a
    rwa [he] at h
  · exact forward e a

private theorem divided_boundary_filtration_iff
    (X : ClassicalObject) (i q : ℕ) (hi : 0 < i) (hiq : i < q)
    (m w v : ℤ) (b : BiHom m w ((SyntheticCategory.biShift (0,-(i:ℤ))).obj
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (q-i)))) :
    FiltrationAtLeast model.syntheticTower v
      (b ≫ ((model.quotients.tower _).triangle hi hiq).lambdaMap ≫
        absoluteBoundary (model.nu.functor.obj (X.obj model.auxiliary)) q) ↔
    FiltrationAtLeast model.syntheticTower v
      (b ≫ (SyntheticCategory.biShift (0,-(i:ℤ))).map
        (absoluteBoundary (model.nu.functor.obj (X.obj model.auxiliary)) (q-i))) := by
  rw [absolute_boundary_division_evaluation X i q hi hiq m w b]
  simpa only [Category.assoc] using iso_filtration_iff
    (.shift (0,-(i:ℤ)) (.shift (1,-((q-i:ℕ):ℤ)) (.nu X)))
    (.shift (1,-(q:ℤ)) (.nu X)) (boundaryDivisionIso X i q hiq.le)
    m w v (b ≫ (SyntheticCategory.biShift (0,-(i:ℤ))).map
      (absoluteBoundary (model.nu.functor.obj (X.obj model.auxiliary)) (q-i)))

end
end KIP126.ProofTools.Internal.Leibniz
