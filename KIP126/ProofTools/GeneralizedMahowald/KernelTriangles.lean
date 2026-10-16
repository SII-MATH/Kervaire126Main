module
import all KIP126.ProofTools.GeneralizedMahowald.NoReturn
import all KIP126.ProofTools.GeneralizedMahowald.Coherence
/-! Proved successor quotient triangle comparisons, original Mahowald 1116–1420 (MIT). -/
@[expose] section
namespace KIP126.ProofTools.Internal.Mahowald
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
theorem successor_cofiber_map_exists (A : SyntheticSpectrum) (d : ℕ) :
    let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-1)
    letI := model.exactness.shiftCommShift (0,-1)
    ∃ c : F.obj (XModLambdaN A d) ⟶ XModLambdaN A (d+1),
      F.map (XModLambdaN.incl A d) ≫ c = lambdaPow 1 A ≫ XModLambdaN.incl A (d+1) ∧
      c ≫ XModLambdaN.proj A (d+1) =
        F.map (XModLambdaN.proj A d) ≫ (F.commShiftIso (1:ℤ)).hom.app _ ≫
          (shiftFunctor SyntheticSpectrum (1:ℤ)).map ((lambdaShiftAddIso d 1 (d+1) rfl).hom.app A) := by
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-1)
  letI := model.exactness.shiftCommShift (0,-1)
  letI := model.exactness.shiftExact (0,-1)
  let T := XModLambdaN.cofiberTriangle A d
  let U := XModLambdaN.cofiberTriangle A (d+1)
  have hs : F.map (lambdaPow d A) ≫ lambdaPow 1 A =
      (lambdaShiftAddIso d 1 (d+1) rfl).hom.app A ≫ lambdaPow (d+1) A :=
    (lambdaPow_add_comparison model.quotients.coherence d 1 (d+1) rfl A).symm
  obtain ⟨c,hc,hd⟩ := complete_distinguished_triangle_morphism
    (F.mapTriangle.obj T) U
    (F.map_distinguished T (XModLambdaN.cofiberTriangle_distinguished A d))
    (XModLambdaN.cofiberTriangle_distinguished A (d+1))
    ((lambdaShiftAddIso d 1 (d+1) rfl).hom.app A) (lambdaPow 1 A) hs
  refine ⟨c,hc,?_⟩
  change (F.map (XModLambdaN.proj A d) ≫ (F.commShiftIso (1:ℤ)).hom.app _) ≫
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map ((lambdaShiftAddIso d 1 (d+1) rfl).hom.app A) =
    c ≫ XModLambdaN.proj A (d+1) at hd
  simpa only [Category.assoc] using hd.symm

theorem successor_lambda_proj_evaluation 
    (X : ClassicalObject) (d : ℕ)
    (l : (SyntheticCategory.biShift (0,-1)).obj
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) d) ⟶
      XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (d+1))
    (hl : (SyntheticCategory.biShift (0,-1)).map
      (XModLambdaN.incl (model.nu.functor.obj (X.obj model.auxiliary)) d) ≫ l =
      lambdaPow 1 (model.nu.functor.obj (X.obj model.auxiliary)) ≫
        XModLambdaN.incl (model.nu.functor.obj (X.obj model.auxiliary)) (d+1))
    (m w : ℤ) (b : BiHom m w ((SyntheticCategory.biShift (0,-1)).obj
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) d))) :
    let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-1)
    letI := model.exactness.shiftCommShift (0,-1)
    b ≫ l ≫ XModLambdaN.proj (model.nu.functor.obj (X.obj model.auxiliary)) (d+1) =
      b ≫ F.map (XModLambdaN.proj (model.nu.functor.obj (X.obj model.auxiliary)) d) ≫
        (F.commShiftIso (1:ℤ)).hom.app _ ≫
          (shiftFunctor SyntheticSpectrum (1:ℤ)).map
            ((lambdaShiftAddIso d 1 (d+1) rfl).hom.app
              (model.nu.functor.obj (X.obj model.auxiliary))) := by
  letI := model.exactness.shiftCommShift (0,-1)
  obtain ⟨c,hc,hp⟩ := successor_cofiber_map_exists
    (model.nu.functor.obj (X.obj model.auxiliary)) d
  have he := shift_minus_one_quotient_maps_equal_on_spheres
    X X d l c (hl.trans hc.symm) m w b
  rw [←Category.assoc,he,Category.assoc,hp]

theorem selected_delta_evaluation_eq_cofiber
    (X : ClassicalObject)
    (i j : ℕ)
    (T : LambdaRhoDeltaTriangle (model.nu.functor.obj (X.obj model.auxiliary)) i j)
    (m w : ℤ)
    (a : BiHom m w (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) i)) :
    a ≫ T.delta = a ≫ XModLambdaN.proj (model.nu.functor.obj (X.obj model.auxiliary)) i ≫
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map
        ((SyntheticCategory.biShift (0,-(i:ℤ))).map
          (XModLambdaN.incl (model.nu.functor.obj (X.obj model.auxiliary)) (j-i))) := by
  let A := model.nu.functor.obj (X.obj model.auxiliary)
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
      quotient_nu_maps_equal_on_spheres X X i T.i_pos c (𝟙 _) hc' m w a
  change XModLambdaN.proj A i ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map
      ((SyntheticCategory.biShift (0,-(i:ℤ))).map (XModLambdaN.incl A (j-i))) =
    c ≫ T.delta at hδ
  calc
    a ≫ T.delta = (a ≫ c) ≫ T.delta := by rw [hac]
    _ = a ≫ XModLambdaN.proj A i ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map
        ((SyntheticCategory.biShift (0,-(i:ℤ))).map (XModLambdaN.incl A (j-i))) := by
      rw [Category.assoc,←hδ]

theorem shift_minus_one_preserves_sphere_evaluation {A B : SyntheticSpectrum}
    (f g : A ⟶ B)
    (h : ∀ (m w : ℤ) (a : BiHom m w A), a ≫ f = a ≫ g)
    (m w : ℤ) (b : BiHom m w ((SyntheticCategory.biShift (0,-1)).obj A)) :
    b ≫ (SyntheticCategory.biShift (0,-1)).map f =
      b ≫ (SyntheticCategory.biShift (0,-1)).map g := by
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-1)
  let e : F.obj (Smn m (w+1)) ≅ Smn m w :=
    (SyntheticCategory.biShift_comp (m,w+1) (0,-1)).app S_0_0 ≪≫
      eqToIso (congrArg (fun p => (SyntheticCategory.biShift p).obj (S_0_0 : SyntheticSpectrum))
        (show (m,w+1)+(0,-1)=(m,w) by ext <;> simp))
  let a : BiHom m (w+1) A :=
    (SyntheticCategory.biShift_fullyFaithful (0,-1)).preimage (e.hom ≫ b)
  have ha : F.map a = e.hom ≫ b :=
    (SyntheticCategory.biShift_fullyFaithful (0,-1)).map_preimage _
  apply (cancel_epi e.hom).mp
  change e.hom ≫ b ≫ F.map f = e.hom ≫ b ≫ F.map g
  rw [←Category.assoc,←ha,←Functor.map_comp,h,Functor.map_comp,ha,Category.assoc]

theorem successor_delta_lambda_evaluation 
    (X : ClassicalObject) (d q : ℕ)
    (hd : 0<d) (hq : 0<q) (m w : ℤ) :
    let A := model.nu.functor.obj (X.obj model.auxiliary)
    let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-1)
    letI := model.exactness.shiftCommShift (0,-1)
    let l : F.obj (XModLambdaN A d) ⟶ XModLambdaN A (d+1) := by
      simpa only [F,Nat.add_sub_cancel,Nat.cast_one] using
        ((model.quotients.tower A).triangle (by omega : 0<1) (by omega : 1<d+1)).lambdaMap
    let δ0 : XModLambdaN A d ⟶
        ((SyntheticCategory.biShift (0,-(d:ℤ))).obj (XModLambdaN A q))⟦(1:ℤ)⟧ := by
      simpa only [Nat.add_sub_cancel_left] using
        ((model.quotients.tower A).triangle hd (show d<d+q by omega)).delta
    let δ1 : XModLambdaN A (d+1) ⟶
        ((SyntheticCategory.biShift (0,-((d+1:ℕ):ℤ))).obj (XModLambdaN A q))⟦(1:ℤ)⟧ := by
      simpa only [Nat.add_sub_cancel_left] using
        ((model.quotients.tower A).triangle (by omega : 0<d+1)
          (show d+1<d+1+q by omega)).delta
    ∀ b : BiHom m w (F.obj (XModLambdaN A d)),
      b ≫ l ≫ δ1 = b ≫ F.map δ0 ≫ (F.commShiftIso (1:ℤ)).hom.app _ ≫
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map
          ((lambdaShiftAddIso d 1 (d+1) rfl).hom.app (XModLambdaN A q)) := by
  dsimp only
  intro b
  let A := model.nu.functor.obj (X.obj model.auxiliary)
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-1)
  let G := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(d:ℤ))
  let J := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-((d+1:ℕ):ℤ))
  letI := model.exactness.shiftCommShift (0,-1)
  let l : F.obj (XModLambdaN A d) ⟶ XModLambdaN A (d+1) := by
    simpa only [F,Nat.add_sub_cancel,Nat.cast_one] using
      ((model.quotients.tower A).triangle (by omega : 0<1) (by omega : 1<d+1)).lambdaMap
  let δ0 : XModLambdaN A d ⟶ (G.obj (XModLambdaN A q))⟦(1:ℤ)⟧ := by
    simpa only [Nat.add_sub_cancel_left] using
      ((model.quotients.tower A).triangle hd (show d<d+q by omega)).delta
  let δ1 : XModLambdaN A (d+1) ⟶ (J.obj (XModLambdaN A q))⟦(1:ℤ)⟧ := by
    simpa only [Nat.add_sub_cancel_left] using
      ((model.quotients.tower A).triangle (by omega : 0<d+1)
        (show d+1<d+1+q by omega)).delta
  have source_transport {S T : SyntheticSpectrum} (Q : ℕ → SyntheticSpectrum) (f : ∀ k, S ⟶ Q k)
      {k k' : ℕ} (h : k=k') (g : Q k ⟶ T) (v : S ⟶ T)
      (hv : f k ≫ g = v) :
      f k' ≫ Eq.mp (congrArg (fun j => Q j ⟶ T) h) g = v := by
    subst k'; exact hv
  have target_transport {S T : SyntheticSpectrum} (Q : ℕ → SyntheticSpectrum) (a : S ⟶ T)
      {k k' : ℕ} (h : k=k') (g : T ⟶ Q k) (v : ∀ j, S ⟶ Q j)
      (hv : a ≫ g = v k) :
      a ≫ Eq.mp (congrArg (fun j => T ⟶ Q j) h) g = v k' := by
    subst k'; exact hv
  have hl : F.map (XModLambdaN.incl A d) ≫ l =
      lambdaPow 1 A ≫ XModLambdaN.incl A (d+1) := by
    exact source_transport (fun k => F.obj (XModLambdaN A k))
      (fun k => F.map (XModLambdaN.incl A k)) (Nat.add_sub_cancel d 1)
      ((model.quotients.tower A).triangle (by omega : 0<1) (by omega : 1<d+1)).lambdaMap _
      ((model.quotients.tower A).triangle (by omega : 0<1) (by omega : 1<d+1)).lambda_quotient
  have hδ0 : ∀ (m' w' : ℤ) (a : BiHom m' w' (XModLambdaN A d)),
      a ≫ δ0 = a ≫ XModLambdaN.proj A d ≫
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map (G.map (XModLambdaN.incl A q)) := by
    intro m' w' a
    exact target_transport (fun k => (G.obj (XModLambdaN A k))⟦(1:ℤ)⟧) a
      (Nat.add_sub_cancel_left d q)
      ((model.quotients.tower A).triangle hd (show d<d+q by omega)).delta
      (fun k => a ≫ XModLambdaN.proj A d ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map (G.map (XModLambdaN.incl A k)))
      (selected_delta_evaluation_eq_cofiber X d (d+q)
        ((model.quotients.tower A).triangle hd (show d<d+q by omega)) m' w' a)
  have hδ1 : (b ≫ l) ≫ δ1 = (b ≫ l) ≫ XModLambdaN.proj A (d+1) ≫
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (J.map (XModLambdaN.incl A q)) := by
    exact target_transport (fun k => (J.obj (XModLambdaN A k))⟦(1:ℤ)⟧) (b ≫ l)
      (Nat.add_sub_cancel_left (d+1) q)
      ((model.quotients.tower A).triangle (by omega : 0<d+1) (show d+1<d+1+q by omega)).delta
      (fun k => (b ≫ l) ≫ XModLambdaN.proj A (d+1) ≫
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map (J.map (XModLambdaN.incl A k)))
      (selected_delta_evaluation_eq_cofiber X (d+1) (d+1+q)
        ((model.quotients.tower A).triangle (by omega : 0<d+1)
          (show d+1<d+1+q by omega)) m w (b ≫ l))
  have hp := successor_lambda_proj_evaluation X d l hl m w b
  have heval := shift_minus_one_preserves_sphere_evaluation δ0
    (XModLambdaN.proj A d ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map (G.map (XModLambdaN.incl A q)))
    hδ0 m w b
  have hκ := (lambdaShiftAddIso d 1 (d+1) rfl).hom.naturality (XModLambdaN.incl A q)
  change F.map (G.map (XModLambdaN.incl A q)) ≫
      (lambdaShiftAddIso d 1 (d+1) rfl).hom.app (XModLambdaN A q) =
    (lambdaShiftAddIso d 1 (d+1) rfl).hom.app A ≫ J.map (XModLambdaN.incl A q) at hκ
  change b ≫ l ≫ δ1 = b ≫ F.map δ0 ≫ (F.commShiftIso (1:ℤ)).hom.app _ ≫ _
  calc
    _ = (b ≫ l ≫ XModLambdaN.proj A (d+1)) ≫
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map (J.map (XModLambdaN.incl A q)) := by
      simpa only [Category.assoc] using hδ1
    _ = (b ≫ F.map (XModLambdaN.proj A d) ≫ (F.commShiftIso (1:ℤ)).hom.app _ ≫
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map ((lambdaShiftAddIso d 1 (d+1) rfl).hom.app A)) ≫
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map (J.map (XModLambdaN.incl A q)) :=
      congrArg (fun z => z ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map
        (J.map (XModLambdaN.incl A q))) hp
    _ = b ≫ F.map δ0 ≫ (F.commShiftIso (1:ℤ)).hom.app _ ≫
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map
          ((lambdaShiftAddIso d 1 (d+1) rfl).hom.app (XModLambdaN A q)) := by
      simp only [Category.assoc]
      rw [←Functor.map_comp,hκ.symm,Functor.map_comp]
      rw [←Functor.commShiftIso_hom_naturality_assoc]
      rw [←Functor.map_comp_assoc,←Category.assoc b,←heval]
      simp only [Category.assoc,F]

theorem successor_shifted_delta_preimage
    [(SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-1)).CommShift ℤ]
    [(SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-1)).IsTriangulated]
    {A : SyntheticSpectrum} (d r : ℕ) (T : LambdaRhoDeltaTriangle A d r)
    (n w : ℤ)
    (c : BiHom (n-1) (w+((d+1:ℕ):ℤ)) (XModLambdaN A (r-d)))
    (hc : (SyntheticCategory.biShift (0,-(d:ℤ))).map c ≫ T.lambdaMap = 0) :
    ∃ a : BiHom n w ((SyntheticCategory.biShift (0,-1)).obj (XModLambdaN A d)),
      a ≫ (SyntheticCategory.biShift (0,-1)).map T.delta ≫
        ((SyntheticCategory.biShift (0,-1)).commShiftIso (1:ℤ)).hom.app _ ≫
          (shiftFunctor SyntheticSpectrum (1:ℤ)).map
            ((lambdaShiftAddIso d 1 (d+1) rfl).hom.app (XModLambdaN A (r-d))) =
        (biSuspensionHomEquiv n w ((d+1:ℕ):ℤ) (XModLambdaN A (r-d))).symm c := by
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-1)
  let Q := XModLambdaN A (r-d)
  let κ : SyntheticCategory.biShift (0,-(d:ℤ)) ⋙ F ≅
      SyntheticCategory.biShift (0,-((d+1:ℕ):ℤ)) :=
    lambdaShiftAddIso (Syn:=SyntheticSpectrum) d 1 (d+1) rfl
  let ε : F.obj (((SyntheticCategory.biShift (0,-(d:ℤ))).obj Q)⟦(1:ℤ)⟧) ≅
      ((SyntheticCategory.biShift (0,-((d+1:ℕ):ℤ))).obj Q)⟦(1:ℤ)⟧ :=
    (F.commShiftIso (1:ℤ)).app _ ≪≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).mapIso (κ.app Q)
  let b := (biSuspensionHomEquiv n w ((d+1:ℕ):ℤ) Q).symm c
  have hc' : (SyntheticCategory.biShift (0,-((d+1:ℕ):ℤ))).map c ≫
      κ.inv.app Q ≫ F.map T.lambdaMap = 0 := by
    rw [←Category.assoc,κ.inv.naturality c,Category.assoc]
    change κ.inv.app (Smn (n-1) (w+((d+1:ℕ):ℤ))) ≫
      F.map ((SyntheticCategory.biShift (0,-(d:ℤ))).map c) ≫ F.map T.lambdaMap = 0
    rw [←Functor.map_comp,hc,Functor.map_zero,comp_zero]
  have hb : b ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map (κ.inv.app Q ≫ F.map T.lambdaMap) = 0 :=
    (shifted_representative_zero_iff n w ((d+1:ℕ):ℤ) Q _
      (κ.inv.app Q ≫ F.map T.lambdaMap) c).mpr hc'
  have hb' : (b ≫ ε.inv) ≫ F.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map T.lambdaMap) = 0 := by
    change (b ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map (κ.inv.app Q) ≫
      (F.commShiftIso (1:ℤ)).inv.app _) ≫ F.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map T.lambdaMap) = 0
    rw [Category.assoc,Category.assoc,←F.commShiftIso_inv_naturality T.lambdaMap (1:ℤ)]
    rw [←Category.assoc ((shiftFunctor SyntheticSpectrum (1:ℤ)).map (κ.inv.app Q)),←Functor.map_comp]
    rw [←Category.assoc,hb,zero_comp]
  let U := F.mapTriangle.obj (CategoryTheory.Pretriangulated.Triangle.mk T.lambdaMap T.rho T.delta)
  have hU : U ∈ distTriang SyntheticSpectrum :=
    F.map_distinguished _ T.distinguished
  have hb'' : (b ≫ ε.inv) ≫ (F.commShiftIso (1:ℤ)).hom.app _ ≫
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (F.map T.lambdaMap) = 0 := by
    rw [←F.commShiftIso_hom_naturality T.lambdaMap (1:ℤ),←Category.assoc,hb',zero_comp]
  have hz : ((b ≫ ε.inv) ≫ (F.commShiftIso (1:ℤ)).hom.app _) ≫ U.rotate.mor₃ = 0 := by
    change ((b ≫ ε.inv) ≫ (F.commShiftIso (1:ℤ)).hom.app _) ≫
      (-((shiftFunctor SyntheticSpectrum (1:ℤ)).map (F.map T.lambdaMap))) = 0
    rw [Preadditive.comp_neg,Category.assoc,hb'',neg_zero]
  obtain ⟨a,ha⟩ := U.rotate.coyoneda_exact₃
    (CategoryTheory.Pretriangulated.rot_of_distTriang U hU) _ hz
  change (b ≫ ε.inv) ≫ (F.commShiftIso (1:ℤ)).hom.app _ =
    a ≫ (F.map T.delta ≫ (F.commShiftIso (1:ℤ)).hom.app _) at ha
  have ha' : a ≫ F.map T.delta = b ≫ ε.inv := by
    apply (cancel_mono ((F.commShiftIso (1:ℤ)).hom.app _)).mp
    simpa only [Category.assoc] using ha.symm
  refine ⟨a,?_⟩
  change a ≫ F.map T.delta ≫ ε.hom = b
  rw [←Category.assoc,ha',Category.assoc,ε.inv_hom_id,Category.comp_id]
theorem successor_shifted_delta_preimage_reindex
    [(SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-1)).CommShift ℤ]
    [(SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-1)).IsTriangulated]
    {A : SyntheticSpectrum} (d r q : ℕ) (hq : r-d=q) (T : LambdaRhoDeltaTriangle A d r)
    (n w : ℤ)
    (c : BiHom (n-1) (w+((d+1:ℕ):ℤ)) (XModLambdaN A q))
    (hc : (SyntheticCategory.biShift (0,-(d:ℤ))).map c ≫
      Eq.mp (congrArg (fun j => (SyntheticCategory.biShift (0,-(d:ℤ))).obj
        (XModLambdaN A j) ⟶ XModLambdaN A r) hq) T.lambdaMap = 0) :
    ∃ a : BiHom n w ((SyntheticCategory.biShift (0,-1)).obj (XModLambdaN A d)),
      a ≫ (SyntheticCategory.biShift (0,-1)).map
        (Eq.mp (congrArg (fun j => XModLambdaN A d ⟶
          ((SyntheticCategory.biShift (0,-(d:ℤ))).obj (XModLambdaN A j))⟦(1:ℤ)⟧) hq) T.delta) ≫
        ((SyntheticCategory.biShift (0,-1)).commShiftIso (1:ℤ)).hom.app _ ≫
          (shiftFunctor SyntheticSpectrum (1:ℤ)).map
            ((lambdaShiftAddIso d 1 (d+1) rfl).hom.app (XModLambdaN A q)) =
        (biSuspensionHomEquiv n w ((d+1:ℕ):ℤ) (XModLambdaN A q)).symm c := by
  subst q
  exact successor_shifted_delta_preimage d r T n w c hc

end
end KIP126.ProofTools.Internal.Mahowald
