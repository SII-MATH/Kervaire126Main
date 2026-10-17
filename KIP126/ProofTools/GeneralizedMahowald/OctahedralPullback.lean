module
import all KIP126.ProofTools.GeneralizedMahowald.Geometry
import all KIP126.ProofTools.GeneralizedMahowald.NoReturn
import all KIP126.ProofTools.StretchingRepresentatives
import all KIP126.ProofTools.GeneralizedMahowald.CofiberIdentification

/-! An intermediate common representative for the two prescribed images in
AimPaper Theorem 6.12 (lines 1875–1917). The actual finite quotient triangle
and a chosen octahedron produce one lift with both images fixed in advance.
The comparison into the fixed final quotient preserves the first restriction
equation on every sphere representative. Its second image factors through a
fixed map K evaluated on the prescribed second input. Identifying K with the
required lambda transition, including its sign, remains a separate step. -/

@[expose] section
namespace KIP126.ProofTools.Internal.Mahowald
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.AdamsSynthetic
open KIP126.Synthetic.SpectralSequence KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Standard
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2000000

/- The final face of an octahedron is a homotopy pullback on represented
Hom groups. The correction uses the same octahedron, not an arbitrary
second preimage. -/
private theorem octahedron_common_lift
    {A B C D E V S : SyntheticSpectrum}
    {u : A ⟶ B} {l : B ⟶ C} {f : A ⟶ C} {hcomp : u≫l=f}
    {j : B ⟶ D} {h : D ⟶ A⟦(1:ℤ)⟧}
    {rho : C ⟶ E} {delta : E ⟶ B⟦(1:ℤ)⟧}
    {incl : C ⟶ V} {proj : V ⟶ A⟦(1:ℤ)⟧}
    {hU : Triangle.mk u j h ∈ distTriang SyntheticSpectrum}
    {hL : Triangle.mk l rho delta ∈ distTriang SyntheticSpectrum}
    {hF : Triangle.mk f incl proj ∈ distTriang SyntheticSpectrum}
    (O : Triangulated.Octahedron hcomp hU hL hF)
    (a : S ⟶ E) (b : S ⟶ A⟦(1:ℤ)⟧)
    (hab : a≫delta=b≫(shiftFunctor SyntheticSpectrum (1:ℤ)).map u) :
    ∃ v : S ⟶ V, v≫O.m₃=a ∧ v≫proj=b := by
  have huj : u ≫ j = 0 := comp_distTriang_mor_zero₁₂ _ hU
  have haz : a ≫ (delta ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map j)=0 := by
    rw [←Category.assoc,hab,Category.assoc,←Functor.map_comp,
      huj,Functor.map_zero,comp_zero]
  obtain ⟨v0,hv0⟩ := O.triangle.coyoneda_exact₃ O.mem a haz
  change S ⟶ V at v0
  change a = v0 ≫ O.m₃ at hv0
  let e := b-v0≫proj
  have he : e ≫ (-((shiftFunctor SyntheticSpectrum (1:ℤ)).map u))=0 := by
    simp only [e,Preadditive.comp_neg,Preadditive.sub_comp,Category.assoc,O.comm₄]
    rw [←Category.assoc,←hv0,←hab,sub_self,neg_zero]
  obtain ⟨c,hc⟩ := (Triangle.mk u j h).rotate.coyoneda_exact₃
    (rot_of_distTriang _ hU) e he
  change S ⟶ D at c
  change e=c≫h at hc
  have hzero : O.m₁ ≫ O.m₃ = 0 := comp_distTriang_mor_zero₁₂ _ O.mem
  refine ⟨v0+c≫O.m₁,?_,?_⟩
  · rw [Preadditive.add_comp,Category.assoc,
      hzero,comp_zero,add_zero]
    exact hv0.symm
  · rw [Preadditive.add_comp,Category.assoc,O.comm₂,←hc]
    dsimp only [e]
    abel

/- Actual finite quotient instance. V uses only Q_q(G), lambda_i and the
chosen cofiber; its pair of output maps is fixed before a and b are chosen. -/
private theorem finite_quotient_octahedral_pullback {A B : SyntheticSpectrum}
    (G : A ⟶ B) (i q : ℕ) (hi : 0 < i) (hq : 0 < q) :
    let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(i:ℤ))
    let L := (model.quotients.tower B).triangle hi (show i < i+q by omega)
    let u := F.map (XModLambdaN.map G (i+q-i))
    let V := HasFunctorialCofiber.cofib (u≫L.lambdaMap)
    ∃ p : V ⟶ XModLambdaN B i,
      HasFunctorialCofiber.cofibι (u≫L.lambdaMap) ≫ p=L.rho ∧
      HasFunctorialCofiber.cofibδ (u≫L.lambdaMap) ≫
          (shiftFunctor SyntheticSpectrum (1:ℤ)).map u=p≫L.delta ∧
      ∀ {S : SyntheticSpectrum} (a : S ⟶ XModLambdaN B i)
        (b : S ⟶ (F.obj (XModLambdaN A (i+q-i)))⟦(1:ℤ)⟧),
        a≫L.delta=b≫(shiftFunctor SyntheticSpectrum (1:ℤ)).map u →
        ∃ v : S ⟶ V,
          v≫p=a ∧ v≫HasFunctorialCofiber.cofibδ (u≫L.lambdaMap)=b := by
  dsimp only
  letI := model.exactness.syntheticTriangulated
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(i:ℤ))
  let L := (model.quotients.tower B).triangle hi (show i < i+q by omega)
  let u := F.map (XModLambdaN.map G (i+q-i))
  let O := Triangulated.someOctahedron rfl
    (HasFunctorialCofiber.cofib_distinguished u) L.distinguished
    (HasFunctorialCofiber.cofib_distinguished (u≫L.lambdaMap))
  refine ⟨O.m₃,O.comm₃,O.comm₄,?_⟩
  intro S a b hab
  exact octahedron_common_lift O a b hab


private theorem finite_quotient_octahedral_pullback_desuspended {A B : SyntheticSpectrum}
    (G : A ⟶ B) (i q : ℕ) (hi : 0 < i) (hq : 0 < q) (m w : ℤ)
    (a : BiHom m w (XModLambdaN B i))
    (b : BiHom (m-1) (w+i) (XModLambdaN A q))
    (hab : b ≫ XModLambdaN.map G q =
      biSuspensionHomEquiv m w i (XModLambdaN B q)
        (by simpa only [Nat.add_sub_cancel_left] using
          a ≫ ((model.quotients.tower B).triangle hi (show i < i+q by omega)).delta)) :
    let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(i:ℤ))
    let L := (model.quotients.tower B).triangle hi (show i < i+q by omega)
    let u := F.map (XModLambdaN.map G (i+q-i))
    let V := HasFunctorialCofiber.cofib (u≫L.lambdaMap)
    ∃ (p : V ⟶ XModLambdaN B i) (v : BiHom m w V),
      HasFunctorialCofiber.cofibι (u≫L.lambdaMap) ≫ p = L.rho ∧
      v ≫ p = a ∧
      biSuspensionHomEquiv m w i (XModLambdaN A q)
        (by simpa only [Nat.add_sub_cancel_left] using
          v ≫ HasFunctorialCofiber.cofibδ (u≫L.lambdaMap)) = b := by
  dsimp only
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(i:ℤ))
  let L := (model.quotients.tower B).triangle hi (show i < i+q by omega)
  let u := F.map (XModLambdaN.map G (i+q-i))
  let b' : BiHom m w ((F.obj (XModLambdaN A (i+q-i)))⟦(1:ℤ)⟧) := by
    simpa only [Nat.add_sub_cancel_left] using
      (biSuspensionHomEquiv m w i (XModLambdaN A q)).symm b
  have source_compare (d : ℕ) (hd : d=q)
      (δ : BiHom m w ((F.obj (XModLambdaN B d))⟦(1:ℤ)⟧)) :
      biSuspensionHomEquiv m w i (XModLambdaN B q)
        (by simpa only [hd] using δ) = b ≫ XModLambdaN.map G q →
      δ = (by simpa only [hd] using
          (biSuspensionHomEquiv m w i (XModLambdaN A q)).symm b) ≫
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map (F.map (XModLambdaN.map G d)) := by
    subst d
    intro hδ
    apply (biSuspensionHomEquiv m w i (XModLambdaN B q)).injective
    rw [bi_susp_natural model.quotients.coherence]
    change (biSuspensionHomEquiv m w i (XModLambdaN B q)) δ =
      (biSuspensionHomEquiv m w i (XModLambdaN A q))
        ((biSuspensionHomEquiv m w i (XModLambdaN A q)).symm b) ≫ XModLambdaN.map G q
    rw [AddEquiv.apply_symm_apply]
    exact hδ
  have hab' : a≫L.delta=b'≫(shiftFunctor SyntheticSpectrum (1:ℤ)).map u :=
    source_compare (i+q-i) (by omega) (a≫L.delta) hab.symm
  obtain ⟨p,hp,_,h⟩ := finite_quotient_octahedral_pullback G i q hi hq
  obtain ⟨v,hvp,hvb⟩ := h a b' hab'
  refine ⟨p,v,hp,hvp,?_⟩
  have cast_boundary (d : ℕ) (hd : d=q)
      (δ : BiHom m w ((F.obj (XModLambdaN A d))⟦(1:ℤ)⟧))
      (hδ : δ = (by simpa only [hd] using
        (biSuspensionHomEquiv m w i (XModLambdaN A q)).symm b)) :
      biSuspensionHomEquiv m w i (XModLambdaN A q)
        (by simpa only [hd] using δ)=b := by
    subst d
    change (biSuspensionHomEquiv m w i (XModLambdaN A q)) δ = b
    change δ = (biSuspensionHomEquiv m w i (XModLambdaN A q)).symm b at hδ
    rw [hδ,AddEquiv.apply_symm_apply]
  exact cast_boundary (i+q-i) (by omega) _ hvb


private theorem finite_quotient_octahedral_comparison
    {A B C D : SyntheticSpectrum} (G : A ⟶ B) (j : B ⟶ C) (h : C ⟶ D)
    (hGj : G≫j=0) (hjh : j≫h=0)
    (i q : ℕ) (hi : 0 < i) (hq : 0 < q) :
    let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(i:ℤ))
    let L := (model.quotients.tower B).triangle hi (show i < i+q by omega)
    let u := F.map (XModLambdaN.map G (i+q-i))
    let f := u≫L.lambdaMap
    let V := HasFunctorialCofiber.cofib f
    ∀ p : V ⟶ XModLambdaN B i,
      HasFunctorialCofiber.cofibι f≫p=L.rho →
      ∃ (φ : V ⟶ XModLambdaN C (i+q))
        (K : (F.obj (XModLambdaN A (i+q-i)))⟦(1:ℤ)⟧ ⟶ XModLambdaN D (i+q))
        (z : (F.obj (XModLambdaN A (i+q-i)))⟦(1:ℤ)⟧ ⟶ XModLambdaN C i),
        HasFunctorialCofiber.cofibι f≫φ=XModLambdaN.map j (i+q) ∧
        HasFunctorialCofiber.cofibδ f≫K=φ≫XModLambdaN.map h (i+q) ∧
        φ≫(model.quotients.tower C).rho i (i+q) (by omega) -
          p≫XModLambdaN.map j i = HasFunctorialCofiber.cofibδ f≫z := by
  dsimp only
  intro p hp
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(i:ℤ))
  let L := (model.quotients.tower B).triangle hi (show i < i+q by omega)
  let u := F.map (XModLambdaN.map G (i+q-i))
  let f := u≫L.lambdaMap
  let T := Triangle.mk f (HasFunctorialCofiber.cofibι f) (HasFunctorialCofiber.cofibδ f)
  have hT := HasFunctorialCofiber.cofib_distinguished f
  have hzero : f≫XModLambdaN.map j (i+q)=0 := by
    dsimp only [f,u,F]
    rw [(model.quotients.natural G).lambda_naturality hi (show i < i+q by omega),
      Category.assoc,quotient_map_comp_zero G j hGj,comp_zero]
  obtain ⟨φ,hφ⟩ := T.yoneda_exact₂ hT (XModLambdaN.map j (i+q)) hzero
  change HasFunctorialCofiber.cofib f ⟶ XModLambdaN C (i+q) at φ
  change XModLambdaN.map j (i+q)=HasFunctorialCofiber.cofibι f≫φ at hφ
  have hz₂ : HasFunctorialCofiber.cofibι f≫(φ≫XModLambdaN.map h (i+q))=0 := by
    rw [←Category.assoc,←hφ,quotient_map_comp_zero j h hjh]
  obtain ⟨K,hK⟩ := T.yoneda_exact₃ hT (φ≫XModLambdaN.map h (i+q)) hz₂
  change φ≫XModLambdaN.map h (i+q)=HasFunctorialCofiber.cofibδ f≫K at hK
  have hz₃ : HasFunctorialCofiber.cofibι f≫
      (φ≫(model.quotients.tower C).rho i (i+q) (by omega)-p≫XModLambdaN.map j i)=0 := by
    rw [Preadditive.comp_sub,←Category.assoc,←hφ,←Category.assoc,hp,
      (model.quotients.tower B).triangle_rho hi (show i < i+q by omega),
      (model.quotients.natural j).rho_naturality,sub_self]
  obtain ⟨z,hz⟩ := T.yoneda_exact₃ hT _ hz₃
  exact ⟨φ,K,z,hφ.symm,hK.symm,hz⟩

private theorem shifted_finite_no_return (X Y : ClassicalObject)
    (q i : ℕ) (hq : 0 < q) (hi : 0 < i) (δ ε : ℤ×ℤ)
    (hgap : (i:ℤ)≤δ.1-δ.2-(ε.1-ε.2)) (m w : ℤ)
    (c : BiHom m w ((SyntheticCategory.biShift δ).obj
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q)))
    (z : (SyntheticCategory.biShift δ).obj
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q) ⟶
      (SyntheticCategory.biShift ε).obj
        (XModLambdaN (model.nu.functor.obj (Y.obj model.auxiliary)) i)) : c≫z=0 := by
  let A : SyntheticObject := .shift δ (.quotient q (.nu X))
  let B : SyntheticObject := .shift ε (.quotient i (.nu Y))
  let L : ℤ := w-m+δ.1-δ.2
  have hzA (k : ℤ) (hk : k < L) :
      IsZero (((model.family.obj (A.obj model.nu model.auxiliary)).sequence.ssData (k,m+k,w)).eInfty) := by
    have hz := finite_infinity_zero_outside X q hq k (m-δ.1+k) (w-δ.2)
      (by dsimp [L] at hk; omega)
    let e := towerInfinityIso (model.convergence (.quotient q (.nu X)))
      (model.convergence A) ((essShift δ).filtered (.quotient q (.nu X)) (m-δ.1,w-δ.2)) k
    have he := hz.of_iso e.symm
    simpa only [e,A,Prod.fst_add,Prod.snd_add,sub_add_cancel] using he
  have hc0 := filtration_at_zero model.syntheticTower _ m w c
  have hcL : FiltrationAtLeast model.syntheticTower L c := by
    by_cases hL : L≤0
    · exact model.syntheticTower.filtrationSubmodule_antitone _ (m,w) hL hc0
    · exact (filtration_iff_of_infinity_zero (model.convergence A) 0 L m w
        (by omega) (fun k _ hk => hzA k hk) c).mp hc0
  have hcz : FiltrationAtLeast model.syntheticTower L (c≫z) :=
    map_preserves_filtration (model.convergentMap A B z) (m,w) L c hcL
  have hzB (k : ℤ) (hk : L≤k) :
      IsZero (((model.family.obj (B.obj model.nu model.auxiliary)).sequence.ssData (k,m+k,w)).eInfty) := by
    have hz := finite_infinity_zero_outside Y i hi k (m-ε.1+k) (w-ε.2)
      (by dsimp [L] at hk; omega)
    let e := towerInfinityIso (model.convergence (.quotient i (.nu Y)))
      (model.convergence B) ((essShift ε).filtered (.quotient i (.nu Y)) (m-ε.1,w-ε.2)) k
    have he := hz.of_iso e.symm
    simpa only [e,B,Prod.fst_add,Prod.snd_add,sub_add_cancel] using he
  apply shifted_quotient_homotopy_separated (.nu Y) i ε m w (c≫z)
  intro k
  by_cases hk : L≤(k:ℤ)
  · exact (filtration_iff_of_infinity_zero (model.convergence B) L k m w hk
      (fun j hj _ => hzB j hj) (c≫z)).mp hcz
  · exact model.syntheticTower.filtrationSubmodule_antitone _ (m,w) (by omega) hcz

private theorem normalized_finite_no_return (X Y : ClassicalObject)
    (C : SyntheticSpectrum) (ef eg : ℤ) (hef : 0 ≤ ef)
    (eC : C ≅ (SyntheticCategory.biShift (1,ef+eg)).obj
      (model.nu.functor.obj (X.obj model.auxiliary)))
    (q i : ℕ) (hq : 0 < q) (hi : 0 < i) (m w : ℤ)
    (c : BiHom m w (((SyntheticCategory.biShift (0,-(i:ℤ))).obj
      (XModLambdaN ((SyntheticCategory.biShift (0,eg)).obj
        (model.nu.functor.obj (Y.obj model.auxiliary))) q))⟦(1:ℤ)⟧))
    (z : (((SyntheticCategory.biShift (0,-(i:ℤ))).obj
      (XModLambdaN ((SyntheticCategory.biShift (0,eg)).obj
        (model.nu.functor.obj (Y.obj model.auxiliary))) q))⟦(1:ℤ)⟧) ⟶
      XModLambdaN C i) : c≫z=0 := by
  let Yν := model.nu.functor.obj (Y.obj model.auxiliary)
  let Xν := model.nu.functor.obj (X.obj model.auxiliary)
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(i:ℤ))
  letI := model.exactness.shiftCommShift (0,eg)
  letI := model.exactness.shiftExact (0,eg)
  obtain ⟨eY,_,_⟩ := quotient_shift_exists model.quotients.coherence (0,eg) q Yν
  letI := model.exactness.shiftCommShift (1,ef+eg)
  letI := model.exactness.shiftExact (1,ef+eg)
  obtain ⟨eX,_,_⟩ := quotient_shift_exists model.quotients.coherence (1,ef+eg) i Xν
  let eA : (F.obj (XModLambdaN ((SyntheticCategory.biShift (0,eg)).obj Yν) q))⟦(1:ℤ)⟧ ≅
      (SyntheticCategory.biShift (1,eg-i)).obj (XModLambdaN Yν q) :=
    (shiftFunctor SyntheticSpectrum (1:ℤ)).mapIso (F.mapIso eY) ≪≫
      (shiftFunctor SyntheticSpectrum (1:ℤ)).mapIso
        ((biShiftAddIso (0,eg) (0,-(i:ℤ)) (0,eg-i) (by ext <;> simp [sub_eq_add_neg])).app _) ≪≫
      (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).symm.app _ ≪≫
      (biShiftAddIso (0,eg-i) (1,0) (1,eg-i) (by ext <;> simp)).app _
  have hz := shifted_finite_no_return Y X q i hq hi (1,eg-i) (1,ef+eg)
    (by dsimp; omega) m w (c≫eA.hom)
    (eA.inv≫z≫XModLambdaN.map eC.hom i≫eX.hom)
  have hz' := congrArg (fun a => a≫eX.inv≫XModLambdaN.map eC.inv i) hz
  simpa only [Category.assoc,Iso.hom_inv_id_assoc,Iso.inv_hom_id_assoc,
    ← model.quotients.functoriality.map_comp,Iso.hom_inv_id,
    model.quotients.functoriality.map_id,Category.comp_id,zero_comp] using hz'

private theorem normalized_octahedral_comparison (X Y : ClassicalObject)
    (B C D : SyntheticSpectrum) (ef eg : ℤ) (hef : 0 ≤ ef)
    (eC : C ≅ (SyntheticCategory.biShift (1,ef+eg)).obj
      (model.nu.functor.obj (X.obj model.auxiliary)))
    (G : (SyntheticCategory.biShift (0,eg)).obj
      (model.nu.functor.obj (Y.obj model.auxiliary)) ⟶ B)
    (j : B ⟶ C) (h : C ⟶ D) (hGj : G≫j=0) (hjh : j≫h=0)
    (i q : ℕ) (hi : 0 < i) (hq : 0 < q) :
    let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(i:ℤ))
    let L := (model.quotients.tower B).triangle hi (show i < i+q by omega)
    let u := F.map (XModLambdaN.map G (i+q-i))
    let f := u≫L.lambdaMap
    let V := HasFunctorialCofiber.cofib f
    ∀ p : V ⟶ XModLambdaN B i,
      HasFunctorialCofiber.cofibι f≫p=L.rho →
      ∃ (φ : V ⟶ XModLambdaN C (i+q))
        (K : (F.obj (XModLambdaN ((SyntheticCategory.biShift (0,eg)).obj
          (model.nu.functor.obj (Y.obj model.auxiliary))) (i+q-i)))⟦(1:ℤ)⟧ ⟶
            XModLambdaN D (i+q)),
        HasFunctorialCofiber.cofibι f≫φ=XModLambdaN.map j (i+q) ∧
        HasFunctorialCofiber.cofibδ f≫K=φ≫XModLambdaN.map h (i+q) ∧
        ∀ (m w : ℤ) (v : BiHom m w V),
          v≫φ≫(model.quotients.tower C).rho i (i+q) (by omega) =
            v≫p≫XModLambdaN.map j i := by
  dsimp only
  intro p hp
  obtain ⟨φ,K,z,hφ,hK,hz⟩ := finite_quotient_octahedral_comparison
    G j h hGj hjh i q hi hq p hp
  refine ⟨φ,K,hφ,hK,?_⟩
  intro m w v
  have hzero := normalized_finite_no_return X Y C ef eg hef eC (i+q-i) i
    (by omega) hi m w
    (v≫HasFunctorialCofiber.cofibδ
      ((SyntheticCategory.biShift (0,-(i:ℤ))).map (XModLambdaN.map G (i+q-i))≫
        ((model.quotients.tower B).triangle hi (show i < i+q by omega)).lambdaMap)) z
  apply sub_eq_zero.mp
  rw [←Preadditive.comp_sub,hz,←Category.assoc]
  exact hzero

/- If two lifts solve the same cofiber boundary equation, their difference is
   exact through the shifted quotient map.  This is the internal K/J
   comparison available without choosing a global ``standard J``. -/
private theorem octahedral_lift_difference_factor
    {A B V D : SyntheticSpectrum}
    {f : A ⟶ B} {ι : B ⟶ V} {δ : V ⟶ A⟦(1:ℤ)⟧}
    (hT : Triangle.mk f ι δ ∈ distTriang SyntheticSpectrum)
    {K J : A⟦(1:ℤ)⟧ ⟶ D}
    (hKJ : δ ≫ K = δ ≫ J) :
    ∃ t : B⟦(1:ℤ)⟧ ⟶ D,
      K - J = (-(shiftFunctor SyntheticSpectrum (1:ℤ)).map f) ≫ t := by
  have hzero : δ ≫ (K-J)=0 := by
    rw [Preadditive.comp_sub,hKJ,sub_self]
  obtain ⟨t,ht⟩ := (Triangle.mk f ι δ).rotate.yoneda_exact₃
    (rot_of_distTriang _ hT) (K-J) hzero
  change B⟦(1:ℤ)⟧ ⟶ D at t
  change K-J = (-(shiftFunctor SyntheticSpectrum (1:ℤ)).map f) ≫ t at ht
  exact ⟨t,ht⟩

/- A representative on the boundary image cannot distinguish such lifts. -/
private theorem octahedral_lift_difference_zero_on_boundary
    {A B V D S : SyntheticSpectrum}
    {f : A ⟶ B} {ι : B ⟶ V} {δ : V ⟶ A⟦(1:ℤ)⟧}
    (hT : Triangle.mk f ι δ ∈ distTriang SyntheticSpectrum)
    {K J : A⟦(1:ℤ)⟧ ⟶ D}
    (hKJ : δ ≫ K = δ ≫ J)
    (v : S ⟶ V) (b : S ⟶ A⟦(1:ℤ)⟧) (hv : v ≫ δ = b) :
    b ≫ K = b ≫ J := by
  obtain ⟨t,ht⟩ := octahedral_lift_difference_factor hT hKJ
  apply sub_eq_zero.mp
  rw [←Preadditive.comp_sub,ht,←Category.assoc,←hv]
  have hzero := comp_distTriang_mor_zero₃₁ (Triangle.mk f ι δ) hT
  change δ ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map f = 0 at hzero
  have hvzero : v ≫ δ ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map f = 0 := by
    simp only [hzero,comp_zero]
  simp only [Category.assoc,Preadditive.comp_neg,hvzero,neg_zero,zero_comp]

end
end KIP126.ProofTools.Internal.Mahowald
