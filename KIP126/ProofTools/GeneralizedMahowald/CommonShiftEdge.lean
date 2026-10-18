module
import all KIP126.ProofTools.GeneralizedMahowald.OctahedralPullback

@[expose] section
namespace KIP126.ProofTools.Internal.Mahowald
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.AdamsSynthetic
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Standard
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2000000

/- The exact defect left on the unquotiented boundary edge. The first term
factors through the original triangle's boundary; the second is a Toda
indeterminacy through the suspension of lambda_i G. Neither is declared zero. -/
private theorem quotient_unquotiented_boundary_defect
    {A B : SyntheticSpectrum} (G : A ⟶ B)
    (i q : ℕ) (hi : 0 < i) (hq : 0 < q) :
    let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(i:ℤ))
    let L := (model.quotients.tower B).triangle hi (show i < i+q by omega)
    let u := F.map (XModLambdaN.map G (i+q-i))
    let f := u≫L.lambdaMap
    let C := HasFunctorialCofiber.cofib G
    let j := HasFunctorialCofiber.cofibι G
    let h := HasFunctorialCofiber.cofibδ G
    ∀ (φ : HasFunctorialCofiber.cofib f ⟶ XModLambdaN C (i+q))
      (K : (F.obj (XModLambdaN A (i+q-i)))⟦(1:ℤ)⟧ ⟶ XModLambdaN (A⟦(1:ℤ)⟧) (i+q)),
      HasFunctorialCofiber.cofibι f≫φ=XModLambdaN.map j (i+q) →
      HasFunctorialCofiber.cofibδ f≫K=φ≫XModLambdaN.map h (i+q) →
      ∃ (d : (F.obj A)⟦(1:ℤ)⟧ ⟶ XModLambdaN C (i+q))
        (t : B⟦(1:ℤ)⟧ ⟶ XModLambdaN (A⟦(1:ℤ)⟧) (i+q)),
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map (F.map (XModLambdaN.incl A (i+q-i)))≫K -
          (shiftFunctor SyntheticSpectrum (1:ℤ)).map (lambdaPow i A)≫
            XModLambdaN.incl (A⟦(1:ℤ)⟧) (i+q) =
        d≫XModLambdaN.map h (i+q) -
          (shiftFunctor SyntheticSpectrum (1:ℤ)).map (lambdaPow i A≫G)≫t := by
  dsimp only
  intro φ K hφ hK
  letI := model.exactness.syntheticTriangulated
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(i:ℤ))
  let L := (model.quotients.tower B).triangle hi (show i < i+q by omega)
  let f := F.map (XModLambdaN.map G (i+q-i))≫L.lambdaMap
  let f₀ := lambdaPow i A≫G
  let a := F.map (XModLambdaN.incl A (i+q-i))
  have hsquare : f₀≫XModLambdaN.incl B (i+q)=a≫f := by
    dsimp only [f₀,a,f,F]
    rw [←lambdaPow_naturality i G,Category.assoc,←L.lambda_quotient,
      ←Category.assoc,←Functor.map_comp,XModLambdaN.incl_naturality G (i+q-i),
      Functor.map_comp,Category.assoc]
  let η := HasFunctorialCofiber.cofibMap f₀ f a (XModLambdaN.incl B (i+q)) hsquare.symm
  have hη₁ := HasFunctorialCofiber.cofibMap_ι f₀ f a (XModLambdaN.incl B (i+q)) hsquare.symm
  have hη₂ := HasFunctorialCofiber.cofibMap_δ f₀ f a (XModLambdaN.incl B (i+q)) hsquare.symm
  let O := Triangulated.someOctahedron rfl
    (XModLambdaN.cofiberTriangle_distinguished A i)
    (HasFunctorialCofiber.cofib_distinguished G)
    (HasFunctorialCofiber.cofib_distinguished f₀)
  let T := Triangle.mk f₀ (HasFunctorialCofiber.cofibι f₀) (HasFunctorialCofiber.cofibδ f₀)
  have hT := HasFunctorialCofiber.cofib_distinguished f₀
  have hd₀ : HasFunctorialCofiber.cofibι f₀≫
      (η≫φ-O.m₃≫XModLambdaN.incl (HasFunctorialCofiber.cofib G) (i+q))=0 := by
    rw [Preadditive.comp_sub,←Category.assoc,←hη₁,Category.assoc,hφ,
      ←Category.assoc,O.comm₃,XModLambdaN.incl_naturality,sub_self]
  obtain ⟨d,hd⟩ := T.yoneda_exact₃ hT _ hd₀
  change (F.obj A)⟦(1:ℤ)⟧ ⟶ XModLambdaN (HasFunctorialCofiber.cofib G) (i+q) at d
  change η≫φ-O.m₃≫XModLambdaN.incl (HasFunctorialCofiber.cofib G) (i+q) =
    HasFunctorialCofiber.cofibδ f₀≫d at hd
  let E := (shiftFunctor SyntheticSpectrum (1:ℤ)).map a≫K -
    (shiftFunctor SyntheticSpectrum (1:ℤ)).map (lambdaPow i A)≫
      XModLambdaN.incl (A⟦(1:ℤ)⟧) (i+q) -
    d≫XModLambdaN.map (HasFunctorialCofiber.cofibδ G) (i+q)
  have hχ : HasFunctorialCofiber.cofibδ f₀≫
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (lambdaPow i A)≫
        XModLambdaN.incl (A⟦(1:ℤ)⟧) (i+q) =
      O.m₃≫XModLambdaN.incl (HasFunctorialCofiber.cofib G) (i+q)≫
        XModLambdaN.map (HasFunctorialCofiber.cofibδ G) (i+q) := by
    rw [←Category.assoc,O.comm₄,Category.assoc,XModLambdaN.incl_naturality]
  have hd' := congrArg (fun z => z≫XModLambdaN.map (HasFunctorialCofiber.cofibδ G) (i+q)) hd
  simp only [Preadditive.sub_comp,Category.assoc] at hd'
  have hE : HasFunctorialCofiber.cofibδ f₀≫E=0 := by
    dsimp only [E]
    rw [Preadditive.comp_sub,Preadditive.comp_sub,←Category.assoc,←hη₂,
      Category.assoc,hK,hχ]
    simpa only [η,Category.assoc] using sub_eq_zero.mpr hd'
  obtain ⟨t,ht⟩ := T.rotate.yoneda_exact₃ (rot_of_distTriang _ hT) E hE
  change B⟦(1:ℤ)⟧ ⟶ XModLambdaN (A⟦(1:ℤ)⟧) (i+q) at t
  change E=(-(shiftFunctor SyntheticSpectrum (1:ℤ)).map f₀)≫t at ht
  rw [Preadditive.neg_comp] at ht
  refine ⟨d,t,?_⟩
  dsimp only [E,f₀,a,F] at ht
  exact (sub_eq_iff_eq_add.mp ht).trans (by abel)


/- Common desuspension preserves the original G factor on the residual;
no spectral-sequence shift comparison is used. -/
private theorem common_shift_residual_factor
    {A B D : SyntheticSpectrum} (G : A ⟶ B) (i : ℕ)
    (t : B⟦(1:ℤ)⟧ ⟶ (SyntheticCategory.biShift (1,-(i:ℤ))).obj D) :
    (biSuspensionIso (i:ℤ) A).hom ≫
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map (lambdaPow i A≫G) ≫ t =
      (SyntheticCategory.biShift (1,-(i:ℤ))).map G ≫
        ((biSuspensionIso (i:ℤ) B).hom ≫
          (shiftFunctor SyntheticSpectrum (1:ℤ)).map (lambdaPow i B) ≫ t) := by
  rw [←lambdaPow_naturality i G,Functor.map_comp]
  simp only [Category.assoc]
  rw [←Category.assoc (biSuspensionIso (i:ℤ) A).hom,
    ←biSuspensionIso_natural]
  simp only [Category.assoc]

/- The actual unquotiented edge equation pulled back by the one common
bigraded shift. Source labels can now be evaluated before any shift. -/
private theorem quotient_common_desuspended_boundary_defect
    {A B C₀ D₀ : SyntheticSpectrum} (G : A ⟶ B)
    (i q : ℕ) (hi : 0 < i) (hq : 0 < q)
    (eC : XModLambdaN (HasFunctorialCofiber.cofib G) (i+q) ≅
      (SyntheticCategory.biShift (1,-(i:ℤ))).obj C₀)
    (eD : XModLambdaN (A⟦(1:ℤ)⟧) (i+q) ≅
      (SyntheticCategory.biShift (1,-(i:ℤ))).obj D₀) :
    let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(i:ℤ))
    let ff := SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) (1,-(i:ℤ))
    let L := (model.quotients.tower B).triangle hi (show i < i+q by omega)
    let u := F.map (XModLambdaN.map G (i+q-i))
    let f := u≫L.lambdaMap
    let h := HasFunctorialCofiber.cofibδ G
    ∀ (φ : HasFunctorialCofiber.cofib f ⟶ XModLambdaN (HasFunctorialCofiber.cofib G) (i+q))
      (K : (F.obj (XModLambdaN A (i+q-i)))⟦(1:ℤ)⟧ ⟶ XModLambdaN (A⟦(1:ℤ)⟧) (i+q)),
      HasFunctorialCofiber.cofibι f≫φ=XModLambdaN.map (HasFunctorialCofiber.cofibι G) (i+q) →
      HasFunctorialCofiber.cofibδ f≫K=φ≫XModLambdaN.map h (i+q) →
      let K₀ := ff.preimage ((biSuspensionIso (i:ℤ) (XModLambdaN A (i+q-i))).hom ≫ K ≫ eD.hom)
      let J₀ := ff.preimage ((biSuspensionIso (i:ℤ) A).hom ≫
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map (lambdaPow i A) ≫
          XModLambdaN.incl (A⟦(1:ℤ)⟧) (i+q) ≫ eD.hom)
      let h₀ := ff.preimage (eC.inv ≫ XModLambdaN.map h (i+q) ≫ eD.hom)
      ∃ (d₀ : A ⟶ C₀) (t₀ : B ⟶ D₀),
        XModLambdaN.incl A (i+q-i) ≫ K₀ - J₀ = d₀≫h₀ - G≫t₀ := by
  dsimp only
  intro φ K hφ hK
  obtain ⟨d,t,hedge⟩ := quotient_unquotiented_boundary_defect G i q hi hq φ K hφ hK
  let ff := SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) (1,-(i:ℤ))
  let d₀ : A ⟶ C₀ := ff.preimage ((biSuspensionIso (i:ℤ) A).hom ≫ d ≫ eC.hom)
  let t₀ : B ⟶ D₀ := ff.preimage ((biSuspensionIso (i:ℤ) B).hom ≫
    (shiftFunctor SyntheticSpectrum (1:ℤ)).map (lambdaPow i B) ≫ t ≫ eD.hom)
  refine ⟨d₀,t₀,?_⟩
  apply ff.map_injective
  simp only [Functor.map_sub,Functor.map_comp,d₀,t₀,Functor.FullyFaithful.map_preimage]
  rw [←Category.assoc _ (biSuspensionIso (i:ℤ) (XModLambdaN A (i+q-i))).hom,
    biSuspensionIso_natural]
  simp only [Category.assoc,Iso.hom_inv_id_assoc]
  have hh := congrArg (fun z => (biSuspensionIso (i:ℤ) A).hom ≫ z ≫ eD.hom) hedge
  simp only [Preadditive.comp_sub,Preadditive.sub_comp,Category.assoc] at hh
  rw [common_shift_residual_factor G i (t≫eD.hom)] at hh
  exact hh

end
end KIP126.ProofTools.Internal.Mahowald
