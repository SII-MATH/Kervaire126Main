module
import KIP126.Def.ProofTools.Laws
import all KIP126.Def.ProofTools.GeneralizedMahowald.Coherence
/-! The first strict finite-quotient lift used in the Mahowald diagram.
The proof uses the prescribed λ–ρ–δ triangles and naturality, so the resulting
lift satisfies the actual restriction equation on the same fixed quotients.
The final lemma also instantiates the paper's May tensor diagram and proves
both signed image equations for the same lift. Comparing these tensor objects
and maps with the fixed quotients above is a separate remaining step. -/
@[expose] section
namespace KIP126.ProofTools.Internal.Mahowald
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard KIP126.Literature
attribute [local instance] HasZeroObject.zero'
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
private theorem quotient_zero_isZero (q : ℕ) :
    IsZero (XModLambdaN (0 : SyntheticSpectrum) q) := by
  letI := model.exactness.shiftAdditive (0,-(q:ℤ))
  have hz₁ : IsZero ((SyntheticCategory.biShift (0,-(q:ℤ))).obj (0 : SyntheticSpectrum)) :=
    Functor.map_isZero _ (isZero_zero _)
  have hz₂ : IsZero (0 : SyntheticSpectrum) := isZero_zero _
  exact (XModLambdaN.cofiberTriangle (0 : SyntheticSpectrum) q).isZero₃_of_isZero₁₂
    (XModLambdaN.cofiberTriangle_distinguished (0 : SyntheticSpectrum) q) hz₁ hz₂
private theorem quotient_map_zero (A B : SyntheticSpectrum) (q : ℕ) :
    XModLambdaN.map (0 : A ⟶ B) q = 0 := by
  have h := model.quotients.functoriality.map_comp (0 : A ⟶ (0 : SyntheticSpectrum)) (0 : (0 : SyntheticSpectrum) ⟶ B) q
  rw [zero_comp] at h
  rw [h]
  rw [(quotient_zero_isZero q).eq_of_tgt (XModLambdaN.map (0 : A ⟶ (0 : SyntheticSpectrum)) q) 0,zero_comp]
private theorem quotient_map_comp_zero {A B C : SyntheticSpectrum}
    (f : A ⟶ B) (g : B ⟶ C) (h : f ≫ g = 0) (q : ℕ) :
    XModLambdaN.map f q ≫ XModLambdaN.map g q = 0 := by
  rw [← model.quotients.functoriality.map_comp,h,quotient_map_zero]
private theorem quotient_boundary_lift {A B C S : SyntheticSpectrum}
    (f : A ⟶ B) (g : B ⟶ C) (h : f ≫ g = 0)
    (i j : ℕ) (hi : 0 < i) (hij : i < j)
    (a : S ⟶ XModLambdaN B i)
    (b : S ⟶ (((SyntheticCategory.biShift (0,-(i:ℤ))).obj (XModLambdaN A (j-i)))⟦(1:ℤ)⟧))
    (hab : a ≫ ((model.quotients.tower B).triangle hi hij).delta =
      b ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map
        ((SyntheticCategory.biShift (0,-(i:ℤ))).map (XModLambdaN.map f (j-i)))) :
    ∃ c : S ⟶ XModLambdaN C j,
      c ≫ (model.quotients.tower C).rho i j hij.le = a ≫ XModLambdaN.map g i := by
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(i:ℤ))
  let V := (model.quotients.tower C).triangle hi hij
  have hz : (a ≫ XModLambdaN.map g i) ≫ V.delta = 0 := by
    rw [Category.assoc,(model.quotients.natural g).delta_naturality hi hij,← Category.assoc,hab]
    simp only [Category.assoc]
    rw [← CategoryTheory.Functor.map_comp,← CategoryTheory.Functor.map_comp,
      quotient_map_comp_zero f g h,Functor.map_zero,Functor.map_zero,comp_zero]
  obtain ⟨c,hc⟩ := (Triangle.mk V.lambdaMap V.rho V.delta).coyoneda_exact₃ V.distinguished
    (a ≫ XModLambdaN.map g i) hz
  refine ⟨c,?_⟩
  simpa only [V,Triangle.mk,(model.quotients.tower C).triangle_rho hi hij] using hc.symm
private theorem quotient_boundary_lift_desuspended {A B C : SyntheticSpectrum}
    (f : A ⟶ B) (g : B ⟶ C) (h : f ≫ g = 0)
    (i q : ℕ) (hi : 0 < i) (hq : 0 < q) (m w : ℤ)
    (a : BiHom m w (XModLambdaN B i))
    (b : BiHom (m-1) (w+i) (XModLambdaN A q))
    (hab : b ≫ XModLambdaN.map f q =
      biSuspensionHomEquiv m w i (XModLambdaN B q)
        (by simpa only [Nat.add_sub_cancel_left] using
          a ≫ ((model.quotients.tower B).triangle hi (show i < i+q by omega)).delta)) :
    ∃ c : BiHom m w (XModLambdaN C (i+q)),
      c ≫ (model.quotients.tower C).rho i (i+q) (by omega) =
        a ≫ XModLambdaN.map g i := by
  have lift_source (d q : ℕ) (hd : d=q)
      (δ : BiHom m w (((SyntheticCategory.biShift (0,-(i:ℤ))).obj (XModLambdaN B d))⟦(1:ℤ)⟧))
      (b : BiHom (m-1) (w+i) (XModLambdaN A q))
      (hb : b ≫ XModLambdaN.map f q =
        biSuspensionHomEquiv m w i (XModLambdaN B q) (by simpa only [hd] using δ)) :
      ∃ b' : BiHom m w (((SyntheticCategory.biShift (0,-(i:ℤ))).obj (XModLambdaN A d))⟦(1:ℤ)⟧),
        δ = b' ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map
          ((SyntheticCategory.biShift (0,-(i:ℤ))).map (XModLambdaN.map f d)) := by
    subst q
    refine ⟨(biSuspensionHomEquiv m w i (XModLambdaN A d)).symm b, ?_⟩
    apply (biSuspensionHomEquiv m w i (XModLambdaN B d)).injective
    rw [bi_susp_natural model.quotients.coherence, AddEquiv.apply_symm_apply]
    exact hb.symm
  obtain ⟨b',hb'⟩ := lift_source (i+q-i) q (Nat.add_sub_cancel_left i q)
    (a ≫ ((model.quotients.tower B).triangle hi (show i < i+q by omega)).delta) b hab
  exact quotient_boundary_lift f g h i (i+q) hi (by omega) a b' hb'

/-- The second arrow of the same chosen quotient lift lies in the actual
λ image. The prescribed source of that λ image is a separate comparison;
this lemma does not identify it with an independently given preimage. -/
private theorem quotient_lift_image_division {A B C S : SyntheticSpectrum}
    (g : A ⟶ B) (h : B ⟶ C) (hgh : g ≫ h = 0)
    (i j : ℕ) (hi : 0 < i) (hij : i < j)
    (a : S ⟶ XModLambdaN A i) (c : S ⟶ XModLambdaN B j)
    (hc : c ≫ (model.quotients.tower B).rho i j hij.le = a ≫ XModLambdaN.map g i) :
    ∃ b : S ⟶ (SyntheticCategory.biShift (0,-(i:ℤ))).obj (XModLambdaN C (j-i)),
      b ≫ ((model.quotients.tower C).triangle hi hij).lambdaMap =
        c ≫ XModLambdaN.map h j := by
  let T := (model.quotients.tower C).triangle hi hij
  have hz : (c ≫ XModLambdaN.map h j) ≫ T.rho = 0 := by
    dsimp only [T]
    rw [(model.quotients.tower C).triangle_rho hi hij]
    rw [Category.assoc,←(model.quotients.natural h).rho_naturality hij.le,
      ←Category.assoc,hc,Category.assoc,quotient_map_comp_zero g h hgh,comp_zero]
  obtain ⟨b,hb⟩ := (Triangle.mk T.lambdaMap T.rho T.delta).coyoneda_exact₂
    T.distinguished (c ≫ XModLambdaN.map h j) hz
  exact ⟨b,hb.symm⟩


/-- The quotient filling and its complementary triangle from three actual
octahedra. The two fillings share their middle cofiber, and the last triangle
retains the signed comparison required by the common-lift argument. -/
private theorem quotient_octahedron_fill {A B : SyntheticSpectrum}
    (f : A ⟶ B) (q : ℕ) :
    ∃ u : XModLambdaN A q ⟶ XModLambdaN B q,
      XModLambdaN.incl A q ≫ u = f ≫ XModLambdaN.incl B q ∧
      u ≫ XModLambdaN.proj B q = XModLambdaN.proj A q ≫
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map
          ((SyntheticCategory.biShift (0,-(q:ℤ))).map f) ∧
      ∃ (l : HasFunctorialCofiber.cofib ((SyntheticCategory.biShift (0,-(q:ℤ))).map f) ⟶
            HasFunctorialCofiber.cofib f)
        (v : HasFunctorialCofiber.cofib f ⟶ HasFunctorialCofiber.cofib u)
        (w : HasFunctorialCofiber.cofib u ⟶
          (HasFunctorialCofiber.cofib ((SyntheticCategory.biShift (0,-(q:ℤ))).map f))⟦(1:ℤ)⟧),
        HasFunctorialCofiber.cofibι ((SyntheticCategory.biShift (0,-(q:ℤ))).map f) ≫ l =
          lambdaPow q B ≫ HasFunctorialCofiber.cofibι f ∧
        l ≫ HasFunctorialCofiber.cofibδ f =
          HasFunctorialCofiber.cofibδ ((SyntheticCategory.biShift (0,-(q:ℤ))).map f) ≫
            (shiftFunctor SyntheticSpectrum (1:ℤ)).map (lambdaPow q A) ∧
        HasFunctorialCofiber.cofibι f ≫ v =
          XModLambdaN.incl B q ≫ HasFunctorialCofiber.cofibι u ∧
        v ≫ HasFunctorialCofiber.cofibδ u =
          HasFunctorialCofiber.cofibδ f ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl A q) ∧
        HasFunctorialCofiber.cofibι u ≫ w = XModLambdaN.proj B q ≫
          (shiftFunctor SyntheticSpectrum (1:ℤ)).map
            (HasFunctorialCofiber.cofibι ((SyntheticCategory.biShift (0,-(q:ℤ))).map f)) ∧
        Triangle.mk v w (-(shiftFunctor SyntheticSpectrum (1:ℤ)).map l) ∈ distTriang SyntheticSpectrum := by
  letI := model.exactness.syntheticTriangulated
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(q:ℤ))
  let c := lambdaPow q A ≫ f
  let O := Triangulated.someOctahedron rfl
    (XModLambdaN.cofiberTriangle_distinguished A q)
    (HasFunctorialCofiber.cofib_distinguished f)
    (HasFunctorialCofiber.cofib_distinguished c)
  let O' := Triangulated.someOctahedron (lambdaPow_naturality q f)
    (HasFunctorialCofiber.cofib_distinguished (F.map f))
    (XModLambdaN.cofiberTriangle_distinguished B q)
    (HasFunctorialCofiber.cofib_distinguished c)
  let u := O.m₁ ≫ O'.m₃
  let l := O'.m₁ ≫ O.m₃
  let O'' := Triangulated.someOctahedron rfl O.mem
    (rot_of_distTriang O'.triangle O'.mem)
    (HasFunctorialCofiber.cofib_distinguished u)
  refine ⟨u, ?_, ?_, l, O''.m₁, O''.m₃, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [u]
    rw [← Category.assoc, O.comm₁, Category.assoc, O'.comm₃]
  · dsimp [u]
    rw [Category.assoc, ← O'.comm₄, ← Category.assoc, O.comm₂]
  · dsimp [l]
    rw [← Category.assoc, O'.comm₁, Category.assoc, O.comm₃]
  · dsimp [l]
    rw [Category.assoc, ← O.comm₄, ← Category.assoc, O'.comm₂]
  · calc
      _ = (HasFunctorialCofiber.cofibι c ≫ O.m₃) ≫ O''.m₁ := by rw [O.comm₃]
      _ = _ := by
        rw [Category.assoc, O''.comm₁]
        change HasFunctorialCofiber.cofibι c ≫ O'.m₃ ≫ _ = _
        rw [← Category.assoc, O'.comm₃]
  · exact O''.comm₂
  · exact O''.comm₃
  · simpa only [Triangulated.Octahedron.triangle, Triangle.rotate, Triangle.mk,
      Preadditive.neg_comp, ← Functor.map_comp] using O''.mem

private def may_normalized_rotated (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g +
      normalizedExponent model.classicalTower T.h = 1)
    (hT : KIP126.Literature.NormalizedTriangleCompatible model T he) :
    HoCofiberSequence (C := SyntheticSpectrum) where
  X := (KIP126.Literature.normalizedTriangle model T he).obj₂
  Y := (KIP126.Literature.normalizedTriangle model T he).obj₃
  Z := (KIP126.Literature.normalizedTriangle model T he).obj₁⟦(1:ℤ)⟧
  f := (KIP126.Literature.normalizedTriangle model T he).mor₂
  g := (KIP126.Literature.normalizedTriangle model T he).mor₃
  h := -(shiftFunctor SyntheticSpectrum (1:ℤ)).map
    (KIP126.Literature.normalizedTriangle model T he).mor₁
  distinguished := rot_of_distTriang _ hT

private def may_relative_unit_rotated (i q : ℕ) (hi : 0 < i) (hq : 0 < q) :
    HoCofiberSequence (C := SyntheticSpectrum) :=
  let L := (model.quotients.tower (𝟙_ SyntheticSpectrum)).triangle hi
    (show i < i+q by omega)
  { X := XModLambdaN (𝟙_ SyntheticSpectrum) (i+q)
    Y := XModLambdaN (𝟙_ SyntheticSpectrum) i
    Z := ((SyntheticCategory.biShift (0,-(i:ℤ))).obj
      (XModLambdaN (𝟙_ SyntheticSpectrum) ((i+q)-i)))⟦(1:ℤ)⟧
    f := L.rho
    g := L.delta
    h := -(shiftFunctor SyntheticSpectrum (1:ℤ)).map L.lambdaMap
    distinguished := rot_of_distTriang _ L.distinguished }

/- The two actual tensor equations, with the rotated minus signs expanded.
Write N=(A--f→B--g→C--h→ΣA), L=(F_-i Qq1--λ→Qr1--ρ→Qi1).
Then a is the suspended [y] slot B⊗ΣF_-i Qq1; b is [xBar] in C⊗Qi1.
The result is c∈π_n(ΣA⊗Qr1), c(ΣA⊗ρ)=b(h⊗Qi1), and
c(Σf⊗Qr1)κ_right = -a(B⊗Σλ)κ_left.
The negative sign is genuine under the registered May conventions. -/
private theorem may_tensor_common_lift
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g +
      normalizedExponent model.classicalTower T.h = 1)
    (hT : KIP126.Literature.NormalizedTriangleCompatible model T he)
    (i q : ℕ) (hi : 0 < i) (hq : 0 < q)
    (n : ℤ)
    (a : HomotopyGroup n ((may_normalized_rotated T he hT).X ⊗
      (may_relative_unit_rotated i q hi hq).Z))
    (b : HomotopyGroup n ((may_normalized_rotated T he hT).Y ⊗
      (may_relative_unit_rotated i q hi hq).Y))
    (hab : a ≫ ((may_normalized_rotated T he hT).f ▷
        (may_relative_unit_rotated i q hi hq).Z) =
      b ≫ ((may_normalized_rotated T he hT).Y ◁
        (may_relative_unit_rotated i q hi hq).g)) :
    let N := KIP126.Literature.normalizedTriangle model T he
    let L := (model.quotients.tower (𝟙_ SyntheticSpectrum)).triangle hi
      (show i < i+q by omega)
    let U := may_relative_unit_rotated i q hi hq
    letI := KIP126.Literature.Standard.may_leftShift
    letI := KIP126.Literature.Standard.may_rightShift
    ∃ c : HomotopyGroup n (N.obj₁⟦(1:ℤ)⟧ ⊗ U.X),
      c ≫ (N.obj₁⟦(1:ℤ)⟧ ◁ L.rho) = b ≫ (N.mor₃ ▷ U.Y) ∧
      c ≫ (tensorRight U.X).map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map N.mor₁) ≫
          ((tensorRight U.X).commShiftIso (1:ℤ)).hom.app N.obj₂ =
        -(a ≫ (tensorLeft N.obj₂).map
          ((shiftFunctor SyntheticSpectrum (1:ℤ)).map L.lambdaMap) ≫
            ((tensorLeft N.obj₂).commShiftIso (1:ℤ)).hom.app U.X) := by
  letI := KIP126.Literature.Standard.may_leftShift
  letI := KIP126.Literature.Standard.may_rightShift
  letI := KIP126.Literature.Standard.may_leftExact
  letI := KIP126.Literature.Standard.may_rightExact
  obtain ⟨P⟩ := KIP126.Literature.Standard.may_pushpull
    (may_normalized_rotated T he hT) (may_relative_unit_rotated i q hi hq)
  obtain ⟨v,hva,hvb⟩ := P.lift n a b hab
  refine ⟨v ≫ P.j3, ?_, ?_⟩
  · change (v ≫ P.j3) ≫ ((may_normalized_rotated T he hT).Z ◁
      (may_relative_unit_rotated i q hi hq).f) =
        b ≫ ((may_normalized_rotated T he hT).g ▷ (may_relative_unit_rotated i q hi hq).Y)
    rw [←hvb]
    simp only [Category.assoc, P.other_square]
  · have hb := congrArg (fun z => v ≫ z) P.boundary
    rw [Preadditive.comp_neg, ←Category.assoc, hva] at hb
    dsimp only [HoCofiberSequence.map, may_normalized_rotated, may_relative_unit_rotated] at hb
    simp only [Functor.map_neg, Preadditive.neg_comp, Preadditive.comp_neg,
      neg_neg] at hb
    simpa only [may_relative_unit_rotated, Category.assoc] using hb.symm

end
end KIP126.ProofTools.Internal.Mahowald
