module

public import KIP126.AdamsSynthetic.Standard
public import KIP126.AdamsSynthetic.Standard.Filtration
public import KIP126.AdamsSynthetic.AdamsFiltration
public import KIP126.AdamsSynthetic.Internal.SteenrodComodules
import all KIP126.AdamsSynthetic.Internal.SteenrodComodules
import all KIP126.AdamsSynthetic.Internal.SteenrodComodules.Abelian
import Mathlib.RingTheory.Flat.Basic
/-! The minimal coefficient-Ext source used by finite-layer composition.
The homology source and comparisons are registered upstream boundaries.
Ext itself and the SES connecting operation use mathlib's derived category;
neither is defined by a synthetic first-quotient operation. -/

@[expose] section
set_option backward.privateInPublic true
namespace KIP126.AdamsSynthetic.Standard
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open Internal.SteenrodComodules
open scoped TensorProduct
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

/-- Internally graded comodules over the specified Milnor polynomial coproduct. -/
public def SteenrodComodule : Type 1 := GradedSteenrodComodule

@[no_expose] public instance steenrodComoduleCategory : Category.{0} SteenrodComodule :=
  inferInstanceAs (Category GradedSteenrodComodule)

@[reducible] private def steenrodComodulePreadditive : Preadditive SteenrodComodule :=
  inferInstanceAs (Preadditive GradedSteenrodComodule)

private def canonicalComoduleAbelian :
    {A : Abelian SteenrodComodule // A.toPreadditive = steenrodComodulePreadditive} :=
  ⟨comoduleAbelian, rfl⟩

/-- The canonical abelian structure on the actual graded comodule category.
Its construction is an upstream responsibility, not an assumption of composition. -/
public instance steenrodComoduleAbelian : Abelian SteenrodComodule :=
  canonicalComoduleAbelian.val

private def homologyCoactionMap (X : Spectrum) :
    coefficients.object ⊗ X ⟶ coefficients.object ⊗ (coefficients.object ⊗ X) :=
  coefficients.object ◁ ((λ_ X).inv ≫ (coefficients.unit ▷ X))

private def coefficientExternalProduct
    (μ : coefficients.object ⊗ coefficients.object ⟶ coefficients.object)
    (X : Spectrum) (m n : ℤ)
    (a : ModTwoHomology coefficients m coefficients.object)
    (b : ModTwoHomology coefficients n X) :
    HomotopyGroup (m+n) (coefficients.object ⊗ (coefficients.object ⊗ X)) := by
  letI := closedBackground.symmetric
  exact (closedBackground.smashSpheres m n).inv ≫ (a ⊗ₘ b) ≫
    tensorμ coefficients.object coefficients.object coefficients.object X ≫
      (μ ▷ (coefficients.object ⊗ X))

/- This recognition boundary fixes the actual HF2 homology and its spectral
coaction, in addition to the polynomial coalgebra and degree grading. -/
private structure HomologyComoduleSource where
  functor : Spectrum ⥤ SteenrodComodule
  additive : functor.Additive
  degree : ∀ (X : Spectrum) (n : ℤ),
    ((functor.obj X).grade n) ≃+ ModTwoHomology coefficients n X
  natural : ∀ {X Y : Spectrum} (f : X ⟶ Y) (n : ℤ)
    (x : (functor.obj X).grade n),
    degree Y n ⟨(functor.map f).linearMap x,
      (functor.map f).graded n x x.property⟩ =
        modTwoHomologyMap coefficients f n (degree X n x)
  multiplication : coefficients.object ⊗ coefficients.object ⟶ coefficients.object
  unit_left : (coefficients.unit ▷ coefficients.object) ≫ multiplication =
    (λ_ coefficients.object).hom
  unit_right : (coefficients.object ◁ coefficients.unit) ≫ multiplication =
    (ρ_ coefficients.object).hom
  associative : (multiplication ▷ coefficients.object) ≫ multiplication =
    (α_ coefficients.object coefficients.object coefficients.object).hom ≫
      (coefficients.object ◁ multiplication) ≫ multiplication
  cooperations : (functor.obj coefficients.object).carrier ≃ₗ[F2] DualSteenrod
  cooperation_grade : ∀ (n : ℤ) (a : (functor.obj coefficients.object).carrier),
    a ∈ (functor.obj coefficients.object).grade n ↔
      if 0 ≤ n then MvPolynomial.IsWeightedHomogeneous milnorWeight (cooperations a) n.toNat
      else a = 0
  cooperation_coproduct :
    TensorProduct.map (LinearMap.id : DualSteenrod →ₗ[F2] DualSteenrod)
      cooperations.toLinearMap ∘ₗ
      (functor.obj coefficients.object).rho =
        milnorCoproduct.toLinearMap ∘ₗ cooperations.toLinearMap
  kunneth : ∀ (X : Spectrum) (n : ℤ),
    HomotopyGroup n (coefficients.object ⊗ (coefficients.object ⊗ X)) ≃+
      tensorGrade (functor.obj X).carrier (functor.obj X).grade n
  kunneth_tensor : ∀ (X : Spectrum) (m n : ℤ)
    (a : (functor.obj coefficients.object).grade m) (b : (functor.obj X).grade n),
    (kunneth X (m+n) (coefficientExternalProduct multiplication X m n
      (degree coefficients.object m a) (degree X n b))).val =
        cooperations a ⊗ₜ[F2] b.val
  coaction : ∀ (X : Spectrum) (n : ℤ) (x : (functor.obj X).grade n),
    (kunneth X n (degree X n x ≫ homologyCoactionMap X)).val =
      (functor.obj X).rho x

private def canonicalHomologyComoduleSource : HomologyComoduleSource := by
  sorry

/-- The actual HF2 homology comodule functor, with the spectral coaction. -/
@[no_expose] public def homologyComodule : Spectrum ⥤ SteenrodComodule :=
  canonicalHomologyComoduleSource.functor

private instance homologyComoduleAdditive : homologyComodule.Additive :=
  canonicalHomologyComoduleSource.additive

/-- Integer-graded derived Ext from H_*(Sigma^t S) to the same H_*X.
For nonnegative s this is mathlib's ordinary Ext; no negative degree is
silently replaced by zero via Int.toNat. -/
@[no_expose] public def ClassicalExt (X : Spectrum) (s t : ℤ) : Type 1 :=
  IntExt (homologyComodule.obj (Sphere t)) (homologyComodule.obj X) s

@[reducible] private def extAddCommGroup (X : Spectrum) (s t : ℤ) :
    AddCommGroup (ClassicalExt X s t) := inferInstanceAs (AddCommGroup (IntExt _ _ s))

public instance classicalExtAddCommGroup (X : Spectrum) (s t : ℤ) :
    AddCommGroup (ClassicalExt X s t) := extAddCommGroup X s t

private structure AdamsExtComparison where
  e2 : ∀ (X : ClassicalObject) (s t : ℤ),
    (classical.obj (X.obj auxiliary)).Page 2 (s,t) ≃+ ClassicalExt (X.obj auxiliary) s t
  natural : ∀ (X Y : ClassicalObject) (f : X.obj auxiliary ⟶ Y.obj auxiliary)
    (s t : ℤ) (x : (classical.obj (X.obj auxiliary)).Page 2 (s,t)),
    e2 Y s t ((classical.functor.map f).pageMap 2 (s,t) x) =
      IntExt.map (homologyComodule.map f) s (e2 X s t x)
  suspended : ∀ (X : ClassicalObject) (s t : ℤ),
    (classical.obj (X.obj auxiliary)).Page 2 (s,t) ≃+
      ClassicalExt ((X.obj auxiliary)⟦(1 : ℤ)⟧) s (t+1)
  suspension : ∀ (X : ClassicalObject) (s t : ℤ)
    (x : (classical.obj (X.obj auxiliary)).Page 2 (s,t))
    (sx : (classical.obj ((X.obj auxiliary)⟦(1 : ℤ)⟧)).Page 2 (s,t+1)),
    (classicalSuspension X).DesuspendsClass s (t+1) sx (by simpa using x) →
      suspended X s t x = e2 (.shift 1 X) s (t+1) sx

private def canonicalAdamsExtComparison : AdamsExtComparison := by
  sorry

/-- The fixed Adams E2/derived coefficient-Ext coordinates. -/
@[no_expose] public def e2ExtEquiv (X : ClassicalObject) (s t : ℤ) :
    (classical.obj (X.obj auxiliary)).Page 2 (s,t) ≃+ ClassicalExt (X.obj auxiliary) s t :=
  canonicalAdamsExtComparison.e2 X s t

/-- The same coordinates followed by the actual internal suspension. -/
@[no_expose] public def suspendedE2ExtEquiv (X : ClassicalObject) (s t : ℤ) :
    (classical.obj (X.obj auxiliary)).Page 2 (s,t) ≃+
      ClassicalExt ((X.obj auxiliary)⟦(1 : ℤ)⟧) s (t+1) :=
  canonicalAdamsExtComparison.suspended X s t

/-- The same actual g and h, viewed as homology-comodule maps. -/
public def cofiberHomologyShortComplex (T : TriangleData model.auxiliary) :
    ShortComplex SteenrodComodule :=
  ShortComplex.mk (homologyComodule.map T.g) (homologyComodule.map T.h) (by
    have hz : T.g ≫ T.h = 0 := comp_distTriang_mor_zero₂₃ _ T.distinguished
    rw [← Functor.map_comp, hz, Functor.map_zero])

/- A degree-zero map commutes with the finite homogeneous decomposition.
Consequently degreewise injectivity, surjectivity, and exactness imply the
corresponding properties of the underlying linear maps. The injective first
map then gives a unique kernel lift; tensoring preserves its injectivity over
F₂, so that lift also preserves the coaction. -/

private def gradeMap {M N : GradedSteenrodComodule} (f : M ⟶ N) (n : ℤ) :
    M.grade n →ₗ[F2] N.grade n := ((GradedSteenrodComodule.gradeForget n).map f).hom

private theorem decompose_natural {M N : GradedSteenrodComodule} (f : M ⟶ N)
    (n : ℤ) (x : M.carrier) :
    letI := M.internal.chooseDecomposition
    letI := N.internal.chooseDecomposition
    DirectSum.decompose N.grade (f.linearMap x) n =
      gradeMap f n (DirectSum.decompose M.grade x n) := by
  classical
  letI := M.internal.chooseDecomposition
  letI := N.internal.chooseDecomposition
  induction x using DirectSum.Decomposition.inductionOn M.grade with
  | zero => simp [gradeMap]
  | homogeneous x =>
    rename_i i
    by_cases h : n = i
    · subst n
      apply Subtype.ext
      change ↑(DirectSum.decompose N.grade (f.linearMap x) i) =
        f.linearMap ↑(DirectSum.decompose M.grade (↑x) i)
      rw [DirectSum.decompose_of_mem_same M.grade x.property,
        DirectSum.decompose_of_mem_same N.grade (f.graded i x x.property)]
    · apply Subtype.ext
      rw [DirectSum.decompose_of_mem_ne N.grade (f.graded i x x.property) (Ne.symm h)]
      change 0 = f.linearMap ↑(DirectSum.decompose M.grade (↑x) n)
      rw [DirectSum.decompose_of_mem_ne M.grade x.property (Ne.symm h), map_zero]
  | add x y hx hy =>
    simp only [map_add, DirectSum.decompose_add, DirectSum.add_apply, hx, hy]

private theorem total_injective {M N : GradedSteenrodComodule} (f : M ⟶ N)
    (hi : ∀ n : ℤ, Function.Injective (gradeMap f n)) :
    Function.Injective f.linearMap := by
  classical
  letI := M.internal.chooseDecomposition
  letI := N.internal.chooseDecomposition
  intro x y h
  apply (DirectSum.decompose M.grade).injective
  ext n
  apply congrArg Subtype.val
  apply hi n
  rw [← decompose_natural, ← decompose_natural, h]

private theorem total_surjective {M N : GradedSteenrodComodule} (f : M ⟶ N)
    (hs : ∀ n : ℤ, Function.Surjective (gradeMap f n)) :
    Function.Surjective f.linearMap := by
  classical
  letI := N.internal.chooseDecomposition
  intro y
  induction y using DirectSum.Decomposition.inductionOn N.grade with
  | zero => exact ⟨0, map_zero _⟩
  | homogeneous y =>
    rename_i n
    obtain ⟨x, hx⟩ := hs n y
    exact ⟨x, congrArg Subtype.val hx⟩
  | add y z hy hz =>
    obtain ⟨x, rfl⟩ := hy
    obtain ⟨w, rfl⟩ := hz
    exact ⟨x + w, map_add _ _ _⟩

private theorem total_exact {M N P : GradedSteenrodComodule}
    (f : M ⟶ N) (g : N ⟶ P)
    (he : ∀ n : ℤ, Function.Exact (gradeMap f n) (gradeMap g n)) :
    Function.Exact f.linearMap g.linearMap := by
  classical
  letI := M.internal.chooseDecomposition
  letI := N.internal.chooseDecomposition
  letI := P.internal.chooseDecomposition
  intro y
  constructor
  · intro hy
    have hcomp : ∀ n, gradeMap g n (DirectSum.decompose N.grade y n) = 0 := by
      intro n
      rw [← decompose_natural, hy, DirectSum.decompose_zero, DirectSum.zero_apply]
    choose x hx using fun n => (he n (DirectSum.decompose N.grade y n)).mp (hcomp n)
    refine ⟨∑ n ∈ (DirectSum.decompose N.grade y).support, (x n).val, ?_⟩
    rw [map_sum]
    simp_rw [show ∀ n, f.linearMap (x n).val = (DirectSum.decompose N.grade y n).val
      from fun n => congrArg Subtype.val (hx n)]
    exact DirectSum.sum_support_decompose N.grade y
  · rintro ⟨x, rfl⟩
    apply (DirectSum.decompose P.grade).injective
    ext n
    rw [decompose_natural, decompose_natural, DirectSum.decompose_zero,
      DirectSum.zero_apply]
    exact congrArg Subtype.val ((he n (gradeMap f n (DirectSum.decompose M.grade x n))).mpr ⟨_, rfl⟩)

private theorem comodule_zero_linearMap [z : HasZeroMorphisms GradedSteenrodComodule]
    (M N : GradedSteenrodComodule) : (0 : M ⟶ N).linearMap = 0 := by
  let z₀ : HasZeroMorphisms GradedSteenrodComodule :=
    @Preadditive.preadditiveHasZeroMorphisms GradedSteenrodComodule _ inferInstance
  have hz : z = z₀ := Subsingleton.elim _ _
  change (@HasZeroMorphisms.zero GradedSteenrodComodule _ z M N).zero.linearMap = 0
  rw [hz]
  rfl

private def comoduleKernelLift [HasZeroMorphisms GradedSteenrodComodule] {M N P K : GradedSteenrodComodule}
    (f : M ⟶ N) (g : N ⟶ P)
    (hi : Function.Injective f.linearMap)
    (he : ∀ n : ℤ, Function.Exact (gradeMap f n) (gradeMap g n))
    (k : K ⟶ N) (hk : k ≫ g = 0) : K ⟶ M := by
  have hk' : ∀ x, g.linearMap (k.linearMap x) = 0 := by
    intro x
    have h := congrArg (fun a : K ⟶ P => a.linearMap x) hk
    rw [comodule_zero_linearMap] at h
    change g.linearMap (k.linearMap x) = 0 at h
    exact h
  have hrange : ∀ x, k.linearMap x ∈ f.linearMap.range := by
    intro x
    exact (total_exact f g he _).mp (hk' x)
  let l := LinearMap.codRestrictOfInjective k.linearMap f.linearMap hi hrange
  have hl : f.linearMap ∘ₗ l = k.linearMap := LinearMap.codRestrictOfInjective_comp ..
  refine ⟨l, ?_, ?_⟩
  · intro n x hx
    have hkgrade := k.graded n x hx
    have hkg : gradeMap g n ⟨k.linearMap x, hkgrade⟩ = 0 :=
      Subtype.ext (hk' x)
    obtain ⟨y, hy⟩ := (he n _).mp hkg
    have hy' : f.linearMap y = k.linearMap x := congrArg Subtype.val hy
    have hly : l x = y := hi ((LinearMap.congr_fun hl x).trans hy'.symm)
    rw [hly]
    exact y.property
  · apply LinearMap.ext
    intro x
    apply Module.Flat.lTensor_preserves_injective_linearMap f.linearMap hi
    have hmaps : f.linearMap.lTensor DualSteenrod ∘ₗ
        (l.lTensor DualSteenrod ∘ₗ K.rho) =
        f.linearMap.lTensor DualSteenrod ∘ₗ (M.rho ∘ₗ l) := by
      calc
        _ = (f.linearMap ∘ₗ l).lTensor DualSteenrod ∘ₗ K.rho := by
          rw [LinearMap.lTensor_comp, LinearMap.comp_assoc]
        _ = k.linearMap.lTensor DualSteenrod ∘ₗ K.rho := by rw [hl]
        _ = N.rho ∘ₗ k.linearMap := k.coaction
        _ = (f.linearMap.lTensor DualSteenrod ∘ₗ M.rho) ∘ₗ l := by
          rw [f.coaction, LinearMap.comp_assoc, hl]
        _ = _ := LinearMap.comp_assoc ..
    exact LinearMap.congr_fun hmaps x

private theorem comoduleKernelLift_fac [HasZeroMorphisms GradedSteenrodComodule] {M N P K : GradedSteenrodComodule}
    (f : M ⟶ N) (g : N ⟶ P)
    (hi : Function.Injective f.linearMap)
    (he : ∀ n : ℤ, Function.Exact (gradeMap f n) (gradeMap g n))
    (k : K ⟶ N) (hk : k ≫ g = 0) :
    comoduleKernelLift f g hi he k hk ≫ f = k := by
  apply GradedSteenrodComodule.Hom.ext
  exact LinearMap.codRestrictOfInjective_comp ..

private theorem comoduleMono {M N : GradedSteenrodComodule} (f : M ⟶ N)
    (hi : Function.Injective f.linearMap) : Mono f := by
  constructor
  intro Z g h hgh
  apply GradedSteenrodComodule.Hom.ext
  apply LinearMap.ext
  intro x
  apply hi
  exact congrArg (fun k : Z ⟶ N => k.linearMap x) hgh

private theorem comoduleEpi {M N : GradedSteenrodComodule} (f : M ⟶ N)
    (hs : Function.Surjective f.linearMap) : Epi f := by
  constructor
  intro Z g h hgh
  apply GradedSteenrodComodule.Hom.ext
  apply LinearMap.ext
  intro y
  obtain ⟨x, rfl⟩ := hs y
  exact congrArg (fun k : M ⟶ Z => k.linearMap x) hgh


section
variable [A : Abelian GradedSteenrodComodule]
local instance : Preadditive GradedSteenrodComodule := A.toPreadditive
private theorem comodule_shortExact
    (S : ShortComplex GradedSteenrodComodule)
    (hi : ∀ n : ℤ, Function.Injective (gradeMap S.f n))
    (he : ∀ n : ℤ, Function.Exact (gradeMap S.f n) (gradeMap S.g n))
    (hs : ∀ n : ℤ, Function.Surjective (gradeMap S.g n)) :
    S.ShortExact := by
  have hf := total_injective S.f hi
  haveI : Mono S.f := comoduleMono S.f hf
  haveI : Epi S.g := comoduleEpi S.g (total_surjective S.g hs)
  refine ⟨S.exact_of_f_is_kernel ?_⟩
  refine KernelFork.IsLimit.ofι S.f S.zero
    (fun k hk => comoduleKernelLift S.f S.g hf he k hk)
    (fun k hk => comoduleKernelLift_fac S.f S.g hf he k hk) ?_
  intro K k hk m hm
  apply (cancel_mono S.f).mp
  rw [hm, comoduleKernelLift_fac]

end

/-- Degreewise HF2 short exactness of the same rotated triangle induces
short exactness in the fixed graded comodule category. The proof uses the
registered homology source and canonical abelian structure. -/
public theorem cofiberHomologyShortComplex_shortExact
    (T : TriangleData model.auxiliary)
    (hH : HomologyShortExact coefficients (Triangle.mk T.f T.g T.h).rotate) :
    (cofiberHomologyShortComplex T).ShortExact := by
  letI : Abelian GradedSteenrodComodule := steenrodComoduleAbelian
  let hd := canonicalHomologyComoduleSource.degree
  have hn {X Y : Spectrum} (f : X ⟶ Y) (n : ℤ)
      (x : (homologyComodule.obj X).grade n) :
      hd Y n (gradeMap (homologyComodule.map f) n x) =
        modTwoHomologyMap coefficients f n (hd X n x) :=
    canonicalHomologyComoduleSource.natural f n x
  have hh (n : ℤ) :
      Function.Injective (modTwoHomologyMap coefficients T.g n) ∧
      Function.Exact (modTwoHomologyMap coefficients T.g n)
        (modTwoHomologyMap coefficients T.h n) ∧
      Function.Surjective (modTwoHomologyMap coefficients T.h n) := hH n
  apply comodule_shortExact
  all_goals dsimp only [cofiberHomologyShortComplex]
  · intro n x y hxy
    apply (hd _ n).injective
    apply (hh n).1
    rw [← hn, ← hn]
    exact congrArg (hd _ n) hxy
  · intro n y
    constructor
    · intro hy
      have hy' := congrArg (hd _ n) hy
      rw [hn, map_zero] at hy'
      obtain ⟨x, hx⟩ := ((hh n).2.1 _).mp hy'
      refine ⟨(hd _ n).symm x, ?_⟩
      apply (hd _ n).injective
      rw [hn, AddEquiv.apply_symm_apply]
      exact hx
    · rintro ⟨x, rfl⟩
      apply (hd _ n).injective
      rw [hn, hn, map_zero]
      exact ((hh n).2.1 _).mpr ⟨_, rfl⟩
  · intro n z
    obtain ⟨y, hy⟩ := (hh n).2.2 (hd _ n z)
    refine ⟨(hd _ n).symm y, ?_⟩
    apply (hd _ n).injective
    rw [hn, AddEquiv.apply_symm_apply]
    exact hy

/-- The genuine connecting map of the same homology SES, transported to
the fixed Adams E2 coordinates. Its definition uses the SES extension class. -/
@[no_expose] public def cofiberExtBoundary
    (T : TriangleData model.auxiliary)
    (hH : HomologyShortExact coefficients (Triangle.mk T.f T.g T.h).rotate)
    (s t : ℤ) (x : (classical.obj (T.X.obj auxiliary)).Page 2 (s,t)) :
    (classical.obj (T.Y.obj auxiliary)).Page 2 (s+1,t+1) :=
  (e2ExtEquiv T.Y (s+1) (t+1)).symm
    (IntExt.sesBoundary (C := SteenrodComodule) (cofiberHomologyShortComplex T)
      (cofiberHomologyShortComplex_shortExact T hH)
      (homologyComodule.obj (Sphere (t+1))) s (suspendedE2ExtEquiv T.X s t x))

end
end KIP126.AdamsSynthetic.Standard
