module

public import KIP126.Def.AdamsSynthetic.Families
public import KIP126.Def.AdamsSynthetic.Configuration

/-! Comparisons use the same classical family, synthetic family and ν.
Only the specified E₂ components are compared; no later-page equivalence
or rigidity theorem is asserted by this interface. Adapted from the fixed
review baseline's Route.ModelData and ComparisonCompatible. -/

@[expose] section
namespace KIP126.AdamsSynthetic

open CategoryTheory KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.Classical.Adams KIP126.Synthetic.SpectralSequence KIP126.Kervaire.Route

universe u v w
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w,v} Syn]
  [HasFunctorialCofiber (C := Syn)]

/-- Selected E₂ labels on one pair of systems. The equations bind the
chosen comparisons to the actual ν, unit isomorphism and λ maps. -/
public structure E2Comparison
    (A : ClassicalAdamsFamily C) (F : SyntheticAdamsFamily Syn)
    (N : NuFunctorData C Syn) (aux : AuxiliaryData C) where
  nuE2 : ∀ (X : ClassicalObject) (a s t : ℤ) (k : ℕ),
    (A.obj (X.obj aux)).Page 2 (s,t) ≃ₗ[ℤ]
      (F.obj ((SyntheticCategory.biShift (0,a)).obj
        (N.functor.obj (X.obj aux)))).sequence.Page 2 (s,t,t+a-k)
  sphereE2 : ∀ (s t : ℤ) (k : ℕ),
    A.sphere.Page 2 (s,t) ≃ₗ[ℤ] F.sphere.sequence.Page 2 (s,t,t-k)
  sphere_nu : ∀ (s t : ℤ) (k : ℕ) (x : A.sphere.Page 2 (s,t)),
    (F.functor.map (SyntheticCategory.biShift_zero.hom.app _ ≫ N.unitIso.hom)).pageMap
      2 (s,t,t-k) (by simpa only [add_zero, ClassicalObject.obj, SyntheticAdamsFamily.obj] using nuE2 .sphere 0 s t k x) = sphereE2 s t k x
  nu_natural : ∀ (X Y : ClassicalObject) (f : X.obj aux ⟶ Y.obj aux)
      (a s t : ℤ) (k : ℕ) (x : (A.obj (X.obj aux)).Page 2 (s,t)),
    (F.functor.map ((SyntheticCategory.biShift (0,a)).map (N.functor.map f))).pageMap
      2 (s,t,t+a-k) (nuE2 X a s t k x) =
      nuE2 Y a s t k ((A.functor.map f).pageMap 2 (s,t) x)
  nu_lambda : ∀ (X : ClassicalObject) (s t : ℤ) (k : ℕ)
      (x : (A.obj (X.obj aux)).Page 2 (s,t)),
    HEq ((F.functor.map (SyntheticCategory.lam.app (N.functor.obj (X.obj aux)))).pageMap
      2 (s,t,t-1-k) (nuE2 X (-1) s t k x))
      (nuE2 X 0 s t (k+1) x)

/-- The given ν takes the specified triangle to a triangle only under the
stated exactness premise. This preserves the backup declaration's actual
Function.Exact hypothesis, rather than strengthening its prose to a short
exact sequence or unconditional preservation of triangles. -/
public structure NuExactTriangleInput (H : ModTwoCoefficients C) (N : NuFunctorData C Syn) where
  preserves : ∀ (T : CategoryTheory.Pretriangulated.Triangle C),
    T ∈ distTriang C →
    (∀ n, Function.Exact
      (inducedMap (MonoidalCategory.whiskerLeft H.object T.mor₁) n)
      (inducedMap (MonoidalCategory.whiskerLeft H.object T.mor₂) n)) →
    ∃ h : N.functor.obj T.obj₃ ⟶ (shiftFunctor Syn (1 : ℤ)).obj (N.functor.obj T.obj₁),
      CategoryTheory.Pretriangulated.Triangle.mk
        (N.functor.map T.mor₁) (N.functor.map T.mor₂) h ∈
          distTriang Syn

end KIP126.AdamsSynthetic
