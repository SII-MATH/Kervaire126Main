module

public import KIP126.Literature.Standard.Sphere.Algebra.Data
public import KIP126.Def.ClassicalAdams.SphereAlgebra.Proofs
public import KIP126.Computation.LinCoordinates.Model.Classes.Data
public import KIP126.Computation.WellFormedness.LinCoordinates.RelationAlgebra.Grading
public import Mathlib.LinearAlgebra.BilinearMap

@[expose] public section

/-! A graded linear comparison from the relation algebra to the sphere E₂
algebra, preserving multiplication and the unit, and bijective in internal
degrees at most 261. The truncated quotient gives the same coordinates
within that range. Differential assertions are separate hypotheses. -/

namespace KIP126.Classical.Adams
open KIP126.Algebra KIP126.LinE2 Sphere.Internal

noncomputable section

/-- Restrict one global map to a homogeneous component, using the injective
inclusion of the *same* actual page into its total direct sum. -/
def linE2ComponentMap (f : RelationAlgebra →ₗ[F2] ActualE2Total)
    (hf : ∀ s t (x : RelationAt s t),
      f x.val ∈ LinearMap.range (embed (s, t))) (s t : ℕ) :
    RelationAt s t →ₗ[F2] ActualE2At (s, t) :=
  LinearMap.codRestrictOfInjective
    (f.comp (relationHomogeneousPart s t).subtype)
    (embed (s, t)) (KIP126.Classical.Adams.Sphere.Algebra.embed_injective KIP126.Def.standardHF2AdamsContext (s, t)) (hf s t)

/-- The original-relation quotient maps globally to the fixed actual sphere E₂.
All natural bidegrees are retained. Only bijectivity has the bound t ≤ 261.
In particular, the actual multiplication is fixed in Def before this object. -/
structure LinE2Presentation where
  toActual : RelationAlgebra →ₗ[F2] ActualE2Total
  preservesDegree : ∀ s t (x : RelationAt s t),
    toActual x.val ∈ LinearMap.range (embed (s, t))
  component_bijective : ∀ (s t : ℕ), t ≤ 261 →
    Function.Bijective (linE2ComponentMap toActual preservesDegree s t)
  preservesMul : ∀ x y : RelationAlgebra,
    toActual (x * y) = toActual x * toActual y
  preservesOne : toActual 1 = embed 0 actualE2Unit

namespace LinE2Presentation

/-- The component map is derived from the single global linear map. -/
abbrev component (P : LinE2Presentation) (s t : ℕ) :=
  linE2ComponentMap P.toActual P.preservesDegree s t

/-- The relation-algebra comparison is an equivalence in internal degree at most 261. -/
def relationComparison (P : LinE2Presentation) (s t : ℕ) (ht : t ≤ 261) :
    RelationAt s t ≃ₗ[F2] ActualE2At (s, t) :=
  LinearEquiv.ofBijective (P.component s t) (P.component_bijective s t ht)

/-- The bounded comparison from the truncated quotient to the sphere E₂ page,
obtained through the relation-algebra comparison and the truncation equivalence. -/
def comparison (P : LinE2Presentation) (s t : ℕ) (ht : t ≤ 261) :
    E2At s t ≃ₗ[ℤ] sphereAdamsData.Page 2 ((s : ℤ), (t : ℤ)) :=
  ((truncateAtEquiv s t ht).symm.trans (P.relationComparison s t ht)).restrictScalars ℤ

/-- Compatibility name for the fixed actual product. It does not select an
operation and is independent of the presentation. -/
def product (_P : LinE2Presentation) (s t s' t' : ℕ) :
    sphereAdamsData.Page 2 ((s : ℤ), (t : ℤ)) →ₗ[ℤ]
    sphereAdamsData.Page 2 ((s' : ℤ), (t' : ℤ)) →ₗ[ℤ]
      sphereAdamsData.Page 2 (((s + s' : ℕ) : ℤ), ((t + t' : ℕ) : ℤ)) :=
  by
    let f := (actualE2Product (s, t) (s', t')).restrictScalars₁₂ ℤ ℤ
    exact { f.toAddMonoidHom with
      map_smul' := fun n x => map_intCast_smul f.toAddMonoidHom ℤ ℤ n x }

end LinE2Presentation
end
end KIP126.Classical.Adams
