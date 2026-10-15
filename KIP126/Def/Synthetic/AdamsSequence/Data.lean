module

public import KIP126.Def.ClassicalAdams.Grading.Data
public import Mathlib.Data.Int.Basic
public import KIP126.Def.SpectralSequence.Basic.Category.Data
public import KIP126.Def.SpectralSequence.Basic.PageHomology.Data
public import KIP126.Def.SpectralSequence.Convergence.Data
public import KIP126.Def.Synthetic.Sphere.Data
public import Mathlib.Algebra.Category.ModuleCat.Abelian

@[expose] public section

/-!
# Internal synthetic Adams objects

All spectral sequences here use the internal nested-subobject model. A family
is explicit functor data on one synthetic category; its values at νX and at a
λ-power cofiber define the respective spectral sequences. No family or convergence
witness is chosen globally, and no Mathlib spectral-sequence comparison is
required. Construction of the family and its literature properties remain
separate obligations.
-/

namespace KIP126.Synthetic.SpectralSequence

open CategoryTheory CategoryTheory.Limits
open KIP126.SpectralSequence KIP126.Synthetic.Context KIP126.StableHomotopy

universe u v u' v'
noncomputable section

abbrev Tridegree := ℤ × ℤ × ℤ

/-! 合成 Adams 微分在整数页 r 上的三次数为 (r, r - 1, 0)。 -/
def syntheticAdamsDifferentialDegree (r : ℤ) : Tridegree := (r, r - 1, 0)

def syntheticAdamsDifferentialTarget (r : ℤ) (i : Tridegree) : Tridegree :=
  i + syntheticAdamsDifferentialDegree r

abbrev SyntheticAdamsSpectralSequence :=
  KIP126.SpectralSequence (ModuleCat.{v} ℤ) Tridegree

/-- An internal sequence with exactly the synthetic Adams page convention.
Standard classes and a λ action are not chosen independently in this record. -/
structure SyntheticAdamsSS where
  sequence : SyntheticAdamsSpectralSequence.{v}
  firstPage : sequence.r₀ = 2
  differentialDegree : ∀ r : ℤ, sequence.diffDeg r = syntheticAdamsDifferentialDegree r

namespace SyntheticAdamsSS

/-- Normalized page accessor; its cycle level is always `(r - 2).toNat`. -/
def Page (A : SyntheticAdamsSS.{v}) (r : ℤ) (i : Tridegree) : ModuleCat.{v} ℤ :=
  (A.sequence.ssData i).page (↑(r - 2).toNat : WithTop ℕ)

def E₂ (A : SyntheticAdamsSS.{v}) := A.Page 2

/-- The actual internal differential, with only its proven degree transported. -/
def d (A : SyntheticAdamsSS.{v}) (r : ℤ) (i : Tridegree) :
    A.Page r i ⟶ A.Page r (syntheticAdamsDifferentialTarget r i) :=
  eqToHom (by simp only [Page, A.firstPage]) ≫
    A.sequence.d r i ≫ eqToHom (by
      simp only [Page, A.firstPage, A.differentialDegree, syntheticAdamsDifferentialTarget])

end SyntheticAdamsSS

/-- The fixed-weight graded page of the same internal sequence. -/
def fixedWeightPage (A : SyntheticAdamsSS.{v}) (w r : ℤ)
    (b : KIP126.Classical.Adams.Bidegree) : ModuleCat.{v} ℤ :=
  A.Page r (b.1, b.2, w)

/-- The same internal differential restricted to a fixed weight. -/
def fixedWeightDifferential (A : SyntheticAdamsSS.{v}) (w r : ℤ)
    (b : KIP126.Classical.Adams.Bidegree) :
    fixedWeightPage A w r b ⟶ fixedWeightPage A w r (b + (r, r - 1)) :=
  A.d r (b.1, b.2, w) ≫ eqToHom (by
    unfold fixedWeightPage syntheticAdamsDifferentialTarget syntheticAdamsDifferentialDegree
    congr 1
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · exact add_zero w)

/-- A single functor on the chosen synthetic category, with the Adams grading
fixed on every object. Its existence and construction are not postulated. -/
structure SyntheticAdamsFamily (Syn : Type u) [SyntheticCategory.{u, v} Syn] where
  functor : Syn ⥤ KIP126.SpectralSequence (ModuleCat.{v} ℤ) Tridegree
  firstPage : ∀ X, (functor.obj X).r₀ = 2
  differentialDegree : ∀ X r, (functor.obj X).diffDeg r = syntheticAdamsDifferentialDegree r

namespace SyntheticAdamsFamily

variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]

def obj (F : SyntheticAdamsFamily Syn) (X : Syn) : SyntheticAdamsSS.{v} where
  sequence := F.functor.obj X
  firstPage := F.firstPage X
  differentialDegree := F.differentialDegree X

/-- The same family on the synthetic sphere; no independently chosen sequence. -/
def sphere (F : SyntheticAdamsFamily Syn) : SyntheticAdamsSS.{v} :=
  F.obj S_0_0

/-- Evaluate the family on the actual ν-image. -/
def nu {Stable : Type u'} [StableHomotopyCategory.{u', v'} Stable]
    (F : SyntheticAdamsFamily Syn) (N : NuFunctorData Stable Syn) (X : Stable) :
    SyntheticAdamsSS.{v} := F.obj (N.functor.obj X)

/-- Evaluate the family on the chosen cofiber of the same λ power. -/
def quotient [HasFunctorialCofiber (C := Syn)]
    (F : SyntheticAdamsFamily Syn) (X : Syn) (n : ℕ) : SyntheticAdamsSS.{v} :=
  F.obj (XModLambdaN X n)

def nuQuotient {Stable : Type u'} [StableHomotopyCategory.{u', v'} Stable]
    [HasFunctorialCofiber (C := Syn)] (F : SyntheticAdamsFamily Syn)
    (N : NuFunctorData Stable Syn) (X : Stable) (n : ℕ) : SyntheticAdamsSS.{v} :=
  F.quotient (N.functor.obj X) n

/-- The quotient projection is the image of the actual cofiber inclusion. -/
def quotientProjection [HasFunctorialCofiber (C := Syn)]
    (F : SyntheticAdamsFamily Syn) (X : Syn) (n : ℕ) :
    (F.obj X).sequence ⟶ (F.quotient X n).sequence :=
  F.functor.map (HasFunctorialCofiber.cofibι (lambdaPow n X))

end SyntheticAdamsFamily

/-- The abutment is the actual bigraded homotopy of the given object. -/
def syntheticHomotopy {Syn : Type u} [SyntheticCategory.{u, v} Syn]
    (X : Syn) (p : ℤ × ℤ) : ModuleCat.{v} ℤ :=
  ModuleCat.of ℤ (BiHom p.1 p.2 X)

/-- A convergence witness for a particular object in the same family. This is
supplied only where justified; arbitrary synthetic objects are not assumed to
converge. The grading is fixed to `E∞^(s,t,w) ≅ gr^s π_(t-s,w) X`. -/
structure SyntheticAdamsConvergence {Syn : Type u} [SyntheticCategory.{u, v} Syn]
    (F : SyntheticAdamsFamily Syn) (X : Syn) where
  filtration : Filtration (syntheticHomotopy X)
  identification : ∀ i : Tridegree,
    ((F.obj X).sequence.ssData i).eInfty ≅
      filtration.associatedGraded i.1 (i.2.1 - i.1, i.2.2)

/-- Express convergence for the given object as convergence of its spectral sequence. -/
def SyntheticAdamsConvergence.toConvergence
    {Syn : Type u} [SyntheticCategory.{u, v} Syn]
    {F : SyntheticAdamsFamily Syn} {X : Syn} (c : SyntheticAdamsConvergence F X) :
    Convergence (F.obj X).sequence (syntheticHomotopy X) c.filtration where
  reindex i := (i.1, i.2.1 - i.1, i.2.2)
  reindex_bijective := by
    constructor
    · rintro ⟨s, t, w⟩ ⟨s', t', w'⟩ h
      simp only [Prod.mk.injEq] at h ⊢
      exact ⟨h.1, by omega, h.2.2⟩
    · rintro ⟨s, m, w⟩
      exact ⟨(s, m + s, w), by simp⟩
  iso := c.identification

end
end KIP126.Synthetic.SpectralSequence
