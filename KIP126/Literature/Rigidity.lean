module

public import KIP126.AdamsSynthetic

/-! BHS/KIP Appendix A rigidity on the same chosen ν-family.
Adapted from the fixed KIPBase Rigidity / AdamsLambdaInversion contracts
(5aa845241533), with the actual E₂ comparison and object closure retained.
No comparison is promoted to an isomorphism outside its stated free range. -/

@[expose] section
set_option autoImplicit false
namespace KIP126.Literature
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route
universe u v w
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w,v} Syn]
  [HasFunctorialCofiber (C := Syn)] (D : Model C Syn)

public def classicalDifferential (X : ClassicalObject) (r s t : ℤ) :
    (D.classical.obj (X.obj D.auxiliary)).Page r (s,t) ⟶
      (D.classical.obj (X.obj D.auxiliary)).Page r (s+r,t+r-1) :=
  (D.classical.obj (X.obj D.auxiliary)).d r (s,t) ≫ eqToHom
    (congrArg ((D.classical.obj (X.obj D.auxiliary)).Page r) (by
    rw [D.classical.differentialDegree]
    ext <;> simp <;> omega))

public def syntheticDifferential (X : ClassicalObject) (r s t w : ℤ) :
    (D.family.nu D.nu (X.obj D.auxiliary)).Page r (s,t,w) ⟶
      (D.family.nu D.nu (X.obj D.auxiliary)).Page r (s+r,t+r-1,w) :=
  (D.family.nu D.nu (X.obj D.auxiliary)).d r (s,t,w) ≫ eqToHom (by
    congr 1
    ext <;> simp [syntheticAdamsRawShift] <;> omega)

/-- Suspension coordinates for the actual ν-family; λ below is the actual
functorial map of the already supplied deformation transformation. -/
public structure NuPageCoordinates where
  weightShift : ∀ (X : ClassicalObject) (r s t w : ℤ),
    (D.family.nu D.nu (X.obj D.auxiliary)).Page r (s,t,w) ≅
      (D.family.obj ((SyntheticCategory.biShift (0,-1)).obj
        (D.nu.functor.obj (X.obj D.auxiliary)))).Page r (s,t,w-1)
  e2 : ∀ (X : ClassicalObject) (s t : ℤ) (k : ℕ)
      (x : (D.classical.obj (X.obj D.auxiliary)).Page 2 (s,t)),
    HEq ((weightShift X 2 s t (t-k)).hom (targetNuLabel D X s t k x))
      (D.comparison.nuE2 X (-1) s t k x)

public def NuPageCoordinates.lambda (P : NuPageCoordinates D)
    (X : ClassicalObject) (r s t w : ℤ) :
    (D.family.nu D.nu (X.obj D.auxiliary)).Page r (s,t,w) ⟶
      (D.family.nu D.nu (X.obj D.auxiliary)).Page r (s,t,w-1) :=
  (P.weightShift X r s t w).hom ≫
    D.family.pageMap (SyntheticCategory.lam.app (D.nu.functor.obj (X.obj D.auxiliary)))
      r (s,t,w-1)

/-- The free component identifies directly with the actual classical page.
This eliminates an independently selected generator object. -/
public structure FreeLambdaPages (P : NuPageCoordinates D) where
  component : ∀ (X : ClassicalObject) (r : ℤ) (_hr : 2 ≤ r)
    (s t w : ℤ) (_h : r-2 ≤ t-w),
    (D.family.nu D.nu (X.obj D.auxiliary)).Page r (s,t,w) ≅
      (D.classical.obj (X.obj D.auxiliary)).Page r (s,t)
  e2 : ∀ (X : ClassicalObject) (s t w : ℤ) (hw : w ≤ t)
      (x : (D.classical.obj (X.obj D.auxiliary)).Page 2 (s,t)),
    (component X 2 (by omega) s t w (by omega)).hom (nuWeightLabel D X s t w hw x) = x
  lambda : ∀ (X : ClassicalObject) (r : ℤ) (hr : 2 ≤ r)
      (s t w : ℤ) (h : r-2 ≤ t-w),
    P.lambda D X r s t w ≫ (component X r hr s t (w-1) (by omega)).hom =
      (component X r hr s t w h).hom
  differential : ∀ (X : ClassicalObject) (r : ℤ) (hr : 2 ≤ r)
      (s t w : ℤ) (h : r-2 ≤ t-w),
    syntheticDifferential D X r s t w ≫
        (component X r hr (s+r) (t+r-1) w (by omega)).hom =
      (component X r hr s t w h).hom ≫ classicalDifferential D X r s t

/-- A specified classical page class has a canonical lift in the free range. -/
public def FreeLambdaPages.classicalLift {P : NuPageCoordinates D} (F : FreeLambdaPages D P)
    (X : ClassicalObject) (r : ℤ) (hr : 2 ≤ r) (s t w : ℤ) (h : r-2 ≤ t-w)
    (x : (D.classical.obj (X.obj D.auxiliary)).Page r (s,t)) :
    (D.family.nu D.nu (X.obj D.auxiliary)).Page r (s,t,w) :=
  (F.component X r hr s t w h).inv x

/-- Differential translation follows from the supplied comparison equation. -/
public theorem FreeLambdaPages.classicalLift_differential {P : NuPageCoordinates D}
    (F : FreeLambdaPages D P) (X : ClassicalObject) (r : ℤ) (hr : 2 ≤ r)
    (s t w : ℤ) (h : r-2 ≤ t-w)
    (x : (D.classical.obj (X.obj D.auxiliary)).Page r (s,t)) :
    syntheticDifferential D X r s t w (F.classicalLift D X r hr s t w h x) =
      F.classicalLift D X r hr (s+r) (t+r-1) w (by omega)
        (classicalDifferential D X r s t x) := by
  have eqn := congrArg (fun f => f ((F.component X r hr s t w h).inv x))
    (F.differential X r hr s t w h)
  have lifted := congrArg (fun z => (F.component X r hr (s+r) (t+r-1) w (by omega)).inv z) eqn
  simpa [classicalLift] using lifted

public theorem FreeLambdaPages.classicalLift_lambda {P : NuPageCoordinates D}
    (F : FreeLambdaPages D P) (X : ClassicalObject) (r : ℤ) (hr : 2 ≤ r)
    (s t w : ℤ) (h : r-2 ≤ t-w)
    (x : (D.classical.obj (X.obj D.auxiliary)).Page r (s,t)) :
    P.lambda D X r s t w (F.classicalLift D X r hr s t w h x) =
      F.classicalLift D X r hr s t (w-1) (by omega) x := by
  have eqn := congrArg (fun f => f ((F.component X r hr s t w h).inv x))
    (F.lambda X r hr s t w h)
  have lifted := congrArg (fun z => (F.component X r hr s t (w-1) (by omega)).inv z) eqn
  simpa [classicalLift] using lifted

/-- The map induced by a nested-data comparison, using the fixed first page. -/
public def comparisonPageMap (X : ClassicalObject)
    (F : SSDataMorphism Tridegree
      (D.family.nu D.nu (X.obj D.auxiliary)).sequence.ssData
      (fun i => (D.classical.obj (X.obj D.auxiliary)).ssData (i.1,i.2.1)))
    (r s t w : ℤ) :
    (D.family.nu D.nu (X.obj D.auxiliary)).Page r (s,t,w) ⟶
      (D.classical.obj (X.obj D.auxiliary)).Page r (s,t) :=
  eqToHom (by simp [SyntheticAdamsSS.Page, Page, SyntheticAdamsFamily.nu,
    SyntheticAdamsFamily.obj, D.family.firstPage]) ≫
    F.pageMap (s,t,w) (↑(r-2).toNat) ≫
    eqToHom (by simp [Page, D.classical.firstPage])

/-- A full filtered-data comparison. Preservation of every Z and B gives
common-representative compatibility at all pages, not just unrelated maps. -/
public structure LambdaInversionComparison (P : NuPageCoordinates D) where
  data : ∀ X : ClassicalObject,
    SSDataMorphism Tridegree
      (D.family.nu D.nu (X.obj D.auxiliary)).sequence.ssData
      (fun i => (D.classical.obj (X.obj D.auxiliary)).ssData (i.1,i.2.1))
  e2 : ∀ (X : ClassicalObject) (s t w : ℤ) (hw : w ≤ t)
      (x : (D.classical.obj (X.obj D.auxiliary)).Page 2 (s,t)),
    comparisonPageMap D X (data X) 2 s t w (nuWeightLabel D X s t w hw x) = x
  differential : ∀ (X : ClassicalObject) (r : ℤ) (hr : 2 ≤ r) (s t w : ℤ),
    let map := fun s t => comparisonPageMap D X (data X) r s t w
    syntheticDifferential D X r s t w ≫ map (s+r) (t+r-1) =
      map s t ≫ classicalDifferential D X r s t
  lambda : ∀ (X : ClassicalObject) (r : ℤ) (hr : 2 ≤ r) (s t w : ℤ),
    let map := fun w => comparisonPageMap D X (data X) r s t w
    P.lambda D X r s t w ≫ map (w-1) = map w

/-- All truncated E₂ components, including the zero regions. -/
public def quotientE2Component (X : ClassicalObject) (n : ℕ) (s t w : ℤ) : ModuleCat.{v} ℤ :=
  if 0 ≤ t-w ∧ t-w < n then (D.classical.obj (X.obj D.auxiliary)).Page 2 (s,t)
  else ModuleCat.of ℤ PUnit.{v+1}

/-- The actual quotient map is an isomorphism only in the retained strip
or the stated later-page safe range. -/
public structure NuModLambdaPageData (X : ClassicalObject) (n : ℕ) where
  component : ∀ s t w : ℤ,
    (D.family.quotient (D.nu.functor.obj (X.obj D.auxiliary)) n).Page 2 (s,t,w) ≅
      quotientE2Component D X n s t w
  component_retained : ∀ (s t w : ℤ) (h : 0 ≤ t-w ∧ t-w < n)
      (x : (D.classical.obj (X.obj D.auxiliary)).Page 2 (s,t)),
    HEq ((component s t w).hom
      ((D.family.quotientProjection (D.nu.functor.obj (X.obj D.auxiliary)) n).pageMap
        2 (s,t,w) (nuWeightLabel D X s t w (by omega) x))) x
  retained : ∀ (s t w : ℤ), 0 ≤ t-w ∧ t-w < n →
    IsIso ((D.family.quotientProjection (D.nu.functor.obj (X.obj D.auxiliary)) n).pageMap 2 (s,t,w))
  safe : ∀ (r s t w : ℤ), 2 ≤ r → 0 ≤ t-w → t-w+r-2 < n →
    IsIso ((D.family.quotientProjection (D.nu.functor.obj (X.obj D.auxiliary)) n).pageMap r (s,t,w))

private structure RigidityBindings where
  pages : NuPageCoordinates D
  free : FreeLambdaPages D pages
  inversion : LambdaInversionComparison D pages
  free_inversion : ∀ (X : ClassicalObject) (r : ℤ) (hr : 2 ≤ r)
    (s t w : ℤ) (h : r-2 ≤ t-w),
    (free.component X r hr s t w h).hom = comparisonPageMap D X (inversion.data X) r s t w
  weights : NuInfinityWeightMaps D

private structure RigidityResults (B : RigidityBindings D) where
  degeneration : ∀ (X : ClassicalObject) (N : ℤ),
    DegeneratesAt (D.classical.obj (X.obj D.auxiliary)) N →
    DegeneratesAt (D.family.nu D.nu (X.obj D.auxiliary)).sequence N
  above_diagonal : ∀ (X : ClassicalObject) (r : ℤ), 2 ≤ r →
    ∀ (s t w : ℤ), t < w → IsZero ((D.family.nu D.nu (X.obj D.auxiliary)).Page r (s,t,w))
  finite_quotient : ∀ (X : ClassicalObject) (n : ℕ), 0 < n → NuModLambdaPageData D X n
  finite_quotient_vanishing : ∀ (X : ClassicalObject) (n : ℕ), 0 < n →
    ∀ (r : ℤ), 2 ≤ r → ∀ (s t w : ℤ), (t-w < 0 ∨ (n : ℤ) ≤ t-w) →
      IsZero ((D.family.quotient (D.nu.functor.obj (X.obj D.auxiliary)) n).Page r (s,t,w))

end
end KIP126.Literature
