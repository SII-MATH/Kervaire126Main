module

public import KIP126.Literature.Classical
import all KIP126.Literature.Classical

/-! The conditional normalized-triangle results of KIPBase/Synthetic/Lift
(5aa845241533), attached to the same maps and normalization exponents. -/

@[expose] section
set_option autoImplicit false
namespace KIP126.Literature
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.AdamsSynthetic
open KIP126.Kervaire.Route
universe u v w
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w,v} Syn]
  [HasFunctorialCofiber (C := Syn)] (D : Model C Syn)

/-- Third-vertex comparison for the actual normalized first arrow. -/
public structure NormalizedCofiberComparison (T : TriangleData D.auxiliary) where
  cofiber : HasFunctorialCofiber.cofib (D.normalizedMap T.X T.Y T.f).map ≅
    (SyntheticCategory.biShift (0,-(normalizedExponent D.classicalTower T.g : ℤ))).obj
      (D.nu.functor.obj (T.Z.obj D.auxiliary))

/-- The triangle's arrows are obtained from this comparison, so the cofiber
and connecting squares commute by construction. -/
public def NormalizedCofiberComparison.triangle {T : TriangleData D.auxiliary}
    (P : NormalizedCofiberComparison D T) : Triangle Syn :=
  Triangle.mk (D.normalizedMap T.X T.Y T.f).map
    (HasFunctorialCofiber.cofibι _ ≫ P.cofiber.hom)
    (P.cofiber.inv ≫ HasFunctorialCofiber.cofibδ _)

public theorem NormalizedCofiberComparison.distinguished {T : TriangleData D.auxiliary}
    (P : NormalizedCofiberComparison D T) : P.triangle D ∈ distTriang Syn := by
  refine isomorphic_distinguished _
    (HasFunctorialCofiber.cofib_distinguished (D.normalizedMap T.X T.Y T.f).map) _ ?_
  exact Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) P.cofiber.symm
    (by simp [triangle, Triangle.mk]) (by simp [triangle, Triangle.mk])
    (by simp [triangle, Triangle.mk])

/-- The unshifted triangle keeps the original exponent-sum hypothesis.
The old theorem supplies arrows, not identities with normalized arrows. -/
private structure NormalizedTriangleResults where
  unshifted : ∀ T : TriangleData D.auxiliary,
    normalizedExponent D.classicalTower T.f +
      normalizedExponent D.classicalTower T.g + normalizedExponent D.classicalTower T.h = 1 →
    ∃ (f : D.nu.functor.obj (T.X.obj D.auxiliary) ⟶ D.nu.functor.obj (T.Y.obj D.auxiliary))
      (g : D.nu.functor.obj (T.Y.obj D.auxiliary) ⟶ D.nu.functor.obj (T.Z.obj D.auxiliary))
      (h : D.nu.functor.obj (T.Z.obj D.auxiliary) ⟶
        (shiftFunctor Syn (1 : ℤ)).obj (D.nu.functor.obj (T.X.obj D.auxiliary))),
      Triangle.mk f g h ∈ distTriang Syn
  normalized_cofiber : ∀ T : TriangleData D.auxiliary, NormalizedCofiberComparison D T

/-- Reexpress a positive-source shift as a negative-target shift, using the
same synthetic shift comparisons. Source: Route/Triangles/Data at bbac1fc05843. -/
public def negativeLift {X Y : Syn} (k : ℕ)
    (f : (SyntheticCategory.biShift (0,(k : ℤ))).obj X ⟶ Y) :
    X ⟶ (SyntheticCategory.biShift (0,-(k : ℤ))).obj Y :=
  SyntheticCategory.biShift_zero.inv.app X ≫
    eqToHom (congrArg (fun p => (SyntheticCategory.biShift p).obj X)
      (show ((0 : ℤ),(0 : ℤ)) = (0,(k : ℤ))+(0,-(k : ℤ)) from by ext <;> simp)) ≫
    (SyntheticCategory.biShift_comp (0,(k : ℤ)) (0,-(k : ℤ))).inv.app X ≫
    (SyntheticCategory.biShift (0,-(k : ℤ))).map f

/-- The connecting arrow uses the model's selected top lift, including its
suspension and weight transport. -/
public def normalizedConnecting (T : TriangleData D.auxiliary)
    (he : (normalizedExponent D.classicalTower T.f : ℤ) +
      normalizedExponent D.classicalTower T.g + normalizedExponent D.classicalTower T.h = 1) :
    (SyntheticCategory.biShift (0,-(normalizedExponent D.classicalTower T.g : ℤ))).obj
      (D.nu.functor.obj (T.Z.obj D.auxiliary)) ⟶
    ((SyntheticCategory.biShift (0,(normalizedExponent D.classicalTower T.f : ℤ))).obj
      (D.nu.functor.obj (T.X.obj D.auxiliary)))⟦(1 : ℤ)⟧ :=
  let eg : ℤ := normalizedExponent D.classicalTower T.g
  let eh : ℤ := normalizedExponent D.classicalTower T.h
  let X := D.nu.functor.obj (T.X.obj D.auxiliary)
  (SyntheticCategory.biShift (0,-eg)).map
      (negativeLift (normalizedExponent D.classicalTower T.h)
        (D.normalizedMap T.Z (.shift 1 T.X) T.h).map) ≫
    (SyntheticCategory.biShift (0,-eg)).map
      ((SyntheticCategory.biShift (0,-eh)).map (D.nu.suspensionIso (T.X.obj D.auxiliary)).hom) ≫
    (SyntheticCategory.biShift (0,-eg)).map
      ((SyntheticCategory.biShift_comp (1,1) (0,-eh)).hom.app X) ≫
    (SyntheticCategory.biShift_comp ((1,1)+(0,-eh)) (0,-eg)).hom.app X ≫
    eqToHom (congrArg (fun p => (SyntheticCategory.biShift p).obj X)
      (show ((1,1)+(0,-eh))+(0,-eg) =
          (0,(normalizedExponent D.classicalTower T.f : ℤ))+(1,0) from by
        dsimp [eg, eh]; ext <;> simp only []; omega)) ≫
    (SyntheticCategory.biShift_comp (0,(normalizedExponent D.classicalTower T.f : ℤ)) (1,0)).inv.app X ≫
    (SyntheticCategory.biShift_compat (Syn := Syn) 1).hom.app _

/-- The three arrows are derived from the three normalized maps already
selected by D; distinguishedness is a separate comparison obligation. -/
public def normalizedTriangle (T : TriangleData D.auxiliary)
    (he : (normalizedExponent D.classicalTower T.f : ℤ) +
      normalizedExponent D.classicalTower T.g + normalizedExponent D.classicalTower T.h = 1) :
    Triangle Syn :=
  Triangle.mk (D.normalizedMap T.X T.Y T.f).map
    (negativeLift (normalizedExponent D.classicalTower T.g) (D.normalizedMap T.Y T.Z T.g).map)
    (normalizedConnecting D T he)

public def NormalizedTriangleCompatible (T : TriangleData D.auxiliary)
    (he : (normalizedExponent D.classicalTower T.f : ℤ) +
      normalizedExponent D.classicalTower T.g + normalizedExponent D.classicalTower T.h = 1) : Prop :=
  normalizedTriangle D T he ∈ distTriang Syn

/-- Sphere comparisons are constructed from this same ν's unit and suspension. -/
public def nuSphereOne : D.nu.functor.obj (Sphere (C := C) 1) ≅ Smn (Syn := Syn) 1 1 :=
  D.nu.suspensionIso SphereSpectrum ≪≫
    (SyntheticCategory.biShift (1,1)).mapIso D.nu.unitIso

public def nuSphereTwo : D.nu.functor.obj (Sphere (C := C) 2) ≅ Smn (Syn := Syn) 2 2 :=
  D.nu.functor.mapIso ((shiftFunctorAdd' C 1 1 2 (by norm_num)).app SphereSpectrum) ≪≫
    D.nu.suspensionIso (Sphere (C := C) 1) ≪≫
    (SyntheticCategory.biShift (1,1)).mapIso (nuSphereOne D) ≪≫
    (SyntheticCategory.biShift_comp (1,1) (1,1)).app S_0_0

public def nuSphereThree : D.nu.functor.obj (Sphere (C := C) 3) ≅ Smn (Syn := Syn) 3 3 :=
  D.nu.functor.mapIso ((shiftFunctorAdd' C 2 1 3 (by norm_num)).app SphereSpectrum) ≪≫
    D.nu.suspensionIso (Sphere (C := C) 2) ≪≫
    (SyntheticCategory.biShift (1,1)).mapIso (nuSphereTwo D) ≪≫
    (SyntheticCategory.biShift_comp (2,2) (1,1)).app S_0_0

/-- The Hopf ν is the normalized map actually selected by D. -/
public def normalizedNu (he : normalizedExponent D.classicalTower D.auxiliary.nuMap = 1) :
    BiHom 3 4 (S_0_0 : Syn) := by
  let e : (SyntheticCategory.biShift (0, (normalizedExponent D.classicalTower D.auxiliary.nuMap : ℤ))).obj
      (D.nu.functor.obj (Sphere (C := C) 3)) ≅ Smn (Syn := Syn) 3 4 := by
    rw [he]
    exact (SyntheticCategory.biShift (0,1)).mapIso (nuSphereThree D) ≪≫
      (SyntheticCategory.biShift_comp (3,3) (0,1)).app S_0_0
  exact e.inv ≫ (D.normalizedMap (.shift 3 .sphere) .sphere D.auxiliary.nuMap).map ≫
    D.nu.unitIso.hom

/-- Source-to-selected-model comparison for the actual Cν triangle, from
SourceLanguage:1190 at bbac1fc05843. The BHS geometric construction must be
bound to these three chosen maps. This is realization data, not a theorem
about arbitrary chosen lifts or an internal conclusion of the paper. -/
private structure NuCofiberApplicability : Prop where
  nu_exponent : normalizedExponent D.classicalTower D.auxiliary.nuMap = 1
  bottom_exponent : normalizedExponent D.classicalTower D.auxiliary.nuRouteTriangle.g = 0
  top_exponent : normalizedExponent D.classicalTower D.auxiliary.nuRouteTriangle.h = 0
  normalized_label : sphereFirstQuotient D 1 4 (quotientClass 1 (normalizedNu D nu_exponent)) =
    D.standardClasses.standardHi 2
  triangle : ∀ he :
      (normalizedExponent D.classicalTower D.auxiliary.nuRouteTriangle.f : ℤ) +
        normalizedExponent D.classicalTower D.auxiliary.nuRouteTriangle.g +
        normalizedExponent D.classicalTower D.auxiliary.nuRouteTriangle.h = 1,
    NormalizedTriangleCompatible D D.auxiliary.nuRouteTriangle he

/-- The needed exponent equation follows from the three supplied values. -/
private theorem NuCofiberApplicability.exponent_sum (A : NuCofiberApplicability D) :
    (normalizedExponent D.classicalTower D.auxiliary.nuRouteTriangle.f : ℤ) +
      normalizedExponent D.classicalTower D.auxiliary.nuRouteTriangle.g +
      normalizedExponent D.classicalTower D.auxiliary.nuRouteTriangle.h = 1 := by
  change (normalizedExponent D.classicalTower D.auxiliary.nuMap : ℤ) + _ + _ = 1
  rw [A.nu_exponent, A.bottom_exponent, A.top_exponent]
  norm_num

private theorem NuCofiberApplicability.distinguished (A : NuCofiberApplicability D) :
    normalizedTriangle D D.auxiliary.nuRouteTriangle (A.exponent_sum D) ∈ distTriang Syn :=
  A.triangle _

end
end KIP126.Literature
