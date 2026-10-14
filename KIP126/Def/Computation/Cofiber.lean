module

public import KIP126.Def.Computation.Route

/-! The same ν-cofiber and its actual bottom/top maps. Source comparison retains
all three summands of the reviewed d₃ source, not only its top-cell summand.
Adapted from Interpretation/Route/Predicates and Route/Consequences at bbac1fc. -/

@[expose] section
namespace KIP126.Computation
open CategoryTheory KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.Kervaire.Route KIP126.Classical.Adams KIP126.Core.SpectralSequence
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w,v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  {D : Model C Syn}

public abbrev cofiberSequence (D : Model C Syn) :=
  D.classical.obj (HasFunctorialCofiber.cofib D.auxiliary.nuMap)

/-- The actual bottom-cell map, evaluated by the given classical functor. -/
public noncomputable def bottom (D : Model C Syn) (s t : ℤ) :
    D.classical.sphere.Page 2 (s,t) →ₗ[ℤ] (cofiberSequence D).Page 2 (s,t) :=
  (D.classical.pageMap (HasFunctorialCofiber.cofibι D.auxiliary.nuMap) 2 (s,t)).hom

/-- The selected top-cell label has the correct image under the actual
connecting arrow and the four supplied tower desuspensions. -/
public def TopCellComparison (B : Bindings D)
    (x : (cofiberSequence D).Page 2 (8,134)) : Prop :=
  ∃ (a3 : (D.classical.obj (Sphere 3)).Page 2 (8,133))
    (a2 : (D.classical.obj (Sphere 2)).Page 2 (8,132))
    (a1 : (D.classical.obj (Sphere 1)).Page 2 (8,131)),
    (D.classicalSuspension (.shift 3 .sphere)).DesuspendsClass 8 134
      (D.classical.pageMap (HasFunctorialCofiber.cofibδ D.auxiliary.nuMap) 2 (8,134) x) a3 ∧
    (D.classicalSuspension (.shift 2 .sphere)).DesuspendsClass 8 133
      (D.classical.pageMap
        ((shiftFunctorAdd' C (2 : ℤ) 1 3 (by decide)).hom.app SphereSpectrum)
        2 (8,133) a3) a2 ∧
    (D.classicalSuspension (.shift 1 .sphere)).DesuspendsClass 8 132
      (D.classical.pageMap
        ((shiftFunctorAdd' C (1 : ℤ) 1 2 (by decide)).hom.app SphereSpectrum)
        2 (8,132) a2) a1 ∧
    (D.classicalSuspension .sphere).DesuspendsClass 8 131 a1 B.X

public structure CofiberBindings (B : Bindings D) where
  topCell : (cofiberSequence D).Page 2 (8,134)
  top_comparison : TopCellComparison B topCell

namespace CofiberBindings
variable {B : Bindings D} (Q : CofiberBindings B)

public noncomputable def source : (cofiberSequence D).Page 2 (8,134) :=
  Q.topCell + bottom D 8 134 (B.atom .x_126_8_2) + bottom D 8 134 (B.atom .x_126_8)

end CofiberBindings

/-- Finite cofiber data. No permanence of the target in Cν is asserted. -/
public structure CofiberResults (B : Bindings D) (Q : CofiberBindings B) : Prop where
  d3 : HasNonzeroDifferential (cofiberSequence D) 3 (8,134) (11,136)
    Q.source (bottom D 11 136 B.Y)
  target_to_e6 : SurvivesTo (cofiberSequence D) 6 (14,139) (bottom D 14 139 B.T)
  target_not_hit_through5 : NeverHitOnWindow (cofiberSequence D) 2 5 (14,139)
    (bottom D 14 139 B.T)

end KIP126.Computation
