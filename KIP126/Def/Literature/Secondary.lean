module

public import KIP126.Def.Literature.Classical
public import KIP126.Def.Literature.Toda
public import KIP126.Def.Literature.May
public import KIP126.Def.Literature.Moss

/-! Correlated secondary-operation input for the one supplied model. The
general Moss contract remains available, while this delivery fixes its route
scope to the actual sphere and its mapping composition to the already chosen
sphere E₂ algebra. No second η or freely selected object-scope predicate is
introduced. -/

@[expose] section
namespace KIP126.Literature
open CategoryTheory
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.AdamsSynthetic
open KIP126.Kervaire.Route
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w,v} Syn]
  [HasFunctorialCofiber (C := Syn)] (D : Model C Syn)

/-- Model-side mapping, tensor and Toda data. The sphere mapping spectrum
uses D's actual tower; its E₂ product and unit agree with D's existing algebra. -/
public structure SecondaryBindings where
  closed : ClosedSymmetricTensorTriangulated C
  mapping : MappingSpectrumSystem closed D.classicalTower
    (fun X : C => X = SphereSpectrum)
  moss : Moss.Context mapping
  sphereComposition : MappingSphereCompatibility moss.composition D.sphereAlgebra rfl
  may : Route.MayContext Syn
  toda : Route.TodaSourceData (Syn := Syn)

/-- Source results are separate from construction of the bound model data.
The Toda statements use precisely the η in the existing classical binding. -/
public structure SecondaryResults (B : ClassicalBindings D) (Q : SecondaryBindings D) : Prop where
  moss : Moss.SourceResults Q.mapping Q.moss
  may : Route.MaySourceResults Syn Q.may
  toda : Route.TodaSourceResults D B.eta Q.toda

end KIP126.Literature
