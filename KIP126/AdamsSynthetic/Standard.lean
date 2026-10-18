module

public import KIP126.AdamsSynthetic.Standard.Operations
public import KIP126.AdamsSynthetic.Standard.FirstQuotientCompatibility
public import KIP126.AdamsSynthetic.Standard.Realization
public import KIP126.AdamsSynthetic.Standard.Separation

/-! The fixed Adams/synthetic system. Consumers call these objects and
theorems directly, while real mathematical hypotheses remain in each type. -/

@[expose] section
namespace KIP126.AdamsSynthetic.Standard
open CategoryTheory KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.Classical.Adams KIP126.Core.SpectralSequence KIP126.Kervaire.Route
noncomputable section

public abbrev sphere : Spectrum := SphereSpectrum
public abbrev syntheticSphere : SyntheticSpectrum := S_0_0
public abbrev sphereSequence := classical.sphere
public abbrev syntheticSphereSequence := family.sphere
public abbrev standardH6 := standardClasses.standardH6
public abbrev standardH6Square := standardClasses.standardH6Square

public theorem standardH6Square_eq_product :
    standardH6Square = sphereAlgebra.product (1,64) (1,64) standardH6 standardH6 :=
  standardClasses.standardH6Square_eq_product

/-- The final goal has no result-package premise; it is not proved here. -/
public def H6SquarePermanent : Prop := NonzeroSurvival sphereSequence (2,128) standardH6Square

public theorem firstPage (X : Spectrum) : (classical.obj X).r₀ = 2 := classical.firstPage X
public theorem differentialDegree (X : Spectrum) (r : ℤ) :
    (classical.obj X).diffDeg r = (r,r-1) := classical.differentialDegree X r

public theorem classical_map_comp {X Y Z : Spectrum} (f : X ⟶ Y) (g : Y ⟶ Z) :
    classical.map (f ≫ g) = classical.map f ≫ classical.map g := classical.map_comp f g

public def realization := recovery.realization
public def spectralYoneda := recovery.spectralYoneda
public def spectralYonedaFullyFaithful : spectralYoneda.FullyFaithful :=
  recovery.fullyFaithfulSpectralYoneda
public def realizationAdjunction : realization ⊣ spectralYoneda := recovery.adjunction
public def nuRealizationIso : nu.functor ⋙ realization ≅ 𝟭 Spectrum := recovery.nuRealizationIso

/-- Canonical tower comparison of the actual chosen map, without an input package. -/
public def convergentMap (X Y : SyntheticObject)
    (f : X.obj nu auxiliary ⟶ Y.obj nu auxiliary) :
    ConvergentMap family f (convergence X).toConvergence (convergence Y).toConvergence :=
  model.convergentMap X Y f

end
end KIP126.AdamsSynthetic.Standard
