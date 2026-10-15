module

public import Batteries.Tactic.OpenPrivate
public import KIP126.Def.Synthetic.Sphere.Homotopy.Proofs
public import KIP126.Def.Synthetic.Sphere.Homotopy.Predicates
public import Init.Data.String.Lemmas.Splits
public import KIP126.Def.SpectralSequence.Basic.Data
public import KIP126.Def.SpectralSequence.Convergence.Data
public import KIP126.Def.SpectralSequence.Basic.Proofs
public import KIP126.Def.SpectralSequence.FilteredComplex.Solutions.Proofs
public import KIP126.Def.SpectralSequence.FilteredComplex.SSData.Proofs
public import KIP126.Def.SpectralSequence.FilteredComplex.Data
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import KIP126.Main.ExtensionLaws.GeneralizedMahowald.Proofs
public import KIP126.Def.AdamsSynthetic.SectionSeven.AlphaOne
public import KIP126.Def.Synthetic.Detection.Vanishing.Proofs
public import KIP126.Def.ClassicalAdams.PageRepresentatives.Quotient.Proofs
public import KIP126.Def.ClassicalAdams.TowerVanishing.Proofs
public import KIP126.Def.SpectralSequence.Permanence.Proofs
public import KIP126.Def.Synthetic.QuotientTower.Proofs
public import KIP126.Def.Synthetic.AdamsFiltration.Convergence.Proofs
public import KIP126.Def.Synthetic.EInfty.Shift.Canonical.Predicates
public import KIP126.Def.ClassicalAdams.TowerNaturality.Isomorphism.Proofs
public import KIP126.Def.Synthetic.EInfty.Shift.Canonical.Data
public import KIP126.Def.StableHomotopy.Toda.Law.Proofs
public import KIP126.Def.ClassicalAdams.TowerNaturality.Page.Proofs
public import KIP126.Def.Synthetic.Context.Coherence.Proofs
public import Mathlib.CategoryTheory.Triangulated.Functor
public import KIP126.Main.Literature.AdamsSynthetic.Theorems
public import KIP126.Computation.LinCoordinates.Interpretation.SphereAndCofiber.Consequences
public import KIP126.Def.ClassicalAdams.SphereVanishing.Proofs
public import KIP126.Computation.LinCoordinates.Certificates.Model.Classes.Proofs
public import KIP126.Def.SpectralSequence.Basic.PageHomology.Data
public import KIP126.Def.SpectralSequence.Computation.Proofs
public import KIP126.Def.ClassicalAdams.PageRepresentatives.Proofs
public import KIP126.Def.ClassicalAdams.PageRepresentatives.Order.Proofs
public import KIP126.Def.Algebra.NestedQuotient.Proofs
public import KIP126.Def.Synthetic.Detection.Proofs
public import KIP126.Def.SpectralSequence.Basic.Category.Proofs
public import KIP126.Main.AdamsSynthetic
public import KIP126.Def.AdamsSynthetic.SectionSeven.Predicates

@[expose] public section

namespace KIP126.Main.SectionSeven
open CategoryTheory
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.SpectralSequence
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.AdamsSynthetic.SectionSeven
open KIP126.Literature.AdamsSynthetic KIP126.Main.AdamsSynthetic
noncomputable section

local notation "D" => adamsComparison

local notation "M" => standardMilnorCooperations

local notation "I" => computationTheorems

/-- This h2 is D's normalized lift of the very nu whose actual cofiber is
used by the computation, with its first-quotient h₂ identification
given by the same ν-cofiber comparison. -/
abbrev h2 := normalizedNu D literatureTheorems.applicability.nuCofiber.nu_exponent

abbrev eB := (I).interpretation.sphere 8 70 KIP126.Computation.Near126.B
abbrev eX := (I).interpretation.sphere 8 130 KIP126.Computation.Near126.X
abbrev eY := (I).interpretation.sphere 11 136 KIP126.Computation.Near126.Y
abbrev eH6B := Sphere.Internal.product standardFoundation.hf2 M
  (s := 1) (t := 64) (s' := 8) (t' := 70)
  (Sphere.Internal.hi standardFoundation.hf2 M 6) eB

end
end KIP126.Main.SectionSeven
