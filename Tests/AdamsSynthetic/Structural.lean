module

import KIP126.Def.AdamsSynthetic

/-! Ordinary-import consumers of the fixed project background.
Only actual objects, maps, classes and mathematical hypotheses are parameters. -/
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.Classical.Adams KIP126.Synthetic.SpectralSequence
open KIP126.Core.SpectralSequence KIP126.AdamsSynthetic KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
example (X Y : SyntheticSpectrum) (w : ℤ) (f : WeightHom X Y w) :
    letI := gradedEnrichment.module X Y
    (Polynomial.X : Polynomial ℤ) • weightHomInclusion w f =
      weightHomInclusion (w-1) (weightHomLambda f) := gradedEnrichment.lambda_smul X Y w f

example (X Y Z : SyntheticSpectrum) (g : TotalWeightHom Y Z) (f : TotalWeightHom X Y) :
    letI := gradedEnrichment.module X Y
    letI := gradedEnrichment.module Y Z
    letI := gradedEnrichment.module X Z
    gradedEnrichment.compose X Y Z ((Polynomial.X : Polynomial ℤ) • g) f =
      gradedEnrichment.compose X Y Z g ((Polynomial.X : Polynomial ℤ) • f) := by
  letI := gradedEnrichment.module X Y
  letI := gradedEnrichment.module Y Z
  letI := gradedEnrichment.module X Z
  rw [gradedEnrichment.compose_lambda_left, gradedEnrichment.compose_lambda_right]

-- Associativity and units are consumed as derived theorems; the enrichment
-- input no longer repeats these consequences of actual shifted composition.
example (W X Y Z : SyntheticSpectrum) (f : TotalWeightHom W X)
    (g : TotalWeightHom X Y) (h : TotalWeightHom Y Z) :
    gradedEnrichment.compose W Y Z h (gradedEnrichment.compose W X Y g f) =
      gradedEnrichment.compose W X Z (gradedEnrichment.compose X Y Z h g) f := gradedEnrichment.assoc W X Y Z f g h

example (X Y : SyntheticSpectrum) (f : TotalWeightHom X Y) :
    gradedEnrichment.compose X Y Y (weightHomInclusion 0 (SyntheticCategory.biShift_zero.hom.app Y)) f = f :=
  gradedEnrichment.left_unit X Y f

-- λ is a graded map, not an endomorphism of a fixed-weight Hom.
example (X Y : SyntheticSpectrum) (w : ℤ) (_f : WeightHom X Y w) : True := by
  fail_if_success have : WeightHom X Y w := weightHomLambda _f
  trivial
example (X : ClassicalObject) (s t w₁ w₂ : ℤ)
    (hw : w₁ ≤ w₂) (ht : w₂ ≤ t)
    (x : (model.classical.obj (X.obj model.auxiliary)).Page 2 (s,t))
    (z : ((model.family.obj (model.nu.functor.obj (X.obj model.auxiliary))).sequence.ssData (s,t,w₂)).eInfty)
    (h : HasInfinityRepresentative _ 2 (s,t,w₂) (nuWeightLabel model X s t w₂ ht x) z) :
    HasInfinityRepresentative _ 2 (s,t,w₁) (nuWeightLabel model X s t w₁ (hw.trans ht) x)
      (weightMaps.map X s t w₁ w₂ hw ht z) := weightMaps.representative X s t w₁ w₂ hw ht x z h

-- A full target coset, not merely a chosen representative, survives the shift.
example (n : ℕ) (X Y : SyntheticObject)
    (g : X.obj model.nu model.auxiliary ⟶ Y.obj model.nu model.auxiliary)
    (p : ℤ × ℤ) (s l : ℤ) {T : ModuleCat.{0} ℤ}
    (y z : T ⟶ (model.convergence Y).filtration.associatedGraded (s+l) p) :
    z ∈ FilteredMapExtension.TargetCoset (model.convergentMap X Y g).filteredMap p s l y ↔
      z ≫ (((essShiftSystem.lambdaBoundary n).filtered Y p).gradedIso (s+l)).hom ∈
        FilteredMapExtension.TargetCoset
          (model.convergentMap (.shift (1,-(n:ℤ)) X) (.shift (1,-(n:ℤ)) Y)
            ((SyntheticCategory.biShift (1,-(n:ℤ))).map g)).filteredMap
          (p+(1,-(n:ℤ))) s l
          (y ≫ (((essShiftSystem.lambdaBoundary n).filtered Y p).gradedIso (s+l)).hom) :=
  ((essShiftSystem.lambdaBoundary n).transport X Y g p).targetCoset_iff y z

example (n : ℕ) (X Y : SyntheticObject)
    (g : X.obj model.nu model.auxiliary ⟶ Y.obj model.nu model.auxiliary)
    (p : ℤ × ℤ) (s l : ℤ) (T : ModuleCat.{0} ℤ) :
    FilteredMapTransport.NoCrossing (model.convergentMap X Y g).filteredMap p s l T ↔
      FilteredMapTransport.NoCrossing
        (model.convergentMap (.shift (1,-(n:ℤ)) X) (.shift (1,-(n:ℤ)) Y)
          ((SyntheticCategory.biShift (1,-(n:ℤ))).map g)).filteredMap
        (p+(1,-(n:ℤ))) s l T :=
  ((essShiftSystem.lambdaBoundary n).transport X Y g p).noCrossing_iff s l T

-- The finite-page label and its common infinite representative move together.
set_option linter.defProp false in
def representativeShiftConsumer (n : ℕ) (X : SyntheticObject) (r : ℤ) (hr : 2 ≤ r)
    (p : ℤ × ℤ) (s : ℤ)
    (x : (model.family.obj (X.obj model.nu model.auxiliary)).Page r (s,p.1+s,p.2))
    (z : ((model.family.obj (X.obj model.nu model.auxiliary)).sequence.ssData (s,p.1+s,p.2)).eInfty)
    (h : HasInfinityRepresentative _ r (s,p.1+s,p.2) x z) :=
  ((essShiftSystem.lambdaBoundary n).representative_iff X r hr p s x z).mp h

-- Actual finite and infinite witnesses can be transported directly. The
-- finite length/page bounds remain in W, while neither consumer assumes
-- a bounded filtration on the untruncated synthetic object.
set_option linter.defProp false in
def finiteShiftConsumer (n : ℕ) (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary) (r : ℕ) (l s t : ℤ) (x y)
    (W : FiniteExtensionWitness model X Y f r l s t x y) :=
  ((essShiftSystem.lambdaBoundary n).towerExtensionEquation_iff
    (.quotient (r-1) (extensionSourceObject model X Y f))
    (.quotient (r-1) (.nu Y)) (finiteExtensionMap model X Y f (r-1))
    (t-s,t+normalizedExponent model.classicalTower f) s l W.source W.target).mp W.equation

set_option linter.defProp false in
def infiniteShiftConsumer (n : ℕ) (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary) (l s t : ℤ) (x y)
    (W : InfiniteExtensionWitness model X Y f l s t x y) :=
  ((essShiftSystem.lambdaBoundary n).towerExtensionEquation_iff
    (extensionSourceObject model X Y f) (.nu Y) (model.normalizedMap X Y f).map
    (t-s,t+normalizedExponent model.classicalTower f) s l W.source W.target).mp W.equation


end
