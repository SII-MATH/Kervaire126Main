module

import KIP126.Def.AdamsSynthetic

/-! Consumers supply structures explicitly. All imports are ordinary public
imports; no global instance, project axiom, or model construction is used. -/
open CategoryTheory KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.Core.SpectralSequence KIP126.AdamsSynthetic
open KIP126.Synthetic.SpectralSequence KIP126.Kervaire.Route
universe u v w
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

section Graded
variable {Syn : Type u} [SyntheticCategory.{u,v} Syn]
  (E : GradedLambdaEnrichment Syn)

example (X Y : Syn) (w : ℤ) (f : WeightHom X Y w) :
    letI := E.module X Y
    (Polynomial.X : Polynomial ℤ) • weightHomInclusion w f =
      weightHomInclusion (w-1) (weightHomLambda f) := E.lambda_smul X Y w f

example (X Y Z : Syn) (g : TotalWeightHom Y Z) (f : TotalWeightHom X Y) :
    letI := E.module X Y
    letI := E.module Y Z
    letI := E.module X Z
    E.compose X Y Z ((Polynomial.X : Polynomial ℤ) • g) f =
      E.compose X Y Z g ((Polynomial.X : Polynomial ℤ) • f) := by
  letI := E.module X Y
  letI := E.module Y Z
  letI := E.module X Z
  rw [E.compose_lambda_left, E.compose_lambda_right]

-- Associativity and units are consumed as derived theorems; the enrichment
-- input no longer repeats these consequences of actual shifted composition.
example (W X Y Z : Syn) (f : TotalWeightHom W X)
    (g : TotalWeightHom X Y) (h : TotalWeightHom Y Z) :
    E.compose W Y Z h (E.compose W X Y g f) =
      E.compose W X Z (E.compose X Y Z h g) f := E.assoc W X Y Z f g h

example (X Y : Syn) (f : TotalWeightHom X Y) :
    E.compose X Y Y (weightHomInclusion 0 (SyntheticCategory.biShift_zero.hom.app Y)) f = f :=
  E.left_unit X Y f

-- λ is a graded map, not an endomorphism of a fixed-weight Hom.
example (X Y : Syn) (w : ℤ) (_f : WeightHom X Y w) : True := by
  fail_if_success have : WeightHom X Y w := weightHomLambda _f
  trivial
end Graded

section Model
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w,v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  (D : Model C Syn)

example (W : NuInfinityWeightMaps D) (X : ClassicalObject) (s t w₁ w₂ : ℤ)
    (hw : w₁ ≤ w₂) (ht : w₂ ≤ t)
    (x : (D.classical.obj (X.obj D.auxiliary)).Page 2 (s,t))
    (z : ((D.family.obj (D.nu.functor.obj (X.obj D.auxiliary))).sequence.ssData (s,t,w₁)).eInfty)
    (h : HasInfinityRepresentative _ 2 (s,t,w₁) (nuWeightLabel D X s t w₁ (hw.trans ht) x) z) :
    HasInfinityRepresentative _ 2 (s,t,w₂) (nuWeightLabel D X s t w₂ ht x)
      (W.map X s t w₁ w₂ hw ht z) := W.representative X s t w₁ w₂ hw ht x z h

example (_D' : Model C Syn) (_W : NuInfinityWeightMaps D) : True := by
  fail_if_success have : NuInfinityWeightMaps _D' := _W
  trivial

variable (S : SyntheticAdamsESSShiftSystem D)

-- A full target coset, not merely a chosen representative, survives the shift.
example (n : ℕ) (X Y : SyntheticObject)
    (g : X.obj D.nu D.auxiliary ⟶ Y.obj D.nu D.auxiliary)
    (p : ℤ × ℤ) (s l : ℤ) {T : ModuleCat.{v} ℤ}
    (y z : T ⟶ (D.convergence Y).filtration.associatedGraded (s+l) p) :
    z ∈ FilteredMapExtension.TargetCoset (D.convergentMap X Y g).filteredMap p s l y ↔
      z ≫ (((S.lambdaBoundary n).filtered Y p).gradedIso (s+l)).hom ∈
        FilteredMapExtension.TargetCoset
          (D.convergentMap (.shift (1,-(n:ℤ)) X) (.shift (1,-(n:ℤ)) Y)
            ((SyntheticCategory.biShift (1,-(n:ℤ))).map g)).filteredMap
          (p+(1,-(n:ℤ))) s l
          (y ≫ (((S.lambdaBoundary n).filtered Y p).gradedIso (s+l)).hom) :=
  ((S.lambdaBoundary n).transport X Y g p).targetCoset_iff y z

example (n : ℕ) (X Y : SyntheticObject)
    (g : X.obj D.nu D.auxiliary ⟶ Y.obj D.nu D.auxiliary)
    (p : ℤ × ℤ) (s l : ℤ) (T : ModuleCat.{v} ℤ) :
    FilteredMapTransport.NoCrossing (D.convergentMap X Y g).filteredMap p s l T ↔
      FilteredMapTransport.NoCrossing
        (D.convergentMap (.shift (1,-(n:ℤ)) X) (.shift (1,-(n:ℤ)) Y)
          ((SyntheticCategory.biShift (1,-(n:ℤ))).map g)).filteredMap
        (p+(1,-(n:ℤ))) s l T :=
  ((S.lambdaBoundary n).transport X Y g p).noCrossing_iff s l T

-- The finite-page label and its common infinite representative move together.
set_option linter.defProp false in
def representativeShiftConsumer (n : ℕ) (X : SyntheticObject) (r : ℤ) (hr : 2 ≤ r)
    (p : ℤ × ℤ) (s : ℤ)
    (x : (D.family.obj (X.obj D.nu D.auxiliary)).Page r (s,p.1+s,p.2))
    (z : ((D.family.obj (X.obj D.nu D.auxiliary)).sequence.ssData (s,p.1+s,p.2)).eInfty)
    (h : HasInfinityRepresentative _ r (s,p.1+s,p.2) x z) :=
  ((S.lambdaBoundary n).representative_iff X r hr p s x z).mp h

-- Actual finite and infinite witnesses can be transported directly. The
-- finite length/page bounds remain in W, while neither consumer assumes
-- a bounded filtration on the untruncated synthetic object.
set_option linter.defProp false in
def finiteShiftConsumer (n : ℕ) (X Y : ClassicalObject)
    (f : X.obj D.auxiliary ⟶ Y.obj D.auxiliary) (r : ℕ) (l s t : ℤ) (x y)
    (W : FiniteExtensionWitness D X Y f r l s t x y) :=
  ((S.lambdaBoundary n).towerExtensionEquation_iff
    (.quotient (r-1) (extensionSourceObject D X Y f))
    (.quotient (r-1) (.nu Y)) (finiteExtensionMap D X Y f (r-1))
    (t-s,t+normalizedExponent D.classicalTower f) s l W.source W.target).mp W.equation

set_option linter.defProp false in
def infiniteShiftConsumer (n : ℕ) (X Y : ClassicalObject)
    (f : X.obj D.auxiliary ⟶ Y.obj D.auxiliary) (l s t : ℤ) (x y)
    (W : InfiniteExtensionWitness D X Y f l s t x y) :=
  ((S.lambdaBoundary n).towerExtensionEquation_iff
    (extensionSourceObject D X Y f) (.nu Y) (D.normalizedMap X Y f).map
    (t-s,t+normalizedExponent D.classicalTower f) s l W.source W.target).mp W.equation

example (_D' : Model C Syn) (_S : SyntheticAdamsESSShiftSystem D) : True := by
  fail_if_success have : SyntheticAdamsESSShiftSystem _D' := _S
  trivial
end Model
end
