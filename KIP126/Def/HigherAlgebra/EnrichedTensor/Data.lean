module

public import KIP126.Def.HigherAlgebra.Operad.Topological.Data
public import Mathlib.CategoryTheory.Enriched.HomCongr
public import Mathlib.Topology.Category.TopCat.Monoidal
public import Mathlib.Logic.Equiv.Bool

@[expose] public section

/-!
Finite tensor presentations on a point-set category with its actual topological
enrichment. The tensor in the model category is not a cartesian product of
spaces. Ordinary product topologies occur only in the enrichment base.

Joint continuity of every finite tensor of mapping spaces is explicit input.
In particular this file supplies no compactly generated or spectral model
instance, and does not identify k-products with ordinary topological products.
The equations imposed on a presentation are in `Predicates`.
-/

namespace KIP126.HigherAlgebra.EnrichedTensor

open CategoryTheory MonoidalCategory
open Operad

universe u v

variable {M : Type u} [Category.{v} M]
  [EnrichedOrdinaryCategory TopCat.{v} M]

/-- The actual enriched mapping space in the chosen point-set category. -/
abbrev MappingSpace (X Y : M) : TopCat.{v} := X ⟶[TopCat.{v}] Y

/-- An ordinary morphism regarded as the corresponding point of its enriched
mapping space, using the given enriched ordinary category structure. -/
def point {X Y : M} (f : X ⟶ Y) : MappingSpace X Y :=
  (eHomEquiv TopCat.{v} f) PUnit.unit

/-- A point of the actual enriched mapping space, regarded as an ordinary
morphism. This uses the constant map from the monoidal unit of `TopCat`. -/
def arrow {X Y : M} (f : MappingSpace X Y) : X ⟶ Y :=
  (eHomEquiv TopCat.{v}).symm (TopCat.ofHom (ContinuousMap.const _ f))

/-- The empty set of inputs, including genuine nullary operations. -/
abbrev empty : FintypeCat.{0} := FintypeCat.of PEmpty

/-- Two inputs, used to bind the presentation to the existing binary tensor. -/
abbrev two : FintypeCat.{0} := FintypeCat.of Bool

variable [MonoidalCategory M]

/-- Chosen finite tensor objects and actual continuous tensor maps. All
comparisons are isomorphisms in the same model category. Their compatibility
conditions are explicit equations in `TensorLaws` and `EndomorphismLaws`;
no existence of such a presentation on a synthetic model is asserted here. -/
structure Presentation (M : Type u) [Category.{v} M] [MonoidalCategory M]
    [EnrichedOrdinaryCategory TopCat.{v} M] where
  tensorObj : (I : FintypeCat.{0}) → (I → M) → M
  tensorMap : (I : FintypeCat.{0}) → (A B : I → M) →
    C(((i : I) → MappingSpace (A i) (B i)),
      MappingSpace (tensorObj I A) (tensorObj I B))
  emptyIso : (A : empty → M) → tensorObj empty A ≅ 𝟙_ M
  oneIso : (A : Arity.one → M) → tensorObj Arity.one A ≅ A PUnit.unit
  binaryIso : (A : two → M) → tensorObj two A ≅ A false ⊗ A true
  tensorRelabel : {I J : FintypeCat.{0}} → (e : I ≃ J) → (A : J → M) →
    tensorObj I (fun i => A (e i)) ≅ tensorObj J A
  flatten : (I : FintypeCat.{0}) → (J : I → FintypeCat.{0}) →
    (A : (i : I) → J i → M) →
    tensorObj (Arity.sum I J) (fun ij => A ij.1 ij.2) ≅
      tensorObj I (fun i => tensorObj (J i) (A i))

namespace Presentation

variable (P : Presentation M)

/-- The finite tensor map on ordinary morphisms, computed from the specified
continuous tensor map and the actual enriched-to-ordinary correspondence. -/
def map (I : FintypeCat.{0}) {A B : I → M} (f : (i : I) → A i ⟶ B i) :
    P.tensorObj I A ⟶ P.tensorObj I B :=
  arrow (P.tensorMap I A B (fun i => point (f i)))

/-- Endomorphism operations have source the actual finite tensor of `X`.
For empty inputs this identifies with maps from the monoidal unit, not with
points of an underlying space of `X`. -/
abbrev Op (X : M) (I : FintypeCat.{0}) : TopCat.{v} :=
  MappingSpace (P.tensorObj I (fun _ => X)) X

/-- Covariant relabelling is precomposition by the inverse tensor comparison. -/
def relabel (X : M) {I J : FintypeCat.{0}} (e : I ≃ J) :
    P.Op X I ≃ₜ P.Op X J :=
  TopCat.homeoOfIso (Iso.eHomCongr TopCat.{v}
    (P.tensorRelabel e (fun _ => X)) (Iso.refl X))

/-- The singleton identity is the actual singleton tensor comparison. -/
def unit (X : M) : P.Op X Arity.one :=
  point (P.oneIso (fun _ => X)).hom

/-- Substitution is precisely flattening, tensoring the inner maps, then
composing with the outer map. Both compositions use the given enrichment;
all joint continuity comes from that enrichment and `tensorMap`. -/
def compose (X : M) (I : FintypeCat.{0}) (J : I → FintypeCat.{0}) :
    C(P.Op X I × ((i : I) → P.Op X (J i)), P.Op X (Arity.sum I J)) :=
  (eHomWhiskerRight TopCat.{v} (P.flatten I J (fun _ _ => X)).hom X).hom.comp
    ((eComp TopCat.{v} _ _ X).hom.comp
      (((P.tensorMap I (fun i => P.tensorObj (J i) (fun _ => X)) (fun _ => X)).comp
        ContinuousMap.snd).prodMk ContinuousMap.fst))

end Presentation
end KIP126.HigherAlgebra.EnrichedTensor
