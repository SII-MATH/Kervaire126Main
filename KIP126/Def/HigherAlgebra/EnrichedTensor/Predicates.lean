module

public import KIP126.Def.HigherAlgebra.EnrichedTensor.Monoidal.Data

@[expose] public section

/-!
Explicit equations for finite tensor presentations and their endomorphism
operations. These conditions are not claims that an arbitrary enriched model
admits such a presentation. Relabelling and substitution always refer to the
operations already computed from actual tensor maps in `Data`.
-/

namespace KIP126.HigherAlgebra.EnrichedTensor

open CategoryTheory MonoidalCategory Operad

universe u v

variable {M : Type u} [Category.{v} M] [MonoidalCategory M]
  [EnrichedOrdinaryCategory TopCat.{v} M]

/-- Functoriality, comparison naturality and coloured substitution coherence
for the same finite tensor maps. No extra operation or free proposition is
chosen by this record. The low arities bind to the existing monoidal tensor. -/
structure TensorLaws (P : Presentation M) : Prop where
  map_id : ∀ (I : FintypeCat.{0}) (A : I → M),
    P.map I (fun i => 𝟙 (A i)) = 𝟙 (P.tensorObj I A)
  map_comp : ∀ (I : FintypeCat.{0}) (A B D : I → M)
    (f : (i : I) → A i ⟶ B i) (g : (i : I) → B i ⟶ D i),
    P.map I (fun i => f i ≫ g i) = P.map I f ≫ P.map I g
  map_empty : ∀ (A B : empty → M) (f : (i : empty) → A i ⟶ B i),
    P.map empty f ≫ (P.emptyIso B).hom = (P.emptyIso A).hom
  map_one : ∀ (A B : Arity.one → M) (f : (i : Arity.one) → A i ⟶ B i),
    P.map Arity.one f ≫ (P.oneIso B).hom = (P.oneIso A).hom ≫ f PUnit.unit
  map_binary : ∀ (A B : two → M) (f : (i : two) → A i ⟶ B i),
    P.map two f ≫ (P.binaryIso B).hom =
      (P.binaryIso A).hom ≫ (f false ⊗ₘ f true)
  relabel_id : ∀ (I : FintypeCat.{0}) (A : I → M),
    (P.tensorRelabel (Equiv.refl I) A).hom = 𝟙 (P.tensorObj I A)
  relabel_comp : ∀ {I J K : FintypeCat.{0}} (e : I ≃ J) (f : J ≃ K) (A : K → M),
    (P.tensorRelabel (e.trans f) A).hom =
      (P.tensorRelabel e (fun j => A (f j))).hom ≫ (P.tensorRelabel f A).hom
  relabel_naturality : ∀ {I J : FintypeCat.{0}} (e : I ≃ J) (A B : J → M)
    (f : (j : J) → A j ⟶ B j),
    P.map I (fun i => f (e i)) ≫ (P.tensorRelabel e B).hom =
      (P.tensorRelabel e A).hom ≫ P.map J f
  flatten_naturality : ∀ (I : FintypeCat.{0}) (J : I → FintypeCat.{0})
    (A B : (i : I) → J i → M) (f : (i : I) → (j : J i) → A i j ⟶ B i j),
    P.map (Arity.sum I J) (fun ij => f ij.1 ij.2) ≫ (P.flatten I J B).hom =
      (P.flatten I J A).hom ≫ P.map I (fun i => P.map (J i) (f i))
  flatten_left_unit : ∀ (I : FintypeCat.{0}) (A : I → M),
    (P.flatten Arity.one (fun _ => I) (fun _ => A)).hom ≫
      (P.oneIso (fun _ => P.tensorObj I A)).hom =
      (P.tensorRelabel (Arity.leftUnit I) A).hom
  flatten_right_unit : ∀ (I : FintypeCat.{0}) (A : I → M),
    (P.flatten I (fun _ => Arity.one) (fun i _ => A i)).hom ≫
      P.map I (fun i => (P.oneIso (fun _ => A i)).hom) =
      (P.tensorRelabel (Arity.rightUnit I) A).hom
  flatten_assoc : ∀ (I : FintypeCat.{0}) (J : I → FintypeCat.{0})
    (K : (i : I) → J i → FintypeCat.{0}) (A : (i : I) → (j : J i) → K i j → M),
    (P.flatten (Arity.sum I J) (fun ij => K ij.1 ij.2)
      (fun ij => A ij.1 ij.2)).hom ≫
      (P.flatten I J (fun i j => P.tensorObj (K i j) (A i j))).hom =
      (P.tensorRelabel (Arity.assoc I J K) (fun ik => A ik.1 ik.2.1 ik.2.2)).hom ≫
        (P.flatten I (fun i => Arity.sum (J i) (K i))
          (fun i jk => A i jk.1 jk.2)).hom ≫
        P.map I (fun i => (P.flatten (J i) (K i) (A i)).hom)
  flatten_outer : ∀ {I I' : FintypeCat.{0}} (e : I ≃ I')
    (J : I' → FintypeCat.{0}) (A : (i : I') → J i → M),
    (P.flatten I (fun i => J (e i)) (fun i => A (e i))).hom ≫
      (P.tensorRelabel e (fun i => P.tensorObj (J i) (A i))).hom =
      (P.tensorRelabel (Arity.outer e J) (fun ij => A ij.1 ij.2)).hom ≫
        (P.flatten I' J A).hom
  flatten_inner : ∀ (I : FintypeCat.{0}) (J J' : I → FintypeCat.{0})
    (e : (i : I) → J i ≃ J' i) (A : (i : I) → J' i → M),
    (P.flatten I J (fun i j => A i (e i j))).hom ≫
      P.map I (fun i => (P.tensorRelabel (e i) (A i)).hom) =
      (P.tensorRelabel (Arity.inner I e) (fun ij => A ij.1 ij.2)).hom ≫
        (P.flatten I J' A).hom

/-- The finite tensor comparisons recover the unitors, associator and braiding
of the *existing* symmetric monoidal category. This prevents the presentation
from silently using different coherence on the same binary tensor functor. -/
structure SymmetricTensorLaws [SymmetricCategory M] (P : Presentation M) : Prop
    extends TensorLaws P where
  binary_swap : ∀ (A : two → M),
    (P.tensorRelabel (I := two) (J := two) Equiv.boolNot A).hom ≫ (P.binaryIso A).hom =
      (P.binaryIso (fun i => A (Equiv.boolNot i))).hom ≫ (β_ (A true) (A false)).hom
  left_unitor : ∀ (X : M),
    P.leftUnitCollapse X =
      (P.tensorRelabel leftUnitLabels (fun _ => X)).hom ≫ (P.oneIso (fun _ => X)).hom
  right_unitor : ∀ (X : M),
    P.rightUnitCollapse X =
      (P.tensorRelabel rightUnitLabels (fun _ => X)).hom ≫ (P.oneIso (fun _ => X)).hom
  associator : ∀ (X Y Z : M),
    P.ternaryLeftCollapse X Y Z ≫ (α_ X Y Z).hom =
      P.ternaryRelabel X Y Z ≫ P.ternaryRightCollapse X Y Z

/-- The complete operad equations for the endomorphism operations calculated
from `P`. This predicate contains only equality conditions; it does not supply
an unrelated operad. Its consequence from the coloured tensor equations is
stated in `Proofs`, rather than installed as an additional model assumption. -/
structure EndomorphismLaws (P : Presentation M) (X : M) : Prop where
  relabel_id : ∀ (I : FintypeCat.{0}) (x : P.Op X I),
    P.relabel X (Equiv.refl I) x = x
  relabel_comp : ∀ {I J K : FintypeCat.{0}} (e : I ≃ J) (f : J ≃ K) (x : P.Op X I),
    P.relabel X (e.trans f) x = P.relabel X f (P.relabel X e x)
  left_unit : ∀ (I : FintypeCat.{0}) (x : P.Op X I),
    P.relabel X (Arity.leftUnit I)
      (P.compose X Arity.one (fun _ => I) (P.unit X, fun _ => x)) = x
  right_unit : ∀ (I : FintypeCat.{0}) (x : P.Op X I),
    P.relabel X (Arity.rightUnit I)
      (P.compose X I (fun _ => Arity.one) (x, fun _ => P.unit X)) = x
  associativity : ∀ (I : FintypeCat.{0}) (J : I → FintypeCat.{0})
    (K : (i : I) → J i → FintypeCat.{0}) (x : P.Op X I)
    (y : (i : I) → P.Op X (J i)) (z : (i : I) → (j : J i) → P.Op X (K i j)),
    P.relabel X (Arity.assoc I J K)
      (P.compose X (Arity.sum I J) (fun ij => K ij.1 ij.2)
        (P.compose X I J (x, y), fun ij => z ij.1 ij.2)) =
      P.compose X I (fun i => Arity.sum (J i) (K i))
        (x, fun i => P.compose X (J i) (K i) (y i, z i))
  outer_equivariance : ∀ {I I' : FintypeCat.{0}} (e : I ≃ I')
    (J : I' → FintypeCat.{0}) (x : P.Op X I) (y : (i : I') → P.Op X (J i)),
    P.relabel X (Arity.outer e J)
      (P.compose X I (fun i => J (e i)) (x, fun i => y (e i))) =
      P.compose X I' J (P.relabel X e x, y)
  inner_equivariance : ∀ (I : FintypeCat.{0}) (J J' : I → FintypeCat.{0})
    (e : (i : I) → J i ≃ J' i) (x : P.Op X I) (y : (i : I) → P.Op X (J i)),
    P.relabel X (Arity.inner I e) (P.compose X I J (x, y)) =
      P.compose X I J' (x, fun i => P.relabel X (e i) (y i))

end KIP126.HigherAlgebra.EnrichedTensor
