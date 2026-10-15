module

public import KIP126.Def.HigherAlgebra.Operad.EnrichedAlgebra.Data

@[expose] public section

/-! Properties needed to form the category and its unit-forgetting functor.
The identities are derived from the enriched algebra and operad axioms. -/

namespace KIP126.HigherAlgebra.Operad.EnrichedAlgebra

open CategoryTheory MonoidalCategory EnrichedTensor

universe u v w

variable {M : Type u} [Category.{v} M] [MonoidalCategory M]
  [EnrichedOrdinaryCategory TopCat.{v} M]
  {P : Presentation M} {hP : TensorLaws P} {O : TopologicalOperad.{w}}

theorem identity_commutes (A : EnrichedAlgebra P hP O)
    (I : FintypeCat.{0}) (x : O.Op I) :
    A.operation I x ≫ 𝟙 A.carrier =
      P.map I (fun _ => 𝟙 A.carrier) ≫ A.operation I x := by
  rw [hP.map_id, Category.comp_id, Category.id_comp]

theorem composition_commutes {A B D : EnrichedAlgebra P hP O}
    (f : Hom A B) (g : Hom B D) (I : FintypeCat.{0}) (x : O.Op I) :
    A.operation I x ≫ (f.hom ≫ g.hom) =
      P.map I (fun _ => f.hom ≫ g.hom) ≫ D.operation I x := by
  rw [hP.map_comp, ← Category.assoc, f.commutes, Category.assoc,
    g.commutes, Category.assoc]

/-- The nullary case of the algebra-morphism equation, transported through
the actual empty tensor comparison, fixes the same unit arrow. -/
theorem unit_naturality (o : O.Op empty) {A B : EnrichedAlgebra P hP O}
    (f : Hom A B) : unit o A ≫ f.hom = unit o B := by
  dsimp [unit]
  rw [Category.assoc, f.commutes]
  have h := hP.map_empty (fun _ => A.carrier) (fun _ => B.carrier) (fun _ => f.hom)
  have hm : P.map empty (fun _ => f.hom) =
      (P.emptyIso (fun _ => A.carrier)).hom ≫
        (P.emptyIso (fun _ => B.carrier)).inv := by
    rw [← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [hm]
  simp

end KIP126.HigherAlgebra.Operad.EnrichedAlgebra
